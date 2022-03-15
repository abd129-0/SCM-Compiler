#use "reader.ml";;

type expr =
  | ScmConst of sexpr
  | ScmVar of string
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmSet of expr * expr
  | ScmDef of expr * expr
  | ScmOr of expr list
  | ScmLambdaSimple of string list * expr
  | ScmLambdaOpt of string list * string * expr
  | ScmApplic of expr * (expr list);;

exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;

let rec list_to_proper_list = function
| [] -> ScmNil
| hd::[] -> ScmPair (hd, ScmNil)
| hd::tl -> ScmPair (hd, list_to_proper_list tl);;

let rec list_to_improper_list = function
| [] -> raise X_proper_list_error
| hd::[] -> hd
| hd::tl -> ScmPair (hd, list_to_improper_list tl);;

let rec scm_append scm_list sexpr =
match scm_list with
| ScmNil -> sexpr
| ScmPair (car, cdr) -> ScmPair (car, scm_append cdr sexpr)
| _ -> raise (X_syntax_error (scm_list, "Append expects a proper list"))

let rec scm_map f sexpr =
match sexpr with
| ScmNil -> ScmNil
| ScmPair (car, cdr) -> ScmPair (f car, scm_map f cdr)
| _ -> raise (X_syntax_error (sexpr, "Map expects a list"));;

let rec scm_zip f sexpr1 sexpr2 =
match sexpr1, sexpr2 with
| ScmNil, ScmNil -> ScmNil
| ScmPair (car1, cdr1), ScmPair (car2, cdr2) -> ScmPair (f car1 car2, scm_zip f cdr1 cdr2)
| _, _ ->
    let sepxrs = list_to_proper_list [ScmSymbol "sexpr1:"; sexpr1; ScmSymbol "sexpr2:"; sexpr2] in
    raise (X_syntax_error (sepxrs, "Zip expects 2 lists of equal length"));;

let rec scm_list_to_list = function
| ScmPair (hd, tl) -> hd::(scm_list_to_list tl)
| ScmNil -> []
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec scm_is_list = function
| ScmPair (hd, tl) -> scm_is_list tl
| ScmNil -> true
| _ -> false

let rec scm_list_length = function
| ScmPair (hd, tl) -> 1 + (scm_list_length tl)
| ScmNil -> 0
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec untag expr =
let untag_vars vars = List.map (fun s -> ScmSymbol s) vars in
let untag_tagged_list tag exprs = list_to_proper_list (ScmSymbol tag::(List.map untag exprs)) in

let untag_lambda_opt vars var body =
let vars = match vars with
| [] -> ScmSymbol var
| _ -> list_to_improper_list (untag_vars (vars@[var])) in
list_to_proper_list ([ScmSymbol "lambda"; vars]@body) in

match expr with
| (ScmConst (ScmSymbol(_) as sexpr)
    | ScmConst (ScmNil as sexpr)
    | ScmConst (ScmPair (_, _) as sexpr)) -> list_to_proper_list [ScmSymbol "quote"; sexpr]
| ScmConst s -> s
| ScmVar (name) -> ScmSymbol(name)
| ScmIf (test, dit, ScmConst (ScmVoid)) -> untag_tagged_list "if" [test; dit]
| ScmIf (test, dit, dif) -> untag_tagged_list "if" [test; dit; dif]
| ScmSeq(exprs) -> untag_tagged_list "begin" exprs
| ScmSet (var, value) -> untag_tagged_list "set!" [var; value]
| ScmDef (var, value) -> untag_tagged_list "define" [var; value]
| ScmOr (exprs) -> untag_tagged_list "or" exprs
| ScmLambdaSimple (vars, ScmSeq(body)) ->
    let vars = list_to_proper_list (untag_vars vars) in
    let body = List.map untag body in
    list_to_proper_list ([ScmSymbol "lambda"; vars]@body)
| ScmLambdaSimple (vars, body) ->
    let vars = list_to_proper_list (untag_vars vars) in
    list_to_proper_list ([ScmSymbol "lambda"; vars; untag body])
| ScmLambdaOpt (vars, var, ScmSeq(body)) ->
    let body = List.map untag body in
    untag_lambda_opt vars var body
| ScmLambdaOpt (vars, var, body) ->
    let body = [untag body] in
    untag_lambda_opt vars var body
| ScmApplic(procedure, args) -> list_to_proper_list (List.map untag (procedure::args));;


let rec string_of_expr expr =
string_of_sexpr (untag expr)

let scm_number_eq n1 n2 =
match n1, n2 with
| ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
        numerator1 = numerator2 && denominator1 = denominator2
| ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
| _, _ -> false

let rec sexpr_eq s1 s2 =
match s1, s2 with
| (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
| ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
| ScmChar(char1), ScmChar(char2) -> char1 = char2
| ScmString(string1), ScmString(string2) -> String.equal string1 string2
| ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
| ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
| ScmVector(sexprs1), ScmVector(sexprs2) -> List.for_all2 sexpr_eq sexprs1 sexprs2
| ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
| _, _ -> false

let rec expr_eq e1 e2 =
  match e1, e2 with
  | ScmConst (sexpr1), ScmConst (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar (var1), ScmVar (var2) -> String.equal var1 var2
  | ScmIf (test1, dit1, dif1), ScmIf (test2, dit2, dif2) -> (expr_eq test1 test2) &&
                                            (expr_eq dit1 dit2) &&
                                              (expr_eq dif1 dif2)
  | (ScmSeq(exprs1), ScmSeq(exprs2) | ScmOr (exprs1), ScmOr (exprs2)) ->
        List.for_all2 expr_eq exprs1 exprs2
  | (ScmSet (var1, val1), ScmSet (var2, val2) | ScmDef (var1, val1), ScmDef (var2, val2)) ->
        (expr_eq var1 var2) && (expr_eq val1 val2)
  | ScmLambdaSimple (vars1, body1), ScmLambdaSimple (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmLambdaOpt (vars1, var1, body1), ScmLambdaOpt (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmApplic (e1, args1), ScmApplic (e2, args2) ->
     (expr_eq e1 e2) && (List.for_all2 expr_eq args1 args2)
  | _ -> false;;

let rec pairs_to_list = function
  | ScmNil-> []
  | ScmPair(x, ScmNil)->[x] 
  | ScmPair(x,y) -> x :: (pairs_to_list y);;

let rec take_body_or_head str isBody =
(match isBody with
| true ->(
  (match (List.rev (make_lst str)) with
    | var::args -> List.rev args))
| false -> ( 
  (match (List.rev (make_lst str)) with
    | var::args -> [var])))
and make_lst str = 
  match str with
  | ScmPair(ScmSymbol(hd), ScmSymbol(tl)) -> hd::tl::[]
  | ScmPair (ScmSymbol(hd), tl) -> hd::(make_lst tl)
  | sexpr -> raise (X_syntax_error (sexpr, "Expected improper list"));;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
end;; 

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;

let rec tag_parse_expression sexpr =
let sexpr = macro_expand sexpr in
match sexpr with
(* Implement tag parsing here *)
(* Constants *)
| ScmNil -> ScmConst(ScmNil) 
| ScmBoolean(x) -> ScmConst(sexpr)
| ScmChar(x) ->ScmConst(sexpr)
| ScmNumber(x) -> ScmConst(sexpr)
| ScmString(x) -> ScmConst(sexpr)
(* Variables *)
| ScmSymbol(x) -> ScmVar(string_of_sexpr sexpr)
(* Quotes *)
| ScmPair(ScmSymbol("quote"),ScmPair(a,ScmNil)) -> ScmConst a 
(* Conditionals*)
| ScmPair(ScmSymbol("if"), ScmPair(test,ScmPair(dit,ScmPair(dif , ScmNil)))) -> ScmIf(tag_parse_expression test,tag_parse_expression dit ,tag_parse_expression dif)
| ScmPair(ScmSymbol("if"), ScmPair(test,ScmPair(dit,ScmNil))) -> ScmIf(tag_parse_expression test,tag_parse_expression dit , ScmConst(ScmVoid))
(* Disjunctions *)
| ScmPair (ScmSymbol "or", ScmNil) -> ScmConst (ScmBoolean false)
| ScmPair (ScmSymbol "or", ScmPair (x, ScmNil)) -> tag_parse_expression x
| ScmPair (ScmSymbol "or", ScmPair (x, ScmPair(y, z))) -> ScmOr(List.map tag_parse_expression (pairs_to_list (ScmPair(x, (ScmPair(y,z))))))

| ScmPair(ScmSymbol("lambda"), rest) -> (match rest with
  | ScmPair(ScmSymbol(args), sexpr) -> 
    ScmLambdaOpt([], args,parse_list (scm_list_to_list sexpr))
  | ScmPair(args, sexpr)-> 
      match (scm_is_list args) with
      | true -> ScmLambdaSimple(
        (List.map (fun symbol ->
        match symbol with 
          | ScmSymbol(str) -> str) 
        (scm_list_to_list args)),parse_list (scm_list_to_list sexpr))
      | false -> ScmLambdaOpt(take_body_or_head args true, List.hd (take_body_or_head args false),parse_list (scm_list_to_list sexpr)))
(* Define *)
| ScmPair(ScmSymbol("define"), rest) ->
    (match rest with
    | ScmPair(ScmSymbol(var) , body) ->
      match (List.length (scm_list_to_list body)) with 
      | 1 -> ScmDef((
        if (List.mem var reserved_word_list) 
        then raise (X_syntax_error(rest,"Expected variable on LHS of define"))
        else ScmVar(var)), 
        (tag_parse_expression (List.hd (scm_list_to_list body))))
      | _ -> ScmDef((
        if (List.mem var reserved_word_list) 
        then raise (X_syntax_error(rest,"Expected variable on LHS of define"))
        else ScmVar(var)),
        (tag_parse_expression (ScmPair(ScmSymbol("lambda"),ScmPair(ScmNil,body))))))
(*Assignments *)
| ScmPair(ScmSymbol("set!"), rest) -> ( 
  let lst = scm_list_to_list rest in
  let head = List.hd lst in
  let tail = List.tl lst in
  match head with
  | ScmSymbol(str) -> ScmSet(tag_parse_expression head,
    match List.length tail with
    | 1 -> tag_parse_expression (List.hd tail)
    | _ -> raise (X_syntax_error(rest,"wrong syntax")))
  | _ -> raise (X_syntax_error(head,"Expected variable on LHS of set!")))
(*Sequences *)
| ScmPair(ScmSymbol("begin"), rest) -> parse_list (scm_list_to_list rest)
(*Applications *)
| ScmPair(hd,tl) -> ScmApplic((tag_parse_expression hd), List.map tag_parse_expression (scm_list_to_list tl))
| _ -> raise (X_syntax_error (sexpr, "Unknown structure"))

and parse_list lst =
  match List.length lst with
    | 1 -> tag_parse_expression (List.hd lst)
    | _ -> ScmSeq(List.map tag_parse_expression lst)

and macro_expand sexpr =
match sexpr with
(* Handle macro expansion patterns here *)
| ScmPair(ScmSymbol("and"), rest) -> 
    (match rest with
      | ScmNil -> ScmBoolean(true)
      | ScmPair(expr, ScmNil) -> (macro_expand expr)
      | ScmPair(expr, res) -> ScmPair(ScmSymbol("if"), ScmPair((macro_expand expr),
        ScmPair((macro_expand (ScmPair(ScmSymbol("and"), res))), ScmPair(ScmBoolean(false), ScmNil)))))
| ScmPair(ScmSymbol("let"), ScmPair(arguments,body)) -> (
      let args = (List.map (fun args -> 
        match args with
          | ScmPair(ScmSymbol(str),value) ->  ScmSymbol(str))
        (scm_list_to_list arguments)) in
      let body1 = macro_expand body in
      let values = (List.map (fun args -> 
        match args with
          | ScmPair(ScmSymbol(str),ScmPair(value,ScmNil)) -> (macro_expand value))
        (scm_list_to_list arguments)) in
      ScmPair(ScmPair(ScmSymbol("lambda"),ScmPair((list_to_proper_list args),body1)),(list_to_proper_list values)))
| ScmPair(ScmSymbol("let*"), rest) -> (
    match rest with
    | ScmPair(args, body) -> (
      match (List.length (scm_list_to_list args)) with
        | 0 -> (macro_expand (ScmPair(ScmSymbol("let"),ScmPair(ScmNil,body))))
        | 1 -> (macro_expand (ScmPair(ScmSymbol("let"),ScmPair(args,body))))
        | _ -> (
      let head = ScmPair((List.hd (scm_list_to_list args)),ScmNil) in
      let tail = (list_to_proper_list (List.tl (scm_list_to_list args))) in
      let body1 = (macro_expand (ScmPair(ScmSymbol("let*"),ScmPair(tail,body)))) in
      (macro_expand (ScmPair(ScmSymbol("let"),ScmPair(head,ScmPair(body1,ScmNil))))))))

| ScmPair(ScmSymbol("letrec"), ScmPair(args,body)) -> (
  let vars = (List.map (fun arg -> match arg with
    | ScmPair(ScmSymbol(str),value) ->  ScmSymbol(str)) (scm_list_to_list args)) in
  let new_vars = (list_to_proper_list (List.map (fun var -> ScmPair(var,ScmPair(ScmPair(ScmSymbol("quote"),
    ScmPair(ScmSymbol("whatever"),ScmNil)),ScmNil))) vars)) in
  let vals = (List.map (fun arg -> match arg with
    | ScmPair(ScmSymbol(str),value) -> value) (scm_list_to_list args)) in
  let values = (scm_zip (fun var value -> 
    ScmPair(ScmSymbol("set!"), ScmPair(var,(macro_expand value)))) 
    (list_to_proper_list vars) (list_to_proper_list vals)) in
  (macro_expand (ScmPair(ScmSymbol("let"),ScmPair(new_vars,(scm_append values body))))))

| ScmPair(ScmSymbol("cond"), rest) -> 
    (match rest with
      | ScmPair(ScmPair(test,ScmPair(ScmSymbol("=>"),body)),rest) -> arrow_rib test body rest
      | ScmPair(ScmPair(test,dit),rest) -> cond_rib test dit rest)
| ScmPair(ScmSymbol("define"), rest) -> ScmPair(ScmSymbol("define"),
  (match rest with
    | ScmPair(ScmPair(ScmSymbol(var) , args) , body) -> (ScmPair(ScmSymbol(var),(ScmPair(ScmPair(ScmSymbol("lambda"),ScmPair(args,body)),ScmNil))))
    | _ -> rest))
|  ScmPair (ScmSymbol ("quasiquote"), ScmPair(rest, ScmNil)) -> quasiquote rest
| _ -> sexpr

and quasiquote rest =
  match rest with
    | ScmPair(ScmSymbol ("unquote"), ScmPair(xp, ScmNil)) -> xp
    | ScmNil -> ScmPair(ScmSymbol("quote"), ScmPair(rest, ScmNil))
    | ScmSymbol(_)-> ScmPair(ScmSymbol("quote"), ScmPair(rest, ScmNil))
    | ScmVector(lst) -> ScmPair(ScmSymbol "list->vector", ScmPair((quasiquote (list_to_proper_list lst)), ScmNil))
    | ScmPair(ScmSymbol ("unquote-splicing"), ScmPair(_, ScmNil)) -> ScmPair(ScmSymbol("quote"), ScmPair(rest, ScmNil))
    | ScmPair((ScmPair((ScmSymbol("unquote-splicing")), (ScmPair(xp, ScmNil)))), xp2) -> 
      (ScmPair((ScmSymbol("append")),(ScmPair(xp, (ScmPair((quasiquote xp2), ScmNil))))))
    | ScmPair(xp, (ScmPair((ScmSymbol("unquote-splicing")), (ScmPair(xp2, ScmNil))))) ->
      (ScmPair((ScmSymbol("cons")), (ScmPair((quasiquote xp), (ScmPair(xp2, ScmNil))))))
    | ScmPair(xp, xp2) -> (ScmPair((ScmSymbol("cons")), (ScmPair((quasiquote xp), (ScmPair((quasiquote xp2), ScmNil))))))
    | _ -> rest

and cond_rib test dit rest =
  match rest with
    | ScmNil -> (
      match test with 
        | ScmSymbol("else") -> (parse_rib dit)
        | _ -> (ScmPair(ScmSymbol("if"), ScmPair(test,ScmPair((parse_rib dit),ScmNil)))))
    | _ -> (
      match test with
        | ScmSymbol("else") -> (parse_rib dit)
        | _ -> (ScmPair(ScmSymbol("if"), ScmPair(test, ScmPair(
            (match (List.length (scm_list_to_list (macro_expand dit))) with
              | 1 -> List.hd (scm_list_to_list (macro_expand dit))
              | _ -> ScmPair(ScmSymbol("begin"),(macro_expand dit)))
          ,(macro_expand (ScmPair(ScmPair(ScmSymbol("cond"),rest),ScmNil))))))))

and parse_rib rib = 
  (match (List.length (scm_list_to_list (macro_expand rib))) with
    | 0 -> raise (X_syntax_error(rib,"wrong syntax"))
    | 1 ->  (macro_expand (List.hd (scm_list_to_list (rib))))
    | _ -> ScmPair(ScmSymbol("begin"), (macro_expand rib)))

and arrow_rib test body rest = 
  match rest with
    | ScmNil -> (macro_expand (ScmPair(ScmSymbol("let"),
      (ScmPair(ScmPair(ScmPair(ScmSymbol("value"),ScmPair((macro_expand test),ScmNil)),
        ScmPair(ScmPair(ScmSymbol("f"),ScmPair(ScmPair(ScmSymbol("lambda"),ScmPair(ScmNil,ScmPair(body,ScmNil))),ScmNil)),
        ScmPair(ScmPair(ScmSymbol("rest"),ScmNil),ScmNil))), ScmPair(ScmPair(ScmSymbol("if"),
        ScmPair(ScmSymbol("value"), ScmPair(ScmPair(ScmPair(ScmSymbol("f"),ScmNil),ScmPair(ScmSymbol("value"),ScmNil)),
        ScmPair(ScmPair(ScmSymbol("rest"),ScmNil),ScmNil)))),ScmNil))))))
    | _ -> (macro_expand (ScmPair(ScmSymbol("let"),
      (ScmPair(ScmPair(ScmPair(ScmSymbol("value"),ScmPair((macro_expand test),ScmNil)),
      ScmPair(ScmPair(ScmSymbol("f"),ScmPair(ScmPair(ScmSymbol("lambda"),ScmPair(ScmNil,(macro_expand body))),ScmNil)),
      ScmPair(ScmPair(ScmSymbol("rest"),ScmPair(ScmPair(ScmSymbol("lambda"),ScmPair(ScmNil,(macro_expand (ScmPair(ScmPair(ScmSymbol("cond"),rest),ScmNil))))),ScmNil)),ScmNil))),
      ScmPair(ScmPair(ScmSymbol("if"), ScmPair(ScmSymbol("value"),
      ScmPair(ScmPair(ScmPair(ScmSymbol("f"),ScmNil),ScmPair(ScmSymbol("value"),ScmNil)),
      ScmPair(ScmPair(ScmSymbol("rest"),ScmNil),ScmNil)))),ScmNil))))))

end;;