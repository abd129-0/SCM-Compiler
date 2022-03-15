#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl :  expr' list -> (sexpr * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (sexpr * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct

let counter = ref 0;;

let get_label_number ()= 
  let increment ()= counter:= !counter + 1 in
  (increment (); !counter);;

let rec generate_help consts fvars e depth= 
  match e with 
    | ScmBoxSet'(var,value) -> box_set consts fvars var depth value 
    | ScmDef'(VarFree(name), vl) ->  generate_define consts fvars depth vl name
    | ScmConst'(c) -> "; Sexpression: Constant\nmov rax,const_tbl+" ^ (find_sexpr_offset c consts) ^ "\n"
    | ScmVar'(VarParam(_,minor)) -> "; Sexpression: Variable\nmov rax, qword[rbp + 8*(4+" ^ (string_of_int minor) ^ ")]\n"
    | ScmSet'(VarParam(_, minor), vl) -> (generate_help consts fvars vl depth) ^ "mov qword [rbp + 8*(4+" ^ (string_of_int minor) ^ ")], rax\nmov rax, SOB_VOID_ADDRESS\n"
    | ScmVar'(VarBound(_,major,minor)) -> "; Sexpression: Variable\nmov rax, qword[rbp + 8*2]\nmov rax, qword[rax + 8 * " ^ (string_of_int major) ^ "]\nmov rax, qword[rax + 8 * " ^ (string_of_int minor) ^ "]\n"
    | ScmSet'(VarBound(_,major,minor), vl) -> (generate_help consts fvars vl depth) ^ "mov rbx, qword [rbp + 8 * 2]\nmov rbx, qword [rbx + 8 *"^(string_of_int major)^ "]\nmov qword [rbx + 8 *" ^ (string_of_int minor) ^"], rax\nmov rax, SOB_VOID_ADDRESS\n"
    | ScmVar'(VarFree(name)) -> "mov rax, qword[fvar_tbl+" ^ (find_fvar_offset name fvars) ^"]\n" 
    | ScmSet'(VarFree(v),vl) -> (generate_help consts fvars vl depth) ^ "mov qword [fvar_tbl+" ^ (find_fvar_offset v fvars) ^ "],rax\nmov rax,SOB_VOID_ADDRESS\n"
    | ScmSeq'(seq) -> String.concat "" (List.map (fun expr -> generate_help consts fvars expr depth) seq) 
    | ScmOr'(ors) -> generate_or consts fvars ors depth
    | ScmIf'(test,dit,dif) -> generate_if consts fvars test dit dif depth
    | ScmBox'(VarParam(_,minor)) -> generate_box consts fvars (string_of_int minor) depth
    | ScmBoxGet'(var) -> box_get consts fvars var depth
    | ScmLambdaSimple'(params,body) ->  generate_lambda_simple consts fvars params body depth
    | ScmApplic'(body,args) -> generate_applic consts fvars body args depth
    | ScmApplicTP'(body,args) -> generate_applicTP consts fvars body args depth
    | ScmLambdaOpt'(mandatory, optional, body) -> generate_lambda_optional consts fvars mandatory optional body depth
    | x -> raise X_this_should_not_happen

and find_sexpr_offset sexp const_tbl = 
  match const_tbl with 
  | entry::rest -> let (cur_sexpr, (offset, _)) = entry in
      if (cur_sexpr = sexp) then (string_of_int offset) else find_sexpr_offset sexp rest
  | [] -> "Undefined Constant"

and find_fvar_offset name fvars =
  match fvars with 
  | entry::rest -> let (cur_name, offset) = entry in 
      if(name = cur_name) then string_of_int offset else find_fvar_offset name rest
  | [] -> "Undefined Free Variable (" ^ name ^ ")"

and generate_define consts fvars depth vl name =
  "; Sexpression: Define\n" ^ 
  generate_help consts fvars vl depth ^ 
  "mov qword[fvar_tbl+" ^ (find_fvar_offset name fvars) ^"], rax\n" ^ "mov rax, SOB_VOID_ADDRESS\n"

and generate_box consts fvars minor depth =
  "; Sexpression: Boxing\n" ^ 
  "mov rax, qword[rbp + 8 * (4 + " ^ minor ^ ")]\n" ^ "push SOB_NIL_ADDRESS\n" ^ 
  "push rax\n" ^ "push 2\n" ^ "push SOB_NIL_ADDRESS\n" ^ "call cons\n" ^ 
  "add rsp,8*1\n" ^ "pop rbx\n" ^ "shl rbx,3\n" ^ "add rsp,rbx\n" ^
  "mov qword[rbp + 8 * (4 + " ^ minor ^ ")],rax\n"

and box_get consts fvars var depth = 
  "; Sexpression: Box Get\n" ^
  generate_help consts fvars (ScmVar'(var)) depth ^ 
  "push rax\n" ^ "push 1\n" ^ "push SOB_NIL_ADDRESS\n" ^ "call car\n" ^
  "add rsp,8*1\n" ^ "pop rbx\n" ^ "shl rbx,3\n" ^ "add rsp, rbx\n" 
  
and box_set consts fvars var depth value = 
  "; Sexpression: Box Set\n" ^
  generate_help consts fvars value depth ^ "push rax\n" ^
  generate_help consts fvars (ScmVar'(var)) depth ^
  "push rax\n" ^ "push 2\n" ^ "push SOB_NIL_ADDRESS\n" ^ "call setcar\n" ^
  "add rsp, 8\n" ^ "pop rbx\n" ^ "shl rbx, 3\n" ^ "add rsp, rbx\n" ^ "mov rax,SOB_VOID_ADDRESS\n"
  
and generate_applic consts fvars body args depth = 
  let n = string_of_int (List.length args) in
  let push_args_code = List.fold_right (fun  arg acc-> acc ^ (generate_help consts fvars arg depth) ^ "push rax\n")  args "" in
  "; Sexpression: Application\n" ^ push_args_code ^ "push " ^ n ^ "\n" ^
  (generate_help consts fvars body depth) ^ "CLOSURE_ENV rbx, rax\n" ^
  "push rbx\n" ^ "CLOSURE_CODE rbx, rax\n" ^ "call rbx\n" ^ "add rsp,8*1\n" ^
  "pop rbx\n" ^ "shl rbx,3\n" ^ "add rsp,rbx\n"

and generate_applicTP consts fvars body args depth =
  let n = string_of_int (List.length args) in
  let push_args_code = List.fold_right (fun  arg acc-> acc ^ (generate_help consts fvars arg depth) ^ "push rax\n")  args "" in
  "; Sexpression: ApplicTP\n" ^ push_args_code ^ "push " ^ n ^ "\n" ^
  (generate_help consts fvars body depth) ^ "CLOSURE_ENV rbx, rax\n" ^
  "push rbx\n" ^ "push qword[rbp + 8 * 1] ;old ret addr\n" ^ "FIX_STACK_APPLICTP " ^ 
  (string_of_int (3 + (List.length args))) ^ "\nCLOSURE_CODE rbx, rax\n" ^ "jmp rbx\n" 
  
and generate_lambda_simple consts fvars params body depth =
  let label_num = get_label_number () in
  "; Sexpression: Simple Lambda" ^ 
  "\nMAKE_EXT_ENV " ^ (string_of_int depth) ^ "\nmov rbx, rax\n"^
  "MAKE_CLOSURE(rax, rbx, Lcode" ^ (string_of_int label_num) ^ ")\n"^
  "jmp Lcont" ^ (string_of_int label_num) ^ "\nLcode" ^ (string_of_int label_num) ^ ":\n
  push rbp\nmov rbp, rsp\n" ^ generate_help consts fvars body (depth + 1) ^
  "leave\nret\nLcont" ^ (string_of_int label_num) ^ ":\n"

and generate_lambda_optional consts fvars mandatory optional body depth =
  let label_num = get_label_number () in
  "; Sexpression: Optional Lambda\n" ^ 
  "MAKE_EXT_ENV " ^ (string_of_int depth) ^ "\nmov rbx, rax\n"^
  "MAKE_CLOSURE(rax, rbx, Lcode" ^ (string_of_int label_num) ^ ")\n"^
  "jmp Lcont" ^ (string_of_int label_num) ^ "\nLcode" ^ (string_of_int label_num) ^ ":\n" ^ 
  "FIX_STACK_LAMBDA_OPT " ^ (string_of_int ((List.length mandatory) + 1)) ^"\npush rbp\nmov rbp, rsp\n" ^
  generate_help consts fvars body (depth + 1) ^ "leave\nret\nLcont" ^ (string_of_int label_num) ^ ":\n"

and generate_or consts fvars ors depth= 
  let exit_label = "Lexit" ^ (string_of_int (get_label_number ()))  in
  (List.fold_left (fun acc o -> acc ^ (generate_help consts fvars o depth) ^ 
  "cmp rax, SOB_FALSE_ADDRESS\njne " ^ exit_label ^ "\n" ) "" ors) ^ exit_label ^":\n"

and generate_if consts fvars test dit dif depth=
  let label_num = get_label_number () in
  "; Sexpression: if\n" ^ 
  (generate_help consts fvars test depth) ^ "cmp rax, SOB_FALSE_ADDRESS\nje Lelse" ^
  (string_of_int label_num) ^ "\n" ^ (generate_help consts fvars dit depth) ^ "jmp Lexit" ^ 
  (string_of_int label_num) ^ "\nLelse" ^ (string_of_int label_num) ^ ":\n" ^
  (generate_help consts fvars dif depth) ^ "Lexit" ^ (string_of_int label_num) ^ ":\n"

let rec make_naive_table input result =
  (match input with
  | [] -> result
  | hd::tl -> (let res = 
    (match hd with
      | ScmConst'(c) -> result@[c]
      | ScmBoxSet'(v, e) -> make_naive_table [e] result
      | ScmIf'(test, caseT, caseF) -> make_naive_table [test; caseT; caseF] result
      | ScmSeq'(l) -> make_naive_table l result
      | ScmSet'(e_var, e_val) -> make_naive_table [e_val] result
      | ScmDef'(e_var, e_val) -> make_naive_table [e_val] result
      | ScmOr'(l) -> make_naive_table l result
      | ScmLambdaSimple'(params, body) -> make_naive_table [body] result
      | ScmLambdaOpt'(params, opt, body) -> make_naive_table [body] result
      | ScmApplic'(proc, args) -> (make_naive_table ([proc]@args) result)
      | ScmApplicTP'(proc, args) -> (make_naive_table ([proc]@args) result)
      | _ -> result) in 
    make_naive_table tl res));;

let rec remove_duplicates lst no_dups= 
  (match lst with
    | first::rest -> if (List.mem first no_dups) then (remove_duplicates rest no_dups) else (remove_duplicates rest (List.append no_dups [first]))
    | [] -> no_dups);;

let rec open_complex l =
  (match l with
  | [] -> []
  | hd::tl -> 
    (match hd with
      | ScmSymbol(s) -> [ScmString(s)]@[hd]@(open_complex tl)
      | ScmPair(car, cdr) -> (open_complex [car; cdr])@[hd]@(open_complex tl)
      | ScmVector(v) -> (open_complex (List.map (fun s -> s) v))@[hd]@(open_complex tl)
      | _ -> [hd]@(open_complex tl)))

let rec make_const_tuples constants_list (position : int) table =
  (match constants_list with
  | [] -> table
  | hd::tl -> 
    (match hd with
      | ScmVoid -> make_const_tuples tl (position + 1) (table@[(ScmVoid, (position, "MAKE_VOID"))])
      | ScmNil -> make_const_tuples tl (position + 1) (table@[(ScmNil, (position, "MAKE_NIL"))])
      | ScmBoolean(v) -> make_const_tuples tl (position + 2) (table@[(ScmBoolean(v), (position, "MAKE_BOOL(" ^ (if v then "1" else "0") ^ ")"))])
      | ScmNumber(ScmRational(num,den)) -> make_const_tuples tl (position + 17) (table@[(ScmNumber(ScmRational(num,den)), (position, "MAKE_LITERAL_RATIONAL(" ^ (string_of_int num) ^"," ^ (string_of_int den) ^ ")"))])
      | ScmNumber(ScmReal(num)) -> make_const_tuples tl (position + 9) (table@[(ScmNumber(ScmReal(num)), (position, "MAKE_LITERAL_FLOAT(" ^ (string_of_float num) ^ ")"))])
      | ScmChar(ch) -> make_const_tuples tl (position + 2) (table@[(ScmChar(ch), (position, "MAKE_LITERAL_CHAR(" ^ string_of_int (int_of_char ch) ^ ")" ))])
      | ScmString(s) -> make_const_tuples tl (position + 9 + (String.length s)) (table@[(ScmString(s), (position, "MAKE_LITERAL_STRING \"" ^ s ^ "\""))])
      | ScmSymbol(sym) -> make_const_tuples tl (position + 9) (table@[(ScmSymbol(sym), (position, "MAKE_LITERAL_SYMBOL(const_tbl+" ^ (string_of_int (find_offset (ScmString(sym)) table)) ^ ")"))])
      | ScmPair(xp1, xp2) -> make_const_tuples tl (position + 17) (table@[(ScmPair(xp1, xp2), (position, "MAKE_LITERAL_PAIR (const_tbl+" ^ (string_of_int (find_offset (xp1) table)) ^ ", const_tbl+" ^ (string_of_int (find_offset (xp2) table)) ^ ")"))])
      | ScmVector(lst) -> let (vectorstring, vectoroffset) = make_vector lst table in
        make_const_tuples tl (position+vectoroffset) (table@[(ScmVector(lst), (position, vectorstring))])))

and make_vector lst table =
  if (List.length lst = 0)
  then ("MAKE_LITERAL_VECTOR", 1)
  else 
    (let hd = "const_tbl+" ^ (string_of_int (find_offset (List.hd lst) table)) ^ " " in
    let tl = List.tl lst in
    let offset_list = List.fold_left (fun acc curr -> acc ^ ", const_tbl+" ^ (string_of_int (find_offset (curr) table))) "" tl in
    ("MAKE_LITERAL_VECTOR " ^ hd ^ offset_list ^ "", (9+8*List.length lst)))

and find_offset c table =
  (match table with
    | [] -> raise X_this_should_not_happen
    | hd::tl -> let (const, (offset, (str: string))) = hd in
      if ((sexpr_eq const c))
      then offset
      else find_offset c tl);;
      
let rec make_naive_table_free input result =
  (match input with
    | [] -> result
    | hd::tl -> (let res = 
      (match hd with
        | ScmVar'(VarFree(var)) -> result@[var]
        | ScmBox'(var) -> make_naive_table_free [ScmVar'(var)] result
        | ScmBoxGet'(var) -> make_naive_table_free [ScmVar'(var)] result
        | ScmBoxSet'(var, e) -> make_naive_table_free [ScmVar'(var); e] result
        | ScmIf'(test, caseT, caseF) -> make_naive_table_free [test; caseT; caseF] result
        | ScmSeq'(seq) -> make_naive_table_free seq result
        | ScmSet'(e_var, e_val) -> make_naive_table_free [e_val] result
        | ScmDef'(e_var, e_val) -> make_naive_table_free [e_val] result
        | ScmOr'(seq) -> make_naive_table_free seq result
        | ScmLambdaSimple'(params, body) -> make_naive_table_free [body] result
        | ScmLambdaOpt'(params, opt, body) -> make_naive_table_free [body] result
        | ScmApplic'(proc, args) -> make_naive_table_free ([proc]@args) result
        | ScmApplicTP'(proc, args) -> make_naive_table_free ([proc]@args) result
        | _ -> result) in
    make_naive_table_free tl res))

let rec make_free_tuples freeValList index table =
  (match freeValList with
    | [] -> table
    | hd::tl -> (make_free_tuples tl (index+8) (table@[(hd, index)])));;

let make_fvars_tbl asts = 
  let primitives = ["car"; "cdr"; "cons" ; "set-car!"; "set-cdr!"; "apply"; "boolean?";"flonum?";
    "rational?"; "pair?"; "null?"; "char?"; "string?" ; "symbol?"; "procedure?";
    "map"; "fold-left"; "fold-right"; "cons*"; "append"; "list"; "list?";
    "not"; "-"; ">"; "gcd"; "zero?"; "integer?"; "number?"; "length"; "string->list"; "equal?";
    "string-ref"; "string-set!";  "make-string"; "symbol->string";
    "char->integer"; "integer->char"; "exact->inexact"; "eq?";
    "+"; "*"; "/"; "="; "<"; "numerator"; "denominator"; "gcd"; "string-length"] in
  let naive = make_naive_table_free asts primitives in
  let naive = remove_duplicates naive [] in
  let table = make_free_tuples naive 0 [] in
  table;;

let make_consts_tbl asts = 
  let naive = make_naive_table asts [] in
  let naive = remove_duplicates naive [] in
  let table = open_complex naive in
  let table = remove_duplicates table [ScmVoid; ScmNil; ScmBoolean(false); ScmBoolean(true)] in
  make_const_tuples table 0 [];;

let generate consts fvars e = generate_help consts fvars e 0;;
end;;