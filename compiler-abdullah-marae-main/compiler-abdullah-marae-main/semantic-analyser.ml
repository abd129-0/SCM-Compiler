(* semantic-analyser.ml
 * The semantic analysis phase of the compiler
 *
 * Programmer: Mayer Goldberg, 2021
 *)

#use "tag-parser.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type var' = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | ScmConst' of sexpr
  | ScmVar' of var'
  | ScmBox' of var'
  | ScmBoxGet' of var'
  | ScmBoxSet' of var' * expr'
  | ScmIf' of expr' * expr' * expr'
  | ScmSeq' of expr' list
  | ScmSet' of var' * expr'
  | ScmDef' of var' * expr'
  | ScmOr' of expr' list
  | ScmLambdaSimple' of string list * expr'
  | ScmLambdaOpt' of string list * string * expr'
  | ScmApplic' of expr' * (expr' list)
  | ScmApplicTP' of expr' * (expr' list);;


let var_eq v1 v2 =
  match v1, v2 with
    | VarFree (name1), VarFree (name2) -> String.equal name1 name2
    | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
      major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
    | VarParam (name1, index1), VarParam (name2, index2) ->
      index1 = index2 && (String.equal name1 name2)
    | _ -> false

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | ScmConst' (sexpr1), ScmConst' (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar' (var1), ScmVar' (var2) -> var_eq var1 var2
  | ScmIf' (test1, dit1, dif1), ScmIf' (test2, dit2, dif2) ->
    (expr'_eq test1 test2) && (expr'_eq dit1 dit2) && (expr'_eq dif1 dif2)
  | (ScmSeq' (exprs1), ScmSeq' (exprs2) | ScmOr' (exprs1), ScmOr' (exprs2)) ->
    List.for_all2 expr'_eq exprs1 exprs2
  | (ScmSet' (var1, val1), ScmSet' (var2, val2) | ScmDef' (var1, val1), ScmDef' (var2, val2)) ->
    (var_eq var1 var2) && (expr'_eq val1 val2)
  | ScmLambdaSimple' (vars1, body1), ScmLambdaSimple' (vars2, body2) ->
    (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmLambdaOpt' (vars1, var1, body1), ScmLambdaOpt' (vars2, var2, body2) ->
    (String.equal var1 var2) && (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmApplic' (e1, args1), ScmApplic' (e2, args2) ->
    (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmApplicTP' (e1, args1), ScmApplicTP' (e2, args2) ->
    (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmBox' (v1), ScmBox' (v2) -> var_eq v1 v2
  | ScmBoxGet' (v1), ScmBoxGet' (v2) -> var_eq v1 v2
  | ScmBoxSet' (v1, e1), ScmBoxSet' (v2, e2) -> (var_eq v1 v2) && (expr'_eq e1 e2)
  | _ -> false;;

module type SEMANTIC_ANALYSIS = sig
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  val run_semantics : expr -> expr'
end;; (* end of module type SEMANTIC_ANALYSIS *)

module Semantic_Analysis : SEMANTIC_ANALYSIS = struct

let rec lookup_in_rib name = function
  | [] -> None
  | name' :: rib ->
    if name = name'
    then Some(0)
    else 
    (match (lookup_in_rib name rib) with
      | None -> None
      | Some minor -> Some (minor + 1));;

let rec lookup_in_env name = function
  | [] -> None
  | rib :: env ->
  (match (lookup_in_rib name rib) with
    | None ->
    (match (lookup_in_env name env) with
      | None -> None
      | Some(major, minor) -> Some(major + 1, minor))
    | Some minor -> Some(0, minor));;

let tag_lexical_address_for_var name params env = 
  match (lookup_in_rib name params) with
  | None ->
    (match (lookup_in_env name env) with
    | None -> VarFree name
    | Some(major, minor) -> VarBound(name, major, minor))
  | Some minor -> VarParam(name, minor);;

let annotate_lexical_addresses pe = 
  let rec run pe params env =
  match pe with
    | ScmLambdaSimple(listOfParams, body) -> ScmLambdaSimple'(listOfParams,(run body listOfParams ([params] @ env)))
    | ScmLambdaOpt(listOfParams, lastParam, body) -> ScmLambdaOpt'(listOfParams, lastParam,  (run body (listOfParams @ [lastParam]) ([params] @ env))) 
    | ScmVar(name) -> ScmVar'(tag_lexical_address_for_var name params env)
    | ScmApplic(lambda, listOfValues) -> ScmApplic'(run lambda params env, run_list listOfValues params env)
    | ScmConst(value) -> ScmConst'(value)
    | ScmIf(cond, th, el) -> ScmIf'((run cond params env), (run th params env), (run el params env))
    | ScmSeq(listOfExp) -> ScmSeq'(run_list listOfExp params env)
    | ScmSet(ScmVar(var), value) -> ScmSet'(tag_lexical_address_for_var var params env, (run value params env))
    | ScmDef(ScmVar(var), value) -> ScmDef'(tag_lexical_address_for_var var params env, (run value params env))
    | ScmOr(listOfExp) -> ScmOr'(run_list listOfExp params env) 
    | _ -> raise X_this_should_not_happen
    and run_list listOfExp params env =
      match listOfExp with
        | [] -> []
        | a::[] -> [run a params env]
        | a::b -> [run a params env] @ (run_list b params env)
        in
  run pe [] [];;

let rec rdc_rac s =
  match s with
  | [e] -> ([], e)
  | e :: s ->
    let (rdc, rac) = rdc_rac s
    in (e :: rdc, rac)
  | _ -> raise X_this_should_not_happen;;
  
let annotate_tail_calls pe =
  let rec run pe in_tail =
  match pe with
    | ScmLambdaSimple'(params, body) -> ScmLambdaSimple'(params, (run body true)) 
    | ScmLambdaOpt'(params, lastparam, body) -> ScmLambdaOpt'(params, lastparam, (run body true))
    | ScmIf'(cond, th, el) -> ScmIf'((run cond false), (run th in_tail), (run el in_tail))
    | ScmOr'(listOfExp) -> ScmOr'(run_last listOfExp in_tail)
    | ScmSeq'(listOfExp) -> ScmSeq'(run_last listOfExp in_tail)
    | ScmSet'(var, body) -> ScmSet'(var, (run body false))
    | ScmDef'(var, value) -> ScmDef'(var, (run value false))
    | ScmApplic'(lambda, args) -> if(in_tail) then ScmApplicTP'(run lambda false, run_last args false) else ScmApplic'(run lambda false, run_last args in_tail)
    | ScmVar'(name) -> ScmVar'(name)
    | x -> x
and run_last listOfExp in_tail = 
  match listOfExp with
    | [a] -> [run a in_tail]
    | a::b -> [run a false] @ run_last b in_tail
    | [] -> [] in 
  run pe false;;

let box_set e =
  let rec rec_box_set e = 
    match e with 
      | ScmBoxSet' (v, expr) -> ScmBoxSet' (v, rec_box_set expr)
      | ScmSeq' eList -> ScmSeq' (List.map (fun exp -> rec_box_set exp) eList)
      | ScmSet' (v, expr) -> ScmSet' (v, rec_box_set expr)
      | ScmIf'(test, dtrue, dfalse)-> ScmIf'(rec_box_set test, rec_box_set dtrue, rec_box_set dfalse)
      | ScmDef' (v, expr) -> ScmDef' (v, rec_box_set expr)
      | ScmOr' eList -> ScmOr' (List.map (fun exp -> rec_box_set exp) eList) 
      | ScmLambdaSimple' (parameters, expr)  ->
        ScmLambdaSimple'(parameters, checkSeq (rec_box_set (run_box_helper parameters expr [])))
      | ScmLambdaOpt' (parameters, optParams, expr) -> 
        ScmLambdaOpt'(parameters,optParams, checkSeq (rec_box_set (run_box_helper (parameters@[optParams]) expr [])))
      | ScmApplic' (exprTag, args) -> ScmApplic' (rec_box_set exprTag, List.map (fun arg -> rec_box_set arg) args)
      | ScmApplicTP' (exprTag, args) -> ScmApplicTP' (rec_box_set exprTag, List.map (fun arg -> rec_box_set arg) args)
      | _ -> e
	     
 		  
and helper_Set_Get boxingParameters expr  = 
  (match boxingParameters with
    | first::last -> let expr_new = main_helper_Set_Get first expr in helper_Set_Get last expr_new 
    | [] -> expr)


and main_helper_Set_Get parameter expr =  
  match expr with
    | ScmVar' (VarBound (name, major, minor)) -> if name = parameter 
    then ScmBoxGet' (VarBound (name, major, minor)) else expr
    | ScmVar' (VarParam (name, minor)) -> if name = parameter
    then ScmBoxGet' (VarParam (name, minor)) else expr
    | ScmSet' (VarBound (name, major, minor), expr) -> if name = parameter 
    then ScmBoxSet' ((VarBound (name, major, minor)), (main_helper_Set_Get parameter expr)) else ScmSet' (VarBound (name, major, minor), (main_helper_Set_Get parameter expr))
    | ScmSet' (VarParam (name, minor), expr) ->  if name = parameter 
    then ScmBoxSet' ((VarParam (name, minor)), (main_helper_Set_Get parameter expr)) else ScmSet' ((VarParam (name, minor)), (main_helper_Set_Get parameter expr))
    | ScmBoxSet' (v,expr) -> ScmBoxSet' (v ,(main_helper_Set_Get parameter expr)) 
    | ScmSeq' seqLst -> ScmSeq' (List.map (fun expr -> (main_helper_Set_Get parameter expr)) seqLst)
    | ScmDef' (v, expr) -> ScmDef' (v, (main_helper_Set_Get parameter expr))
    | ScmOr' expLst -> ScmOr' (List.map (fun expr -> main_helper_Set_Get parameter expr) expLst)
    | ScmIf'(test, dtrue, dif)-> ScmIf' ((main_helper_Set_Get parameter test), (main_helper_Set_Get parameter dtrue), (main_helper_Set_Get parameter dif))
    | ScmLambdaSimple' (parameters, exprs)  -> if List.mem parameter parameters 
    then ScmLambdaSimple' (parameters, exprs) else ScmLambdaSimple' (parameters, main_helper_Set_Get parameter exprs)
    | ScmLambdaOpt' (parameters, optPar,exprs) -> if List.mem parameter parameters || List.mem parameter [optPar]
    then ScmLambdaOpt' (parameters, optPar, exprs) else ScmLambdaOpt' (parameters, optPar, main_helper_Set_Get parameter exprs)
    | ScmApplic' (exprTag, args) -> ScmApplic' ((main_helper_Set_Get parameter exprTag) , List.map (fun arg -> (main_helper_Set_Get parameter arg)) args)
    | ScmApplicTP' (exprTag, args) -> ScmApplicTP' ((main_helper_Set_Get parameter exprTag) , List.map (fun arg -> (main_helper_Set_Get parameter arg)) args)
    | _ -> expr
                          
and run_box_helper parameters expr boxingParameters = 
  match parameters with
  | first::last -> let boolBoxParam = checkifboxParam first expr in 
    run_box_helper last expr (if boolBoxParam  then (boxingParameters@[first]) else boxingParameters)
  | [] -> (let setGetParametersList = helper_Set_Get boxingParameters expr in
    let setsList = List.map (fun parameter -> add_Set parameter expr) boxingParameters in
    ScmSeq' (setsList@[rec_box_set setGetParametersList])) 
and add_Set parameter expr= 
  let minor_of_set = getMinorSet parameter expr in
  let makeNew_varParam = (VarParam (parameter, minor_of_set)) in
  let box_ScmSet = ScmSet' (makeNew_varParam, (ScmBox' makeNew_varParam )) in
  box_ScmSet  
and checkifboxParam parameter expr = let (case1,case2,case3) = scan parameter expr (false,false,false) in (case1 && case2 && case3)

and scan parameter expr (case1,case2,case3) = 
  match expr with 
    | ScmSet' (VarBound (name, _, _), exp) -> if name = parameter 
    then scan parameter exp (true,true,case3) else scan parameter exp (case1,case2,case3) 
    | ScmSet' (VarParam (name, _), exp) -> if name = parameter 
    then scan parameter exp (case1,true,case3) else scan parameter exp (case1,case2,case3)
    | ScmVar' (VarBound (name, _, _)) -> if name = parameter 
    then (true,case2,true) else (case1,case2,case3) 
    | ScmVar' (VarParam (name, _)) -> if name = parameter 
    then (case1,case2,true) else (case1,case2,case3)
    | ScmSet' (v, exp) -> scan parameter exp (case1,case2,case3)
    | ScmDef' (v, exp) -> scan parameter exp (case1,case2,case3)
    | ScmBoxSet' (_,expr) -> scan parameter expr (case1,case2,case3)
    | ScmIf'(test, dtrue, dif)-> checkCons parameter (test::dtrue::dif::[]) (case1,case2,case3)
    | ScmOr' expLst -> checkCons parameter expLst (case1,case2,case3)
    | ScmSeq' seqLst -> checkCons parameter seqLst (case1,case2,case3)
    | ScmLambdaSimple' (params, exp)  ->  if List.mem parameter params then (false,false,false) else scan parameter exp (case1,case2,case3)
    | ScmLambdaOpt' (params, optPar,exp) -> if List.mem parameter params || List.mem parameter [optPar] then (false,false,false) else scan parameter exp (case1,case2,case3)
    | ScmApplic' (exprTag, args) -> checkCons parameter (exprTag::args) (case1,case2,case3)
    | ScmApplicTP' (exprTag, args) ->  checkCons parameter (exprTag::args) (case1,case2,case3)
    | _ -> (case1,case2,case3)
      
and checkCons parameter expLst (case1,case2,case3) = 
  match expLst with
    | (first::last) -> let (newcase1,newcase2,newcase3) = scan parameter first (case1,case2,case3) in checkCons parameter  last (newcase1,newcase2,newcase3)
    | [] -> (case1,case2,case3)


and checkSeq exp = 
  (match exp with
    | ScmSeq' [e] -> e 
    |  _ -> exp )

and getMinorSet parameter expr = 
  match expr with
    | ScmSet' (VarBound (par, _, mi), _) -> if par = parameter 
    then mi else (-1)
    | ScmSet' (VarParam (par, mi), _) -> if par = parameter 
    then mi else (-1)
    | ScmVar' (VarBound (par, _, mi)) -> if par = parameter
     then mi else (-1)
    | ScmVar' (VarParam (par, mi)) ->  if par = parameter
     then mi else (-1)
    | ScmBox' (VarParam (par, mi)) -> if par = parameter 
    then mi else (-1)
    | ScmBoxGet' bGet -> getMinorSet parameter (ScmVar' bGet)
    | ScmBoxSet' (bSet,exp) -> maxIndex [(getMinorSet parameter (ScmVar' bSet)) ; (getMinorSet parameter exp)] (-1) 
    | ScmIf'(test, dtrue, dif)-> maxIndex [(getMinorSet parameter test) ; (getMinorSet parameter dtrue) ; (getMinorSet parameter dif)] (-1)
    | ScmSet' (v, expr) -> maxIndex [(getMinorSet parameter (ScmVar' v)) ; (getMinorSet parameter expr)] (-1)
    | ScmOr' expLst -> maxIndex (List.map (fun exp -> getMinorSet parameter exp) expLst) (-1)
    | ScmDef' (v, expr) -> maxIndex [(getMinorSet parameter (ScmVar' v)) ; (getMinorSet parameter expr)] (-1)
    | ScmSeq' seqLst -> maxIndex (List.map (fun exp -> getMinorSet parameter exp) seqLst) (-1)
    | ScmLambdaSimple' (params, expr)  -> getMinorSet parameter expr
    | ScmLambdaOpt' (params, optPar,expr) -> getMinorSet parameter expr
    | ScmApplic' (exprTag, args) |ScmApplicTP' (exprTag, args) -> maxIndex ((getMinorSet parameter exprTag)::(List.map (fun arg -> getMinorSet parameter arg) args)) (-1)
    | _ -> -1
and  maxIndex l x = 
  match l with
    | [] -> x
    | first::last -> let newIndex = if (x > first) then x else first in maxIndex last newIndex 
    in rec_box_set e;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
        (annotate_lexical_addresses expr))


end;; (* end of module Semantic_Analysis *)