(* reader.ml
 * A skeleton for the reader for the 2021-2022 course on compiler-construction
 *)

#use "pc.ml";;

let rec gcd a b =
  match (a, b) with
  | (0, b) -> b
  | (a, 0) -> a
  | (a, b) -> gcd b (a mod b);;

type scm_number =
  | ScmRational of (int * int)
  | ScmReal of float;;

type sexpr =
  | ScmVoid
  | ScmNil
  | ScmBoolean of bool
  | ScmChar of char
  | ScmString of string
  | ScmSymbol of string
  | ScmNumber of scm_number
  | ScmVector of (sexpr list)
  | ScmPair of (sexpr * sexpr);;

module type READER = sig
    val nt_sexpr : sexpr PC.parser
end;; (* end of READER signature *)

module Reader : READER = struct
open PC;;

let char_prefix str = 
  let nt1 = char '#' in
  let nt2 = char '\\' in
  let nt1 = caten nt1 nt2 in
  nt1 str

let natural =
  let nt1 = range '0' '9' in
  let nt1 = plus nt1 in
  let nt1 = pack nt1 (fun num -> (int_of_string (list_to_string num))) in
  nt1

let sign = 
  let nt1 = disj (char '+') (char '-') in
  nt1

let unitify nt = pack nt (fun _ -> ());;

let to_float_1 (str : float option) = (fun (num) -> match num with 
  | Some(num) -> num
  | None -> 1.0);;
let to_float_0 (str : float option) = (fun (num) -> match num with 
  | Some(num) -> num
  | None -> 0.0);;

let rec nt_whitespace str =
  const (fun ch -> ch <= ' ') str
and nt_end_of_line_or_file str =
  let nt1 = unitify (char '\n') in
  let nt2 = unitify nt_end_of_input in
  let nt1 = disj nt1 nt2 in
  nt1 str;
and nt_line_comment str = 
  let nt1 = char ';' in
  let nt2 = diff nt_any nt_end_of_line_or_file in
  let nt2 = star nt2 in
  let nt1 = caten nt1 (caten nt2 nt_end_of_line_or_file) in
  let nt1 = unitify nt1 in
  nt1 str
and nt_paired_comment str =
  let nt1 = char '{' in
  let nt2 = disj_list[unitify nt_char; unitify nt_string; unitify nt_comment] in
  let nt2' = disj nt2 (unitify (one_of "{}")) in
  let nt3 = diff nt_any nt2' in
  let nt3 = unitify nt3 in
  let nt3 = disj nt3 nt2 in
  let nt3 = star nt3 in
  let nt4 = char '}' in
  let nt1 = unitify (caten nt1 (caten nt3 nt4)) in
  nt1 str
and nt_sexpr_comment str =
  let prefix = word "#;" in
  let nt = caten prefix nt_sexpr in
  let nt = unitify nt in
  nt str
and nt_comment str =
  disj_list
    [nt_line_comment;
     nt_paired_comment;
     nt_sexpr_comment] str
and nt_skip_star str =
  let nt1 = disj (unitify nt_whitespace) nt_comment in
  let nt1 = unitify (star nt1) in
  nt1 str
and make_skipped_star (nt : 'a parser) =
  let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
  let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
  nt1
and nt_frac str = 
  let nt1 = caten nt_int (caten (not_followed_by (char '/') (char '0')) natural) in
  let nt2 = pack nt1 (fun(numerator,(_, denominator)) -> let res = gcd (abs numerator) denominator in
  if (numerator * denominator = 0)
  then ScmRational(numerator, denominator)
  else ScmRational(numerator/res , denominator/res)) in
  nt2 str;
and nt_integer_part str = 
  let nt1 = range '0' '9' in
  let nt1 = plus nt1 in
  let nt2 = pack nt1 (fun (num)-> float_of_string(list_to_string(num))) in
  nt2 str;
and nt_mantissa str = 
  let nt1 = range '0' '9' in
  let nt1 = plus nt1 in
  let nt2 = pack nt1 (fun (num)-> float_of_string("0." ^ list_to_string(num))) in
  nt2 str;
and nt_exponent str = 
  let nt = disj_list [word "e"; word "E"; word "*10^"; word "*10**"] in
  let nt = caten nt nt_int in
  let nt1 = pack nt (fun(token,num)-> 10.**(float_of_int num)) in
  nt1 str;
and nt_float str = 
  let nt1 = pack (disj_list[(nt_floatC);(nt_floatB);(nt_floatA)]) (fun(v)-> ScmReal v) in
  nt1 str;
and nt_floatA str = 
  let nt1 = caten nt_integer_part (caten (char '.') (caten (maybe nt_mantissa) (maybe nt_exponent))) in
  let nt1 = pack nt1 (fun (int_part, (dot, (mant, expo))) -> match mant,expo with 
    | Some mantesa,Some exponent ->(int_part +. mantesa) *. exponent
    | Some mantesa,None -> int_part +. mantesa
    | None,Some exponent -> int_part *. exponent
    | None,None -> int_part) in
  nt1 str;
and nt_floatB str =
  let nt1 = caten (char '.') (caten  nt_mantissa (maybe nt_exponent)) in
  let nt1 = pack nt1 (fun (dot, (mant, expo)) -> match expo with
    | Some exponent ->  mant *. exponent
    | None -> mant) in
  nt1 str;
and nt_floatC str =
  let nt1 = caten nt_integer_part nt_exponent in
  let nt1 = pack nt1 (fun (int_part,expo) -> int_part *. expo) in
  nt1 str;
and nt_int str = 
  let nt1 = maybe sign in
  let nt2 = caten nt1 natural in
  let nt3 = pack nt2 (fun(sign, num) -> match sign with 
    | Some '+' -> num
    | Some '-' -> (-1)*num
    | None -> num
    | _ -> assert false) in
  nt3 str
and nt_number str =
  let nt1 = nt_float in
  let nt2 = nt_frac in
  let nt3 = pack nt_int (fun n -> ScmRational(n, 1)) in
  let nt1 = disj nt1 (disj nt2 nt3) in
  let nt1 = pack nt1 (fun r -> ScmNumber r) in
  let nt1 = not_followed_by nt1 nt_symbol_char in
  nt1 str
and nt_boolean str = 
  let nt1 = word_ci "#f" in
  let nt1 = pack nt1 (fun _ -> false) in
  let nt2 = word_ci "#t" in
  let nt2 = pack nt2 (fun _ -> true) in
  let nt1 = disj nt1 nt2 in
  let nt1 = pack nt1 (fun b -> ScmBoolean b) in
  nt1 str;
and nt_char_simple str = 
  let nt1 = diff nt_any nt_whitespace in
  let nt1 = not_followed_by nt1 nt1 in
  nt1 str;
and make_named_char char_name ch = pack (word_ci char_name) (fun e -> ch)
and nt_char_named str =
  let nt1 =
    disj_list [(make_named_char "newline" '\n');
               (make_named_char "page" '\012');
               (make_named_char "return" '\r');
               (make_named_char "space" ' ');
               (make_named_char "nul" '\000');
               (make_named_char "tab" '\t')] in
  nt1 str
and nt_char_hex str =
  let nt1 = char_ci 'x' in
  let nt2 = plus (disj_list [range '0' '9'; range_ci 'a' 'f']) in
  let nt2 = caten nt1 nt2 in
  let nt3 = pack nt2 (fun(x, num) -> char_of_int(int_of_string("0x" ^ list_to_string(num)))) in
  nt3 str;
and nt_char str = 
  let nt1 = disj_list [nt_char_hex;nt_char_named;nt_char_simple] in
  let nt2 = caten char_prefix nt1 in
  let nt3 = pack nt2 (fun(pre,ch)-> ScmChar ch) in
  nt3 str;
and nt_symbol_char str = 
  let nt1 = disj_list [(range '0' '9');(range_ci 'a' 'z');(char '!');(char '$');(char '^');(char '*');(char '-');(char '_');(char '=');(char '+');(char '<');(char '>');(char '?');(char '/');(char ':');] in
  nt1 str;
and nt_symbol str =
  let nt1 = plus nt_symbol_char in
  let nt1 = pack nt1 list_to_string in
  let nt1 = pack nt1 (fun name -> ScmSymbol name) in
  let nt1 = diff nt1 nt_number in
  nt1 str;
and nt_vector str =
  let nt1 = word "#(" in
  let nt2 = caten nt_skip_star (char ')') in
  let nt2 = pack nt2 (fun _ -> ScmVector []) in
  let nt3 = plus nt_sexpr in
  let nt4 = char ')' in
  let nt3 = caten nt3 nt4 in
  let nt3 = pack nt3 (fun (sexprs, _) -> ScmVector sexprs) in
  let nt2 = disj nt2 nt3 in
  let nt1 = caten nt1 nt2 in
  let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
  nt1 str;
and nt_list str = (disj nt_proper_list nt_improper_list) str
and nt_proper_list str = 
  let nt1 = caten (word "(") (caten (star nt_sexpr) (word ")")) in
  pack nt1 (fun(lp,(exp,rp))-> match exp with
  | []-> ScmNil
  | _ -> List.fold_right (fun a b -> ScmPair(a,b)) exp ScmNil) str
and nt_improper_list str = 
  let nt1 = caten (word "(")  (caten (plus nt_sexpr) (caten (word ".") (caten nt_sexpr (word")")))) in 
  pack nt1 (fun (lp ,(strdexp ,(dot,(exp, rp))))-> match strdexp with
  _ -> List.fold_right(fun a b -> ScmPair(a,b)) strdexp exp)
  str
and nt_quoted str =
  let nt = word "'" in
  let nt = pack (caten nt nt_sexpr) (fun(a,b)->ScmPair(ScmSymbol("quote"),ScmPair(b,ScmNil))) in
  nt str;
and nt_quasiquoted str = 
  let nt = word "`" in
  let nt = pack (caten nt nt_sexpr) (fun(a,b)->ScmPair(ScmSymbol("quasiquote"),ScmPair(b,ScmNil))) in
  nt str;
and nt_unquoted str =
  let nt = word "," in
  let nt = pack (caten nt nt_sexpr) (fun(a,b)->ScmPair(ScmSymbol("unquote"),ScmPair(b,ScmNil))) in
  nt str;
and nt_unquoteSpliced str =
  let nt = word ",@" in
  let nt = pack (caten nt nt_sexpr) (fun(a,b)->ScmPair(ScmSymbol("unquote-splicing"),(ScmPair(b,ScmNil)))) in
  nt str;
and nt_quoted_forms str = disj_list[(nt_quoted);(nt_quasiquoted);(nt_unquoted);(nt_unquoteSpliced)] str;
and nt_string_meta_char str =  
  let nt1 = disj_list [pack (word "\\\"") (fun _-> '\"');
    pack (word "\\t") (fun _-> '\t') ;
    pack (word "\\\\") (fun _-> '\\');
    pack (word "\\r") (fun _-> '\r');
    pack (word "\\n") (fun _-> '\n');
    pack (word "~~") (fun _-> '~');
    pack (word "\\f") (fun _-> '\012')] in
  nt1 str
and nt_string_literal_char str =
  let nt1 = range (char_of_int 0) (char_of_int 33) in
  let nt2 = range (char_of_int 35) (char_of_int 91) in
  let nt3 = range (char_of_int 93) (char_of_int 125) in
  let nt4 = range (char_of_int 127) (char_of_int 255) in
  let nt5 = pack (disj_list[nt1;nt2;nt3;nt4]) (fun(c) -> c) in
  nt5 str;

(* double check later *)
and nt_string_hex_char str = 
  let nt1 = disj (range '0' '9') (range 'a' 'f') in
  let nt2 = pack (word_ci "\\x") (fun _ -> ['0'; 'x']) in
  let nt3 = pack (caten (caten nt2 (plus nt1)) (char ';')) (fun ((p, list_hex), sem) -> (p@list_hex)) in
  let nt4 = pack nt3 (fun l -> char_of_int(int_of_string(list_to_string l))) in
  nt4 str;

and nt_string_char str = 
  let nt1 = disj_list[nt_string_literal_char;nt_string_hex_char;nt_string_meta_char] in
  nt1 str;
(* double check *)
and string_interpolated str = 
  let nt1 = word "~{" in
  let nt2 = word "}" in
  let prefix = unitify (pack (caten nt1 nt_skip_star) (fun _-> ScmVoid)) in
  let postfix = unitify (pack (caten nt_skip_star nt2) (fun _-> ScmVoid)) in
  let nt3 = caten (caten prefix nt_sexpr) postfix in
  let nt3 = pack nt3 (fun ((_,sexpr),_) -> List.fold_right (fun hd tl -> ScmPair(hd,tl))
    [ScmSymbol ("format");ScmString("~a");sexpr] ScmNil) in
  nt3 str

and nt_string str =
  let nt1 = char '\"' in
  let nt2 = pack (pack (plus nt_string_char) (fun e -> list_to_string e)) (fun str -> ScmString(str)) in
  let nt3 = caten (caten nt1 (star (disj nt2 string_interpolated))) nt1 in
  let nt4 = pack nt3 (fun ((_,st),_) -> match st with
    | [] -> ScmString("")
    | a::[]-> a
    | _ -> ScmPair(ScmSymbol("string-append"),List.fold_right (fun hd tl -> ScmPair(hd,tl))
      st ScmNil)) in
  nt4 str

and nt_sexpr str =
  let nt1 =
    disj_list [nt_number; nt_boolean; nt_char; nt_symbol;
      nt_string; nt_vector; nt_list; nt_quoted_forms] in
  let nt1 = make_skipped_star nt1 in
  nt1 str;;

end;; (* end of struct Reader *)

let rec string_of_sexpr = function
  | ScmVoid -> "#<void>"
  | ScmNil -> "()"
  | ScmBoolean(false) -> "#f"
  | ScmBoolean(true) -> "#t"
  | ScmChar('\n') -> "#\\newline"
  | ScmChar('\r') -> "#\\return"
  | ScmChar('\012') -> "#\\page"
  | ScmChar('\t') -> "#\\tab"
  | ScmChar(' ') -> "#\\space"
  | ScmChar(ch) ->
     if (ch < ' ')
     then let n = int_of_char ch in
          Printf.sprintf "#\\x%x" n
     else Printf.sprintf "#\\%c" ch
  | ScmString(str) ->
     Printf.sprintf "\"%s\""
       (String.concat ""
          (List.map
             (function
              | '\n' -> "\\n"
              | '\012' -> "\\f"
              | '\r' -> "\\r"
              | '\t' -> "\\t"
              | ch ->
                 if (ch < ' ')
                 then Printf.sprintf "\\x%x;" (int_of_char ch)
                 else Printf.sprintf "%c" ch)
             (string_to_list str)))
  | ScmSymbol(sym) -> sym
  | ScmNumber(ScmRational(0, _)) -> "0"
  | ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
  | ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
  | ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
  | ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
  | ScmVector(sexprs) ->
     let strings = List.map string_of_sexpr sexprs in
     let inner_string = String.concat " " strings in
     Printf.sprintf "#(%s)" inner_string
  | ScmPair(ScmSymbol "quote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "'%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "quasiquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "`%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote-splicing",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",@%s" (string_of_sexpr sexpr)
  | ScmPair(car, cdr) ->
     string_of_sexpr' (string_of_sexpr car) cdr
and string_of_sexpr' car_string = function
  | ScmNil -> Printf.sprintf "(%s)" car_string
  | ScmPair(cadr, cddr) ->
     let new_car_string =
       Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
     string_of_sexpr' new_car_string cddr
  | cdr ->
     let cdr_string = (string_of_sexpr cdr) in
     Printf.sprintf "(%s . %s)" car_string cdr_string;;
