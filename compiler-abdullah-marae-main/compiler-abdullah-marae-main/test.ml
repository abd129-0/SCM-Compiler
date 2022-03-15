#use "pc.ml";;
open PC;;


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

let unitify nt = pack nt (fun _ -> ());;

let nt_end_of_line_or_file str =
  let nt1 = unitify (char '\n') in
  let nt2 = unitify nt_end_of_input in
  let nt1 = disj nt1 nt2 in
  nt1 str

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

let rec nt_boolean str =
  let nt1 = word_ci "#f" in
  let nt1 = pack nt1 (fun _ -> false) in
  let nt2 = word_ci "#t" in
  let nt2 = pack nt2 (fun _ -> true) in
  let nt1 = disj nt1 nt2 in
  let nt1 = pack nt1 (fun b-> ScmBoolean b) in
  nt1 str;
and nt_line_comment = 
  let nt1 = char ';' in
  let nt2 = diff nt_any nt_end_of_line_or_file in
  let nt2 = star nt2 in
  let nt1 = caten nt1 (caten nt2 nt_end_of_line_or_file) in
  let nt1 = unitify nt1 in
  nt1;
and nt_char_simple str =
  let nt1 = diff nt_any nt_whitespace in
  let nt1 = not_followed_by nt1 nt1 in
  nt1 str;
and nt_char_hex str = 
  let nt1 = char_ci 'x' in
  let nt2 = plus (disj_list [range '0' '9'; range_ci 'a' 'f']) in
  let nt2 = caten nt1 nt2 in
  let nt3 = pack nt2 (fun(x, num) -> char_of_int(int_of_string("0x" ^ list_to_string(num)))) in
  nt3 str;
and nt_int str = 
  let nt1 = maybe sign in
  let nt2 = caten nt1 natural in
  let nt3 = pack nt2 (fun(sign, num) -> match sign with 
    | Some '+' -> num
    | Some '-' -> (-1)*num
    | None -> num
    | _ -> assert false) in
  nt3 str
and nt_integer_part str = 
  let nt1 = range '0' '9' in
  let nt1 = plus nt1 in
  let nt2 = pack nt1 (fun (num)-> float_of_string(list_to_string(num))) in
  nt2 str
and nt_mantissa str = 
  let nt1 = range '0' '9' in
  let nt1 = plus nt1 in
  let nt2 = pack nt1 (fun (num)-> float_of_string("0." ^ list_to_string(num))) in
  nt2 str
and nt_exponent str = 
  let nt = disj_list [word "e"; word "E"; word "*10^"; word "*10**"] in
  let nt = caten nt nt_int in
  let nt1 = pack nt (fun(token,num)-> 10.**(float_of_int num)) in
  nt1 str
and nt_float str = 
  let nt1 = pack (disj_list[(nt_floatC);(nt_floatB);(nt_floatA)]) (fun(v)-> ScmReal v) in
  nt1 str;
and nt_floatA str = 
  let nt1 = caten nt_integer_part (caten (char '.') (caten (maybe nt_mantissa) (maybe nt_exponent))) in
  let nt1 = pack nt1 (fun (int_part, (dot, (mant, expo))) -> match mant,expo with 
    | Some m,Some e ->(int_part +. m) *. e 
    | Some m,None -> int_part +. m
    | None,Some e -> int_part *. e
    | None,None -> int_part) in
  nt1 str;
and nt_floatB str =
  let nt1 = caten (char '.') (caten  nt_mantissa (maybe nt_exponent)) in
  let nt1 = pack nt1 (fun (dot, (mant, expo)) -> match expo with
    | Some e ->  mant *. e
    | None -> mant) in
  nt1 str;
and nt_floatC str =
  let nt1 = caten nt_integer_part nt_exponent in
  let nt1 = pack nt1 (fun (int_part,expo) -> int_part *. expo) in
  nt1 str;
and nt_symbol_char str = 
  let nt = disj_list [(range '0' '9');(range_ci 'a' 'z');(char '!');(char '$');(char '^');(char '*');(char '-');(char '_');(char '=');(char '+');(char '<');(char '>');(char '?');(char '/');(char ':');] in
  nt str;
and nt_symbol str =
  let nt1 = plus nt_symbol_char in
  let nt1 = pack nt1 list_to_string in
  let nt1 = pack nt1 (fun name -> ScmSymbol name) in
  nt1 str;
and make_named_char char_name ch = pack (word_ci char_name) (fun e -> ch)
and nt_char_named str =
  let nt1 =
    disj_list [(make_named_char "newline" '\n');
               (make_named_char "page" '\012');
               (make_named_char "return" '\r');
               (make_named_char "space" ' ');
               (make_named_char "tab" '\t')] in
  nt1 str;
and nt_char str = 
  let nt1 = disj_list [nt_char_hex;nt_char_named;nt_char_simple] in
  let nt2 = caten char_prefix nt1 in
  let nt3 = pack nt2 (fun(pre,ch)-> ScmChar ch) in
  nt3 str;
and string_meta_char str = 
  let nt1 =
    disj_list [(make_named_char "\\" '\\');
               (make_named_char "\"" '"');
               (make_named_char "\t" '\t');
               (make_named_char "\\f" '\012');
               (make_named_char "\n" '\n');
               (make_named_char "\r" '\r');
               (make_named_char "~~" '~')] in
  nt1 str;
  let nt = disj_list [char '\\';char '\"';char '\t';char '\n';char '\r';char '~';char 'f'] in
  nt str;
and nt_string_literal_char str = 
  let nt1 = range (char_of_int 0) (char_of_int 33) in
  let nt2 = range (char_of_int 35) (char_of_int 91) in
  let nt3 = range (char_of_int 93) (char_of_int 255) in
  let nt4 = pack (disj_list[nt1;nt2;nt3]) (fun(c) -> c) in
  nt4 str;
and nt_string_hex_char str = 
  let nt1 = disj (range '0' '9') (range 'a' 'f') in
  let nt2 = pack (word_ci "\\x") (fun _ -> ['0'; 'x']) in
  let nt3 = pack (caten (caten nt2 (plus nt1)) (char ';')) (fun ((p, list_hex), sem) -> (p@list_hex)) in
  let nt4 = pack nt3 (fun l -> char_of_int(int_of_string(list_to_string l))) in
  nt4 str;
and nt_string_char str = 
  let nt1 = disj_list[nt_string_literal_char;nt_string_hex_char;string_meta_char] in
  let nt1 = pack nt1 (fun c -> c) in
  nt1 str;
and nt_string str = 
  let nt1 = pack (star nt_string_char) (fun l-> (list_to_string l)) in
  let nt1 = pack (caten (char '"') (caten nt1 (char '"'))) (fun (q, (s, q_)) -> ScmString(s)) in
  nt1 str;;