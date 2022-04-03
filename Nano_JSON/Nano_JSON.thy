(***********************************************************************************
 * Copyright (c) 2019-2022 Achim D. Brucker
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 ***********************************************************************************)

section\<open>An Import/Export of JSON-like Formats for Isabelle/HOL\<close>
theory
  "Nano_JSON"
imports 
  Main 
keywords
      "import_JSON" :: thy_decl
  and "definition_JSON" :: thy_decl
  and "serialize_JSON" :: thy_decl

begin


text\<open>
  This theory implements an import/export format for Isabelle/HOL that is inspired by 
  JSON (JavaScript Object Notation). While the format defined in this theory is inspired 
  by the JSON standard (@{url "https://www.json.org"}), it is not fully compliant. Most 
  notably, 

  \<^item> only basic support for Unicode characters 
  \<^item> numbers are mapped to a polymorphic type, which can, e.g., be instantiated with 
    \<^item> @{term "real"} real, which is not a faithful representation of IEEE floating 
          point numbers and requires Complex\_Main
    \<^item> @{type "int"} we extended the abstract syntax to allow for representing integers as 
    \<^item> @{type "string"}.

  Still, our JSON-like import/expert should work with most real-world JSON files, i.e., simplifying 
  the data exchange between Isabelle/HOL and tools that can read/write JSON. 

  Overall, this theory should enable you to work with JSON encoded data in Isabelle/HOL without
  the need of implementing parsers or serialization in Isabelle/ML. You should be able to implement
  mapping from the Nano JSON HOL data types to your own data types on the level of Isabelle/HOL (i.e., 
  as executable HOL functions). Nevertheless, the provided ML routine that converts between the 
  ML representation and the HOL representation of Nano JSON can also serve as a starting point 
  for converting the ML representation to your own, domain-specific, HOL encoding. 
\<close>

subsection\<open>Defining a JSON-like Data Structure\<close>

datatype ('string, 'number) json = 
     OBJECT "('string * ('string, 'number) json) list"
     | ARRAY "('string, 'number) json list"
  | NUMBER "'number" 
  | STRING "'string" 
  | BOOL "bool" 
  | NULL 

subsection\<open>Example\<close>
text\<open>
  Using the data type @{typ "('string, 'number) json"}, we can now represent JSON encoded data 
  easily in HOL, e.g., using the concrete instance @{typ "(string, int) json"}:\<close>
definition example01::\<open>(string, int) json\<close> where 
"example01 = 
  OBJECT [(''menu'', OBJECT [(''id'', STRING ''file''), (''value'', STRING ''File''),
          (''popup'', OBJECT [(''menuitem'', ARRAY
                       [OBJECT [(''value'', STRING ''New''), (''onclick'', STRING ''CreateNewDoc()'')], 
                        OBJECT [(''value'', STRING ''Open''), (''onclick'', STRING ''OpenDoc()'')],
                        OBJECT [(''value'', STRING ''Close''), (''onclick'', STRING ''CloseDoc()'')]
                       ])]
           )]),(''flag'', BOOL True), (''number'', NUMBER 42)
]"

text\<open>
  The translation of the data type @{typ "('string, 'number) json"} to ML is straight forward with the exception 
  that we do not need to distinguish different String representations.
  In addition, we also 
  provide methods for converting JSON instances between the representation as Isabelle terms and 
  the representation as ML data structure.
\<close>

subsection\<open>ML Implementation\<close>


ML\<open>
signature NANO_JSON_TYPE = sig
    datatype NUMBER = INTEGER of int | REAL of IEEEReal.decimal_approx
    datatype json = OBJECT of (string * json) list
                  | ARRAY of json list
                  | NUMBER of NUMBER
                  | STRING of string
                  | BOOL of bool
                  | NULL

    val term_of_real: IEEEReal.decimal_approx -> term 
    val term_of_json: typ -> typ -> json -> term
    val json_of_term: term -> json
end
structure Nano_Json_Type : NANO_JSON_TYPE = struct
    datatype NUMBER = INTEGER of int | REAL of IEEEReal.decimal_approx
    datatype json = OBJECT of (string * json) list
                  | ARRAY of json list
                  | NUMBER of NUMBER
                  | STRING of string
                  | BOOL of bool
                  | NULL


    fun ieee_real_to_rat_approx (rat:IEEEReal.decimal_approx) = let
           (* val _ = warning ("Conversion of real numbers is not JSON compliant.") *)
           fun pow (_, 0) = 1  
             | pow (x, n) = if n mod 2 = 0 then pow (x*x, n div 2)  
                                           else x * pow (x*x, n div 2); 
           fun rat_of_dec rat = let
                 val sign = #sign rat
                 val digits = #digits rat
                 val exp = #exp rat
                 fun numerator_of _ [] = 0
                   | numerator_of c (x::xs) = x*pow(10,c) + (numerator_of (c+1) xs)
                 val numerator_abs = numerator_of 0 (rev digits)
                 val denominator = pow(10, (List.length digits - exp))  
               in
                 (if sign then ~ numerator_abs else numerator_abs, denominator)
               end
        in
          case #class rat of      
             IEEEReal.ZERO      => (0,0)
           | IEEEReal.SUBNORMAL => rat_of_dec rat
           | IEEEReal.NORMAL    => rat_of_dec rat 
           | IEEEReal.INF => error "Real is INF, not yet supported."
           | IEEEReal.NAN => error "Real is NaN, not yet supported."
        end


    fun mk_funT typ = Type("fun", typ)

    fun divide_classC realT = Const(@{const_name Rings.divide_class.divide} , mk_funT [realT, mk_funT [realT, realT]])
    fun mk_divide realT t1 t2 = (divide_classC realT) $ t1 $ t2
    fun mk_real_num realT i = HOLogic.mk_number realT i
    fun mk_real realT (p,q) = if q = 1 then mk_real_num realT p else mk_divide realT (mk_real_num realT p) (mk_real_num realT q)
    fun term_of_real  r = (mk_real HOLogic.realT (ieee_real_to_rat_approx r))

    fun dest_real (Const(@{const_name Rings.divide_class.divide} , _)$a$b) = 
                                      Real.toDecimal(Real.fromInt(HOLogic.dest_number a |> snd)
                                                       / Real.fromInt(HOLogic.dest_number b |> snd))
      | dest_real t = Real.toDecimal (Real.fromInt (HOLogic.dest_number t |> snd))

    fun json_real_of_term r   = (NUMBER (REAL (dest_real r)))
    fun mk_integer i = HOLogic.mk_number @{typ "int"} i



    fun json_int_of_term i    =   (NUMBER (INTEGER (snd (HOLogic.dest_number i)))) 
    fun json_string_of_term s = STRING (HOLogic.dest_string s)
    fun json_string_literal_of_term s = STRING (HOLogic.dest_literal s)

    fun mk_jsonT stringT numberT = Type(@{type_name "json"},[stringT, numberT])
    fun mk_json_object stringT numberT = Const(@{const_name OBJECT}, mk_funT [
        HOLogic.listT (HOLogic.mk_prodT (stringT, mk_jsonT stringT numberT)), mk_jsonT stringT numberT])

    fun mk_str (@{typ "string"}) s         = HOLogic.mk_string s
      | mk_str (@{typ "String.literal"}) s = HOLogic.mk_literal s
      | mk_str _ _ = error "String type not supported"

    fun mk_json_array stringT numberT = Const(@{const_name "ARRAY"}, mk_funT [HOLogic.listT (mk_jsonT stringT numberT), mk_jsonT stringT numberT])
    fun mk_json_number stringT numberT = Const(@{const_name "NUMBER"}, mk_funT [numberT, mk_jsonT stringT numberT])
    fun mk_json_string stringT numberT = Const(@{const_name "STRING"}, mk_funT [stringT, mk_jsonT stringT numberT])
    fun mk_json_bool stringT numberT = Const(@{const_name "BOOL"}, mk_funT [@{typ bool}, mk_jsonT stringT numberT])
    fun mk_json_null stringT numberT = Const(@{const_name "NULL"}, mk_jsonT stringT numberT)

    fun fix_tilde_sign s =  String.implode (map (fn #"~" => #"-" | c => c)
                                     (String.explode s))


    fun mk_number @{typ "int"} (INTEGER i)            = HOLogic.mk_number @{typ "int"} i
      | mk_number @{typ "nat"} (INTEGER i)            = if i >= 0 then HOLogic.mk_number @{typ "nat"} i
                                                        else error "mk_number: JSON contains negative number and target is nat."
      | mk_number @{typ "int"} (REAL r)             = error (String.concat["mk_number: JSON contains real number and target is nat or int: ", 
     IEEEReal.toString  r])
      | mk_number (Type("Real.real",[])) (INTEGER i) = term_of_real (Real.toDecimal (Real.fromInt i))
      | mk_number (Type("Real.real",[])) (REAL r)    = term_of_real  r

      | mk_number @{typ "string"} n         = (case n of 
                                                 (INTEGER i) => Int.toString i |> fix_tilde_sign |> HOLogic.mk_string
                                               | (REAL r)    => IEEEReal.toString r |> fix_tilde_sign |> HOLogic.mk_string 
                                                 ) 
      | mk_number @{typ "String.literal"} n  = (case n of 
                                                 (INTEGER i) => HOLogic.mk_literal (Int.toString i |> fix_tilde_sign)
                                               | (REAL r)    => HOLogic.mk_literal (IEEEReal.toString r |> fix_tilde_sign) 
                                                 )

      | mk_number _ _ = error "mk_number: type not supported"

    fun dest_funT (Type ("fun", [d,i])) = d


    fun json_of_number t n = case dest_funT t of 
                               (@{typ "int"}) => json_int_of_term n
                             | (@{typ "nat"}) => json_int_of_term n
                             | (Type("Real.real" , [])) => json_real_of_term n
                             | (@{typ "string"}) => json_string_of_term n
                             | (@{typ "String.literal"}) => json_string_literal_of_term n 
                             | (Type(x,_))  => error (String.concat["ERROR  in json_of_number: ", x] )
                             | _  => error "Unknown ERROR  in json_of_number."
                          
    fun json_of_string t s = 
                            case dest_funT t of 
                               (@{typ "string"}) => json_string_of_term s
                             | (@{typ "String.literal"}) => json_string_literal_of_term s 
                             | (Type(x,_))  => error (String.concat["ERROR  in json_of_string: ", x] )
                             | _  => error "Unknown ERROR  in json_of_string."

                                    
    fun term_of_json strT numT (OBJECT l) = mk_json_object strT numT 
                                  $(HOLogic.mk_list ((HOLogic.mk_prodT (strT, mk_jsonT strT numT )))  
                                    (map (fn (s,j) => HOLogic.mk_tuple[mk_str strT s, term_of_json strT numT j]) l))
      | term_of_json strT numT (ARRAY l)  = mk_json_array strT numT 
                                  $(HOLogic.mk_list ( mk_jsonT strT numT) (map (term_of_json strT numT) l))
      | term_of_json strT numT (NUMBER n) = (mk_json_number strT numT)$(mk_number numT n)  
      | term_of_json strT numT (STRING s) = (mk_json_string strT numT)$(mk_str strT s)
      | term_of_json strT numT (BOOL v)   = (mk_json_bool strT numT)$(if v then @{const "True"} else @{const "False"}) 
      | term_of_json strT numT  (NULL)    = mk_json_null strT numT 


fun string_of_typ (Type (s, _))     = s
  | string_of_typ (TFree (s, _))    = s
  | string_of_typ (TVar ((s,_), _)) = s;

    fun json_of_term t = let
        fun dest_key_value [string, json] = ((HOLogic.dest_string string, json_of json)
                                           handle _ => (HOLogic.dest_literal string, json_of json))
          | dest_key_value _              = error "dest_key_value: not a key-value pair." 
        and json_of (Const(@{const_name "OBJECT"}, _) $ l) = OBJECT (map (dest_key_value o HOLogic.strip_tuple) (HOLogic.dest_list l))
          | json_of (Const(@{const_name "ARRAY"}, _)  $ l) = ARRAY (map json_of (HOLogic.dest_list l))
          | json_of (Const(@{const_name "NUMBER"}, numT) $ n ) = json_of_number numT n 
          | json_of (Const(@{const_name "STRING"}, stringT) $ s) = json_of_string stringT s 
          | json_of (Const(@{const_name "BOOL"}, _) $ @{const "True"}) = BOOL true
          | json_of (Const(@{const_name "BOOL"}, _) $ @{const "False"}) = BOOL false
          | json_of (Const(@{const_name "NULL"}, _))  = NULL
          | json_of t = error (String.concat ["Term not supported in json_of_term: ", string_of_typ (type_of t)])



    in
        case type_of t of 
          Type("Nano_JSON.json",[strT,numT]) => json_of t 
          | _ => error (String.concat ["Term not of type json: ", string_of_typ (type_of t)])
    end
end
\<close>

ML\<open>
  val x = @{typ "(dummy, dummy) json"}
  val y = Type("Nano_JSON.json",[dummyT,dummyT])
\<close>

section\<open>Parsing Nano JSON\<close>

text\<open>
  In this section, we define the infrastructure for parsing JSON-like data structures as
  well as for importing them into Isabelle/HOL. This implementation was inspired by the 
  ``Simple Standard ML JSON parser'' from Chris Cannam.
\<close>

subsection\<open>ML Implementation\<close>
subsubsection\<open>Lexer\<close>
ML\<open>
signature NANO_JSON_LEXER = sig
    structure T : sig
        datatype token = NUMBER of char list
                       | STRING of string
                       | BOOL of bool
                       | NULL
                       | CURLY_L
                       | CURLY_R
                       | SQUARE_L
                       | SQUARE_R
                       | COLON
                       | COMMA

        val string_of_T : token -> string
    end
    val tokenize_string: string -> T.token list
end
\<close>
ML\<open>

structure Nano_Json_Lexer : NANO_JSON_LEXER = struct
    structure T = struct
        datatype token = NUMBER of char list
                       | STRING of string
                       | BOOL of bool
                       | NULL
                       | CURLY_L
                       | CURLY_R
                       | SQUARE_L
                       | SQUARE_R
                       | COLON
                       | COMMA

        fun string_of_T t =
            case t of NUMBER digits => String.implode digits
                    | STRING s => s
                    | BOOL b => Bool.toString b
                    | NULL => "null"
                    | CURLY_L => "{"
                    | CURLY_R => "}"
                    | SQUARE_L => "["
                    | SQUARE_R => "]"
                    | COLON => ":"
                    | COMMA => ","
    end

    fun lexer_error pos text = error (text ^ " at character position " ^
                                Int.toString (pos - 1))
    fun token_error pos = lexer_error pos ("Unexpected token")

    fun bmp_to_utf8 cp = map (Char.chr o Word.toInt)
                         (if cp < 0wx80 
                          then [cp]
                          else if cp < 0wx800 
                               then [Word.orb(0wxc0, Word.>>(cp,0w6)), 
                                      Word.orb(0wx8, Word.andb (cp, 0wx3f))]
                               else if cp < 0wx10000 
                                    then [Word.orb(0wxe0,Word.>>(cp, 0w12)),
                                          Word.orb(0wx80, Word.andb(Word.>>(cp,0w6), 0wx3f)),
                                          Word.orb(0wx80,Word.andb(cp, 0wx3f))]
                                    else error ("Invalid BMP point  in bmp_to_utf8 " ^ (Word.toString cp)))

    fun lexNull pos acc (#"u" :: #"l" :: #"l" :: xs) =
        lex (pos + 3) (T.NULL :: acc) xs
      | lexNull pos _  _ = token_error pos

    and lexTrue pos acc (#"r" :: #"u" :: #"e" :: xs) =
        lex (pos + 3) (T.BOOL true :: acc) xs
      | lexTrue pos _ _ = token_error pos

    and lexFalse pos acc (#"a" :: #"l" :: #"s" :: #"e" :: xs) =
        lex (pos + 4) (T.BOOL false :: acc) xs
      | lexFalse pos _ _ = token_error pos

    and lexChar tok pos acc xs =
        lex pos (tok :: acc) xs
        
    and lexString pos acc cc =
        let datatype escaped = ESCAPED | NORMAL
            fun lexString' pos _ ESCAPED [] =
                lexer_error pos "End of input during escape sequence"
              | lexString' pos _ NORMAL [] = 
                lexer_error pos "End of input during string"
              | lexString' pos text ESCAPED (x :: xs) =
                let fun esc c = lexString' (pos + 1) (c :: text) NORMAL xs
                in case x of
                       #"\"" => esc x
                     | #"\\" => esc x
                     | #"/"  => esc x
                     | #"b"  => esc #"\b"
                     | #"f"  => esc #"\f"
                     | #"n"  => esc #"\n"
                     | #"r"  => esc #"\r"
                     | #"t"  => esc #"\t"
                     | _     => lexer_error pos ("Invalid escape \\" ^
                                           Char.toString x)
                end
              | lexString' pos text NORMAL (#"\\" :: #"u" ::a::b::c::d:: xs) =
                if List.all Char.isHexDigit [a,b,c,d]
                then case Word.fromString ("0wx" ^ (String.implode [a,b,c,d])) of
                         SOME w => (let val utf = rev (bmp_to_utf8 w) in
                                        lexString' (pos + 6) (utf @ text)
                                                   NORMAL xs
                                    end
                                    handle Fail err => lexer_error pos err)
                       | NONE => lexer_error pos "Invalid Unicode BMP escape sequence"
                else lexer_error pos "Invalid Unicode BMP escape sequence"
              | lexString' pos text NORMAL (x :: xs) =
                if Char.ord x < 0x20
                then lexer_error pos "Invalid unescaped control character"
                else
                    case x of
                        #"\"" => (rev text, xs, pos + 1)
                      | #"\\" => lexString' (pos + 1) text ESCAPED xs
                      | _     => lexString' (pos + 1) (x :: text) NORMAL xs
          val (text, rest, newpos) = lexString' pos [] NORMAL cc
        in
                lex newpos (T.STRING (String.implode text) :: acc) rest
        end

    and lexNumber firstChar pos acc cc =
        let val valid = String.explode ".+-e"
            fun lexNumber' pos digits [] = (rev digits, [], pos)
              | lexNumber' pos digits (x :: xs) =
                if x = #"E" then lexNumber' (pos + 1) (#"e" :: digits) xs
                else if Char.isDigit x orelse List.exists (fn c => x = c) valid
                then lexNumber' (pos + 1) (x :: digits) xs
                else (rev digits, x :: xs, pos)
            val (digits, rest, newpos) =
                lexNumber' (pos - 1) [] (firstChar :: cc)
        in
            case digits of
                [] => token_error pos
              | _ => lex newpos (T.NUMBER digits :: acc) rest
        end
                                           
    and lex _ acc [] = rev acc
      | lex pos acc (x::xs) = 
        (case x of
             #" "  => lex
           | #"\t" => lex
           | #"\n" => lex
           | #"\r" => lex
           | #"{"  => lexChar T.CURLY_L
           | #"}"  => lexChar T.CURLY_R
           | #"["  => lexChar T.SQUARE_L
           | #"]"  => lexChar T.SQUARE_R
           | #":"  => lexChar T.COLON
           | #","  => lexChar T.COMMA
           | #"\"" => lexString
           | #"t"  => lexTrue
           | #"f"  => lexFalse
           | #"n"  => lexNull
           | x     => lexNumber x) (pos + 1) acc xs

    fun tokenize_string str = lex 1 [] (String.explode str)
end
\<close>

subsubsection\<open>Parser\<close>
ML\<open>

signature NANO_JSON_PARSER = sig
    val json_of_string : string -> Nano_Json_Type.json
    val term_of_json_string : typ -> typ -> string -> term
    val numT: theory -> string -> typ
    val stringT: string -> typ
end

structure Nano_Json_Parser : NANO_JSON_PARSER  = struct 
    open Nano_Json_Type 
    open Nano_Json_Lexer

    fun show [] = "end of input"
      | show (tok :: _) = T.string_of_T tok

    val parse_error = error

    fun parseNumber digits =
        let open Char

            fun okExpDigits [] = false
              | okExpDigits (c :: []) = isDigit c
              | okExpDigits (c :: cs) = isDigit c andalso okExpDigits cs

            fun okExponent [] = false
              | okExponent (#"+" :: cs) = okExpDigits cs
              | okExponent (#"-" :: cs) = okExpDigits cs
              | okExponent cc = okExpDigits cc

            fun okFracTrailing [] = true
              | okFracTrailing (c :: cs) =
                (isDigit c andalso okFracTrailing cs) orelse
                (c = #"e" andalso okExponent cs)

            fun okFraction [] = false
              | okFraction (c :: cs) =
                isDigit c andalso okFracTrailing cs

            fun okPosTrailing [] = true
              | okPosTrailing (#"." :: cs) = okFraction cs
              | okPosTrailing (#"e" :: cs) = okExponent cs
              | okPosTrailing (c :: cs) =
                isDigit c andalso okPosTrailing cs
                                                      
            fun okPositive [] = false
              | okPositive (#"0" :: []) = true
              | okPositive (#"0" :: #"." :: cs) = okFraction cs
              | okPositive (#"0" :: #"e" :: cs) = okExponent cs
              | okPositive (#"0" :: _) = false
              | okPositive (c :: cs) = isDigit c andalso okPosTrailing cs
                    
            fun okNumber (#"-" :: cs) = okPositive cs
              | okNumber cc = okPositive cc
            fun getPositive (#"-" :: cs) = cs
              | getPositive  cc = cc

        in
            if okNumber digits then let 
                val number = String.implode digits
            in  
              if List.all (Char.isDigit) (getPositive digits)
              then   (case Int.fromString (String.implode digits) of
                     NONE => parse_error "Number out of range"
                   | SOME i =>  INTEGER i)
              else   (case IEEEReal.fromString (String.implode digits) of
                     NONE => parse_error "Number out of range"
                   | SOME r => REAL r) 
            end
            else parse_error ("Invalid number \"" ^ (String.implode digits) ^ "\"")
        end
                                     
    fun parseObject (T.CURLY_R :: xs) =  (OBJECT [], xs)
      | parseObject tokens =
        let fun parsePair (T.STRING key :: T.COLON :: xs) = let 
                    val (j, xs) = parseTokens xs
                in
                    ((key, j), xs)
                end
              | parsePair other =
                parse_error("Object key/value pair expected around \"" ^
                       show other ^ "\"")
            fun parseObject' _ [] = parse_error "End of input during object"
              | parseObject' acc tokens =
                case parsePair tokens of
                    (pair, T.COMMA :: xs) =>
                    parseObject' (pair :: acc) xs
                  | (pair, T.CURLY_R :: xs) =>
                    (OBJECT (rev (pair :: acc)), xs)
                  | (_, _) =>parse_error "Expected , or } after object element"
        in
            parseObject' [] tokens
        end

    and parseArray (T.SQUARE_R :: xs) =  (ARRAY [], xs)
      | parseArray tokens =
        let fun parseArray' _ [] = error "End of input during array"
              | parseArray' acc tokens =
                case parseTokens tokens of
                    (j, T.COMMA :: xs) => parseArray' (j :: acc) xs
                  | (j, T.SQUARE_R :: xs) => (ARRAY (rev (j :: acc)), xs)
                  | (_, _) => error "Expected , or ] after array element"
        in
            parseArray' [] tokens
        end

    and parseTokens [] = parse_error "Value expected"
      | parseTokens (tok :: xs) =
        (case tok of
             T.NUMBER d => (NUMBER ((parseNumber d)), xs)
           | T.STRING s => (STRING s, xs)
           | T.BOOL b   => (BOOL b, xs)
           | T.NULL     => (NULL, xs)
           | T.CURLY_L  => parseObject xs
           | T.SQUARE_L => parseArray xs
           | _ => parse_error ("Unexpected token " ^ T.string_of_T tok ^
                         " before " ^ show xs))
                                   
    fun json_of_string str = case parseTokens (Nano_Json_Lexer.tokenize_string str) of
                            (value, []) =>  value
                          | (_, _) => parse_error "Extra data after input"
    fun term_of_json_string strT numT = (term_of_json strT numT) o json_of_string

    fun checkReal thy = SOME (Thm.global_ctyp_of thy  HOLogic.realT)
                                                handle _ => NONE 


 fun numT thy x = case x of 
                 "int" => @{typ \<open>int\<close>} 
               | "nat" => @{typ \<open>nat\<close>} 
               | "real" =>  ( case checkReal thy of 
                              SOME _ => HOLogic.realT
                              |NONE => error ("Using 'real' requires the import of the theory 'Main_Complex' ('Real')."))
               | "string" =>  @{typ \<open>string\<close>} 
               | "String.literal" => @{typ \<open>String.literal\<close>}
               | "" => ( case checkReal thy of 
                              SOME _ => HOLogic.realT
                              |NONE => @{typ \<open>int\<close>})
               | _ => error (String.concat ["Only 'nat', 'int', 'real', 'string', and 'String.literal' are supported for numbers, got '",x,"'"]) 

fun stringT x = case x of 
                 "" => @{typ \<open>string\<close>}
               | "string" =>  @{typ \<open>string\<close>} 
               | "String.literal" => @{typ \<open>String.literal\<close>}
               | _ => error (String.concat ["Only 'string' and 'String.literal' are supported for strings, got '",x,"'"]) 


end
\<close>

ML\<open>

Nano_Json_Parser.term_of_json_string (@{typ string}) (@{typ int}) "{\"name\": [true,false,\"test\"]}"
\<close>
subsection\<open>Isar Setup\<close>

subsubsection\<open>The JSON Cartouche\<close>

ML\<open>
Scan.lift Args.cartouche_input
\<close>


syntax "_cartouche_nano_json" :: "cartouche_position \<Rightarrow> 'a"  ("JSON _")
parse_translation\<open>
let
  fun translation strT numT args =
    let
      fun err () = raise TERM ("Common._cartouche_nano_json", args)
      fun input s pos = Symbol_Pos.implode (Symbol_Pos.cartouche_content (Symbol_Pos.explode (s, pos)))
    in
      case args of
        [(c as Const (@{syntax_const "_constrain"}, _)) $ Free (s, _) $ p] =>
          (case Term_Position.decode_position p of
            SOME (pos, _) => c $ Nano_Json_Parser.term_of_json_string strT numT (input s pos) $ p
          | NONE => err ())
      | _ => err ()
  end
in
  [(@{syntax_const "_cartouche_nano_json"}, K (translation (Nano_Json_Parser.stringT "string") 
               (Nano_Json_Parser.numT (Context.the_global_context()) "int" )))] (* TODO *)
end
\<close>  

(* Antiqoutation with config *)

lemma \<open>y == JSON \<open>{"name": true}\<close> \<close>
  oops 



lemma \<open>y == JSON\<open>{"name": [true,false,"test"]}\<close> \<close>
  oops
lemma \<open>y == JSON\<open>{"name": [true,false,"test"],
                  "bool": true, 
                  "number" : 1 }\<close> \<close>
  oops


subsubsection\<open>Isar Top-Level Commands\<close>
ML\<open>
structure Nano_Json_Parser_Isar = struct
    fun make_const_def (binding, trm) lthy = let
            val lthy' =  snd ( Local_Theory.begin_nested lthy )
            val arg = ((binding, NoSyn), ((Thm.def_binding binding,@{attributes [code]}), trm)) 
            val ((_, (_ , thm)), lthy'') = Local_Theory.define arg lthy'
        in
            (thm, Local_Theory.end_nested lthy'')
        end


    fun def_json strN numN name json lthy = let 
            val thy = Proof_Context.theory_of lthy    
            val strT = Nano_Json_Parser.stringT strN 
            val numT = Nano_Json_Parser.numT thy numN
    in 
       (snd o (make_const_def (Binding.name name, Nano_Json_Parser.term_of_json_string strT numT json ))) lthy
    end 
    fun def_json_file strN numN name (filename:string) (lthy:local_theory) = let 
            val abs_filename = Resources.check_file lthy NONE (Syntax.read_input filename) 
            val json = File.read abs_filename
            val chksum = SHA1.digest json
            val provide = Resources.provide (abs_filename, chksum)
            val lthy' = Local_Theory.background_theory provide lthy
                        handle (ERROR _) => lthy
        in
            def_json strN numN name json lthy'
        end
    val typeCfgParse  = Scan.optional (Args.parens (Parse.name -- Args.$$$ "," -- Parse.name)) (("",""),"");
    val jsonFileP = typeCfgParse -- (Parse.name -- Parse.name)
    val jsonP = typeCfgParse -- (Parse.name -- Parse.cartouche)


end
\<close>

ML\<open>
val _ = Outer_Syntax.local_theory @{command_keyword "definition_JSON"} "Define JSON." 
        (Nano_Json_Parser_Isar.jsonP >>  (fn (((stringN, _), numN), (name, json))  
        => Nano_Json_Parser_Isar.def_json stringN numN name json));
val _ = Outer_Syntax.local_theory @{command_keyword "import_JSON"} "Define JSON from file." 
        (Nano_Json_Parser_Isar.jsonFileP >>  (fn (((stringN,_),numN),(name, filename))  => 
        Nano_Json_Parser_Isar.def_json_file stringN numN name filename));
\<close>



import_JSON  example03 "example.json"

thm example03_def

import_JSON (string,int) example04 "example.json"


thm example03_def
thm example04_def


subsection\<open>Examples\<close>

text\<open>
Now we can use the JSON Cartouche for defining JSON-like data ``on-the-fly'', e.g.:
\<close>

  text\<open>
  Note that you need to escape quotes within the JSON Cartouche, if you are using 
  quotes as lemma delimiters, e.g.,:
\<close>
lemma "y == JSON\<open>{\"name\": [true,false,\"test\"]}\<close>"
  oops
text\<open>
  Thus, we recommend to use the Cartouche delimiters when using the JSON Cartouche with non 
  trivial data structures:
\<close>

lemma \<open> example01 == JSON \<open>{"menu": {
                            "id": "file",
                            "value": "File",
                            "popup": {
                              "menuitem": [
                               {"value": "New", "onclick": "CreateNewDoc()"},
                               {"value": "Open", "onclick": "OpenDoc()"},
                               {"value": "Close", "onclick": "CloseDoc()"}
                              ] 
                            }},
                           "flag": true,
                           "number": 42
                           }\<close>\<close>
  by(simp add: example01_def)

text\<open>
  Using the top level Isar commands defined in the last section, we can now easily define
  JSON-like data: 
\<close>

definition_JSON example02 \<open>
{"menu": {
  "id": "file",
  "value": "File",
  "popup": {
    "menuitem": [
      {"value": "New", "onclick": "CreateNewDoc()"},
      {"value": "Open", "onclick": "OpenDoc()"},
      {"value": "Close", "onclick": "CloseDoc()"}
    ]
  }
}, "flag":true, "number":42}
\<close>
thm example02_def


definition_JSON (String.literal,int) example02' \<open>
{"menu": {
  "id": "file",
  "value": "File",
  "popup": {
    "menuitem": [
      {"value": "New", "onclick": "CreateNewDoc()"},
      {"value": "Open", "onclick": "OpenDoc()"},
      {"value": "Close", "onclick": "CloseDoc()"}
    ]
  }
}, "flag":true, "number":42}
\<close>
thm example02'_def


ML\<open> 
@{term \<open>JSON\<open>{"number":31}\<close>\<close>}
\<close>

lemma "example01 = example02"
  by(simp add: example01_def example02_def)

text\<open>
  Moreover, we can import JSON from external files:
\<close>

import_JSON example03' "example.json"
thm example03'_def

lemma "example01 = example03"
  by(simp add: example01_def example03_def)

section\<open>Serializing Nano JSON\<close>

text\<open>
  In this section, we define the necessary infrastructure to serialize (export) data from HOL using 
  a JSON-like data structure that other JSON tools should be able to import.
\<close>

subsection\<open>ML Implementation\<close>
ML\<open>
signature NANO_JSON_SERIALIZER = sig
    val serialize_json: Nano_Json_Type.json -> string
    val serialize_json_pretty: Nano_Json_Type.json -> string
    val serialize_term: term -> string
    val serialize_term_pretty: term -> string
end

structure Nano_Json_Serializer : NANO_JSON_SERIALIZER = struct
     open Nano_Json_Type 

    fun escapeJsonString s =
        let fun bs c = "\\"^(Char.toString c)
            fun escape #"\"" = bs #"\"" 
              | escape #"\\" = bs #"\\" 
              | escape #"\b" = bs #"b"
              | escape #"\f" = bs #"f"
              | escape #"\n" = bs #"n"
              | escape #"\r" = bs #"r"
              | escape #"\t" = bs #"t"
              | escape c = 
                let val ord = Char.ord c
                in
                    if ord < 0x20
                    then let val hex = Word.toString (Word.fromInt ord)
                             val prfx = if ord < 0x10 then "\\u000" else "\\u00"
                         in  
                             prfx^hex
                         end
                    else
                    Char.toString c
                end
        in
            String.concat (map escape (String.explode s))
        end

    fun serialize pretty json = let 
            val nl = if pretty = NONE then "" else "\n"
            fun indent' 0 = ""
              | indent' n = " "^(indent' (n-1)) 
            fun indent n = (case pretty of NONE => "" 
                                         | SOME n' => indent' (n+n'))
            fun serialize' _ (OBJECT []) = "{}"
              | serialize' _ (ARRAY []) = "[]"
              | serialize' n (OBJECT pp) = "{"^nl^(indent (n+1)) ^ String.concatWith
                                   (","^nl^(indent (n+1))) 
                                   (map (fn (key, value) =>
                                                serialize' (n+1) (STRING key) ^ ":" ^
                                                serialize' (n+1) value) pp) ^
                                   nl^(indent n)^"}"
              | serialize' n (ARRAY arr) = "["^nl^(indent (n+1)) ^ String.concatWith
                                           (","^nl^(indent (n+1)))
                                           (map (serialize' (n+1) ) arr) ^
                                   nl^(indent n)^"]"
              | serialize' _ (NUMBER (REAL n)) = String.implode (map (fn #"~" => #"-" | c => c)
                                     (String.explode (IEEEReal.toString n)))
              | serialize' _ (NUMBER (INTEGER n)) = String.implode (map (fn #"~" => #"-" | c => c)
                                     (String.explode (Int.toString n)))
              | serialize' _ (STRING s) = "\"" ^ escapeJsonString s ^ "\""
              | serialize' _ (BOOL b) = Bool.toString b
              | serialize' _ NULL = "null"
            
        in
            (serialize' 0 json)^nl
        end

    val serialize_json = serialize NONE
    val serialize_json_pretty = serialize (SOME 0)
    val serialize_term = (serialize NONE) o json_of_term
    val serialize_term_pretty = (serialize (SOME 0)) o json_of_term
end
\<close>

subsection\<open>Isar Setup\<close>
ML\<open>
structure Nano_Json_Serialize_Isar = struct
  fun export_json thy json_const filename =
    let
        val term = Thm.concl_of (Global_Theory.get_thm thy (json_const^"_def"))
         fun export binding content thy =
  let
    val thy' = thy |> Generated_Files.add_files (binding, content);
    val _ = Export.export thy' binding [XML.Text content];
  in thy' end;
        val json_term = case term of
                              Const (@{const_name "Pure.eq"}, _) $ _ $ json_term => json_term
                           |  _ $ (_ $ json_term) => json_term
                           | _ => error ("Term structure not supported.")
        val json_string  = Nano_Json_Serializer.serialize_term_pretty json_term 
    in
        case filename of 
             SOME filename => let 
                                val filename = Path.explode (filename^".json")
                                val thy' = export (Path.binding (Path.append (Path.explode "json") 
                                                   filename,Position.none)) json_string thy
                                val _ =  writeln (Export.message thy (Path.basic "json"))
                              in
                                 thy'                                 
                              end
           | NONE =>  (tracing json_string; thy) 
    end
end
\<close>

ML\<open>
  Outer_Syntax.command ("serialize_JSON", Position.none) "export JSON data to an external file"
  (Parse.name -- Scan.option Parse.name  >> (fn (const_name,filename) =>
    (Toplevel.theory (fn state => Nano_Json_Serialize_Isar.export_json state const_name filename))));
\<close>


subsection\<open>Examples\<close>
text\<open>
  We can now serialize JSON and print the result in the output window of Isabelle/HOL:
\<close>
serialize_JSON example02
thm example01_def

text\<open>
  Alternatively, we can export the serialized JSON into a file:
\<close>
serialize_JSON example01 example01.json

section\<open>Putting Everything Together\<close>
text\<open>
  For convenience, we provide an ML structure that provides access to both the parser and the 
  serializer:,  
\<close>
ML\<open>
structure Nano_Json = struct
    open Nano_Json_Type 
    open Nano_Json_Parser
    open Nano_Json_Serializer
end
\<close>

end
