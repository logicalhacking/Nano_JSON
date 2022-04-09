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
      "JSON_file" :: thy_load
  and "JSON" :: thy_decl
  and "JSON_export" :: thy_decl
  and "defining"::quasi_command

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
\<close>
ML_file Nano_JSON_Type.ML


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
ML_file Nano_JSON_Lexer.ML

subsubsection\<open>Parser\<close>

ML\<open>
  val json_num_type = let
    val (json_num_type_config, json_num_type_setup) =
      Attrib.config_string (Binding.name "JSON_num_type") (K "int")
  in
    Context.>>(Context.map_theory json_num_type_setup);
    json_num_type_config
  end
  val json_string_type = let
    val (json_string_type_config, json_string_type_setup) =
      Attrib.config_string (Binding.name "JSON_string_type") (K "string")
  in
    Context.>>(Context.map_theory json_string_type_setup);
    json_string_type_config
  end
  val json_verbose = let
    val (json_string_type_config, json_string_type_setup) =
      Attrib.config_bool (Binding.name "JSON_verbose") (K false)
  in
    Context.>>(Context.map_theory json_string_type_setup);
    json_string_type_config
  end


\<close>

ML\<open>

signature NANO_JSON_PARSER = sig
    val json_of_string : string -> Nano_Json_Type.json
    val term_of_json_string : typ -> typ -> string -> term
    val numT: theory -> typ
    val stringT: theory -> typ
end
\<close>

ML_file "Nano_JSON_Parser.ML"

ML\<open>

Nano_Json_Parser.term_of_json_string (@{typ string}) (@{typ int}) "{\"name\": [true,false,\"test\"]}"
\<close>
subsection\<open>Isar Setup\<close>

subsubsection\<open>The JSON Cartouche\<close>

syntax "_cartouche_nano_json" :: "cartouche_position \<Rightarrow> 'a"  ("JSON _")
parse_translation\<open> 
let
  fun translation u args = let
      val thy = Context.the_global_context u
      val strT = Nano_Json_Parser.stringT thy
      val numT = Nano_Json_Parser.numT thy
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
  [(@{syntax_const "_cartouche_nano_json"}, K (translation ()))] 
end
\<close>  

declare [[JSON_string_type = string]]
lemma \<open>y == JSON \<open>{"name": true}\<close> \<close>
  oops

declare [[JSON_string_type = String.literal]]
lemma \<open>y == JSON \<open>{"name": true}\<close> \<close>
  oops 
declare [[JSON_string_type = string]]

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


    fun def_json name json lthy = let 
            val thy = Proof_Context.theory_of lthy    
            val strT = Nano_Json_Parser.stringT thy  
            val numT = Nano_Json_Parser.numT thy 
    in 
       (snd o (make_const_def (Binding.name name, Nano_Json_Parser.term_of_json_string strT numT json ))) lthy
    end 

    val typeCfgParse  = Scan.optional (Args.parens (Parse.name -- Args.$$$ "," -- Parse.name)) (("",""),"");
    val jsonP = (Parse.name -- Parse.cartouche)

end
\<close>


ML\<open>
val _ = Outer_Syntax.local_theory @{command_keyword "JSON"} "Define JSON." 
        ((Parse.cartouche -- \<^keyword>\<open>defining\<close> -- Parse.name) >>  (fn ((json, _), name)  
        => Nano_Json_Parser_Isar.def_json name json))

val _ = Outer_Syntax.command \<^command_keyword>\<open>JSON_file\<close> "Import JSON and bind it to a definition."
        ((Resources.parse_file -- \<^keyword>\<open>defining\<close> -- Parse.name) >> (fn ((get_file,_),name) =>
          Toplevel.theory (fn thy =>
          let
             val ({lines, ...}:Token.file) = get_file thy;
             val thy'' = Named_Target.theory_map (Nano_Json_Parser_Isar.def_json name (String.concat lines)) thy
          in thy'' end)))
\<close>
       
JSON_file "example.json" defining example03

JSON \<open>
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
\<close> defining example04

thm example03_def example04_def

lemma "example03 = example04"
  by (simp add:example03_def example04_def)

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

JSON \<open>
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
\<close> defining example02


thm example02_def

declare [[JSON_string_type = String.literal]]
JSON \<open>
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
\<close> defining example02'

thm example02'_def


ML\<open> 
@{term \<open>JSON\<open>{"number":31}\<close>\<close>}
\<close>

lemma "example01 = example02"
  by(simp add: example01_def example02_def)

text\<open>
  Moreover, we can import JSON from external files:
\<close>

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
\<close>

ML_file "Nano_JSON_Serializer.ML"

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
  Outer_Syntax.command ("JSON_export", Position.none) "export JSON data to an external file"
  ((Parse.name -- Scan.option (\<^keyword>\<open>file\<close>-- Parse.name))  >> (fn (const_name,filename) =>
    (Toplevel.theory (fn state => Nano_Json_Serialize_Isar.export_json state const_name (Option.map snd filename)))));
\<close>


subsection\<open>Examples\<close>
text\<open>
  We can now serialize JSON and print the result in the output window of Isabelle/HOL:
\<close>
JSON_export example02
thm example01_def

text\<open>
  Alternatively, we can export the serialized JSON into a file:
\<close>
JSON_export example01 file example01

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
