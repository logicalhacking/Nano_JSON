(***********************************************************************************
 * Copyright (c) 2019-2021 Achim D. Brucker
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

section\<open>Query Infrastructure\<close>

theory Nano_JSON_Query
imports 
Nano_JSON
begin

ML\<open>
structure Nano_Json_Query = struct
open Nano_Json_Type
fun nj_filter key json =
    let 
        fun nj_filter' key (prfx, OBJECT json) =  ((map (fn  (k,v) => (prfx@[k],v)) (filter (fn (k,_) =>  key = k) json) )
                                                 @(List.concat (map (nj_filter' key) (map (fn (k,v) => (prfx@[k],v)) json)))) 
          | nj_filter' key (prfx, ARRAY json) = (List.concat (map (nj_filter' key) (map (fn v => (prfx,v)) json)))
          | nj_filter' _ (_, NUMBER _) = []
          | nj_filter' _ (_, STRING _) = []
          | nj_filter' _ (_, BOOL _) = []
          | nj_filter' _ (_,NULL) = []
    in 
        nj_filter' key ([],json)
    end

fun nj_update f key (OBJECT kjson) =  OBJECT (map (fn (k,json) => if k = key then (k, f json) else (k, nj_update f key json)) kjson) 
  | nj_update f key (ARRAY json) = ARRAY (map (nj_update f key) json)
  | nj_update _ _ (NUMBER n) = NUMBER n
  | nj_update _ _ (STRING s) = STRING s
  | nj_update _ _ (BOOL b) = BOOL b
  | nj_update _ _ NULL = NULL

end
\<close>


definition_JSON  example_literal_literal \<open>
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



fun jq_filter :: \<open>'a \<Rightarrow> ('a, 'b) json \<Rightarrow> ('a list \<times> ('a, 'b) json) list\<close> 
  where
  \<open>jq_filter key (OBJECT json) =( (map (\<lambda> (k,v) \<Rightarrow> ([k],v)) (filter (\<lambda> (k,d) \<Rightarrow> key = k) json) )
                        @ (List.concat (map (jq_filter key) (map snd json)))
                         )\<close>
| \<open>jq_filter key (ARRAY json) = (List.concat (map (jq_filter key) (json)))\<close>
| \<open>jq_filter _ (NUMBER _) = []\<close>
| \<open>jq_filter _ (STRING _) = []\<close>
| \<open>jq_filter _ (BOOL _) = []\<close>
| \<open>jq_filter _ (NULL) = []\<close>

 
value \<open>jq_filter ''onclick'' example_literal_literal\<close>


end
