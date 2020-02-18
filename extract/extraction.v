Require Extraction.

(* From HafniumCore *)
(* YJ: Having some makefile problem. (dependency checking) need to solve that !! *)
Require Import Lang LangTest.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.

(* Avoid name clashes *)
Extraction Blacklist List String Int.

(* Needed in Coq 8.4 to avoid problems with Function definitions. *)
(* Set Extraction AccessOpaque. *)

(* Go! *)



(* Extraction "Lang.ml" load_store_applied eval_stmt stmt_Assume print_val main handle_Event *)
(*            cl2s. *)

Cd "extract".

Separate Extraction
         Lang.eval_program
         LangTest.load_store_program
         LangTest.print_val
         LangTest.main
         LangTest.handle_Event
         LangTest.cl2s
         (* ITreeDefinition.observe *)
.

Cd "..".