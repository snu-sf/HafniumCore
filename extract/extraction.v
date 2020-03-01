Require Extraction.

(* From HafniumCore *)
(* YJ: Having some makefile problem. (dependency checking) need to solve that !! *)
Require Import Lang LangTest.
Require Import MpoolSeq MpoolConcur.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
(* Require Import ExtrOcamlNatInt. *)

(* Avoid name clashes *)
Extraction Blacklist List String Int.

Cd "extract".

(*** TODO: I just want to write as below, but it does NOT work!!!!! ***)
(* Separate Extraction MpoolSeq MpoolConcur Lang LangTest. *)

Separate Extraction
         Lang.eval_program
         Lang.Vtrue
         Lang.Vfalse
         LangTest.LoadStore.program
         LangTest.Rec.program
         LangTest.MutRec.program
         LangTest.Move.program
         LangTest.CoqCode.program
         LangTest.Control.program
         LangTest.DoubleReturn.program
         LangTest.MultiCore.programs
         LangTest.MultiModule.isem
         LangTest.MultiModuleLocalState.isem
         (* LangTest.print_val *)
         (* LangTest.main *)
         (* LangTest.handle_Event *)
         (* LangTest.cl2s *)

         MpoolSeq.TEST.TEST1.program
         MpoolSeq.TEST.TEST2.program
         MpoolSeq.TEST.TEST3.program
         MpoolSeq.TEST.TEST4.program

         MpoolConcur.TEST.TEST2.isem
         MpoolConcur.TEST.TEST3.isem
         MpoolConcur.TEST.TEST4.isem

         LangTest.round_robin
         LangTest.run_till_yield
         LangTest.my_rr_match

ITreeDefinition.observe
.

Cd "..".
