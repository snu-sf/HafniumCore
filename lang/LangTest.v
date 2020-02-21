From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Structures.Foldable
     Structures.Reducible
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.StateFacts.

From ITree Require Import
     ITree ITreeFacts.

Import ITreeNotations.
Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.
Require Import sflib.

Require Import ClassicalDescription.
About excluded_middle_informative.

(* From HafniumCore *)
Require Import Lang.
Import ImpNotations.

Set Implicit Arguments.



Module LoadStore.

  Definition main x sum: stmt :=
    sum #:= Vnat 0#;
        x #:= Vptr (repeat (Vnat 0) 3)#;
        #put x#;
        (Store x 0 10)#;
        #put x#;
        (Store x 1 20)#;
        #put x#;
        (Store x 2 30)#;
        #put x#;
        #put sum#;
        sum #:= sum + (Load x 0)#;
                                #put sum#;
                                sum #:= sum + (Load x 1)#;
                                                        #put sum#;
                                                        sum #:= sum + (Load x 2)#;
                                                                                #put sum#;
                                                                                Skip
  .

  Definition function: function := mk_function [] (main "x" "sum").

  Definition program: program := [("main", function)].

  (* Extraction "LangTest.ml" load_store_program. *)
  Check (eval_program program).

End LoadStore.


Section TMP.
  Variable a: var.
  Variable b: val.
  Check (Var a).
  Check (Lit b).
  Local Open Scope expr_scope.
  Local Open Scope stmt_scope.
  Check ((Var a) + (Lit b)).
End TMP.

Local Open Scope expr_scope.
Local Open Scope stmt_scope.


Module Rec.
  Definition f x y r: stmt :=
    (#if x
      then (y #:= (x - 1) #;
              (Call r "f" [y]) #;
              r #:= r + x)
      else (r #:= 0)
             fi)
      #;
      Return r
  .

  Definition f_function: function := mk_function ["x"] (f "x" "local0" "local1").

  Definition main x r: stmt :=
    x #:= 10 #;
      (Call  r "f" [x]) #;
      #put r
  .

  Definition main_function: function := mk_function [] (main "local0" "local1").

  Definition program: program := [("main", main_function) ;
                                    ("f", f_function)].

End Rec.



Module MutRec.

  Definition f x y r: stmt :=
    (#if x
      then (y #:= (x - 1) #;
              (Call r "g" [y]) #;
              r #:= r + x)
      else (r #:= 0)
             fi)
      #;
      Return r
  .

  Definition g x y r: stmt :=
    (#if x
      then (y #:= (x - 1) #;
              (Call r "f" [y]) #;
              r #:= r + x)
      else (r #:= 0)
             fi)
      #;
      Return r
  .

  Definition f_function: function := mk_function ["x"] (f "x" "local0" "local1").
  Definition g_function: function := mk_function ["x"] (g "x" "local0" "local1").

  Definition program: program := [("main", Rec.main_function) ;
                                    ("f", f_function) ;
                                    ("g", g_function)].
End MutRec.



(* YJ: if we just use "r", not "unused", something weird will happen *)
(* TODO: address it better *)
Module Move.
  Definition f x y accu unused: stmt :=
    (#if x
      then (y #:= (x - 1) #;
              (Call unused "f" [y ; accu]) #;
              accu #:= accu + x #;
                                Skip
           )
      else
        (accu #:= 0)
          fi)
      #;
      Return 77777
  .

  Definition main x accu unused: stmt :=
    x #:= 10 #;
      accu #:= 1000 #;
      (Call unused "f" [x ; accu]) #;
      #put accu
  .

  Definition f_function: function := mk_function ["x" ; "accu"]
                                                      (f "x" "local0" "accu" "local1").
  Definition main_function: function :=
    mk_function [] (main "local0" "local1" "local2").

  Definition program: program := [("main", main_function) ;
                                    ("f", f_function)].

End Move.





Module CoqCode.

  Definition coqcode: list val -> val :=
    (fun v =>
       match v with
       | hd :: _ => if excluded_middle_informative (exists w, w * w = hd)
                    then Vtrue
                    else Vfalse
       | _ => Vfalse
       end).

  (* Extract Constant excluded_middle_informative => "true". (* YJ: To avouid crash *) *)
  Extract Constant coqcode => "fun _ -> print_endline ""Is Prop true?"" ;
                                      if (read_int() = 0) then coq_Vtrue else coq_Vfalse
                                      ".

  Definition main x: stmt :=
    x #:= 25 #;
      (#if (CoqCode [Var x] coqcode)
        then #put 555
        else #put 666 fi)
  .

  Definition main_function: function :=
    mk_function [] (main "local0").

  Definition program: program := [("main", main_function)].

End CoqCode.





(* Definition cl2s (cl: string): string := cl. *)
(* Definition load_store_applied := load_store "x" "sum". *)
(* Check (eval_stmt load_store_applied). *)
(* Definition print_val: unit := tt. *)
(* Definition handle_Event: unit := tt. *)
(* Definition main: unit := *)
(*   let _ := print_val in *)
(*   let _ := load_store_applied in *)
(*   let _ := handle_Event in *)
(*   tt. *)
(* Extract Constant print_val => " *)
(* let rec go v = *)
(*   match v with *)
(*   | Vnat n -> print_string ((string_of_int n) ^ "" "") *)
(*   | Vptr cts -> print_string ""["" ; List.iter go cts ; print_string ""]"" in *)
(* fun v -> go v ; print_endline "" "" *)
(* " *)
(* . *)

(* Extract Constant cl2s => "fun cl -> String.concat """" (List.map (String.make 1) cl)". *)

(* Extract Constant handle_Event => *)
(* " *)
(* fun e k -> match e with *)
(*   | NB -> failwith ""NB OCCURED"" *)
(*   | UB -> failwith ""UB OCCURED"" *)
(*   (* | Syscall (['p'], [v]) -> print_val v ; k (Obj.magic ()) *) *)
(*   | Syscall ('p'::[], v::[]) -> print_val v ; k (Obj.magic ()) *)
(*   | Syscall (cl, vs) -> print_endline (cl2s cl) ; *)
(* (* print_val (List.nth vs 0) ; *) *)
(* (* print_int (length cl) ; *) *)
(* (* print_int (length vs) ; *) *)
(*                         failwith ""UNSUPPORTED SYSCALL"" *)
(*   | _ -> failwith ""NO MATCH"" *)
(* " *)
(* . *)
(* Extract Constant main => *)
(* " *)
(* let rec run t = *)
(*   match observe t with *)
(*   | RetF r -> r *)
(*   | TauF t -> run t *)
(*   | VisF (e, k) -> handle_Event e (fun x -> run (k x)) in *)
(* run (eval_stmt load_store_applied) *)
(* " *)
(* . *)






(* Axiom dummy_client: forall A, A -> unit. *)
(* Extract Constant dummy_client => "fun _ -> ()". *)
(* Fixpoint val_iter (v: val) (f: nat -> unit): unit := *)
(*   match v with *)
(*   | Vnat n => dummy_client (f n) *)
(*   | Vptr cts => List.fold_left (fun s i => dummy_client i) cts tt *)
(*   end *)
(* . *)

