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
              r #:= (Call "f" [y: expr]) #;
              r #:= r + x)
      else (r #:= 0)
             fi)
      #;
      Return r
  .

  Definition f_function: function := mk_function ["x"] (f "x" "local0" "local1").

  Definition main x r: stmt :=
    x #:= 10 #;
      r #:= (Call "f" [x: expr]) #;
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
              r #:= (Call "g" [y: expr]) #;
              r #:= r + x)
      else (r #:= 0)
             fi)
      #;
      Return r
  .

  Definition g x y r: stmt :=
    (#if x
      then (y #:= (x - 1) #;
              r #:= (Call "f" [y: expr]) #;
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
  Definition f (x y accu unused: var): stmt :=
    (#if x
      then (y #:= (x - 1) #;
              unused #:= (Call "f" [y: expr ; accu: expr]) #;
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
      unused #:= (Call "f" [x: expr ; accu: expr]) #;
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
  (* Extract Constant coqcode => "fun _ -> print_endline ""Is Prop true?"" ; *)
  (*                                     if (read_int() = 0) then coq_Vtrue else coq_Vfalse *)
  (*                                     ". *)
  Extract Constant coqcode => "fun _ -> coq_Vtrue".

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



Module Control.

  Definition f ctrl ret iter: stmt :=
    iter #:= 10 #;
    ret #:= 0 #;
    (* #put ctrl #; *)
    (* #put iter #; *)
    (* #put ret #; *)
    (* #put 7777777 #; *)
    #while iter
     do (
          iter #:= iter - 1#;
          (* 0 --> break *)
          (* 1 --> continue *)
          (* 2 --> return *)
          (* 3 --> normal *)
          #if ctrl == 0 then Break else Skip fi #;
          (* #put 1111 #; *)
          ret #:= ret + 1 #;
          #if ctrl == 1 then Continue else Skip fi #;
          (* #put 2222 #; *)
          ret #:= ret + 10 #;
          #if ctrl == 2 then (Return (ret + 100)) else Skip fi #;
          (* #put 3333 #; *)
          ret #:= ret + 1000 #;

          Skip
          ) #;
     Return ret
  .

  Definition f_function: function := mk_function ["ctrl"] (f "ctrl" "local0" "local1").

  Definition main r: stmt :=
    r #:= (Call "f" [0: expr]) #; #if r == 0 then Skip else Assume fi #;
    r #:= (Call "f" [1: expr]) #; #if r == 10 then Skip else Assume fi #;
    r #:= (Call "f" [2: expr]) #; #if r == 111 then Skip else Assume fi #;
    r #:= (Call "f" [3: expr]) #; #if r == 10110 then Skip else Assume fi #;
    Skip
  .

  Definition main_function: function :=
    mk_function [] (main "local0")
  .

  Definition program: program := [("main", main_function) ;
                                    ("f", f_function)].

End Control.




Module Concur.

  Definition main: stmt :=
    #put 1 #;
    #put 2 #;
    #put 3 #;
    #put 4 #;
    Skip
  .

  Definition main_function: function :=
    mk_function [] (main)
  .

  Definition program: program := [("main", main_function) ].

  Definition programs: list Lang.program := repeat program 3.

End Concur.


Section RUN.
Variable shuffle: forall A, list A -> list A.

(* Definition rr_match {E R} `{Event -< E} *)
(*            (rr : list (itree E R) -> itree E R) *)
(*            (q:list (itree E R)) : itree E R *)
(*   := *)
(*     match q with *)
(*     | [] => triggerUB *)
(*     | t::ts => *)
(*       match observe t with *)
(*       | RetF _ => Tau (rr ts) *)
(*       | TauF u => Tau (rr (u :: ts)) *)
(*       | @VisF _ _ _ X o k => Vis o (fun x => rr (shuffle (k x :: ts))) *)
(*       end *)
(*     end. *)

(* CoFixpoint round_robin {E R} `{Event -< e} (q:list (itree E R)) : itree E R := *)
(*   rr_match round_robin q. *)
Definition rr_match {R}
           (rr : list (itree Event R) -> itree Event R)
           (q:list (itree Event R)) : itree Event R
  :=
    match q with
    | [] => triggerUB
    | t::ts =>
      match observe t with
      | RetF _ => Tau (rr ts)
      | TauF u => Tau (rr (u :: ts))
      | @VisF _ _ _ X o k => Vis o (fun x => rr (shuffle (k x :: ts)))
      end
    end.

CoFixpoint round_robin {R} (q:list (itree Event R)) : itree Event R :=
  rr_match round_robin q.




Variable handle_Event: forall E R X, Event X -> (X -> itree E R) -> itree E R.
(* Extract Constant handle_Event => "handle_Event". *)

Definition run_till_event_aux {R} (rr : itree Event R -> (itree Event R))
           (q: itree Event R) : (itree Event R)
  :=
    match observe q with
    | RetF _ => q
    | TauF u => Tau (rr u)
      (* w <- (rr u) ;; (Tau w) *)
    | @VisF _ _ _ X o k => (handle_Event o k)
    (* Vis o (fun x => rr (shuffle (ts ++ [k x]))) *)
    end.

CoFixpoint run_till_event {R} (q: itree Event R): (itree Event R) :=
  run_till_event_aux run_till_event q
.

Definition my_rr_match {R} (rr : list (itree Event R) -> list (itree Event R))
           (q:list (itree Event R)) : list (itree Event R)
  :=
    match q with
    | [] => []
    | t::ts =>
      let t2 := run_till_event t in
      rr (shuffle (t2::ts))
    end.

Fail CoFixpoint my_round_robin {R} (q:list (itree Event R)) : list (itree Event R) :=
  my_rr_match my_round_robin q.

End RUN.
