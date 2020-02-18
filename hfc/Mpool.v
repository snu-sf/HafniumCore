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



(* From HafniumCore *)
Require Import Lang.
Import ImpNotations.

Set Implicit Arguments.




Module MPOOL.

  (*
Mpool := Vptr [Vptr//chunk_list ; Vptr//fallback]
   *)

  Definition entry_size: nat := 4096.

  Definition p: string := "p".

  Definition init (arg: val): stmt :=
    p #:= arg#;

      (Store p 0 Vnull)#;
      (Store p 1 Vnull)#;

      Skip
  .

  (* Definition fini (arg: val): stmt := *)
  (*   p #:= arg#; *)

  (*     #if (Load p 1) *)
  (*           then *)
  (*             else *)
  (*               fi *)
  (* . *)

  (* sum #:= Vnat 0#; *)
  (* x #:= Vptr (repeat (Vnat 0) 3)#; *)
  (* #put x#; *)
  (* (Store x 0 10)#; *)
  (* #put x#; *)
  (* (Store x 1 20)#; *)
  (* #put x#; *)
  (* (Store x 2 30)#; *)
  (* #put x#; *)
  (* #put sum#; *)
  (* sum #:= sum + (Load x 0)#; *)
  (* #put sum#; *)
  (* sum #:= sum + (Load x 1)#; *)
  (* #put sum#; *)
  (* sum #:= sum + (Load x 2)#; *)
  (* #put sum#; *)
  (* Skip *)

End MPOOL.

