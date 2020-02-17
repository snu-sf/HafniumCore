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



From HafniumCore
     Require Import Lang.
Import ImpNotations.

Set Implicit Arguments.




Module MPOOL.

  (*
     ONLY: fallback & chunk_list
   *)

  Definition entry_size: nat := 4096.

  Definition init: stmt :=
    "p" #<- "entry_size"
  .

  Definition fini: stmt :=
  .

End MPOOL.

