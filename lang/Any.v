Require Import sflib.
Require Import ClassicalDescription EquivDec.

Set Implicit Arguments.

Definition Any := { ty: Type & ty }.
Hint Unfold Any.
(* Notation Any := { ty: Type & ty }. *)

Definition try_type (a: Any) (T: Type): option T.
  destruct a.
  destruct (excluded_middle_informative (x = T)).
  - subst. apply Some. assumption.
  - apply None.
Defined.
