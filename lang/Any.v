Require Import sflib.
Require Import ClassicalDescription EquivDec.

Set Implicit Arguments.

Definition Any := { ty: Type & ty }.
Hint Unfold Any.
(* Notation Any := { ty: Type & ty }. *)

Definition excluded_middle_informative_extract_true := excluded_middle_informative.
Extract Constant excluded_middle_informative_extract_true => "true".

Definition try_type (a: Any) (T: Type): option T.
  destruct a.
  destruct (excluded_middle_informative_extract_true (x = T)).
  - subst. apply Some. assumption.
  - apply None.
Defined.

Require Import Program.
Definition Any_dec (a0 a1: Any): {a0=a1} + {a0<>a1}.
  destruct a0, a1.
  simpl_depind.
  destruct (excluded_middle_informative (x = x0)).
  - clarify.
    destruct (excluded_middle_informative (p = p0)).
    + clarify. left. rewrite sigT_eta. ss.
    + right. ii. simpl_depind. clarify.
  - right. ii. simpl_depind.
Defined.
