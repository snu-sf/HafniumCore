Require Import Lists.List.
Import ListNotations.

Set Implicit Arguments.



Fixpoint filter_map A B (f: A -> option B) (l: list A): list B :=
  match l with
  | [] => []
  | hd :: tl =>
    match (f hd) with
    | Some b => b :: (filter_map f tl)
    | _ => filter_map f tl
    end
  end
.

Definition try_left A B (ab: A + B): option A :=
  match ab with
  | inl a => Some a
  | _ => None
  end
.

Definition try_right A B (ab: A + B): option B :=
  match ab with
  | inr b => Some b
  | _ => None
  end
.

Notation unwrap :=
  (fun x default => match x with
                    | Some y => y
                    | _ => default
                    end)
.

(* Notation "'unwrap' x default" := *)
(*   (match x with *)
(*    | Some y => y *)
(*    | _ => default *)
(*    end) (at level 60) *)
(* . *)

(* Definition unwrap X (x: option X) (default: X): X := *)
(*   match x with *)
(*   | Some x => x *)
(*   | _ => default *)
(*   end *)
(* . *)
