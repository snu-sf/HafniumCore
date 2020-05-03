(*
 * Copyright 2020 Youngju Song
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ExtLib Require Import
     RelDec
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ExtLib Require Import
     Sets ListSet.

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
Require Import Coqlib sflib.


(* From HafniumCore *)
Require Import Lang Lock.
Import LangNotations.
Require Import Any.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.



Set Implicit Arguments.




Section NOTATIONTEST.
  Local Close Scope itree_scope.
  Local Open Scope monad_scope.
  From ExtLib Require Import OptionMonad.
  Print Instances Monad.
  Print Instances PMonad.
  Variable oa: option nat.
  Fail Check (a <- oa ;; a).
  Local Existing Instance Monad_option | 100.
  Local Existing Instance Monad_option | 0.
  Notation "x ?? c1 !! c2" := (@pbind _ _ _ _ _ c1 (fun x => c2))
                                (at level 61, c1 at next level, right associativity).
  Fail Check ((a ?? oa !! a): option nat).
  Notation "x <- c1 ;; c2" := (@pbind _ (PMonad_Monad Monad_option) _ _ _ c1 (fun x => c2))
                                (at level 61, c1 at next level, right associativity).
  Check ((a <- oa ;; Some a): option nat).
End NOTATIONTEST.

Notation "x <- c1 ;; c2" := (@pbind _ (PMonad_Monad Monad_option) _ _ _ c1 (fun x => c2))
                              (at level 61, c1 at next level, right associativity).




(** Note: Lock is internalized **)
Module MPOOLSPEC.

  Definition ident := nat.

  Instance RelDec_ident: RelDec (@eq ident) :=
    { rel_dec := fun n0 n1 => if (Nat.eqb n0 n1) then true else false}.

  Record mpool: Type := mk {
    chunklist: list (nat * nat); (* paddr, limit *)
    fallback: option ident; (* mpoolid *)
  }
  .

  Definition manager: Type := ident -> option mpool.
  Definition inital_manager: manager := fun _ => None.
  Definition update (m: manager) (k0: ident) (v: option mpool): manager :=
    fun k1 => if rel_dec k0 k1 then v else m k1
  .



  Let init_aux (vs: list val): val :=
    match vs with
    | [(Vabs a) ; (Vptr (Some p_id) _)] =>
      match downcast a manager with
      | Some mm0 => let mm1 := (update mm0 p_id (Some (mk nil None))) in
                    Vabs (upcast mm1)
      | _ => Vnodef
      end
    | _ => Vnodef
    end
  .

  Definition init (p: var) r: stmt :=
    r #= GetOwnedHeap #;
    PutOwnedHeap (CoqCode [Var r ; Var p] init_aux) #;
    Skip
  .



  Let init_with_fallback_aux (vs: list val): val :=
    match vs with
    | [(Vabs a) ; (Vptr (Some p_id) _) ; (Vptr (Some fb_id) _)] =>
      match downcast a manager with
      | Some mm0 => let mm1 := (update mm0 p_id (Some (mk nil (Some fb_id)))) in
                    Vabs (upcast mm1)
      | _ => Vnodef
      end
    | _ => Vnodef
    end
  .

  Definition init_with_fallback (p fallback: var) r: stmt :=
    r #= GetOwnedHeap #;
    PutOwnedHeap (CoqCode [Var r ; Var p ; Var fallback] init_with_fallback_aux) #;
    Skip
  .

  Let check_fallback (vs: list val): val :=
    match vs with
    | [(Vabs a) ; (Vptr (Some p_id) _)]=>
      match downcast a manager with
      | Some mm0 =>
        match mm0 p_id with
        | Some mp => is_some (mp.(fallback))
        | _ => Vnodef
        end
      | _ => Vnodef
      end
    | _ => Vnodef
    end
  .

  Let get_chunk_list (vs: list val): val :=
    match vs with
    | [(Vabs a) ; (Vptr (Some p_id) _)]=>
      unwrap (mm <- downcast a manager ;;
              mp <- mm p_id ;;
              Some (Vabs (upcast mp.(chunklist)))
             ) Vnodef
    | _ => Vnodef
    end
  .

  Let fini_add_chunk_aux (vs: list val): val :=
    match vs with
    | [(Vabs a) ; (Vptr (Some p_id) _)]=>
      unwrap (mm <- downcast a manager ;;
              mp <- mm p_id ;;
              fb_id <- mp.(fallback) ;;
              fb <- mm fb_id ;;
              Some (Vabs (upcast mp.(chunklist)))
             ) Vnodef
    | _ => Vnodef
    end
  .

  (*** NOTE: Very interesting point.
    It is somewhat desirable to call "add_chunk" (instead of "inlining") in high level spec too,
    because it will prevent code duplication.
    However, "add_chunk"'s interface expects low-level, and we only have high-level data.
    1) Call "add_chunk". We need some form of "abstraction relation" && non-det
       in order to rebuild low-level data from high-level one.
    2) Inline it.
   ***)

  (*** TODO: We access mp.(fallback) without locking it.
    I think we are implicitly exploiting the fact that this data is const.
  ***)

  (*** TODO: It would be better if CoqCode can update variable outside. Maybe we can use CBV/CBR here too.
  ***)
  Definition fini (p: var)
             chunk r: stmt :=
    r #= GetOwnedHeap #;
    #if !(CoqCode [Var r ; Var p] check_fallback)
     then Return Vnull
     else Skip #;
    #while (chunk)
    do (
      Yield #;
      (CoqCode [Var r ; Var p] fini_aux) #;
      Skip
    )#;
    Skip
  .
    p #= (Call "Lock.acquire" [CBV (p #@ lock_ofs)]) #;
    chunk #= (p #@ chunk_list_ofs) #;
    #while (chunk)
    do (
      size #= (chunk #@ limit_ofs) #;
      (*** Below two instructions' order is reversed from original code ***)
      Call "add_chunk" [CBV (p #@ fallback_ofs) ; CBV chunk ; CBV size] #;
      chunk #= (chunk #@ next_chunk_ofs)
    ) #;
    p @ chunk_list_ofs #:= Vnull #;
    p @ fallback_ofs   #:= Vnull #;
    (Call "Lock.release" [CBV (p #@ lock_ofs) ; CBV p]) #;
    Skip
  .

End MPOOLSPEC.












