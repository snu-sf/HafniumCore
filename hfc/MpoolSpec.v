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
Local Open Scope expr_scope.
Local Open Scope stmt_scope.



Set Implicit Arguments.



Section LIB.
  Definition lset_choose T `{RelDec T} (ls: lset T) (f: T -> bool): option T :=
    let ls' := Sets.filter f ls in hd_error ls'
  .
  Definition lset_update T `{RelDec T} (ls: lset T) (t: T) (f: T -> option T): lset T :=
    let ls' := Sets.remove t ls in
    match (f t) with
    | Some t' => Sets.add t' ls'
    | _ => ls'
    end
  .
  Definition Vundef := Vnodef. (* TODO: Define it *)
End LIB.

(** Note: Lock is internalized **)

(** When we write a slightly lower level spec (lock is not internalized),
  we should call "Lock.release" as in MpoolConcur, and it should synchronize some value.
  Synch abstract mpool --> should put "Vabs" in val, which turns out to be tricky (univ. inconsistency)
  Synch dummy data --> somewhat unnatural.
    Root of the problem? --> Lang.v does not have memory, so MpoolConcur needed some way to synch. data.
    If we have the notion of memory, we will not see this unnatural situation.
**)

Module MPOOLSPEC.

  Definition entry_size: nat := 4.

  Inductive case: Type :=
  | case_init
  | case_init_with_fallback
  | case_fini
  | case_alloc_contiguous
  | case_add_chunk

  | case_other
  .

  Definition case_analysis (func_name: string): case :=
    if rel_dec func_name "Mpool.init"
    then case_init
    else
      if rel_dec func_name "Mpool.init_with_fallback"
      then case_init_with_fallback
      else
        if rel_dec func_name "Mpool.fini"
        then case_fini
        else
          if rel_dec func_name "Mpool.alloc_contiguous"
          then case_alloc_contiguous
          else
            if rel_dec func_name "Mpool.add_chunk"
            then case_add_chunk
            else case_other
  .

  Definition ident := nat.

  Record mpool: Type := mk {
    (* chunklist: list (nat * nat); (* (paddr, limit) *) *)
    chunks: lset (nat * nat); (* paddr, limit *)
    (* chunklist: list (nat * nat); (* (paddr, limit) *) *)
    fallback: option ident; (* mpoolid *)
  }
  .

  Instance RelDec_chunk: RelDec (@eq (nat * nat)) :=
    { rel_dec := fun '(n0, m0) '(n1, m1) => if andb (Nat.eqb n0 n1) (Nat.eqb m0 m1) then true else false}.

  Definition owned_heap := ident -> option mpool.

  Inductive MpoolE: Type -> Type :=
  | MEGet (id: ident): MpoolE (option mpool)
  | MESet (id: ident) (mp: option mpool): MpoolE unit
  | MESkip : MpoolE unit (* TODO: can we do it better ? *)
  .

  Notation "'guarantee(' cond ')' ';;' i" := (if cond then i else triggerNB "guarantee fail")
                                             (at level 200).

  Definition fragmentation_nondet: bool := true.

  Definition sem: CallExternalE ~> itree (CallExternalE +' MpoolE +' GlobalE +' Event) :=
    (fun _ '(CallExternal func_name args) =>
       match case_analysis func_name with
       | case_init =>
         guarantee(Nat.eq_dec (length args) 1) ;;
         arg0 <- unwrapN (nth_error args 0) ;;
         match arg0 with
         | (Vptr (Some paddr) cts) =>
           guarantee(Nat.eq_dec (length cts) 3) ;;
           trigger (MESet paddr (Some (mk Sets.empty None))) ;;
           Ret (Vnodef, [Vptr (Some paddr) []])
           (* NB: We should return "empty" pointer (i.e. freed pointer).
If we just fill in with Vundef, it is not enough.
e.g., if caller uses "p := undef ; p.(some_method)" then src is ok but tgt is UB
            *)
         | _ => triggerUB "Mpool:init0"
         end
       | case_init_with_fallback =>
         guarantee(Nat.eq_dec (length args) 2) ;;
         arg0 <- unwrapN (nth_error args 0) ;;
         arg1 <- unwrapN (nth_error args 1) ;;
         match arg0, arg1 with
         | (Vptr (Some paddr0) cts), (Vptr (Some paddr1) nil) =>
           guarantee(Nat.eq_dec (length cts) 3) ;;
           (* TODO: paddr0 <> paddr1 ? *)
           trigger (MESet paddr0 (Some (mk Sets.empty (Some paddr1)))) ;;
           Ret (Vnodef, [Vptr (Some paddr0) [] ; arg1])
         | _, _ => triggerUB "Mpool:init_with_fallback0"
         end
       | case_fini =>
         guarantee(Nat.eq_dec (length args) 1) ;;
         arg0 <- unwrapN (nth_error args 0) ;;
         match arg0 with
         | Vptr (Some paddr) nil =>
           mp <- (trigger (MEGet paddr)) ;;
           mp <- unwrapU mp ;;
           match mp.(fallback) with
           | Some fbaddr =>
             fb <- trigger (MEGet fbaddr) ;;
             fb <- unwrapU fb ;;
             let fb' := mk (Sets.union fb.(chunks) mp.(chunks)) fb.(fallback) in
(*
NOTE: Basically, we should put "YIELD" between each "add_chunk".
E.g., consdier following scenario: free - alloc(succ) - alloc(fail) - free
where one threads allocs, and the other frees (via "fini").
If these two "free"s are sticked together (i.e., no "YIELD"), then its behavior is not refined!

However, we CAN remove such yield because we KNOW alloc_contiguous can always fail.
(because of fragmentation)
Linearization point: earliest free.
We free EARLY, but following "alloc"s can still fail because of the fragmentation.
 *)
             trigger (MESet fbaddr (Some fb'))
           | _ => trigger MESkip
           end ;;
           trigger (MESet paddr None) ;;
           Ret (Vnodef, args)
         | _ => triggerUB "Mpool:fini"
         end
       | case_alloc_contiguous =>
         guarantee(Nat.eq_dec (length args) 2) ;;
         arg0 <- unwrapN (nth_error args 0) ;;
         arg1 <- unwrapN (nth_error args 1) ;;
         if fragmentation_nondet
         then
           match arg0, arg1 with
           | Vptr (Some paddr) nil, Vnat sz =>
             (* let iter: forall E, (ident -> itree E (ident + val)) := *)
             let iter :=
                 (fun paddr =>
                    mp <- trigger (MEGet paddr) ;;
                    mp <- unwrapU mp ;;
                    match lset_choose mp.(chunks) (fun '(pg, lim) => Nat.leb sz lim) with
                    | Some elem =>
                      let chunks' := lset_update (mp.(chunks)) elem
                          (fun '(paddr, lim) => (paddr + entry_size * sz, lim - sz)) in
                      trigger (MESet paddr (Some (mk chunks' mp.(fallback)))) ;;
                      Ret (inr (Vptr (Some paddr) (repeat Vundef (entry_size * sz))))
                    | None =>
                      match mp.(fallback) with
                      | Some fb => Ret (inl fb)
                      | None => Ret (inr Vnull)
                      end
                    end
                 )
             in
             v <- (ITree.iter iter (inr paddr)) ;;
             Ret (v, args)
             (* Ret (Vnull, args) *)
           | _, _ => triggerUB "Mpool:case_alloc_contiguous0"
           end
         else Ret (Vnull, args)
(*
NOTE: Basically, we should put "YIELD" between each "add_chunk".
E.g., consdier following scenario: alloc(p)#1 - free(p)#2  - alloc(fb)#2 - alloc(fb)#1
where initial state is: "p -> empty // fb -> one page".
An attempt to alloc (by #1) FAILs in both "p" and "fb".
If these two "allocs"s are sticked together (i.e., no "YIELD"), all possible behavior SUCCEEDs!
So, its behavior is not refined.

However, we CAN remove such yield because we KNOW alloc_contiguous can always fail.
(because of fragmentation)
Linearization point: successful "alloc_contiguous_no_fallback" (which is the latest one).
In other words, we alloc LATE, and possible problem here was that,
allocs except the last one should fail but it may succeed.
This problem is avoided because we can always fail because of fragmentation.
 *)
       | case_add_chunk
       | _ => triggerNB "Lock-no such function"
       end)
  .

End MPOOLSPEC.

