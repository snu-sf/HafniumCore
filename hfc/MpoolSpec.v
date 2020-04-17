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



Definition DebugMpool := Syscall "md".


(* Module MPOOLSPEC. *)

(*   Definition lock_ofs := 0. *)
(*   Definition chunk_list_ofs := 1. *)
(*   Definition fallback_ofs := 2. *)
(*   Definition next_chunk_ofs := 0. *)
(*   Definition limit_ofs := 1. *)

(*   Definition entry_size: nat := 4. *)
(* (* *)
(* Simplified Mpool := Vptr [Vnat//lock ; Vptr//chunk_list ; Vptr//fallback] *)
(*    *) *)
(*   Inductive mpool: Type := mk { *)
(*     lockid: nat; *)
(*     chunklist: list (nat * nat); (* (paddr, limit) *) *)
(*     fallback: option mpool; *)
(*   } *)
(*   . *)
  
(*   Definition init (p: var): stmt := *)
(*     CoqCode ( *)
(*       ) *)
(*     (p @ chunk_list_ofs #:= Vnull) #; *)
(*     (p @ fallback_ofs   #:= Vnull) #; *)
(*     (p @ lock_ofs       #:= (Call "Lock.new" [])) #; *)
(*     (Call "Lock.release" [CBV (p #@ lock_ofs) ; CBV p]) #; *)
(*     Skip *)
(*   . *)

(*   (* void mpool_init_with_fallback(struct mpool *p, struct mpool *fallback) *) *)
(*   (* { *) *)
(*   (* 	mpool_init(p, fallback->entry_size); *) *)
(*   (* 	p->fallback = fallback; *) *)
(*   (* } *) *)

(*   (*** DELTA: Add call to "Lock.release"  ***) *)
(*   Definition init_with_fallback (p fallback: var): stmt := *)
(*     (* Call "init" [CBR p] #; *) *)
(*     (* (Store p fallback_ofs fallback) #; *) *)
(*     (* (Call "Lock.release" [CBV (p #@ lock_ofs) ; CBV p]) #; *) *)
(*     (p @ chunk_list_ofs #:= Vnull) #; *)
(*     (p @ fallback_ofs   #:= fallback) #; *)
(*     (p @ lock_ofs       #:= (Call "Lock.new" [])) #; *)
(*     (Call "Lock.release" [CBV (p #@ lock_ofs) ; CBV p]) #; *)
(*     Skip *)
(*   . *)

(*   Definition lock_ofs := 0. *)
(*   Definition chunk_list_ofs := 1. *)
(*   Definition fallback_ofs := 2. *)
(*   Definition next_chunk_ofs := 0. *)
(*   Definition limit_ofs := 1. *)

(*   Definition entry_size: nat := 4. *)




(* End MPOOLSPEC. *)





