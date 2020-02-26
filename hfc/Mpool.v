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
Require Import sflib.


(* From HafniumCore *)
Require Import Lang.
Import ImpNotations.

Set Implicit Arguments.




Module MPOOLSEQ.

  (*
Mpool := Vptr [Vptr//chunk_list ; Vptr//fallback]
   *)

  Definition entry_size: nat := 4096.

  (* void init(struct mpool *p, size_t entry_size) *)
  (* { *)
  (*   p->entry_size = entry_size; *)
  (*   p->chunk_list = NULL; *)
  (*   p->entry_list = NULL; *)
  (*   p->fallback = NULL; *)
  (*   sl_init(&p->lock); *)
  (* } *)
  Definition init p: stmt :=
    (Store p 0 Vnull) #;
    (Store p 1 Vnull)
  .

  (* void *mpool_alloc_contiguous(struct mpool *p, size_t count, size_t align) *)
  (* { *)
  (*   do { *)
  (*     void *ret = mpool_alloc_contiguous_no_fallback(p, count, align); *)
  
  (*     if (ret != NULL) { *)
  (*       return ret; *)
  (*     } *)
  
  (*     p = p->fallback; *)
  (*   } while (p != NULL); *)
  
  (*   return NULL; *)
  (* } *)
  Definition alloc_contiguous (p count ret: var): stmt :=
    #while Vtrue
     do (
       ret #:= (Call "alloc_contiguous_no_fallback" [(p: expr) ; (count: expr)]) #;
       #if (ret)
       then (Return ret)
       else Skip
       fi #;
       p #:= (Load p 1) #;
       #if (p)
       then Skip
       else Break
       fi
     ) #;
    Return Vnull
  .

  (* void *mpool_alloc_contiguous_no_fallback(struct mpool *p, size_t count, *)
  (*       				 size_t align) *)
  (* { *)
  (*   struct mpool_chunk **prev; *)
  (*   void *ret = NULL; *)
  
  (*   align *= p->entry_size; *)
  
  (*   mpool_lock(p); *)
  
  (*   prev = &p->chunk_list; *)
  (*   while ( *prev != NULL) { *)
  (*     uintptr_t start; *)
  (*     struct mpool_chunk *new_chunk; *)
  (*     struct mpool_chunk *chunk = *prev; *)
  
  (*     start = (((uintptr_t)chunk + align - 1) / align) * align; *)
  
  (*     new_chunk = *)
  (*       (struct mpool_chunk * )(start + (count * p->entry_size)); *)
  (*     if (new_chunk <= chunk->limit) { *)
  (*       if (new_chunk == chunk->limit) { *)
  (*         *prev = chunk->next_chunk; *)
  (*       } else { *)
  (*         *new_chunk = *chunk; *)
  (*         *prev = new_chunk; *)
  (*       } *)
  
  (*       if (start - (uintptr_t)chunk >= p->entry_size) { *)
  (*         chunk->next_chunk = *prev; *)
  (*         *prev = chunk; *)
  (*         chunk->limit = (struct mpool_chunk * )start; *)
  (*       } *)
  
  (*       ret = (void * )start; *)
  (*       break; *)
  (*     } *)
  
  (*     prev = &chunk->next_chunk; *)
  (*   } *)
  
  (*   mpool_unlock(p); *)
  
  (*   return ret; *)
  (* } *)
  Definition alloc_contiguous_no_fallback
             (p count prev ret start new_chunk chunk: var): stmt :=
    prev #:= (Load p 0) #;
    #while prev
     do (
       ret #:= (Call "alloc_contiguous_no_fallback" [(p: expr) ; (count: expr)]) #;
       #if (ret)
       then (Return ret)
       else Skip
       fi #;
       p #:= (Load p 1) #;
       #if (p)
       then Skip
       else Break
       fi
     ) #;
    Return Vnull
  .


End MPOOLSEQ.

