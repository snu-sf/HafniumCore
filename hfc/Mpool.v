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
Local Open Scope expr_scope.
Local Open Scope stmt_scope.



Set Implicit Arguments.

Notation "#* e" :=
  (Load e 0) (at level 40, e at level 50): stmt_scope.

Definition bool_to_val (b: bool): val :=
  match b with
  | true => Vtrue
  | false => Vfalse
  end
.

Coercion bool_to_val: bool >-> val.



Module MPOOLSEQ.

  (*
Mpool := Vptr [Vptr//chunk_list ; Vptr//fallback]
   *)

  Definition chunk_list_ofs := 0.
  Definition fallback_ofs := 1.
  Definition next_chunk_ofs := 0.
  Definition limit_ofs := 1.

  Definition entry_size: nat := 4.

  Fixpoint chunk_list_wf (chunk_list: val): bool :=
    match chunk_list with
    | Vptr cts =>
      match cts with
      | [] => true
      | _ :: []  => false
      | next_chunk :: limit :: _ =>
        match limit with
        | Vnat limit =>
          if Nat.eq_dec (length cts) (limit * entry_size)
          then chunk_list_wf next_chunk 
          else false
        | _ => false
        end
      end
    | _ => false
    end
  .

  Fixpoint mpool_wf (p: val): bool :=
    match p with
    | Vptr p =>
      match p with
      | [] => true
      | [chunk_list ; fallback] =>
        chunk_list_wf chunk_list && mpool_wf fallback
      | _ => false
      end
    | _ => false
    end
  .







  (* void init(struct mpool *p, size_t entry_size) *)
  (* { *)
  (*   p->entry_size = entry_size; *)
  (*   p->chunk_list = NULL; *)
  (*   p->entry_list = NULL; *)
  (*   p->fallback = NULL; *)
  (*   sl_init(&p->lock); *)
  (* } *)
  Definition init (p: var): stmt :=
    (Store p chunk_list_ofs Vnull) #;
    (Store p fallback_ofs Vnull)
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
  Definition alloc_contiguous
             (p count: var)
             (ret: var): stmt :=
    #while Vtrue
     do (
       ret #:= (Call "alloc_contiguous_no_fallback" [(p: expr) ; (count: expr)]) #;
       #if (ret)
       then (Return ret)
       else Skip
       #;
       p #:= (Load p fallback_ofs) #;
       #if (p)
       then Skip
       else Break
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

  (***********************************************************************)
  (***********************************************************************)
  (***************************SIMPLIFIED**********************************)
  (***********************************************************************)
  (***********************************************************************)

  (* void *mpool_alloc_contiguous_no_fallback(struct mpool *p, size_t count, *)
  (*       				 size_t align) *)
  (* { *)
  (*   struct mpool_chunk **prev; *)
  (*   void *ret = NULL; *)
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
             (p count: var)
             (prev ret new_chunk chunk: var): stmt :=
    #if (CoqCode [p: expr] (fun p => mpool_wf (nth 0 p Vnull)))
     then Skip
     else Guarantee
    #;
    prev #:= (#& (Load p chunk_list_ofs)) #;
    #while prev
     do (
       chunk #:= (#* prev) #;
       new_chunk #:= (SubPointerFrom chunk (count * entry_size)) #;
       (* if (new_chunk <= chunk->limit) *)
       (* #if new_chunk *)
       #if (count <= (Load chunk limit_ofs))
        then
          (
           #if count == (Load chunk limit_ofs)
            then (
                Store prev 0 (Load chunk next_chunk_ofs) (** should write to p **)
              )
            else (
                Store new_chunk next_chunk_ofs (Load chunk next_chunk_ofs) #;
                Store new_chunk limit_ofs (Load chunk limit_ofs) #;
                Store prev 0 new_chunk
              )
           #;
           (* ret = (void * )start; *) (** code doesn't specify the size, but we need too **)
           ret #:= (SubPointerTo chunk (count * entry_size)) #;
           Break
          )
        else
          prev #:= #& (Load chunk next_chunk_ofs)
     ) #;
    Return ret
  .

  (* bool mpool_add_chunk(struct mpool *p, void *begin, size_t size) *)
  (* { *)
  (* 	struct mpool_chunk *chunk; *)
  (* 	uintptr_t new_begin; *)
  (* 	uintptr_t new_end; *)

  (* 	/* Round begin address up, and end address down. */ *)
  (* 	new_begin = ((uintptr_t)begin + p->entry_size - 1) / p->entry_size * *)
  (* 		    p->entry_size; *)
  (* 	new_end = ((uintptr_t)begin + size) / p->entry_size * p->entry_size; *)

  (* 	/* Nothing to do if there isn't enough room for an entry. */ *)
  (* 	if (new_begin >= new_end || new_end - new_begin < p->entry_size) { *)
  (* 		return false; *)
  (* 	} *)

  (* 	chunk = (struct mpool_chunk * )new_begin; *)
  (* 	chunk->limit = (struct mpool_chunk * )new_end; *)

  (* 	mpool_lock(p); *)
  (* 	chunk->next_chunk = p->chunk_list; *)
  (* 	p->chunk_list = chunk; *)
  (* 	mpool_unlock(p); *)

  (* 	return true; *)
  (* } *)

  Definition add_chunk
             (p begin: var)
             (chunk: var): stmt :=
    chunk #:= begin #;
    Store chunk limit_ofs ((GetLen chunk) / entry_size) #;

    Store chunk next_chunk_ofs (Load p chunk_list_ofs) #;
    Store p chunk_list_ofs chunk
  .

  Definition initF: function :=
    mk_function ["p"] (init "p").
  Definition alloc_contiguousF: function :=
    mk_function ["p" ; "count"] (alloc_contiguous "p" "count" "ret").
  Definition alloc_contiguous_no_fallbackF: function :=
    mk_function ["p" ; "count"]
                (alloc_contiguous_no_fallback "p" "count" "prev" "ret" "new_chunk" "chunk").
  Definition add_chunkF: function :=
    mk_function ["p" ; "begin"] (add_chunk "p" "begin" "chunk").

  Definition big_chunk: val := Vptr (repeat Vnull (entry_size * 10)).
  Definition main
             (p r1 r2 r3: var): stmt :=
    p #:= Vptr [0: val ; 0: val] #;
    Call "init" [p: expr] #;
    Call "add_chunk" [p: expr ; big_chunk: expr] #;

    r1 #:= Call "alloc_contiguous" [p: expr ; 7: expr] #;
    #put r1 #;

    r2 #:= Call "alloc_contiguous" [p: expr ; 7: expr] #;
    #put r2 #;

    Call "add_chunk" [p: expr ; r1: expr] #;

    r3 #:= Call "alloc_contiguous" [p: expr ; 7: expr] #;
    #put r3 #;
    Skip
  .
  Definition mainF: function := mk_function [] (main "p" "r1" "r2" "r3").

  Definition program: program :=
    [
      ("main", mainF) ;
        ("init", initF) ;
        ("alloc_contiguous", alloc_contiguousF) ;
        ("alloc_contiguous_no_fallback", alloc_contiguous_no_fallbackF) ;
        ("add_chunk", add_chunkF)
    ].

End MPOOLSEQ.





Module MPOOLCONCUR.

End MPOOLCONCUR.

