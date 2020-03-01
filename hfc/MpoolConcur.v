
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
Require Import Lang.
Import ImpNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.



Set Implicit Arguments.







(* From ITree Require Import *)
(*      Events.MapDefault. *)

From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.



Module LOCK.

  Definition ident := nat.

  Inductive LockEvent: Type -> Type :=
  | TryLockE (id: ident): LockEvent (unit + val) (* inl: is already running, inr: not *)
  | UnlockE (id: ident) (v: val): LockEvent unit
  | InitE (v: val): LockEvent ident
  .

  Definition get_id (v: val): option ident :=
    match v with
    | Vnat n => Some n
    | _ => None
    end
  .

  Inductive case: Type :=
  | case_init
  | case_unlock
  | case_lock
  | case_other
  .

  Definition case_analysis (func_name: string): case :=
    if rel_dec func_name "unlock"
    then case_unlock
    else
      if rel_dec func_name "lock"
      then case_lock
      else
        if rel_dec func_name "init"
        then case_lock
        else case_other
  .

  Definition sem: CallExternalE ~> itree (CallExternalE +' Event +' LockEvent) :=
    (fun _ '(CallExternal func_name args) =>
       match case_analysis func_name with
       | case_init =>
         v <- (unwrapN (nth_error args 0)) ;;
         id <- trigger (InitE v) ;;
         Ret (Vnat id, [])
       | case_unlock =>
         id <- (unwrapN (nth_error args 0 >>= get_id)) ;;
            v <- (unwrapN (nth_error args 1)) ;;
            trigger (UnlockE id v) ;;
            trigger EYield ;;
            Ret (Vnodef, [])
       | case_lock =>
         (* trigger EYield ;; *)
         (* id <- (unwrapN (nth_error args 0) >>= (unwrapN <*> get_id)) ;; *)
         id <- (unwrapN (nth_error args 0 >>= get_id)) ;;
            (* (trigger (LockE id)) >>= unwrapN >>= fun v => Ret (v, []) *)
            v <- (ITree.iter (fun _ => trigger EYield ;; trigger (TryLockE id)) tt) ;;
            Ret (v, [])
            (* v <- ((trigger (TryLockE id)) >>= unwrapN) ;; *)
            (* Ret (v, []) *)
       | _ => triggerNB "Lock-no such function"
       end)
  .

  Definition owned_heap := (nat * (alist ident val))%type.

  Definition handler: LockEvent ~> stateT owned_heap (itree Event) :=
    (* State.interp_state  *)
    fun _ e '(ctr, m) =>
      match e with
      | UnlockE k v => Ret ((ctr, Maps.add k v m), tt)
      | TryLockE k =>
        match Maps.lookup k m with
        | Some v => Ret ((ctr, Maps.remove k m), inr v)
        | None => Ret ((ctr, m), inl tt)
        end
      (* Ret ((ctr, m), Maps.lookup k m) *)
      | GetUidE => Ret ((S ctr, m), ctr)
      end
  .

  Definition modsem: ModSem :=
    mk_ModSem
      (fun s => existsb (string_dec s) ["Lock.unlock" ; "Lock.lock" ; "Lock.init"])
      (* in_dec Strings.String.string_dec s ["Lock.unlock" ; "Lock.lock" ; "Lock.init"]) *)
      (5252, [])
      LockEvent
      handler
      sem
  .

End LOCK.

































Module MPOOLCONCUR.

  (*
Simplified Mpool := Vptr [Vnat//lock ; Vptr//chunk_list ; Vptr//fallback]
   *)

  Definition lock_ofs := 0.
  Definition chunk_list_ofs := 1.
  Definition fallback_ofs := 2.
  Definition next_chunk_ofs := 0.
  Definition limit_ofs := 1.

  Definition entry_size: nat := 4.

  Fixpoint chunk_list_wf (chunk_list: val): bool :=
    match chunk_list with
    | Vptr paddr cts =>
      is_some paddr &&
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

  Definition lock_wf (lock: val): bool :=
    match lock with
    | Vnat _ => true
    | _ => false
    end
  .

  Fixpoint mpool_wf (p: val): bool :=
    match p with
    | Vptr _ p =>
      match p with
      | [] => true
      | [chunk_list ; fallback ; lock] =>
        chunk_list_wf chunk_list && mpool_wf fallback && lock_wf lock
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

  (*** DELTA: Use function return value instead of borrowing && Add param to "Lock.init" **)
  Definition init (p: var): stmt :=
    (Store p chunk_list_ofs Vnull) #;
    (Store p fallback_ofs Vnull) #;
    (Store p lock_ofs (Call "Lock.init" [CBV p])) #;
    (* (Call "Lock.push" [CBV (Load p lock_ofs) ; CBV p]) #; *)
    Skip
  .

  (* void mpool_init_with_fallback(struct mpool *p, struct mpool *fallback) *)
  (* { *)
  (* 	mpool_init(p, fallback->entry_size); *)
  (* 	p->fallback = fallback; *)
  (* } *)

  Definition init_with_fallback (p fallback: var): stmt :=
    Call "init" [CBR p] #;
    (Store p fallback_ofs fallback)
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

  (*** DELTA: while -> recursion && call no_fallback with chunk_list, not mpool ***)
  Definition alloc_contiguous
             (p count: var)
             (ret next nextp: var): stmt :=
    #if (CoqCode [p: expr] (fun p => mpool_wf (nth 0 p Vnull)))
     then Skip
     else Guarantee
    #;
    next #:= (Load p chunk_list_ofs) #;
    p #:= (Call "Lock.lock" [CBV (Load p lock_ofs)]) #;
    ret #:= (Call "alloc_contiguous_no_fallback" [CBR next ; CBV count]) #;
    (Call "Lock.unlock" [CBV (Load p lock_ofs) ; CBV p]) #;
    Store p chunk_list_ofs next #;
    #if (ret)
     then (Return ret)
     else (
         nextp #:= (Load p fallback_ofs) #;
         #if (! nextp) then Return Vnull else Skip #;
         ret #:= (Call "alloc_contiguous" [CBR nextp ; CBV count]) #;
         (Store p fallback_ofs nextp) #;
         Return ret
       )
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

  (*** DELTA: while -> recursion && "limit" ptr -> offset "nat" && no alignment ***)
  Definition alloc_contiguous_no_fallback
             (cur count: var)
             (ret next cur_ofs new_cur: var): stmt :=
    #if ! cur then Return Vnull else Skip #;
    cur_ofs #:= (Load cur limit_ofs) #;
    #if (count <= cur_ofs)
     then (
           (Put "If1-limit: " cur_ofs) #;
           #if count == cur_ofs
            then (
                ret #:= (SubPointerTo cur (count * entry_size)) #;
                cur #:= (Load cur next_chunk_ofs) #;
                Return ret
              )
            else (
                new_cur #:= (SubPointerFrom cur (count * entry_size)) #;
                Store new_cur next_chunk_ofs (Load cur next_chunk_ofs) #;
                Store new_cur limit_ofs (cur_ofs - count) #;
                ret #:= (SubPointerTo cur (count * entry_size)) #;
                cur #:= new_cur #;
                Return ret
              )
          )
     else (
         (Put "Else1-limit: " cur_ofs) #;
         next #:= (Load cur next_chunk_ofs) #;
         ret #:= (Call "alloc_contiguous_no_fallback2" [CBR next ; CBV count]) #;
         Store cur next_chunk_ofs next #;
         Return ret
         )
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

  (*** DELTA: no alignment ***)
  Definition add_chunk
             (p begin size: var)
             (chunk: var): stmt :=
    chunk #:= begin #;
    (* Store chunk limit_ofs ((GetLen chunk) / entry_size) #; *)
    Store chunk limit_ofs size #;

    p #:= (Call "Lock.lock" [CBV (Load p lock_ofs)]) #;
    Store chunk next_chunk_ofs (Load p chunk_list_ofs) #;
    Store p chunk_list_ofs chunk #;
    (Call "Lock.unlock" [CBV (Load p lock_ofs) ; CBV p]) #;
    Skip
  .

  Definition initF: function :=
    mk_function ["p"] (init "p").
  Definition init_with_fallbackF: function :=
    mk_function ["p" ; "fb"] (init_with_fallback "p" "fb").
  Definition alloc_contiguousF: function :=
    mk_function ["p" ; "count"] (alloc_contiguous "p" "count" "ret" "next" "nextp").
  Definition alloc_contiguous_no_fallbackF: function :=
    mk_function ["cur" ; "count"]
                (alloc_contiguous_no_fallback "cur" "count" "ret" "next"
                                              "cur_ofs" "new_cur").
  Definition add_chunkF: function :=
    mk_function ["p" ; "begin" ; "size"] (add_chunk "p" "begin" "size" "chunk").


End MPOOLCONCUR.

