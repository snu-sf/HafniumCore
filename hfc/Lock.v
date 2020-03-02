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
    if rel_dec func_name "Lock.unlock"
    then case_unlock
    else
      if rel_dec func_name "Lock.lock"
      then case_lock
      else
        if rel_dec func_name "Lock.init"
        then case_init
        else case_other
  .

  Definition sem: CallExternalE ~> itree (CallExternalE +' Event +' LockEvent) :=
    (fun _ '(CallExternal func_name args) =>
       match case_analysis func_name with
       | case_init =>
         triggerSyscall "d" "lock-init" [Vnull] ;;
         v <- (unwrapN (nth_error args 0)) ;;
         id <- trigger (InitE v) ;;
         Ret (Vnat id, [])
       | case_unlock =>
         id <- (unwrapN (nth_error args 0 >>= get_id)) ;;
            v <- (unwrapN (nth_error args 1)) ;;
            triggerSyscall "d" "lock-unlock <--- " [Vnat id ; v] ;;
            trigger (UnlockE id v) ;;
            trigger EYield ;;
            Ret (Vnodef, [])
       | case_lock =>
         (* triggerSyscall "d" "lock-lock" [Vnull] ;; *)
         (* trigger EYield ;; *)
         (* id <- (unwrapN (nth_error args 0) >>= (unwrapN <*> get_id)) ;; *)
         id <- (unwrapN (nth_error args 0 >>= get_id)) ;;
         (* triggerSyscall "d" "lock-lock looking for: " [Vnat id] ;; *)
            (* (trigger (LockE id)) >>= unwrapN >>= fun v => Ret (v, []) *)

            v <- (ITree.iter (fun _ => trigger EYield ;; trigger (TryLockE id)) tt) ;;
            triggerSyscall "d" "lock-lock   ---> " [Vnat id ; v] ;;
            Ret (v, [])
            (* v <- trigger (TryLockE id) ;; *)
            (* match v with *)
            (* | inr v => Ret (v, []) *)
            (* | inl _ => Ret (Vnull, []) *)
            (* end *)


            (* v <- (ITree.iter (fun _ => *)
            (*                     trigger EYield ;; *)
            (*                     trigger (TryLockE id)) tt) ;; *)
            (* v <- ((trigger (TryLockE id)) >>= unwrapN) ;; *)
            (* Ret (v, []) *)
       | _ => triggerNB "Lock-no such function"
       end)
  .

  Definition owned_heap := (nat * (alist ident val))%type.

  (* Definition extract_to_print (al: alist ident val): unit := tt. *)
  
  Definition debug_print (A: Type) (printer: A -> unit) (content: A): A :=
    let unused := printer content in content.
  Extract Constant debug_print =>
  (* "fun printer content -> printer content ; content" *)
  "fun printer content -> content"
  .
  Variable alist_printer: alist ident val -> unit.
  (* Variable dummy_client: unit -> unit. *)
  (* Extract Constant dummy_client => "fun x -> x". *)
  Extract Constant alist_printer =>
  "
  let rec nat_to_int = function | O -> 0 | S n -> succ (nat_to_int n) in
  fun al -> print_string ""]]] "" ; print_int (nat_to_int (length al)) ; print_string "" "" ; (List.iter (fun kv -> print_int (nat_to_int (fst kv)) ; print_string "" "") al) ; print_endline "" "" "
  .

  Definition handler: LockEvent ~> stateT owned_heap (itree Event) :=
    (* State.interp_state  *)
    fun _ e '(ctr, m) =>
      match e with
      | UnlockE k v =>
        let m := debug_print alist_printer m in
        Ret ((ctr, Maps.add k v m), tt)
      | TryLockE k =>
        let m := debug_print alist_printer m in
        match Maps.lookup k m with
        | Some v =>
          let m' := debug_print alist_printer (Maps.remove k m) in
          Ret ((ctr, m'), inr v)
          (* Ret ((ctr, Maps.remove k m), inr v) *)
        | None => Ret ((ctr, m), inl tt)
        end
      (* | WHY_ANY_NAME_WORKS_HERE_THIS_IS_WEIRD => Ret ((S ctr, m), ctr) *)
      | InitE v =>
        let m := debug_print alist_printer m in
        let m' := debug_print alist_printer (Maps.add ctr v m) in
        Ret ((S ctr, m'), ctr)
        (* Ret ((S ctr, (Maps.add ctr v m)), ctr) *)
      end
  .

  Definition modsem: ModSem :=
    mk_ModSem
      (fun s => existsb (string_dec s) ["Lock.unlock" ; "Lock.lock" ; "Lock.init"])
      (* in_dec Strings.String.string_dec s ["Lock.unlock" ; "Lock.lock" ; "Lock.init"]) *)
      (5252, Maps.empty)
      LockEvent
      handler
      sem
  .

End LOCK.

