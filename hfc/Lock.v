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
         triggerSyscall "d" "lock-unlock" [Vnull] ;;
         id <- (unwrapN (nth_error args 0 >>= get_id)) ;;
            v <- (unwrapN (nth_error args 1)) ;;
            trigger (UnlockE id v) ;;
            trigger EYield ;;
            Ret (Vnodef, [])
       | case_lock =>
         triggerSyscall "d" "lock-lock" [Vnull] ;;
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
      (* | WHY_ANY_NAME_WORKS_HERE_THIS_IS_WEIRD => Ret ((S ctr, m), ctr) *)
      | InitE v => Ret ((S ctr, (Maps.add ctr v m)), ctr)
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

