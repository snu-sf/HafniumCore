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
     Structures.Foldable
     Structures.Reducible
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

Require Import ClassicalDescription.
About excluded_middle_informative.

Set Implicit Arguments.
(* Set Typeclasess Depth 4. *)
(* Typeclasses eauto := debug 4. *)

Definition var : Set := string.

Inductive val: Type :=
| Vnat (n: nat)
| Vptr (contents: list val)
(* | Vundef *)
(* | Vnodef *)
.
Definition Vnull := Vptr [].
(* YJ: is it really same with nodef? or we need explicit nodef? *)
Definition Vnodef := Vnull.

Axiom dummy_client: forall A, A -> unit.

(** Expressions are made of variables, constant literals, and arithmetic operations. *)
Inductive expr : Type :=
| Var (_ : var)
| Lit (_ : val)
| Plus  (_ _ : expr)
| Minus (_ _ : expr)
| Mult  (_ _ : expr)
| Load (_: var) (_: expr)
.

(** The statements are straightforward. The [While] statement is the only
 potentially diverging one. *)

Inductive stmt : Type :=
| Assign (x : var) (e : expr)    (* x = e *)
| Seq    (a b : stmt)            (* a ; b *)
| If     (i : expr) (t e : stmt) (* if (i) then { t } else { e } *)
| While  (t : expr) (b : stmt)   (* while (t) { b } *)
| Skip                           (* ; *)
| Assume
| Guarantee
| Store (x: var) (ofs: expr) (e: expr) (* x->ofs := e *)
| Put (v: var)
(* | Get (x: var) *)
| Call (retv_name: var) (func_name: string) (params: list var)
(* YJ: "Call" has nome collision *)
(* YJ: I used "var" instead of "var + val". We should "update" retvs into variables. *)
| Expr (e: expr)
.

Inductive function: Type := mk_function { params: list var ; body: stmt }.
Definition program: Type := (* list function. *) string -> option function.

(* ========================================================================== *)
(** ** Notations *)

Module ImpNotations.

  (** A few notations for convenience.  *)
  Definition Var_coerce: string -> expr := Var.
  Definition Lit_coerce: val -> expr := Lit.
  Definition nat_coerce: nat -> val := Vnat.
  Coercion Var_coerce: string >-> expr.
  Coercion Lit_coerce: val >-> expr.
  Coercion nat_coerce: nat >-> val.

  Bind Scope expr_scope with expr.

  Infix "+" := Plus : expr_scope.
  Infix "-" := Minus : expr_scope.
  Infix "*" := Mult : expr_scope.
  (* Notation "'NULL'" := (Vptr []) (at level 40): expr_scope. *)

  Bind Scope stmt_scope with stmt.

  (* Notation "x '←' e" := *)
  (*   (Assign x e) (at level 60, e at level 50): stmt_scope. *)

  (* Notation "a ';;;' b" := *)
  (*   (Seq a b) *)
  (*     (at level 100, right associativity, *)
  (*      format *)
  (*        "'[v' a  ';;;' '/' '[' b ']' ']'" *)
  (*     ): stmt_scope. *)

  (* Notation "'IF' i 'THEN' t 'ELSE' e 'FI'" := *)
  (*   (If i t e) *)
  (*     (at level 100, *)
  (*      right associativity, *)
  (*      format *)
  (*        "'[v ' 'IF'  i '/' '[' 'THEN'  t  ']' '/' '[' 'ELSE'  e ']' 'FI' ']'"). *)

  (* Notation "'WHILE' t 'DO' b" := *)
  (*   (While t b) *)
  (*     (at level 100, *)
  (*      right associativity, *)
  (*      format *)
  (*        "'[v  ' 'WHILE'  t  'DO' '/' '[v' b  ']' ']'"). *)

  Notation "x '#:=' e" :=
    (Assign x e) (at level 60, e at level 50): stmt_scope.

  Notation "a '#;' b" :=
    (Seq a b)
      (at level 100, right associativity,
       format
         "'[v' a  '#;' '/' '[' b ']' ']'"
      ): stmt_scope.

  Notation "'#if' i 'then' t 'else' e 'fi'" :=
    (If i t e)
      (at level 100,
       right associativity,
       format
         "'[v ' '#if'  i '/' '[' 'then'  t  ']' '/' '[' 'else'  e ']' 'fi' ']'").

  Notation "'#while' t 'do' b" :=
    (While t b)
      (at level 100,
       right associativity,
       format
         "'[v  ' '#while'  t  'do' '/' '[v' b  ']' ']'").

  (* Notation "x '#->' ofs '#:=' e" := *)
  (*   (Store x ofs e) (at level 60, e at level 50): stmt_scope. *)

  (* Notation "x '#->' ofs" := *)
  (*   (Load x ofs) (at level 99): expr_scope. *)

  Notation "#put e" :=
    (Put e) (at level 60, e at level 50): stmt_scope.

  (* Notation "x '#:=' '#get' e" := *)
  (*   (Get x e) (at level 60, e at level 50): stmt_scope. *)

End ImpNotations.

Import ImpNotations.

(* ========================================================================== *)
(** ** Semantics *)

(** _Imp_ produces effects by manipulating its variables.  To account for this,
    we define a type of _external interactions_ [ImpState] modeling reads and
    writes to global variables.

    A read, [GetVar], takes a variable as an argument and expects the
    environment to answer with a val, hence defining an event of type
    [ImpState val].

    Similarly, [SetVar] is a write event parameterized by both a variable and a
    val to be written, and defines an event of type [ImpState unit], no
    informative answer being expected from the environment.  *)
Variant ImpState : Type -> Type :=
| GetVar (x : var) : ImpState val
| SetVar (x : var) (v : val) : ImpState unit
(* | StoreVar (x: var) (ofs: nat) (v: val): ImpState bool *)
.

Variant Event: Type -> Type :=
| NB: Event void
| UB: Event void
| Syscall
    (name: string)
    (arg: list val): Event val
| Yield: Event unit
.

(* YJ: Will be consumed internally *)
Variant EventInternal: Type -> Type :=
| CallInternal (func_name: string) (args: list val): EventInternal (val * list val)
(* ordinary return value, "updated" args *)
.

Definition triggerUB {E A} `{Event -< E} : itree E A :=
  vis UB (fun v => match v: void with end)
.
Definition triggerNB {E A} `{Event -< E} : itree E A :=
  vis NB (fun v => match v: void with end)
.
Definition triggerSyscall {E} `{Event -< E} : string -> list val -> itree E val :=
  embed Syscall
.

Definition unwrapN {E X} `{Event -< E} (x: option X): itree E X :=
  match x with
  | Some x => ret x
  | None => triggerNB
  end.

Definition unwarpU {E X} `{Event -< E} (x: option X): itree E X :=
  match x with
  | Some x => ret x
  | None => triggerUB
  end.

Section Denote.

  (** We now proceed to denote _Imp_ expressions and statements.
      We could simply fix in stone the universe of events to be considered,
      taking as a semantic domain for _Imp_ [itree ImpState X]. That would be
      sufficient to give meaning to _Imp_, but would prohibit us from relating this
      meaning to [itree]s stemmed from other entities. Therefore, we
      parameterize the denotation of _Imp_ by a larger universe of events [eff],
      of which [ImpState] is assumed to be a subevent. *)

  Context {eff : Type -> Type}.
  Context {HasImpState : ImpState -< eff}.
  Context {HasEvent : Event -< eff}.
  Context {HasEventInternal : EventInternal -< eff}.

  (** _Imp_ expressions are denoted as [itree eff val], where the returned
      val in the tree is the val computed by the expression.
      In the [Var] case, the [trigger] operator smoothly lifts a single event to
      an [itree] by performing the corresponding [Vis] event and returning the
      environment's answer immediately.
      A constant (literal) is simply returned.
      Usual monadic notations are used in the other cases: we can [bind]
      recursive computations in the case of operators as one would expect. *)

  Fixpoint denote_expr (e : expr) : itree eff val :=
    match e with
    | Var v     => trigger (GetVar v)
    | Lit n     => ret n
    | Plus a b  => l <- denote_expr a ;; r <- denote_expr b ;;
                     match l, r with
                     | Vnat l, Vnat r => ret (Vnat (l + r))
                     | _, _ => triggerNB
                     end
    | Minus a b => l <- denote_expr a ;; r <- denote_expr b ;;
                     match l, r with
                     | Vnat l, Vnat r => ret (Vnat (l - r))
                     | _, _ => triggerNB
                     end
    | Mult a b  => l <- denote_expr a ;; r <- denote_expr b ;;
                     match l, r with
                     | Vnat l, Vnat r => ret (Vnat (l - r))
                     | _, _ => triggerNB
                     end
    | Load x ofs => x <- trigger (GetVar x) ;; ofs <- denote_expr ofs ;;
                      match x, ofs with
                      | Vptr cts, Vnat ofs =>
                        match nth_error cts ofs with
                        | Some v => ret v
                        | _ => triggerNB
                        end
                      | _, _ => triggerNB
                      end
    end.

  (** We turn to the denotation of statements. As opposed to expressions,
      statements do not return any val: their semantic domain is therefore
      [itree eff unit]. The most interesting construct is, naturally, [while].

      To define its meaning, we make use of the [iter] combinator provided by
      the [itree] library:

      [iter : (A -> itree E (A + B)) -> A -> itree E B].

      The combinator takes as argument the body of the loop, i.e. a function
      that maps inputs of type [A], the accumulator, to an [itree] computing
      either a new [A] that can be fed back to the loop, or a return val of
      type [B]. The combinator builds the fixpoint of the body, hiding away the
      [A] argument from the return type.

      Compared to the [mrec] and [rec] combinators introduced in
      [Introduction.v], [iter] is more restricted in that it naturally
      represents tail recursive functions.  It, however, enjoys a rich equational
      theory: its addition grants the type of _continuation trees_ (named
      [ktree]s in the library), a structure of _traced monoidal category_.

      We use [loop] to first build a new combinator [while].
      The accumulator degenerates to a single [unit] val indicating
      whether we entered the body of the while loop or not. Since the
      the operation does not return any val, the return type is also
      taken to be [unit].
      That is, the right tag [inr tt] says to exit the loop,
      while the [inl tt] says to continue. *)

  Definition while (step : itree eff (unit + unit)) : itree eff unit :=
    iter (C := Kleisli _) (fun _ => step) tt.

  (** Casting vals into [bool]:  [0] corresponds to [false] and any nonzero
      val corresponds to [true].  *)
  Definition is_true (v : val) : bool :=
    match v with
    | Vnat n => if (n =? 0)%nat then false else true
    | Vptr (_ :: _) => true (* nonnull pointer *)
                         (* YJ: THIS IS TEMPORARY HACKING *)
    | Vptr _ => false (* null pointer *)
    end
  .

  (** The meaning of Imp statements is now easy to define.  They are all
      straightforward, except for [While], which uses our new [while] combinator
      over the computation that evaluates the conditional, and then the body if
      the former was true.  *)
  Typeclasses eauto := debug 4.
  Fixpoint denote_stmt (s : stmt) : itree eff unit :=
    match s with
    | Assign x e =>  v <- denote_expr e ;; trigger (SetVar x v)
    | Seq a b    =>  denote_stmt a ;; denote_stmt b
    | If i t e   =>
      v <- denote_expr i ;;
      if is_true v then denote_stmt t else denote_stmt e

    | While t b =>
      while (v <- denote_expr t ;;
	           if is_true v
             then denote_stmt b ;; ret (inl tt)
             else ret (inr tt))

    | Skip => ret tt
    | Assume => triggerUB
    | Guarantee => triggerNB
    | Store x ofs e => ofs <- denote_expr ofs ;; e <- denote_expr e ;;
                           v <- trigger (GetVar x) ;;
                           match ofs, v with
                           | Vnat ofs, Vptr cts0 =>
                             cts1 <- (unwrapN (update_err cts0 ofs e)) ;;
                                  (**** BELOW WAS AN ACTUAL MISTAKE *****)
                             (* cts1 <- (getN (update_err cts0 ofs v)) ;; *)
                                  trigger (SetVar x (Vptr cts1))
                           | _, _ => triggerNB
                           end
    | Put x => v <- trigger (GetVar x) ;;
                 _ <- triggerSyscall "p" [v] ;; Ret tt
    (* | Get x => retv <- triggerSyscall (1) [];; trigger (SetVar x retv);; Ret tt *)
    | Call retv_name name params =>
      args <- mapT (fun arg => trigger (GetVar arg)) params;;
      retv_and_args_updated <- trigger (CallInternal name args);;
      let '(retv, args_updated) := retv_and_args_updated in
      if (length args_updated =? length params)%nat
      then 
        mapT (fun param_and_arg_updated =>
                let '(param, arg_updated) := param_and_arg_updated in
                trigger (SetVar param arg_updated))
             (combine params args_updated);;
             trigger (SetVar retv_name retv)
      else triggerNB
    | Expr e => ret tt
    end.

  Fixpoint denote_stmt2 (s : stmt) : itree eff val :=
    match s with
    | Assign x e =>  v <- denote_expr e ;; trigger (SetVar x v) ;; ret Vnodef
    | Seq a b    =>  denote_stmt2 a ;; denote_stmt2 b
    | If i t e   =>
      v <- denote_expr i ;;
      if is_true v then denote_stmt2 t else denote_stmt2 e

    | While t b =>
      while (v <- denote_expr t ;;
               if is_true v
               then v <- denote_stmt2 b ;; ret (inl tt)
               else ret (inr tt))
            ;;
            ret Vnodef (* YJ: this is temporary. *)
    | Skip => ret Vnodef
    | Assume => triggerUB
    | Guarantee => triggerNB
    | Store x ofs e => ofs <- denote_expr ofs ;; e <- denote_expr e ;;
                           v <- trigger (GetVar x) ;;
                           match ofs, v with
                           | Vnat ofs, Vptr cts0 =>
                             cts1 <- (unwrapN (update_err cts0 ofs e)) ;;
                                  (**** BELOW WAS AN ACTUAL MISTAKE *****)
                             (* cts1 <- (getN (update_err cts0 ofs v)) ;; *)
                                  trigger (SetVar x (Vptr cts1))
                           | _, _ => triggerNB
                           end ;;
                           ret Vnodef
    | Put x => v <- trigger (GetVar x) ;;
                 _ <- triggerSyscall "p" [v] ;; Ret Vnodef
    (* | Get x => retv <- triggerSyscall (1) [];; trigger (SetVar x retv);; Ret tt *)
    | Call retv_name name params =>
      args <- mapT (fun arg => trigger (GetVar arg)) params;;
      retv_and_args_updated <- trigger (CallInternal name args);;
      let '(retv, args_updated) := retv_and_args_updated in
      if (length args_updated =? length params)%nat
      then
        mapT (fun param_and_arg_updated =>
                let '(param, arg_updated) := param_and_arg_updated in
                trigger (SetVar param arg_updated))
             (combine params args_updated);;
             trigger (SetVar retv_name retv) ;;
             ret Vnodef
      else triggerNB
    | Expr e => denote_expr e
    end.

End Denote.

Section Denote.

  Open Scope expr_scope.
  Open Scope stmt_scope.

  Context {eff : Type -> Type}.
  Context {HasImpState : ImpState -< eff}.
  Context {HasEvent : Event -< eff}.

  Definition denote_function (f: function): ktree (EventInternal +' eff) (list val) unit :=
    fun args =>
      if (length f.(params) =? length args)%nat
      then
        let new_body := fold_left (fun s i => (fst i) #:= (Lit (snd i)) #; s)
                                  (* YJ: Why coercion does not work ?? *)
                                  (combine f.(params) args) f.(body) in
        denote_stmt new_body
      else triggerNB
  .

  (* Axiom tm: forall T, itree (EventInternal +' eff) T. *)
  (* Axiom tmp: itree (EventInternal +' eff) (val * list val). *)

  (* Variable A B: Type. *)
  (* (* Variable a: A. *) *)
  (* Variable consumer: A -> B. *)
  (* Inductive foo: Type -> Type := *)
  (* | foo_intro (a: A): foo A *)
  (* . *)
  (* Definition bar: forall T, foo T -> consumer . *)
  (* intros. destruct X. auto. *)
  (* Defined. *)

  Print Instances Traversable.
  Print Instances Reducible.
  Print Instances Foldable.

  (* Variable params: list var. *)
  (* Check (mapT (fun param => trigger (GetVar param)) params). *)

  Definition denote_function2 (f: function):
    (EventInternal ~> itree (EventInternal +' eff)) :=
    fun T ei =>
      let '(CallInternal func_name args) := ei in
      if (length f.(params) =? length args)%nat
      then
        let new_body := fold_left (fun s i => (fst i) #:= (Lit (snd i)) #; s)
                                  (* YJ: Why coercion does not work ?? *)
                                  (combine f.(params) args) f.(body) in
        retv <- denote_stmt2 new_body;;
             params_updated <- mapT (fun param => trigger (GetVar param)) (f.(params));;
             ret (retv, params_updated)
      else triggerNB
  .

  Definition denote_function3 (ctx: program):
    (EventInternal ~> itree (EventInternal +' eff)) :=
    fun T ei =>
      let '(CallInternal func_name args) := ei in
      f <- unwrapN (ctx func_name) ;;
      if (length f.(params) =? length args)%nat
      then
        let new_body := fold_left (fun s i => (fst i) #:= (Lit (snd i)) #; s)
                                  (* YJ: Why coercion does not work ?? *)
                                  (combine f.(params) args) f.(body) in
        retv <- denote_stmt2 new_body;;
             params_updated <- mapT (fun param => trigger (GetVar param)) (f.(params));;
             ret (retv, params_updated)
      else triggerNB
  .

  Definition denote_program (p: program) :=
    (* mrec (denote_function3 p) (CallInternal "MAIN" []). *)
    let sem := mrec (denote_function3 p) in
    sem _ (CallInternal "MAIN" []).
  (* Better readability *)

  (* Definition denote_program (p: program): *)
  (*   mrec-fix _ _ . *)
End Denote.

(* ========================================================================== *)
(** ** EXAMPLE: Factorial *)

Section Example_Fact.

  (** We briefly illustrate the language by writing the traditional factorial.
      example.  *)

  Open Scope expr_scope.
  Open Scope stmt_scope.
  Variable input: var.
  Variable output: var.

  (* Definition fact (n:nat): stmt := *)
  (*   input ← n;;; *)
  (*   output ← 1;;; *)
  (*   WHILE input *)
  (*   DO output ← output * input;;; *)
  (*      input  ← input - 1. *)
  Definition fact (n:nat): stmt :=
    input #:= Vnat n#;
    output #:= Vnat 1#;
    #while input
    do output #:= output * input#;
       input  #:= input - Vnat 1.

  (** We have given _a_ notion of denotation to [fact 6] via [denote_imp].
      However, this is naturally not actually runnable yet, since it contains
      uninterpreted [ImpState] events.  We therefore now need to _handle_ the
      events contained in the trees, i.e. give a concrete interpretation of the
      environment.  *)

End Example_Fact.

(* ========================================================================== *)
(** ** Interpretation *)

(* begin hide *)
From ITree Require Import
     Events.MapDefault.

From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

(** These enable typeclass instances for Maps keyed by strings and vals *)
Instance RelDec_string : RelDec (@eq string) :=
  { rel_dec := fun s1 s2 => if string_dec s1 s2 then true else false}.

Instance RelDec_string_Correct: RelDec_Correct RelDec_string.
Proof.
  constructor; intros x y.
  split.
  - unfold rel_dec; simpl.
    destruct (string_dec x y) eqn:EQ; [intros _; apply string_dec_sound; assumption | intros abs; inversion abs].
  - intros EQ; apply string_dec_sound in EQ; unfold rel_dec; simpl; rewrite EQ; reflexivity.
Qed.
(* end hide *)

(** We provide an _ITree event handler_ to interpret away [ImpState] events.  We
    use an _environment event_ to do so, modeling the environment as a
    0-initialized map from strings to vals.  Recall from [Introduction.v] that
    a _handler_ for the events [ImpState] is a function of type [forall R, ImpState R
    -> M R] for some monad [M].  Here we take for our monad the special case of
    [M = itree E] for some universe of events [E] required to contain the
    environment events [mapE] provided by the library. It comes with an event
    interpreter [interp_map] that yields a computation in the state monad.  *)
Definition handle_ImpState {E: Type -> Type} `{(mapE var (Vnat 0)) -< E}:
  ImpState ~> itree E :=
  fun _ e =>
    match e with
    | GetVar x => lookup_def x
    | SetVar x v => insert x v
    end.

(** We now concretely implement this environment using ExtLib's finite maps. *)
Definition env := alist var val.

(** Finally, we can define an evaluator for our statements.
   To do so, we first denote them, leading to an [itree ImpState unit].
   We then [interp]ret [ImpState] into [mapE] using [handle_ImpState], leading to
   an [itree (mapE var val) unit].
   Finally, [interp_map] interprets the latter [itree] into the state monad,
   resulting in an [itree] free of any event, but returning the final
   _Imp_ env.
 *)
(* SAZ: would rather write something like the following:
 h : E ~> M A
 h' : F[void1] ~> M A
forall eff, {pf:E -< eff == F[E]} (t : itree eff A)
        interp pf h h' t : M A
*)

Definition interp_imp  {E A} (t : itree (ImpState +' E) A) :
  stateT env (itree E) A :=
  let t' := interp (bimap handle_ImpState (id_ E)) t in
  interp_map t'.

(* Definition handle_Event *)
(*   : Event ~> itree void1 := *)
(*   fun T e => *)
(*     match e with *)
(*     | UB => ITree.spin *)
(*     | NB => ITree.spin *)
(*     end *)

(* Definition interp_Event {E A} (t: itree (Event +' E) A): itree (void1 +' E) A := *)
(*   let t' := interp (bimap handle_Event (id_ E)) t in *)
(*   t'. *)

(* Definition interp_Event2 {A} (t: itree (Event) A): itree (void1) A := *)
(*   let t' := interp (handle_Event) t in *)
(*   t'. *)

Variable s: stmt.
Check (denote_imp s).
Check interp_imp (denote_imp s) empty.
(* Check (@interp_Event _ _ (interp_imp (denote_imp s) empty)). *)
(* Check (interp_Event2 (interp_imp (denote_imp s) empty)). *)

(* Definition eval_imp2 (s: stmt) : itree void1 (env * unit) *)
(*   := (interp_Event2 (interp_imp (denote_imp s) empty)) *)
(* . *)

(* Definition eval_imp (s: stmt) {E} : itree (void1 +' E) (env * unit) := *)
(*   interp_Event (interp_imp (denote_imp s) empty). *)

Fail Definition eval_imp (s: stmt) : itree void1 (env * unit) :=
  interp_imp (denote_imp s) empty.

Definition eval_imp (s: stmt) : itree Event (env * unit)
  := ((interp_imp (denote_imp s) empty))
.

(** Equipped with this evaluator, we can now compute.
    Naturally since Coq is total, we cannot do it directly inside of it.
    We can either rely on extraction, or use some fuel.
 *)
Definition test_assume := eval_imp Assume.
                            
(* Definition test_interp : itree IO unit -> bool := fun t => *)
Definition stmt_Assume: stmt := Assume.
Compute (burn 200 (eval_imp (fact "input" "output" 6))).
Compute (burn 200 (eval_imp Assume)).
Compute (burn 200 (eval_imp Guarantee)).
Goal forall E R, (burn 200 (@ITree.spin E R)) = (burn 2 (ITree.spin)).
  reflexivity.
Qed.

Goal (burn 200 (@eval_imp Assume)) = (burn 2 (eval_imp Assume)).
  reflexivity.
Qed.

Require Extraction.

(* Extraction "Lang.ml" burn. *)
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.


Definition load_store x sum: stmt :=
  sum #:= Vnat 0#;
  x #:= Vptr (repeat (Vnat 0) 3)#;
  #put x#;
  (Store x 0 10)#;
  #put x#;
  (Store x 1 20)#;
  #put x#;
  (Store x 2 30)#;
  #put x#;
  #put sum#;
  sum #:= sum + (Load x 0)#;
  #put sum#;
  sum #:= sum + (Load x 1)#;
  #put sum#;
  sum #:= sum + (Load x 2)#;
  #put sum#;
  Skip
.

Compute (burn 200 (eval_imp (load_store "x" "sum"))).
(* Definition main := (burn 100 (eval_imp2 stmt_Assume)). *)
(* Definition main := (burn 200 (eval_imp2 (load_store "x" "sum"))). *)

(* Require Import ExtrOcamlString. *)
(* Extraction Blacklist String. *)

Definition load_store_applied := load_store "x" "sum".
Definition print_val: unit := tt.
Definition handle_Event: unit := tt.
Definition main: unit :=
  let _ := print_val in
  let _ := load_store_applied in
  let _ := handle_Event in
  tt.
Extract Constant dummy_client => "fun _ -> ()".
Extract Constant print_val => "
let rec go v =
  match v with
  | Vnat n -> print_string ((string_of_int n) ^ "" "")
  | Vptr cts -> print_string ""["" ; List.iter go cts ; print_string ""]"" in
fun v -> go v ; print_endline "" ""
"
.
Extract Constant handle_Event =>
"
fun e k -> match e with
  | NB -> failwith ""NB OCCURED""
  | UB -> failwith ""UB OCCURED""
  | Syscall (['p'], [v]) -> print_val v ; k (Obj.magic ())
  | _ -> failwith ""NO MATCH""
"
.
Extract Constant main =>
"
let rec run t =
  match observe t with
  | RetF r -> r
  | TauF t -> run t
  | VisF (e, k) -> handle_Event e (fun x -> run (k x)) in
run (eval_imp load_store_applied)
"
.

(* Fixpoint val_iter (v: val) (f: nat -> unit): unit := *)
(*   match v with *)
(*   | Vnat n => dummy_client (f n) *)
(*   | Vptr cts => List.fold_left (fun s i => dummy_client i) cts tt *)
(*   end *)
(* . *)

Extraction "Lang.ml" load_store_applied eval_imp stmt_Assume print_val main handle_Event.

(* ========================================================================== *)
Section InterpImpProperties.
  (** We can lift the underlying equational theory on [itree]s to include new
      equations for working with [interp_imp].

      In particular, we have:
         - [interp_imp] respects [≈]
         - [interp_imp] commutes with [bind].

      We could justify more equations than just the ones below.  For instance,
      _Imp_ programs also respect a coarser notation of equivalence for the
      [env] state.  We exploit this possibility to implement optimzations
      at the _Asm_ level (see AsmOptimizations.v).
   *)

  Context {E': Type -> Type}.
  Notation E := (ImpState +' E').

  (** This interpreter is compatible with the equivalence-up-to-tau. *)
  Global Instance eutt_interp_imp {R}:
    Proper (@eutt E R R eq ==> eq ==> @eutt E' (prod (env) R) (prod _ R) eq)
           interp_imp.
  Proof.
    repeat intro.
    unfold interp_imp.
    unfold interp_map.
    rewrite H0. eapply eutt_interp_state_eq; auto.
    rewrite H. reflexivity.
  Qed.

  (** [interp_imp] commutes with [bind]. *)
  Lemma interp_imp_bind: forall {R S} (t: itree E R) (k: R -> itree E S) (g : env),
      (interp_imp (ITree.bind t k) g)
    ≅ (ITree.bind (interp_imp t g) (fun '(g',  x) => interp_imp (k x) g')).
  Proof.
    intros.
    unfold interp_imp.
    unfold interp_map.
    repeat rewrite interp_bind.
    repeat rewrite interp_state_bind.
    apply eqit_bind. red. intros.
    destruct a as [g'  x].
    simpl.
    reflexivity.
    reflexivity.
  Qed.

End InterpImpProperties.



(** We now turn to our target language, in file [Asm].v *)
