Require Import Map.
Require Import Language.Syntax.
Require Import Language.Security.
Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

(** ** Semantics *)
Definition valuation := fmap var nat.
(** Our first step is to give a meaning to these new constructs.  Let's start with
    an interpreter for binary operators: *)
Definition interp_binop (b: BinopName) (n1 n2: nat) :=
  match b with
  | LogAnd => Nat.land n1 n2
  | Eq => if (n1 =? n2) then 1 else 0
  | Plus => n1 + n2
  | Minus => n1 - n2
  | Times => n1 * n2
  | Divide => n1 / n2
  | ShiftLeft => Nat.shiftl n1 n2
  | ShiftRight => Nat.shiftr n1 n2
  | Modulo => Nat.modulo n1 n2
  end.

(** For expressions, we'll use an interpreter to implement the following rules::

                 n1 = n2
              ------------
               ⟦n2⟧ᵥ = n1
   
       (x ↦ a) ∈ v         x ∉ v
      --------------     ----------
         ⟦x⟧ᵥ = a         ⟦x⟧ᵥ = 0
   
               ⟦e1⟧ᵥ = a1
               ⟦e2⟧ᵥ = a2
         a = interp_binop b a1 a2
      -----------------------------
          ⟦Binop b e1 e2⟧ᵥ = a
*)
 
Inductive trace_event := 
| Branch: bool -> trace_event
| MemWrite: var -> trace_event.


(* 
   Keep two contexts, for parallel work, we will migrate to a single context later
   sec_context will be rename to just context and the old one will be removed.
 *)
Definition context := (valuation * list trace_event)%type.
Definition sec_context := (valuation * sec_env * list trace_event)%type.

(* Getters for contexts *)
Definition val_of (ctx: context) := fst ctx.
Definition trace_of (ctx: context) := snd ctx.

(* Getters for sec_context *)
Definition sec_val_of (ctx : sec_context) := fst (fst ctx).
Definition sec_of (ctx : sec_context) := snd (fst ctx).
Definition sec_trace_of (ctx : sec_context) := snd ctx.


(* Some custom notations to make writing contexts more convenient.  For example, we can write
   [($0, nil) t++ Branch true] 
   instead of
   [($0, nil), trace_of ($0, nil) ++ (Branch true :: nil)].
*)


(* Prepending an event to the trace *)
Notation "ev 't::' ctx" :=
  (val_of ctx, ev :: trace_of ctx)
  (at level 60).

(* Appending an event to the trace *)
Notation "ctx 't++' ev" :=
  (val_of ctx, trace_of ctx ++ (ev :: nil))
  (at level 60).

(* Updating the valuation in the context *)
Notation "ctx 'v$+' ( k , v )" :=
  (val_of ctx $+ (k, v), trace_of ctx)
  (at level 50, left associativity).

(* Updating the valuation in a security context *)
Notation "ctx 'sv$+' ( k , v )" :=
  (sec_val_of ctx $+ (k, v), sec_of ctx, sec_trace_of ctx)
  (at level 50, left associativity).

(* Updating the security environment in a security context *)
Notation "ctx 's$+' ( k , level )" :=
  (sec_val_of ctx, sec_of ctx $+ (k, level), sec_trace_of ctx)
  (at level 50, left associativity).

(* Appending an event to the trace in a security context *)
Notation "ctx 'st++' ev" :=
  (sec_val_of ctx, sec_of ctx, sec_trace_of ctx ++ (ev :: nil))
  (at level 60).

(* Define empty contexts to make writing examples easier *)
Definition empty_context : context := ($0, nil).
Definition empty_sec_context : sec_context := ($0, $0, nil).

Fixpoint interp_arith (e: expr) (v: valuation) {struct e}: nat :=
  match e with
  | Const n => n
  | Var x => match v $? x with Some a => a | None => 0 end
  | Binop b e1 e2 => interp_binop b (interp_arith e1 v) (interp_arith e2 v)
  end.

(*
  Compute the security level of an expression, given a security environment.
   Using join_sec to combine the security levels of subexpressions.
 *) 
Fixpoint interp_sec (e : expr) (se : sec_env) {struct e} : sec_level :=
  match e with
  | Const _ => Public
  | Var x => sec_lookup se x
  | Binop _ e1 e2 => join_sec (interp_sec e1 se) (interp_sec e2 se)
  end.



(*2 programs agree on public variables, with potentially different secrets *)
Definition agree_on_public (se : sec_env) (v1 v2 : valuation) : Prop :=
  forall x, sec_lookup se x = Public -> v1 $? x = v2 $? x.

(* Another way is to say that two valuations are low-equivalent, meaning they agree on all public variables *)
Definition low_equiv := agree_on_public.

(** For commands, we'll use an inductive [Prop] to define big-step semantics.
    This is an opportunity to show that compiler proofs can work with a variety
    of semantics styles, since we focused on small-step semantics in lecture.
    The rules for [Assign], [While], [If], and [Skip] are the same as usual; for
    example:

                    ⟦e⟧ᵥ = a
      ----------------------------------- EvalAssign
       (v, Assign x e) ↓ᵩ (v $+ (x, a))
   
       (c1, v) ↓ᵩ v'   (c2, v') ↓ᵩ v''
      ----------------------------------- EvalSequence
          (v, Sequence c1 c2) ↓ᵩ v''

    Notice the subscript φ: this indicates that we have an function_env of functions.
    This function_env of functions gives the body of each function, the names of its
    arguments, and the name of its return value.  For example, to say that the
    function "collatz" has body [CollatzBody], takes arguments "start" and "flight",
    and writes its result to "out", we would write::

        phi = $0 $+ ("collatz", (("start", "flight"), "out", CollatzBody))

    and to say that function "factorial" has body [FactBody], takes argument "n",
    and writes its result to "f", we might write the following (every function takes
    two parameters, so we use "" as the name of the second argument of "factorial").

        phi = $0 $+ ("factorial", (("n", ""), "f", FactBody))

    We need an additional rule [EvalAssignCall] for function calls:

               (f ↦ ((x1, x2), y, body)) ∈ φ
                  ⟦e1⟧ᵥ = a1    ⟦e2⟧ᵥ = a2
          (body, ($0 $+ (x1, a1) $+ (x2, a2))) ↓ᵩ v'
                        (y ↦ a) ∈ v'
       ------------------------------------------------
         (AssignCall x f e1 e2, v) ↓ᵩ (v $+ (x, a))

   A few notes:
   
   - This rule passes arguments by value: that is, the function's arguments are
     evaluated in the current valuation [v]: [⟦e⟧ᵥ = a].
   
   - The function function_env [phi] (represented as φ above) maps function names
     (strings) to function signatures and function bodies:
     [(f ↦ ((x1, x2), y, body)) ∈ φ].
   
   - Functions return their output in variables indicated by their signatures:
     [(y ↦ a) ∈ v1].
   
   - Functions do not have access to the contexts of their callers: [body] runs
     in a clean environment.
   
   Here is how it looks in Rocq: *)

Inductive eval (phi: function_env): context -> cmd -> context -> Prop :=
  | EvalSkip: forall ctx,
      eval phi ctx Skip ctx
  | EvalAssign: forall ctx x e a,
      interp_arith e (val_of ctx) = a ->
      eval phi ctx (Assign x e) (ctx v$+ (x, a))
  | EvalAssignCall: forall x f e1 e2 x1 x2 y body a1 a2 a ctx ctx',
    phi $? f = Some ((x1, x2), y, body) ->
    interp_arith e1 (val_of ctx) = a1 ->
    interp_arith e2 (val_of ctx) = a2 ->
    (*reset the environmnet, but keep the trace. we could also simply append it after*)
    eval phi (($0 $+ (x1, a1) $+ (x2, a2)), trace_of ctx) body ctx' ->
    val_of ctx' $? y = Some a ->
    eval phi ctx (AssignCall x f e1 e2) (val_of ctx $+ (x, a), trace_of ctx')
  | EvalSequence: forall ctx c1 ctx1 c2 ctx2,
      eval phi ctx c1 ctx1 ->
      eval phi ctx1 c2 ctx2 ->
      eval phi ctx (Sequence c1 c2) ctx2
  | EvalIfTrue: forall ctx e thn els ctx' c,
      interp_arith e (val_of ctx) = c ->
      c <> 0 ->
      eval phi (ctx t++ Branch true) thn ctx' ->
      eval phi ctx (If e thn els) ctx'
  | EvalIfFalse: forall ctx e thn els ctx',
      interp_arith e (val_of ctx) = 0 ->
      eval phi (ctx t++ Branch false) els ctx' ->
      eval phi ctx (If e thn els) ctx'
  | EvalWhileTrue: forall ctx e body ctx' ctx'' c,
      interp_arith e (val_of ctx) = c ->
      c <> 0 ->
      eval phi (ctx t++ Branch true) body ctx' ->
      eval phi ctx' (While e body) ctx'' ->
      eval phi ctx (While e body) ctx''
  | EvalWhileFalse: forall ctx e body,
      interp_arith e (val_of ctx) = 0 ->
      eval phi ctx (While e body) (ctx t++ Branch false).


(* The evaluation relation is deterministic: if a command can evaluate to two
different contexts, those contexts must be the same. *)
Theorem eval_deterministic : forall phi c ctx ctx1 ctx2,
  eval phi ctx c ctx1 ->
  eval phi ctx c ctx2 ->
  ctx1 = ctx2.
Proof.
    Ltac invert_eval :=
    match goal with
    | H : eval _ _ _ _ |- _ => inversion H; subst; clear H
    end.

  intros phi c ctx ctx1 ctx2 Heval1.
  revert ctx2.
  induction Heval1; intros ? Heval2.
  - (* Skip *)
    invert_eval. auto.
  - (* Assign *)
    invert_eval. auto.
  - (* AssignCall *)
    invert_eval.
    rewrite H in H7. inversion H7. subst.
    apply IHHeval1 in H12. subst.
    rewrite H2 in H13. inversion H13. auto.
  - (* Sequence *)
    invert_eval.
    apply IHHeval1_1 in H2. subst.
    apply IHHeval1_2 in H4. auto.
  - (* IfTrue *)
    invert_eval.
    + apply IHHeval1 in H8. assumption.
    + lia.
  - (* IfFalse *)
    invert_eval.
    + lia.
    + apply IHHeval1 in H6. assumption.
  - (* WhileTrue *)
    invert_eval.
    + apply IHHeval1_1 in H6. subst.
      apply IHHeval1_2 in H8. assumption.
    + lia.
  - (* WhileFalse *)
    invert_eval.
    + lia.
    + reflexivity.
Qed.


(* 
   Augment the eval relation to also track security levels.
   The new rules are detailed below.


   [EvalSecAssign] 
   adds the premise
    [interp_sec e (sec_of ctx) = level] 
   and updates both the valuation and the security environment, 
   so the assigned variable receives both its value and its computed security label.

   [EvalSecAssignCall]
   adds security-level evaluation premises for the two arguments,
    [interp_sec e1 (sec_of ctx) = level1] and
    [interp_sec e2 (sec_of ctx) = level2].  
   The callee then runs in a fresh security environment initialized
   with those argument labels. 
   The caller additionally requires 
    [sec_lookup (sec_of ctx') y = level] 
   so that the return variable's security label can
   be propagated back to the assignee.
 *)
  

Inductive eval_sec (phi : function_env) : sec_context -> cmd -> sec_context -> Prop :=
  | EvalSecSkip : forall ctx,
      eval_sec phi ctx Skip ctx
  | EvalSecAssign : forall ctx x e a level,
      interp_arith e (sec_val_of ctx) = a ->
      interp_sec e (sec_of ctx) = level ->
      eval_sec phi ctx (Assign x e) ((ctx sv$+ (x, a)) s$+ (x, level))
  | EvalSecAssignCall : forall x f e1 e2 x1 x2 y body a1 a2 level1 level2 ctx ctx' a level,
      phi $? f = Some ((x1, x2), y, body) ->
      interp_arith e1 (sec_val_of ctx) = a1 ->
      interp_arith e2 (sec_val_of ctx) = a2 ->
      interp_sec e1 (sec_of ctx) = level1 ->
      interp_sec e2 (sec_of ctx) = level2 ->
      eval_sec phi (($0 $+ (x1, a1) $+ (x2, a2)), ($0 $+ (x1, level1) $+ (x2, level2)), sec_trace_of ctx) body ctx' ->
      sec_val_of ctx' $? y = Some a ->
      sec_lookup (sec_of ctx') y = level ->
      eval_sec phi ctx (AssignCall x f e1 e2) ((sec_val_of ctx $+ (x, a)), (sec_of ctx $+ (x, level)), sec_trace_of ctx')
  | EvalSecSequence : forall ctx c1 ctx1 c2 ctx2,
      eval_sec phi ctx c1 ctx1 ->
      eval_sec phi ctx1 c2 ctx2 ->
      eval_sec phi ctx (Sequence c1 c2) ctx2
  | EvalSecIfTrue : forall ctx e thn els ctx' c,
      interp_arith e (sec_val_of ctx) = c ->
      c <> 0 ->
      eval_sec phi (ctx st++ Branch true) thn ctx' ->
      eval_sec phi ctx (If e thn els) ctx'
  | EvalSecIfFalse : forall ctx e thn els ctx',
      interp_arith e (sec_val_of ctx) = 0 ->
      eval_sec phi (ctx st++ Branch false) els ctx' ->
      eval_sec phi ctx (If e thn els) ctx'
  | EvalSecWhileTrue : forall ctx e body ctx' ctx'' c,
      interp_arith e (sec_val_of ctx) = c ->
      c <> 0 ->
      eval_sec phi (ctx st++ Branch true) body ctx' ->
      eval_sec phi ctx' (While e body) ctx'' ->
      eval_sec phi ctx (While e body) ctx''
  | EvalSecWhileFalse : forall ctx e body,
      interp_arith e (sec_val_of ctx) = 0 ->
      eval_sec phi ctx (While e body) (ctx st++ Branch false).

(* The evaluation relation is deterministic: if a command can evaluate to two
different contexts, those contexts must be the same. *)

(* A small inversion helper: it looks at the command in the goal first, then
inverts the matching evaluation hypothesis.  That makes the proof script read
like a case split on the command, not like a search through generated names. *)

Theorem eval_sec_deterministic : forall phi c ctx ctx1 ctx2,
  eval_sec phi ctx c ctx1 ->
  eval_sec phi ctx c ctx2 ->
  ctx1 = ctx2.
Proof.
  Ltac invert_eval_sec :=
    match goal with
    | H : eval_sec _ _ _ _ |- _ => inversion H; subst; clear H
    end.

  intros phi c ctx ctx1 ctx2 Heval1.
  revert ctx2.
  induction Heval1; intros ? Heval2.
  - (* Skip *)
    invert_eval_sec. auto.
  - (* Assign *)
    invert_eval_sec. auto.
  - (* AssignCall *)
    invert_eval_sec.
    rewrite H in H10. inversion H10. subst.
    apply IHHeval1 in H17. subst.
    rewrite H4 in H18. inversion H18. subst. auto.
  - (* Sequence *)
    invert_eval_sec.
    apply IHHeval1_1 in H2. subst.
    apply IHHeval1_2 in H4. auto.
  - (* IfTrue *)
    invert_eval_sec.
    + apply IHHeval1 in H8. assumption.
    + lia.
  - (* IfFalse *)
    invert_eval_sec.
    + lia.
    + apply IHHeval1 in H6. assumption.
  - (* WhileTrue *)
    invert_eval_sec.
    + apply IHHeval1_1 in H6. subst.
      apply IHHeval1_2 in H8. assumption.
    + lia.
  - (* WhileFalse *)
    invert_eval_sec.
    + lia.
    + reflexivity.
Qed.

(* Constant-time semantics.

   Unlike [eval] and [eval_sec], this relation does not execute a command to a
   final valuation.  Instead, it checks whether the command is well-labeled with
   respect to constant-time discipline, threading only a security environment.

   The structural rules [CtSkip] and [CtSequence] mirror the corresponding rules
   in the evaluation relations, but over [sec_env] instead of execution contexts.

   [CtAssign] updates the assigned variable with the label computed by
   [interp_sec], recording how information may flow through the assignment.

   [CtAssignCall] mirrors function-call structure, but initializes the callee
   with the argument labels rather than argument values, checks the callee body
   under those labels, and propagates the return variable's label back to the
   caller via [sec_lookup body_se y].

   The new constant-time condition appears in [CtIf]: the guard must satisfy
   [interp_sec e se = Public], ensuring that branching does not depend on secret
   data.  Both branches are checked, and their resulting environments are joined
   with [join_sec_env].

   [CtWhile] similarly requires the loop guard to be public, but also adds the
   invariant premise [join_sec_env se se_inv = se_inv].  This ensures that the
   loop body is checked in a security environment stable enough to soundly model
   any number of iterations.
 *)

Inductive ct_cmd (phi : function_env) : sec_env -> cmd -> sec_env -> Prop :=
  | CtSkip : forall se,
      ct_cmd phi se Skip se
  | CtAssign : forall se x e level,
      interp_sec e se = level ->
      ct_cmd phi se (Assign x e) (se $+ (x, level))
  | CtAssignCall : forall se x f e1 e2 x1 x2 y body body_se level1 level2 level,
      phi $? f = Some ((x1, x2), y, body) ->
      interp_sec e1 se = level1 ->
      interp_sec e2 se = level2 ->
      ct_cmd phi
        ($0 $+ (x1, level1) $+ (x2, level2))
        body
        body_se ->
      sec_lookup body_se y = level ->
      ct_cmd phi se (AssignCall x f e1 e2) (se $+ (x, level))
  | CtSequence : forall se c1 se1 c2 se2,
      ct_cmd phi se c1 se1 ->
      ct_cmd phi se1 c2 se2 ->
      ct_cmd phi se (Sequence c1 c2) se2
  | CtIf : forall se e thn els se_thn se_els se_join,
      interp_sec e se = Public ->
      ct_cmd phi se thn se_thn ->
      ct_cmd phi se els se_els ->
      join_sec_env se_thn se_els = se_join ->
      ct_cmd phi se (If e thn els) (se_join)
  | CtWhile : forall se se_inv se_body e body,
      join_sec_env se se_inv = se_inv ->
      interp_sec e se_inv = Public ->
      ct_cmd phi se_inv body se_body ->
      join_sec_env se_inv se_body = se_inv ->
      ct_cmd phi se (While e body) se_inv.
