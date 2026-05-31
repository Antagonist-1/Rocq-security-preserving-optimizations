Require Import Map.
Require Import VarSets.
Require Import Language.Syntax.
Require Import Language.Security.
Require Import Language.EvalContext.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

(* The core of syntax and semantics were taken from Lab 6 from the CS-428 course *)


(** ** Semantics *)
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

Fixpoint interp_arith (e: expr) (v: valuation): nat :=
  match e with
  | Const n => n
  | Var x => match v $? x with Some a => a | None => 0 end
  | Binop b e1 e2 => interp_binop b (interp_arith e1 v) (interp_arith e2 v)
  end.

(** For commands, we'll use an inductive [Prop] to define big-step semantics.
    This is an opportunity to show that compiler proofs can work with a variety
    of semantics styles, since we focused on small-step semantics in lecture.
    The rules for [Assign], [While], [If], and [Skip] are the same as usual; for
    example:

                    ⟦e⟧ᵥ = a
      ----------------------------------- EvalTraceAssign
       (v, Assign x e) ↓ (v $+ (x, a))

       (c1, v) ↓ v'   (c2, v') ↓ v''
      ----------------------------------- EvalTraceSequence
          (v, Sequence c1 c2) ↓ v''

   Here is how it looks in Rocq: *)

   (* We also add rules [EvalCmovTrue] and [EvalCmovFalse] for conditional moves:

               ⟦cond⟧ᵥ = c    c <> 0
               ⟦e1⟧ᵥ = a1    ⟦e2⟧ᵥ = a2
       ----------------------------------------- EvalCmovTrue
        (v, Cmov x cond e1 e2) ↓ᵩ (v $+ (x, a1))

                  ⟦cond⟧ᵥ = 0
               ⟦e1⟧ᵥ = a1    ⟦e2⟧ᵥ = a2
       ----------------------------------------- EvalCmovFalse
        (v, Cmov x cond e1 e2) ↓ᵩ (v $+ (x, a2))
   *)



Inductive eval: valuation -> cmd -> valuation -> Prop :=
  | EvalSkip: forall v,
      eval v Skip v
  | EvalAssign: forall v x e a,
      interp_arith e v = a ->
      eval v (Assign x e) (v $+ (x, a))
  | EvalCmovTrue: forall v x cond e1 e2 c a1 a2,
      interp_arith cond v = c ->
      c <> 0 ->
      interp_arith e1 v = a1 ->
      interp_arith e2 v = a2 ->
      eval v (Cmov x cond e1 e2) (v $+ (x, a1))
  | EvalCmovFalse: forall v x cond e1 e2 a1 a2,
      interp_arith cond v = 0 ->
      interp_arith e1 v = a1 ->
      interp_arith e2 v = a2 ->
      eval v (Cmov x cond e1 e2) (v $+ (x, a2))
  | EvalSequence: forall v c1 v1 c2 v2,
      eval v c1 v1 ->
      eval v1 c2 v2 ->
      eval v (Sequence c1 c2) v2
  | EvalIfTrue: forall v e thn els v' c,
      interp_arith e v = c ->
      c <> 0 ->
      eval v thn v' ->
      eval v (If e thn els) v'
  | EvalIfFalse: forall v e thn els v',
      interp_arith e v = 0 ->
      eval v els v' ->
      eval v (If e thn els) v'
  | EvalWhileTrue: forall v e body v' v'' c,
      interp_arith e v = c ->
      c <> 0 ->
      eval v body v' ->
      eval v' (While e body) v'' ->
      eval v (While e body) v''
  | EvalWhileFalse: forall v e body,
      interp_arith e v = 0 ->
      eval v (While e body) v.


Theorem eval_deterministic :
    forall c v0 v1 v2,
      eval v0 c v1 ->
      eval v0 c v2 ->
      v1 = v2.
  Proof.
    intros c v0 v1 v2 H.
    revert v2.
    induction H; simpl; intros.
    - inversion H. reflexivity.
    - inversion H0; subst;
    reflexivity.
    - inversion H3; subst; try reflexivity; congruence.
    - inversion H2; subst; try reflexivity; congruence.
    - inversion H1; subst.
      apply IHeval1 in H5.
      subst.
      firstorder.
    - inversion H2; subst; firstorder.
    - inversion H1; subst; firstorder.
    - inversion H3; subst.
      + apply IHeval1 in H9.
        subst.
        apply IHeval2 in H11.
        assumption.
      + congruence.
    - inversion H0; subst; firstorder.
Qed.


(* 
eval_trace builds the same tree as eval, but carries extra interpretation information: the trace
The trace is useful for security purposes. We write down each of the branch the program chose. 
The trace could later be generalized to carry other information, such as memory accesses.
*)

Inductive eval_trace: context -> cmd -> context -> Prop :=
  | EvalTraceSkip: forall ctx,
      eval_trace ctx Skip ctx
  | EvalTraceAssign: forall ctx x e a,
      interp_arith e (val_of ctx) = a ->
      eval_trace ctx (Assign x e) (ctx v$+ (x, a))
  | EvalTraceCmovTrue: forall ctx x cond e1 e2 c a1 a2,
      interp_arith cond (val_of ctx) = c ->
      c <> 0 ->
      interp_arith e1 (val_of ctx) = a1 ->
      interp_arith e2 (val_of ctx) = a2 ->
      eval_trace ctx (Cmov x cond e1 e2) (ctx v$+ (x, a1))
  | EvalTraceCmovFalse: forall ctx x cond e1 e2 a1 a2,
      interp_arith cond (val_of ctx) = 0 ->
      interp_arith e1 (val_of ctx) = a1 ->
      interp_arith e2 (val_of ctx) = a2 ->
      eval_trace ctx (Cmov x cond e1 e2) (ctx v$+ (x, a2))
  | EvalTraceSequence: forall ctx c1 ctx1 c2 ctx2,
      eval_trace ctx c1 ctx1 ->
      eval_trace ctx1 c2 ctx2 ->
      eval_trace ctx (Sequence c1 c2) ctx2
  | EvalTraceIfTrue: forall ctx e thn els ctx' c,
      interp_arith e (val_of ctx) = c ->
      c <> 0 ->
      eval_trace (ctx t++ Branch true) thn ctx' ->
      eval_trace ctx (If e thn els) ctx'
  | EvalTraceIfFalse: forall ctx e thn els ctx',
      interp_arith e (val_of ctx) = 0 ->
      eval_trace (ctx t++ Branch false) els ctx' ->
      eval_trace ctx (If e thn els) ctx'
  | EvalTraceWhileTrue: forall ctx e body ctx' ctx'' c,
      interp_arith e (val_of ctx) = c ->
      c <> 0 ->
      eval_trace (ctx t++ Branch true) body ctx' ->
      eval_trace ctx' (While e body) ctx'' ->
      eval_trace ctx (While e body) ctx''
  | EvalTraceWhileFalse: forall ctx e body,
      interp_arith e (val_of ctx) = 0 ->
      eval_trace ctx (While e body) (ctx t++ Branch false).


(* The evaluation relation is deterministic: if a command can evaluate to two
different contexts, those contexts must be the same. *)
Theorem eval_trace_deterministic : forall c ctx ctx1 ctx2,
  eval_trace ctx c ctx1 ->
  eval_trace ctx c ctx2 ->
  ctx1 = ctx2.
Proof.
    Ltac invert_eval :=
    match goal with
    | H : eval_trace _ _ _ |- _ => inversion H; subst; clear H
    end.

  intros c ctx ctx1 ctx2 Heval1.
  revert ctx2.
  induction Heval1; intros ? Heval2.
  - (* Skip *)
    invert_eval. auto.
  - (* Assign *)
    invert_eval. auto.
  - (* CmovTrue *)
    invert_eval.
    + auto.
    + lia.
  - (* CmovFalse *)
    invert_eval.
    + lia.
    + auto.
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
   Some things were changed about the original eval to allow only secure programs to execute:

  [EvalSecAssign] adds the associated security level (derived from the assignee) in the sec_env
 *)


Inductive eval_sec : sec_context -> cmd -> sec_context -> Prop :=
  | EvalSecSkip : forall ctx,
      eval_sec ctx Skip ctx
  | EvalSecAssign : forall ctx x e a level ,
      interp_arith e (sec_val_of ctx) = a ->
      interp_sec e (sec_of ctx) = level ->
      eval_sec ctx (Assign x e) ((ctx sv$+ (x, a)) s$+ (x, level))
  | EvalSecCmovTrue : forall ctx x cond e1 e2 c a1 a2 level,
      interp_arith cond (sec_val_of ctx) = c ->
      c <> 0 ->
      interp_arith e1 (sec_val_of ctx) = a1 ->
      interp_arith e2 (sec_val_of ctx) = a2 ->
      join_sec (interp_sec cond (sec_of ctx)) (join_sec (interp_sec e1 (sec_of ctx)) (interp_sec e2 (sec_of ctx))) = level ->
      eval_sec ctx (Cmov x cond e1 e2) ((ctx sv$+ (x, a1)) s$+ (x, level))
  | EvalSecCmovFalse : forall ctx x cond e1 e2 a1 a2 level,
      interp_arith cond (sec_val_of ctx) = 0 ->
      interp_arith e1 (sec_val_of ctx) = a1 ->
      interp_arith e2 (sec_val_of ctx) = a2 ->
      join_sec (interp_sec cond (sec_of ctx)) (join_sec (interp_sec e1 (sec_of ctx)) (interp_sec e2 (sec_of ctx))) = level ->
      eval_sec ctx (Cmov x cond e1 e2) ((ctx sv$+ (x, a2)) s$+ (x, level))
  | EvalSecSequence : forall ctx c1 ctx1 c2 ctx2,
      eval_sec ctx c1 ctx1 ->
      eval_sec ctx1 c2 ctx2 ->
      eval_sec ctx (Sequence c1 c2) ctx2
  | EvalSecIfTrue : forall ctx e thn els ctx' c,
      interp_arith e (sec_val_of ctx) = c ->
      c <> 0 ->
      eval_sec (ctx st++ Branch true) thn ctx' ->
      eval_sec ctx (If e thn els) ctx'
  | EvalSecIfFalse : forall ctx e thn els ctx',
      interp_arith e (sec_val_of ctx) = 0 ->
      eval_sec (ctx st++ Branch false) els ctx' ->
      eval_sec ctx (If e thn els) ctx'
  | EvalSecWhileTrue : forall ctx e body ctx' ctx'' c,
      interp_arith e (sec_val_of ctx) = c ->
      c <> 0 ->
      eval_sec (ctx st++ Branch true) body ctx' ->
      eval_sec ctx' (While e body) ctx'' ->
      eval_sec ctx (While e body) ctx''
  | EvalSecWhileFalse : forall ctx e body,
      interp_arith e (sec_val_of ctx) = 0 ->
      eval_sec ctx (While e body) (ctx st++ Branch false).

(* The evaluation relation is deterministic: if a command can evaluate to two
different contexts, those contexts must be the same. *)

(* A small inversion helper: it looks at the command in the goal first, then
inverts the matching evaluation hypothesis.  That makes the proof script read
like a case split on the command, not like a search through generated names. *)

Theorem eval_sec_deterministic : forall c ctx ctx1 ctx2,
  eval_sec ctx c ctx1 ->
  eval_sec ctx c ctx2 ->
  ctx1 = ctx2.
Proof.
  Ltac invert_eval_sec :=
    match goal with
    | H : eval_sec _ _ _ |- _ => inversion H; subst; clear H
    end.

  intros c ctx ctx1 ctx2 Heval1.
  revert ctx2.
  induction Heval1; intros ? Heval2.
  - (* Skip *)
    invert_eval_sec. auto.
  - (* Assign *)
    invert_eval_sec. auto.
  - (* CmovTrue *)
    invert_eval_sec.
    + auto.
    + lia.
  - (* CmovFalse *)
    invert_eval_sec.
    + lia.
    + auto.
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

Lemma eval_trace_prefix : forall c ctx ctx_final,
  eval_trace ctx c ctx_final ->
  exists t, trace_of ctx_final = trace_of ctx ++ t.
Proof.
  intros c ctx ctx_final H.
  induction H; simpl.
  - exists nil. rewrite app_nil_r. reflexivity.
  - exists nil. rewrite app_nil_r. reflexivity.
  - exists nil. rewrite app_nil_r. reflexivity.
  - exists nil. rewrite app_nil_r. reflexivity.
  - destruct IHeval_trace1 as [t1 Ht1]. destruct IHeval_trace2 as [t2 Ht2].
    exists (t1 ++ t2). rewrite Ht2, Ht1. rewrite app_assoc. reflexivity.
  - destruct IHeval_trace as [t Ht]. exists (Branch true :: t).
    rewrite Ht. simpl. rewrite <- app_assoc. reflexivity.
  - destruct IHeval_trace as [t Ht]. exists (Branch false :: t).
    rewrite Ht. simpl. rewrite <- app_assoc. reflexivity.
  - destruct IHeval_trace1 as [t1 Ht1]. destruct IHeval_trace2 as [t2 Ht2].
    exists (Branch true :: t1 ++ t2). rewrite Ht2, Ht1. simpl.
    do 2 rewrite <- app_assoc. reflexivity.
  - exists [Branch false]. reflexivity.
Qed.

Lemma branch_contradiction : forall A (t_in: list A) t1 t2 b1 b2,
  t_in ++ b1 :: t1 = t_in ++ b2 :: t2 ->
  b1 = b2.
Proof.
  intros A t_in t1 t2 b1 b2 H.
  apply app_inv_head in H. inversion H. reflexivity.
Qed.

Definition is_prefix {A} (t1 T : list A) := exists tail, T = t1 ++ tail.

Lemma prefix_trans : forall A (t1 t2 T : list A),
  is_prefix t1 t2 -> is_prefix t2 T -> is_prefix t1 T.
Proof.
  intros A t1 t2 T [tail1 H1] [tail2 H2].
  exists (tail1 ++ tail2). subst. rewrite app_assoc. reflexivity.
Qed.

Lemma eval_trace_is_prefix : forall c ctx ctx_final,
  eval_trace ctx c ctx_final ->
  is_prefix (trace_of ctx) (trace_of ctx_final).
Proof.
  intros c ctx ctx_final H.
  destruct (eval_trace_prefix _ _ _ H) as [t Ht].
  exists t. exact Ht.
Qed.
