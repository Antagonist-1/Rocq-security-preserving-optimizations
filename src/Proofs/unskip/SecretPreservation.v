Require Import Map.
Require Import Language.Main.
Require Import Language.Analysis.
Require Import Language.Optimizations.Safe.Unskip.
Require Import Proofs.unskip.UnskipHints.

From Stdlib Require Import List.
Import ListNotations.

Definition same_sec_state (sctx1 sctx2 : sec_context) : Prop :=
  sec_val_of sctx1 = sec_val_of sctx2 /\
  sec_of sctx1 = sec_of sctx2.

Ltac sync_state Hstate :=
  unfold same_sec_state in Hstate;
  destruct Hstate as [Hval Hsec];
  try rewrite Hval in *; try rewrite Hsec in *.

(* If two states have the exact same valuation and security labels, running a
command on both will result in the same valuation and security labels. *)
Lemma eval_sec_same_state : forall c sctx sctx_out sctx',
  eval_sec sctx c sctx_out ->
  same_sec_state sctx sctx' ->
  exists sctx_out',
    eval_sec sctx' c sctx_out' /\
    same_sec_state sctx_out sctx_out'.
Proof.
  intros c sctx sctx_out sctx' Heval.
  revert sctx'.
  induction Heval; intros sctx' Hstate;
  try solve [sync_state Hstate; eexists; split; eauto with unskip_db; unfold same_sec_state; auto].
   
  - (* Sequence: apply the induction hypotheses in order. *)
    destruct (IHHeval1 _ Hstate) as [sctx1' [Hstep1 Hstate1]].
    destruct (IHHeval2 _ Hstate1) as [sctx2' [Hstep2 Hstate2]].
    exists sctx2'; split; eauto with unskip_db.

  - (* IfTrue: the true branch is still taken. *)
    destruct (IHHeval (sctx' st++ Branch true) Hstate) as [sctx_out' [Hstep Hstate_out]].
    sync_state Hstate; eexists; split; eauto with unskip_db.

  - (* IfFalse: the false branch is still taken. *)
    destruct (IHHeval (sctx' st++ Branch false) Hstate) as [sctx_out' [Hstep Hstate_out]].
    sync_state Hstate; eexists; split; eauto with unskip_db.

  - (* WhileTrue: replay the body, then the recursive loop step. *)
    destruct (IHHeval1 (sctx' st++ Branch true) Hstate) as [sctx1' [Hstep1 Hstate1]].
    destruct (IHHeval2 _ Hstate1) as [sctx2' [Hstep2 Hstate2]].
    sync_state Hstate; eexists; split; eauto with unskip_db.
Qed.

Hint Resolve eval_sec_same_state : unskip_db.

Lemma opt_unskip_sec_forward : forall c sctx sctx_out sctx_opt,
  eval_sec sctx c sctx_out ->
  same_sec_state sctx sctx_opt ->
  exists sctx_opt_out,
    eval_sec sctx_opt (opt_unskip_cmd c) sctx_opt_out /\
    same_sec_state sctx_out sctx_opt_out.
Proof.
  intros c sctx sctx_out sctx_opt Heval.
  revert sctx_opt.
  induction Heval; intros sctx_opt Hstate; simpl;
  try eauto with unskip_db.
  - (* Sequence: We get the intermediate state from c1, then feed it into c2. *)
    destruct (IHHeval1 _ Hstate) as [sctx1_opt [Hstep1 Hstate1]].
    destruct (IHHeval2 _ Hstate1) as [sctx2_opt [Hstep2 Hstate2]].
    destruct (opt_unskip_cmd c1) eqn:Hc1;
    destruct (opt_unskip_cmd c2) eqn:Hc2;
    repeat match goal with
      | Hskip : eval_sec _ Skip _ |- _ => inversion Hskip; subst; clear Hskip
    end;
    eexists; split; eauto with unskip_db.

  - (* IfTrue: append branch true before calling IH *)
    destruct Hstate as [Hval Hsec].
    assert (Hbranch :
      same_sec_state (ctx st++ Branch true) (sctx_opt st++ Branch true))
      by (split; simpl; assumption).
    destruct (IHHeval _ Hbranch) as [sctx_opt_out [Hstep Hstate_out]].
    destruct (opt_unskip_cmd thn) eqn:Hthn;
    destruct (opt_unskip_cmd els) eqn:Hels.
    1: (* Both branches are skip. If instruction was removed *)
    inversion Hstep; subst; eauto with unskip_db.
    all: (* If cmd is was kept. Apply EvalSecIfTrue step *)
    (exists sctx_opt_out; split;
      [ eapply EvalSecIfTrue; [rewrite <- Hval; exact H | exact H0 | exact Hstep]
      | exact Hstate_out ]).

  - (* IfFalse: append branch false before calling IH *)
    destruct Hstate as [Hval Hsec].
    assert (Hbranch :
      same_sec_state (ctx st++ Branch false) (sctx_opt st++ Branch false))
      by (split; simpl; assumption).
    destruct (IHHeval _ Hbranch) as [sctx_opt_out [Hstep Hstate_out]].
    destruct (opt_unskip_cmd thn) eqn:Hthn;
    destruct (opt_unskip_cmd els) eqn:Hels.
    1: (* Both branches are skip. If instruction was removed *)
    inversion Hstep; subst; eauto with unskip_db.
    all: (* If cmd is was kept. Apply EvalSecIfFalse step *)
    (exists sctx_opt_out; split;
      [ eapply EvalSecIfFalse; [rewrite <- Hval; exact H | exact Hstep]
      | exact Hstate_out ]).

    - (* WhileTrue: append branch true before calling IH *)
    destruct Hstate as [Hval Hsec].
    assert (Hbranch :
      same_sec_state (ctx st++ Branch true) (sctx_opt st++ Branch true))
      by (split; simpl; assumption).
    destruct (IHHeval1 _ Hbranch) as [sctx1_opt [Hstep1 Hstate1]].
    destruct (IHHeval2 _ Hstate1) as [sctx2_opt [Hstep2 Hstate2]].
    exists sctx2_opt. split.
    + eapply EvalSecWhileTrue; [rewrite <- Hval; exact H | exact H0 | exact Hstep1 | exact Hstep2].
    + exact Hstate2.
Qed.

(* Main theorem of secret preservation *)
(* [opt_keeps_secrets_secret] proves the secret preservation half of
   [is_safe_opt]. [opt_unskip_sec_forward] simulates optimized executions from
   source executions, and the determinism of eval_sec ensures that the optimized
   execution must have the same final state as the source execution *)

Lemma opt_unskip_keeps_secrets_secret :
  opt_keeps_secrets_secret opt_unskip.
Proof.
  unfold opt_keeps_secrets_secret, opt_unskip.
  intros sctx sctx' sctx'' [c out] [c' out'] Hopt Hsrc Hopt_eval x.
  simpl in *.
  inversion Hopt; subst; clear Hopt.
  (* Forward simulation gives us optimized output state *)
  destruct (opt_unskip_sec_forward c sctx sctx' sctx Hsrc (conj eq_refl eq_refl)) 
    as [sctx_opt [Hopt_from_src Hstate_out]].
  (* By determinism of eval_sec, the optimized output state must be the same as
     the one from the optimization *)
  assert (Hsame : sctx'' = sctx_opt) by (eapply eval_sec_deterministic; eauto). subst.
  destruct Hstate_out as [Hval Hsec].
  split.
  - rewrite Hsec. reflexivity.
  - unfold agree_on_secret.
    intros y Hsecret.
    rewrite Hval. reflexivity.
Qed.
