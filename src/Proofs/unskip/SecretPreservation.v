Require Import Map.
Require Import Language.Main.
Require Import Language.Analysis.
Require Import Language.Optimizations.Safe.Unskip.
From Stdlib Require Import List.
Import ListNotations.


Create HintDb unskip_db.
Hint Constructors eval eval_trace eval_sec : unskip_db.

Definition same_sec_state (sctx1 sctx2 : sec_context) : Prop :=
  sec_val_of sctx1 = sec_val_of sctx2 /\
  sec_of sctx1 = sec_of sctx2.

Lemma eval_sec_same_state : forall c sctx sctx_out sctx',
  eval_sec sctx c sctx_out ->
  same_sec_state sctx sctx' ->
  exists sctx_out',
    eval_sec sctx' c sctx_out' /\
    same_sec_state sctx_out sctx_out'.
Proof.
  intros c sctx sctx_out sctx' Heval.
  revert sctx'.
  induction Heval; intros sctx' [Hval Hsec].
  - exists sctx'. split; [constructor | split; assumption].
  - exists ((sctx' sv$+ (x, a)) s$+ (x, level)). split.
    + eapply EvalSecAssign; [rewrite <- Hval | rewrite <- Hsec]; eassumption.
    + unfold same_sec_state. simpl. split.
      * rewrite Hval. reflexivity.
      * rewrite Hsec. reflexivity.
  - exists ((sctx' sv$+ (x, a1)) s$+ (x, level)). split.
    + eapply EvalSecCmovTrue.
      * rewrite <- Hval. exact H.
      * exact H0.
      * rewrite <- Hval. exact H1.
      * rewrite <- Hval. exact H2.
      * rewrite <- Hsec. exact H3.
    + unfold same_sec_state. simpl. split.
      * rewrite Hval. reflexivity.
      * rewrite Hsec. reflexivity.
  - exists ((sctx' sv$+ (x, a2)) s$+ (x, level)). split.
    + eapply EvalSecCmovFalse.
      * rewrite <- Hval. exact H.
      * rewrite <- Hval. exact H0.
      * rewrite <- Hval. exact H1.
      * rewrite <- Hsec. exact H2.
    + unfold same_sec_state. simpl. split.
      * rewrite Hval. reflexivity.
      * rewrite Hsec. reflexivity.
  - destruct (IHHeval1 _ (conj Hval Hsec))
      as [sctx1' [Hstep1 Hstate1]].
    destruct (IHHeval2 _ Hstate1) as [sctx2' [Hstep2 Hstate2]].
    exists sctx2'. split; [eapply EvalSecSequence; eauto | exact Hstate2].
  - assert (Hbranch :
      same_sec_state (ctx st++ Branch true) (sctx' st++ Branch true))
      by (split; simpl; assumption).
    destruct (IHHeval _ Hbranch) as [sctx_out' [Hstep Hstate_out]].
    exists sctx_out'. split.
    + eapply EvalSecIfTrue; [rewrite <- Hval; exact H | exact H0 | exact Hstep].
    + exact Hstate_out.
  - assert (Hbranch :
      same_sec_state (ctx st++ Branch false) (sctx' st++ Branch false))
      by (split; simpl; assumption).
    destruct (IHHeval _ Hbranch) as [sctx_out' [Hstep Hstate_out]].
    exists sctx_out'. split.
    + eapply EvalSecIfFalse; [rewrite <- Hval; exact H | exact Hstep].
    + exact Hstate_out.
  - assert (Hbranch :
      same_sec_state (ctx st++ Branch true) (sctx' st++ Branch true))
      by (split; simpl; assumption).
    destruct (IHHeval1 _ Hbranch) as [sctx1' [Hstep1 Hstate1]].
    destruct (IHHeval2 _ Hstate1) as [sctx2' [Hstep2 Hstate2]].
    exists sctx2'. split.
    + eapply EvalSecWhileTrue; [rewrite <- Hval; exact H | exact H0 | exact Hstep1 | exact Hstep2].
    + exact Hstate2.
  - exists (sctx' st++ Branch false). split.
    + eapply EvalSecWhileFalse. rewrite <- Hval. exact H.
    + unfold same_sec_state. simpl. split; assumption.
Qed.

Lemma opt_unskip_sec_forward : forall c sctx sctx_out sctx_opt,
  eval_sec sctx c sctx_out ->
  same_sec_state sctx sctx_opt ->
  exists sctx_opt_out,
    eval_sec sctx_opt (opt_unskip_cmd c) sctx_opt_out /\
    same_sec_state sctx_out sctx_opt_out.
Proof.
  intros c sctx sctx_out sctx_opt Heval.
  revert sctx_opt.
  induction Heval; intros sctx_opt Hstate; simpl.
  - eapply eval_sec_same_state; [constructor | exact Hstate].
  - eapply eval_sec_same_state; [eapply EvalSecAssign; eauto | exact Hstate].
  - eapply eval_sec_same_state; [eapply EvalSecCmovTrue; eauto | exact Hstate].
  - eapply eval_sec_same_state; [eapply EvalSecCmovFalse; eauto | exact Hstate].
  - destruct (IHHeval1 _ Hstate) as [sctx1_opt [Hstep1 Hstate1]].
    destruct (IHHeval2 _ Hstate1) as [sctx2_opt [Hstep2 Hstate2]].
    destruct (opt_unskip_cmd c1) eqn:Hc1;
    destruct (opt_unskip_cmd c2) eqn:Hc2;
    repeat match goal with
      | Hskip : eval_sec _ Skip _ |- _ => inversion Hskip; subst; clear Hskip
    end;
    eexists; split; eauto with unskip_db.
  - destruct Hstate as [Hval Hsec].
    assert (Hbranch :
      same_sec_state (ctx st++ Branch true) (sctx_opt st++ Branch true))
      by (split; simpl; assumption).
    destruct (IHHeval _ Hbranch) as [sctx_opt_out [Hstep Hstate_out]].
    destruct (opt_unskip_cmd thn) eqn:Hthn;
    destruct (opt_unskip_cmd els) eqn:Hels.
    1: {
      inversion Hstep; subst; clear Hstep.
      exists sctx_opt. split; [constructor |].
      unfold same_sec_state in *. simpl in *. exact Hstate_out.
    }
    all: (exists sctx_opt_out; split;
      [ eapply EvalSecIfTrue; [rewrite <- Hval; exact H | exact H0 | exact Hstep]
      | exact Hstate_out ]).
  - destruct Hstate as [Hval Hsec].
    assert (Hbranch :
      same_sec_state (ctx st++ Branch false) (sctx_opt st++ Branch false))
      by (split; simpl; assumption).
    destruct (IHHeval _ Hbranch) as [sctx_opt_out [Hstep Hstate_out]].
    destruct (opt_unskip_cmd thn) eqn:Hthn;
    destruct (opt_unskip_cmd els) eqn:Hels.
    1: {
      inversion Hstep; subst; clear Hstep.
      exists sctx_opt. split; [constructor |].
      unfold same_sec_state in *. simpl in *. exact Hstate_out.
    }
    all: (exists sctx_opt_out; split;
      [ eapply EvalSecIfFalse; [rewrite <- Hval; exact H | exact Hstep]
      | exact Hstate_out ]).
  - destruct Hstate as [Hval Hsec].
    assert (Hbranch :
      same_sec_state (ctx st++ Branch true) (sctx_opt st++ Branch true))
      by (split; simpl; assumption).
    destruct (IHHeval1 _ Hbranch) as [sctx1_opt [Hstep1 Hstate1]].
    destruct (IHHeval2 _ Hstate1) as [sctx2_opt [Hstep2 Hstate2]].
    exists sctx2_opt. split.
    + eapply EvalSecWhileTrue; [rewrite <- Hval; exact H | exact H0 | exact Hstep1 | exact Hstep2].
    + exact Hstate2.
  - destruct Hstate as [Hval Hsec].
    exists (sctx_opt st++ Branch false). split.
    + eapply EvalSecWhileFalse. rewrite <- Hval. exact H.
    + unfold same_sec_state. simpl. split; assumption.
Qed.

Lemma opt_unskip_keeps_secrets_secret :
  opt_keeps_secrets_secret opt_unskip.
Proof.
  unfold opt_keeps_secrets_secret, opt_unskip.
  intros sctx sctx' sctx'' [c out] [c' out'] Hopt Hsrc Hopt_eval x.
  simpl in Hopt.
  inversion Hopt; subst; clear Hopt.
  simpl in Hopt_eval.
  destruct (opt_unskip_sec_forward c sctx sctx' sctx
    Hsrc (conj eq_refl eq_refl))
    as [sctx_opt [Hopt_from_src Hstate_out]].
  assert (Hsame : sctx'' = sctx_opt)
    by (eapply eval_sec_deterministic; eauto).
  subst sctx_opt.
  destruct Hstate_out as [Hval Hsec].
  split.
  - rewrite Hsec. reflexivity.
  - unfold agree_on_secret.
    intros y Hsecret.
    rewrite Hval. reflexivity.
Qed.
