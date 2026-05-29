Require Import Map.
Require Import VarSets.
Require Import Language.Main.
Require Import Proofs.SecLookup.
From Stdlib Require Import Program.Equality.


(* If two valuations agree on public data, then the interpretation of any public
expression should be the same. *)
Lemma interp_sec_public_agree : forall e se v1 v2,
  agree_on_public se v1 v2 ->
  interp_sec e se = Public ->
  interp_arith e v1 = interp_arith e v2.
Proof.
  induction e; cbn in *;
  intros se v1 v2 Hagree Hsec.
  - (* const *)
    reflexivity.
  - (* var *)
    apply pub_not_sec in Hsec.
    specialize (Hagree s Hsec).
    rewrite Hagree. reflexivity.
  - (* binop *)
    unfold agree_on_public in Hagree.
    destruct (interp_sec e1 se) eqn:Hsec1;
    destruct (interp_sec e2 se) eqn:Hsec2;
    simpl in Hsec; try discriminate.
    rewrite (IHe1 se v1 v2 Hagree Hsec1).
    rewrite (IHe2 se v1 v2 Hagree Hsec2).
    reflexivity.
Qed.

(* Declare two helper lemmas to reason about loop invariants *)

(* If two valuations agree on public before executing an iteration of a
loop, then they agree on the loop invariant environment (se_inv) *)
Lemma agree_on_public_inv : forall se se_inv v1 v2,
  VarSet.Equal (join_sec_env se se_inv) se_inv ->
  agree_on_public se v1 v2 ->
  agree_on_public se_inv v1 v2.
Proof.
  intros se se_inv v1 v2 Hjoin Hagree.
  unfold agree_on_public in *. intros x Hpub.
  apply Hagree.
  apply pub_not_sec.
  apply join_sec_public_thn with se_inv.
  unfold sec_lookup.
  rewrite Hjoin. 
  apply pub_not_sec.
  exact Hpub.
Qed.

(* If two valuations agree on the output of the body of a loop, then they
agree on the loop invariant environment (se_inv) *)
Lemma agree_on_public_body_inv : forall se_inv se_body v1 v2,
  VarSet.Equal (join_sec_env se_inv se_body) se_inv ->
  agree_on_public se_body v1 v2 ->
  agree_on_public se_inv v1 v2.
Proof.
  intros se_inv se_body v1 v2 Hjoin Hagree.
  unfold agree_on_public in *. intros x Hpub.
  apply Hagree.
  apply pub_not_sec.
  apply join_sec_public_els with se_inv.
  unfold sec_lookup.
  rewrite Hjoin. 
  apply pub_not_sec in Hpub.
  exact Hpub.
Qed.

Lemma cmov_non_inference : forall se x cond e1 e2 level,
  join_sec (interp_sec cond se) (join_sec (interp_sec e1 se) (interp_sec e2 se)) = level ->
  non_inference se (Cmov x cond e1 e2) (update_sec se x level).
Proof.
  unfold non_inference.
  Ltac resolve_cmov_maps :=
    unfold agree_on_public, sec_lookup in *; intros param Hparam;
    autorewrite with core in *; cbn in *.
  intros se x cond e1 e2 level Hjoin
    v1 v2 t_in final_v1 final_v2 trace1 trace2 Hagree Heval1 Heval2.
  split.
  { inversion Heval1; inversion Heval2; subst; reflexivity. }
  inversion Heval1; inversion Heval2; subst; resolve_cmov_maps.
  all: destruct (param ==v x);
  [ subst; destruct (x ==v x); [ | congruence ];
    autorewrite with core in *;
    destruct (interp_sec cond se) eqn:Hcond_sec;
    destruct (interp_sec e1 se) eqn:He1_sec;
    destruct (interp_sec e2 se) eqn:He2_sec;
    cbn in Hparam; try VarSetDecide.fsetdec;
    try (apply f_equal; eapply interp_sec_public_agree; eauto);
    try (assert (Hcond_val: interp_arith cond v1 = interp_arith cond v2) by (eapply interp_sec_public_agree; eauto); congruence)
  | destruct (x ==v param); [ congruence | ];
    autorewrite with core in *; apply Hagree;
    rewrite <- VarSet.mem_spec in *; rewrite simplify_update_ne in Hparam; auto ].
Qed.


(* A program that is constant time according to our definition should satisfy
non-inference. *)
Theorem ct_cmd_soundness : forall se c se_out,
  ct_cmd se c se_out ->
  non_inference se c se_out.
Proof.
  Ltac invert_evals :=
    inversion Heval1; inversion Heval2; subst.

  Ltac resolve_maps :=
    unfold agree_on_public, sec_lookup in *; intros param Hparam;
    autorewrite with core in *; cbn in *.


  intros se c se_out Hct.
  unfold non_inference.
  induction Hct;
  intros v1 v2 t_in final_v1 final_v2 trace1 trace2 Hagree Heval1 Heval2.
  - (* Skip *)
    split; invert_evals; [reflexivity | assumption].
  - (* Assign *)
    split; invert_evals; [reflexivity |].
      resolve_maps. destruct (param ==v x).
      + subst. destruct (x ==v x); [ | congruence ].
        autorewrite with core in *. apply f_equal.
        apply pub_not_sec in Hparam.

        eapply interp_sec_public_agree; eauto.
        destruct (interp_sec e se).
        * reflexivity.
        * simpl in Hparam.
          unfold sec_lookup in Hparam.
          rewrite VarSetEqProps.add_mem_1 in Hparam.
          discriminate.

      + destruct (x ==v param); [ congruence | ].
        autorewrite with core in *. apply Hagree.
        destruct (interp_sec e se) eqn:Hinterp_e; simpl in Hparam.
        * rewrite VarSet.remove_spec in Hparam.
          auto.
        * rewrite VarSet.add_spec in Hparam.
          auto.
  - (* Cmov *)
    eapply cmov_non_inference; eauto.
  - (* Sequence *)
    (* Pipeline safety properties directly from c1 into c2. *)
    invert_evals. destruct ctx1 as [v1' t1'], ctx3 as [v2' t2'].
    edestruct IHHct1 as [Htrace1 Hmem1]; eauto; subst.
    eapply IHHct2; eauto.
  - (* If *)
    assert (Hcond: interp_arith e v1 = interp_arith e v2).
    { eapply interp_sec_public_agree; eauto. }
    invert_evals.
    + (* Case 1: True / True *)
      edestruct IHHct1 as [Htrace Hmem]; eauto.
      split; [exact Htrace |].
      unfold agree_on_public in *. intros x Hpub.
      apply Hmem. (* This Hmem comes from IHHct2, so it uses se_els *)
      apply pub_not_sec. apply pub_not_sec in Hpub.
      eapply join_sec_public_thn. 
      unfold sec_lookup.
      rewrite H0.
      apply Hpub.
    + (* Case 2: True / False (IMPOSSIBLE) *)
      cbn in *.
      rewrite H14 in Hcond.
      congruence.
    + (* Case 3: False / True (IMPOSSIBLE) *)
      cbn in *.
      rewrite H6 in Hcond.
      congruence.
    + (* Case 4: False / False *)
      edestruct IHHct2 as [Htrace Hmem]; eauto.
      split; [exact Htrace |].
      (* Memory safety for the joined environment *)
      unfold agree_on_public in *. intros x Hpub.
      apply Hmem.
      apply pub_not_sec. apply pub_not_sec in Hpub.
      eapply join_sec_public_els. 
      unfold sec_lookup.
      rewrite H0.
      apply Hpub.
  - (* While *)
    (* The initial valuations agree on the loop invariant environment *)
    assert (Hagree_inv: agree_on_public se_inv v1 v2).
    { eapply agree_on_public_inv; eauto. }
    clear Hagree.

    revert v2 final_v2 trace2 Hagree_inv Heval2.
    dependent induction Heval1.

    + (* EvalTraceWhileTrue *)
      intros v2 final_v2 trace2 Hagree_inv Heval2.
      inversion Heval2; subst; clear Heval2.
      * (* Case 1: Both take True branch *)
        cbn in *.
        destruct ctx' as [v1' t1'].
        match goal with
        | H : eval_trace _ body ?ctx2' |- _ => destruct ctx2' as [v2' t2']
        end.

        edestruct IHHct as [Htrace_body Hmem_body]; eauto.
        subst t2'.

        assert (Hagree_inv_after: agree_on_public se_inv v1' v2').
        { eapply agree_on_public_body_inv; eauto. }
        eauto.

      * (* Case 2: Contradiction - v1 True, v2 False *)
        cbn in *.
        (* inversion unified v2 with final_v2 because EvalTraceWhileFalse doesn't change the valuation *)
        assert (Hcond: interp_arith e v1 = interp_arith e final_v2).
        {eapply interp_sec_public_agree; eauto. }
        congruence.

    + (* EvalTraceWhileFalse *)
      intros v2 final_v2 trace2 Hagree_inv Heval2.
      inversion Heval2; subst; clear Heval2.
      * (* Case 3: Contradiction - v1 False, v2 True *)
        cbn in *.
        (* inversion unified v1 with final_v1 because EvalTraceWhileFalse doesn't change the valuation *)
        assert (Hcond: interp_arith e final_v1 = interp_arith e v2) by (eapply interp_sec_public_agree; eauto).
        congruence.

      * (* Case 4: Both take False branch and exit *)
        cbn in *.
        eauto.
Qed.

(* Two security contexts agree if they have the same values AND the same 
   dynamic security labels for all statically public variables. *)
Definition agree_on_public_sec_ctx (se_static : sec_env) (ctx1 ctx2 : sec_context) : Prop :=
  (* 1. The valuations agree on public variables *)
  agree_on_public se_static (sec_val_of ctx1) (sec_val_of ctx2) /\
  (* 2. The dynamic security environments agree on public variables *)
  (forall x, sec_lookup se_static x = Public -> 
             sec_lookup (sec_of ctx1) x = sec_lookup (sec_of ctx2) x).

Definition non_inference_sec (se_static: sec_env) (c: cmd) (se_static_out: sec_env) : Prop :=
  forall ctx1_in ctx2_in ctx1_out ctx2_out,
    (* If the initial contexts agree on public data and labels... *)
    agree_on_public_sec_ctx se_static ctx1_in ctx2_in ->
    (* ...and they start with identical traces... *)
    sec_trace_of ctx1_in = sec_trace_of ctx2_in ->
    (* ...and they both evaluate the command... *)
    eval_sec ctx1_in c ctx1_out ->
    eval_sec ctx2_in c ctx2_out ->
    (* ...then their output traces must be identical... *)
    sec_trace_of ctx1_out = sec_trace_of ctx2_out /\ 
    (* ...and their output contexts must still agree on public data and labels. *)
    agree_on_public_sec_ctx se_static_out ctx1_out ctx2_out.


(* --- Helper Lemmas for If --- *)

Lemma agree_on_public_sec_ctx_join_thn : forall se_thn se_els se_join ctx1 ctx2,
  VarSet.Equal (join_sec_env se_thn se_els) se_join ->
  (* If two contexts agree on public data and labels for "then" branch env... *)
  agree_on_public_sec_ctx se_thn ctx1 ctx2 ->
  (* ...then they agree on public data and labels for the joined environment. *)
  agree_on_public_sec_ctx se_join ctx1 ctx2.
Proof.
  intros se_thn se_els se_join ctx1 ctx2 Hjoin [Hval Hdyn].
  split; intros x Hpub.
  - rewrite <- pub_not_sec in Hpub.
    unfold sec_lookup in Hpub; rewrite <- Hjoin in Hpub.
    apply join_sec_public in Hpub. destruct Hpub as [Hthn Hels].
    apply Hval. rewrite <- pub_not_sec. exact Hthn.
  - unfold sec_lookup in Hpub; rewrite <- Hjoin in Hpub.
    apply join_sec_public in Hpub. destruct Hpub as [Hthn Hels].
    apply Hdyn. exact Hthn.
Qed.

Lemma agree_on_public_sec_ctx_join_els : forall se_thn se_els se_join ctx1 ctx2,
  VarSet.Equal (join_sec_env se_thn se_els) se_join ->
  (* If two contexts agree on public data and labels for "else" branch env... *)
  agree_on_public_sec_ctx se_els ctx1 ctx2 ->
  (* ...then they agree on public data and labels for the joined environment. *)
  agree_on_public_sec_ctx se_join ctx1 ctx2.
Proof.
  intros se_thn se_els se_join ctx1 ctx2 Hjoin [Hval Hdyn].
  split; intros x Hpub.
  - rewrite <- pub_not_sec in Hpub.
    unfold sec_lookup in Hpub; rewrite <- Hjoin in Hpub.
    apply join_sec_public in Hpub. destruct Hpub as [Hthn Hels].
    apply Hval. rewrite <- pub_not_sec. exact Hels.
  - unfold sec_lookup in Hpub; rewrite <- Hjoin in Hpub.
    apply join_sec_public in Hpub. destruct Hpub as [Hthn Hels].
    apply Hdyn. exact Hels.
Qed.

(* --- Helper Lemmas for While --- *)
Lemma agree_on_public_sec_ctx_inv : forall se se_inv ctx1 ctx2,
  VarSet.Equal (join_sec_env se se_inv) se_inv ->
  (* If two contexts agree on public data and labels for the original env... *)
  agree_on_public_sec_ctx se ctx1 ctx2 ->
  (* ...then they agree on public data and labels for the loop invariant env. *)
  agree_on_public_sec_ctx se_inv ctx1 ctx2.
Proof.
  intros se se_inv ctx1 ctx2 Hjoin [Hval Hdyn].
  split; intros x Hpub.
  - apply Hval. rewrite <- pub_not_sec. rewrite <- pub_not_sec in Hpub. eapply join_sec_public_thn. unfold sec_lookup. rewrite Hjoin. exact Hpub.
  - apply Hdyn. eapply join_sec_public_thn. unfold sec_lookup. rewrite Hjoin. exact Hpub.
Qed.

Lemma agree_on_public_sec_ctx_body_inv : forall se_inv se_body ctx1 ctx2,
  VarSet.Equal (join_sec_env se_inv se_body) se_inv ->
  (* If two contexts agree on public data and labels for the body env... *)
  agree_on_public_sec_ctx se_body ctx1 ctx2 ->
  (* ...then they agree on public data and labels for the loop invariant env. *)
  agree_on_public_sec_ctx se_inv ctx1 ctx2.
Proof.
  intros se_inv se_body ctx1 ctx2 Hjoin [Hval Hdyn].
  split; intros x Hpub.
  - apply Hval. rewrite <- pub_not_sec. rewrite <- pub_not_sec in Hpub. eapply join_sec_public_els. unfold sec_lookup. rewrite Hjoin. exact Hpub.
  - apply Hdyn. eapply join_sec_public_els. unfold sec_lookup. rewrite Hjoin. exact Hpub.
Qed.

Lemma while_soundness_sec : forall se_inv e body se_body,
  interp_sec e se_inv = Public ->
  ct_cmd se_inv body se_body ->
  non_inference_sec se_inv body se_body ->
  VarSet.Equal (join_sec_env se_inv se_body) se_inv ->
  non_inference_sec se_inv (While e body) se_inv.
Proof.
  intros se_inv e body se_body Hguard Hct_body Hni_body Hjoin.
  unfold non_inference_sec.
  intros ctx1_in ctx2_in ctx1_out ctx2_out Hagree_inv Htrace_in Heval1.

  revert ctx2_in ctx2_out Htrace_in Hagree_inv.
  dependent induction Heval1; intros ctx2_in ctx2_out Htrace_in Hagree_inv Heval2.

  - (* EvalSecWhileTrue *)
    inversion Heval2; subst; clear Heval2.
    + (* Case 1: Both True *)
      assert (Htrace_branched: sec_trace_of (ctx st++ Branch true) = sec_trace_of (ctx2_in st++ Branch true))
        by (cbn; rewrite Htrace_in; reflexivity).

      (* Traces don't affect valuations/labels, exact Hagree_inv works *)
      assert (Hagree_branched: agree_on_public_sec_ctx se_inv (ctx st++ Branch true) (ctx2_in st++ Branch true))
        by exact Hagree_inv.

      edestruct Hni_body as [Htrace_body Hagree_body]; eauto.

      assert (Hagree_inv_after: agree_on_public_sec_ctx se_inv ctx' ctx'0).
      { eapply agree_on_public_sec_ctx_body_inv; eauto. }

      edestruct IHHeval1_2 as [Htrace_loop Hagree_loop]; eauto.

    + (* Case 2: True / False (Contradiction) *)
      cbn in *.
      assert (Hcond: interp_arith e (sec_val_of ctx) = interp_arith e (sec_val_of ctx2_in)).
      { destruct Hagree_inv as [Hval _]. eapply interp_sec_public_agree; eauto. }
      congruence.

  - (* EvalSecWhileFalse *)
    inversion Heval2; subst; clear Heval2.
    + (* Case 3: False / True (Contradiction) *)
      cbn in *.
      assert (Hcond: interp_arith e (sec_val_of ctx) = interp_arith e (sec_val_of ctx2_in)).
      { destruct Hagree_inv as [Hval _]. eapply interp_sec_public_agree; eauto. }
      congruence.

    + (* Case 4: False / False *)
      split.
      * cbn. rewrite Htrace_in. reflexivity.
      * exact Hagree_inv.
Qed.

Lemma cmov_non_inference_sec : forall se x cond e1 e2 level,
  join_sec (interp_sec cond se) (join_sec (interp_sec e1 se) (interp_sec e2 se)) = level ->
  non_inference_sec se (Cmov x cond e1 e2) (update_sec se x level).
Proof.
  Ltac resolve_sec_update_main :=
    intros param Hparam; cbn in *.

  unfold non_inference_sec.
  intros se x cond e1 e2 level Hjoin ctx1_in ctx2_in ctx1_out ctx2_out Hagree Htrace Heval1 Heval2.
  inversion Heval1; inversion Heval2; subst;
    (split; [assumption |]);
    destruct Hagree as [Hval_agree Hdyn_agree];
    unfold agree_on_public_sec_ctx, agree_on_public in *;
    split; resolve_sec_update_main.
  all: destruct (x ==v param);
  [ subst;
    try rewrite lookup_add_eq in Hparam by reflexivity;
    repeat rewrite lookup_add_eq by reflexivity;
    try rewrite <- pub_not_sec in *;
    repeat rewrite lookup_update_sec_eq in *;
    destruct (interp_sec cond se) eqn:Hcond_sec;
    destruct (interp_sec e1 se) eqn:He1_sec;
    destruct (interp_sec e2 se) eqn:He2_sec;
    cbn in *; try discriminate;
    try match goal with
    | |- Some _ = Some _ =>
        try (apply f_equal; eapply interp_sec_public_agree; eauto);
        try (assert (Hcond_val: interp_arith cond (sec_val_of ctx1_in) = interp_arith cond (sec_val_of ctx2_in))
             by (eapply interp_sec_public_agree; eauto); congruence)
    | |- join_sec _ _ = join_sec _ _ =>
        rewrite (interp_sec_dynamic_agree cond se (sec_of ctx1_in) (sec_of ctx2_in) Hdyn_agree Hcond_sec);
        rewrite (interp_sec_dynamic_agree e1 se (sec_of ctx1_in) (sec_of ctx2_in) Hdyn_agree He1_sec);
        rewrite (interp_sec_dynamic_agree e2 se (sec_of ctx1_in) (sec_of ctx2_in) Hdyn_agree He2_sec);
        reflexivity
    end
  | try rewrite lookup_add_ne in Hparam by congruence;
    repeat rewrite lookup_add_ne by congruence;
    try rewrite <- pub_not_sec in *;
    repeat rewrite lookup_update_sec_ne in * by congruence;
    try match goal with
    | |- _ $? ?v = _ $? ?v =>
        apply Hval_agree; rewrite <- pub_not_sec; exact Hparam
    | |- sec_lookup _ ?v = sec_lookup _ ?v =>
        apply Hdyn_agree; exact Hparam
    end ].
Qed.


Theorem ct_cmd_soundness_sec : forall se c se_out,
  ct_cmd se c se_out ->
  non_inference_sec se c se_out.
Proof.
  Ltac invert_evals_sec :=
    inversion Heval1; inversion Heval2; subst.

  Ltac resolve_sec_update x :=
  intros param Hparam; cbn in *; destruct (x ==v param);
  [ subst;
    try rewrite lookup_add_eq in Hparam by reflexivity;
    repeat rewrite lookup_add_eq by reflexivity;
    try rewrite <- pub_not_sec in *;
    repeat rewrite lookup_update_sec_eq in *
  | try rewrite lookup_add_ne in Hparam by congruence;
    repeat rewrite lookup_add_ne by congruence;
    try rewrite <- pub_not_sec in *;
    repeat rewrite lookup_update_sec_ne in * by congruence
  ].

  intros se c se_out Hct.
  unfold non_inference_sec.

  induction Hct;
    intros ctx1_in ctx2_in ctx1_out ctx2_out Hagree Htrace Heval1 Heval2.

  - (* CtSkip *)
    invert_evals_sec.
    split; assumption.

  - (* CtAssign *)
    invert_evals_sec.
    split; [assumption |].

    destruct Hagree as [Hval_agree Hdyn_agree].
    unfold agree_on_public_sec_ctx, agree_on_public in *.
    split.

    + (* Prove values agree *)
      resolve_sec_update x.
      * apply f_equal. eapply interp_sec_public_agree; eauto.
      * apply Hval_agree. rewrite <- pub_not_sec. exact Hparam.
    + (* Prove dynamic labels agree *)
      resolve_sec_update x.
      * eapply interp_sec_dynamic_agree; eauto.
      * apply Hdyn_agree. exact Hparam.

  - (* CtCmov *)
    pose proof (cmov_non_inference_sec se x cond e1 e2 level H) as Hcmov.
    unfold non_inference_sec in Hcmov.
    eapply Hcmov; eauto.

  - (* CtSequence *)
    inversion Heval1; inversion Heval2; subst; clear Heval1 Heval2.
    (* IHHct1 tells us that after executing c1, the intermediate contexts
       (ctx1 and ctx0) will agree on se1 and have identical traces. *)
    edestruct IHHct1 as [Htrace_mid Hagree_mid]; eauto.

  - (* CtIf *)
    (* 1. Prove the guard evaluates equally in both contexts *)
    assert (Hcond: interp_arith e (sec_val_of ctx1_in) = interp_arith e (sec_val_of ctx2_in)).
    { destruct Hagree as [Hval _]. eapply interp_sec_public_agree; eauto. }

    invert_evals_sec.

    + (* Case 1: True / True *)
      (* Traces append the branch decision *)
      assert (Htrace_branched: sec_trace_of (ctx1_in st++ Branch true) = sec_trace_of (ctx2_in st++ Branch true))
        by (cbn; rewrite Htrace; reflexivity).

      (* Explicitly prove branched agreement *)
      assert (Hagree_branched: agree_on_public_sec_ctx se (ctx1_in st++ Branch true) (ctx2_in st++ Branch true))
        by exact Hagree.

      (* Force Coq to use the branched contexts instead of guessing *)
      edestruct (IHHct1 (ctx1_in st++ Branch true) (ctx2_in st++ Branch true) ctx1_out ctx2_out) as [Htrace_thn Hagree_thn]; eauto.

      split; [exact Htrace_thn |].

      eapply agree_on_public_sec_ctx_join_thn; eauto.

    + (* Case 2: True / False (Contradiction) *)
      cbn in *. congruence.

    + (* Case 3: False / True (Contradiction) *)
      cbn in *. congruence.

    + (* Case 4: False / False *)
      assert (Htrace_branched: sec_trace_of (ctx1_in st++ Branch false) = sec_trace_of (ctx2_in st++ Branch false))
        by (cbn; rewrite Htrace; reflexivity).

      (* Explicitly prove branched agreement *)
      assert (Hagree_branched: agree_on_public_sec_ctx se (ctx1_in st++ Branch false) (ctx2_in st++ Branch false))
        by exact Hagree.

      (* Force Coq to use the branched contexts instead of guessing *)
      edestruct (IHHct2 (ctx1_in st++ Branch false) (ctx2_in st++ Branch false) ctx1_out ctx2_out) as [Htrace_els Hagree_els]; eauto.

      split; [exact Htrace_els |].
      eapply agree_on_public_sec_ctx_join_els; eauto.

  - (* CtWhile *)
    (* Cast the starting agreement to the loop invariant *)
    assert (Hagree_inv: agree_on_public_sec_ctx se_inv ctx1_in ctx2_in).
    { eapply agree_on_public_sec_ctx_inv; eauto. }

    eapply while_soundness_sec with (se_body := se_body); eauto.
Qed.
