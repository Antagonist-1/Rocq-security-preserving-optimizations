Require Import Map.
Require Import VarSets.
Require Import Language.Main.
Require Import Language.Analysis.
Require Import Language.Optimizations.Safe.DSE.
Require Import Proofs.SecEnvProofs.
Require Import Proofs.UnskipProofs.
Require Import Proofs.UnsafeDSEProofs.
Require Import Proofs.SafeDSEAnalysisProofs.
Require Import Proofs.SecurityProofs.

Create HintDb dse_db.
Hint Constructors eval eval_trace eval_sec : dse_db.

Ltac destruct_agree H :=
  match type of H with
  | agree_on (_ [∪] _) _ _ =>
      apply agree_on_union in H;
      let Hl := fresh H in
      let Hr := fresh H in
      destruct H as [Hl Hr];
      destruct_agree Hl; destruct_agree Hr
  | _ => idtac
  end.

Ltac destruct_agree_while H :=
  match type of H with
  | agree_on (while_fixpoint (liveness ?body) (vars_in_expr ?e) ?out ?fuel) _ _ =>
    pose proof (liveness_while_cond_subset body e out) as He;
    pose proof (agree_on_subset _ _ _ _ He H) as Hagree_vars; 
    pose proof (while_fixpoint_contains_out) as Hout;
    pose proof (agree_on_subset _ _ _ _ (Hout _ _ _ _) H)  as Hagree_out;
    clear He Hout
  end.

Lemma sec_env_sub_public : forall se_actual se_static x,
  sec_env_sub se_actual se_static ->
  sec_lookup se_static x = Public ->
  sec_lookup se_actual x = Public.
Proof.
  intros se_actual se_static x Hsub Hpub.
  destruct (sec_lookup se_actual x) eqn:Hactual; auto.
  pose proof (Hsub x Hactual).
  congruence.
Qed.

Lemma interp_sec_public_under_sub : forall e se_actual se_static,
  sec_env_sub se_actual se_static ->
  interp_sec e se_static = Public ->
  interp_sec e se_actual = Public.
Proof.
  intros e se_actual se_static Hsub Hpub.
  destruct (interp_sec e se_actual) eqn:Hactual; auto.
  pose proof (interp_sec_secret_monotone e se_actual se_static Hsub Hactual).
  congruence.
Qed.

Lemma cmov_level_public_under_sub : forall cond e1 e2 se_actual se_static,
  sec_env_sub se_actual se_static ->
  join_sec (interp_sec cond se_static)
    (join_sec (interp_sec e1 se_static) (interp_sec e2 se_static)) = Public ->
  join_sec (interp_sec cond se_actual)
    (join_sec (interp_sec e1 se_actual) (interp_sec e2 se_actual)) = Public.
Proof.
  intros cond e1 e2 se_actual se_static Hsub Hpub.
  destruct (join_sec (interp_sec cond se_actual)
    (join_sec (interp_sec e1 se_actual) (interp_sec e2 se_actual))) eqn:Hactual; auto.
  pose proof (cmov_level_secret_monotone cond e1 e2 se_actual se_static Hsub Hactual).
  congruence.
Qed.

Lemma agree_on_secret_public_update_left : forall se v x a,
  sec_lookup se x = Public ->
  agree_on_secret se (v $+ (x, a)) v.
Proof.
  unfold agree_on_secret.
  intros se v x a Hpub y Hsecret.
  destruct (x ==v y).
  - subst. congruence.
  - rewrite lookup_add_ne by congruence.
    reflexivity.
Qed.

Lemma interp_sec_lookup_agree : forall e se1 se2,
  (forall x, sec_lookup se1 x = sec_lookup se2 x) ->
  interp_sec e se1 = interp_sec e se2.
Proof.
  induction e; intros se1 se2 Hagree; cbn.
  - reflexivity.
  - apply Hagree.
  - rewrite (IHe1 se1 se2 Hagree), (IHe2 se1 se2 Hagree).
    reflexivity.
Qed.

Lemma sec_lookup_update_agree : forall se1 se2 x level1 level2,
  (forall y, sec_lookup se1 y = sec_lookup se2 y) ->
  level1 = level2 ->
  forall y, sec_lookup (update_sec se1 x level1) y = sec_lookup (update_sec se2 x level2) y.
Proof.
  intros se1 se2 x level1 level2 Hagree Hlevel y.
  subst level2.
  destruct (x ==v y).
  - subst. rewrite lookup_update_sec_eq. rewrite lookup_update_sec_eq. reflexivity.
  - repeat rewrite lookup_update_sec_ne by congruence.
    apply Hagree.
Qed.

Lemma eval_sec_liveness_coincidence : forall phi c out ctx1 ctx2 ctx1_out,
  eval_sec phi ctx1 c ctx1_out ->
  (forall x, sec_lookup (sec_of ctx1) x = sec_lookup (sec_of ctx2) x) ->
  sec_trace_of ctx1 = sec_trace_of ctx2 ->
  agree_on (liveness c out) (sec_val_of ctx1) (sec_val_of ctx2) ->
  exists ctx2_out,
    eval_sec phi ctx2 c ctx2_out /\
    (forall x, sec_lookup (sec_of ctx1_out) x = sec_lookup (sec_of ctx2_out) x) /\
    sec_trace_of ctx1_out = sec_trace_of ctx2_out /\
    agree_on out (sec_val_of ctx1_out) (sec_val_of ctx2_out).
Proof.
Admitted.

Lemma eval_trace_liveness_coincidence : forall phi c out v1 v2 t v1' t1,
  eval_trace phi (v1, t) c (v1', t1) ->
  agree_on (liveness c out) v1 v2 ->
  exists v2', eval_trace phi (v2, t) c (v2', t1) /\ agree_on out v1' v2'.
Proof.
  intros phi c out v1 v2 t v1' t1 Heval Hagree.
  revert out v2 Hagree.
  dependent induction Heval; simpl in *; intros.
  - exists v2. split; [constructor | assumption].
  - destruct (VarSet.mem x out) eqn:Hx.
    + exists (v2 $+ (x, interp_arith e v1)). destruct_agree Hagree. split.
      * constructor. simpl. apply interp_arith_agree; apply agree_on_sym; eauto.
      * apply agree_on_remove_add; eauto.
    + exists (v2 $+ (x, interp_arith e v2)). split; [constructor; eauto | apply agree_on_dead_update_both; eauto].
  - destruct (VarSet.mem x out) eqn:Hx.
    + exists (v2 $+ (x, interp_arith e1 v1)). destruct_agree Hagree. split.
      * econstructor; eauto. simpl. assert (interp_arith cond v2 = interp_arith cond v1) by (apply interp_arith_agree; apply agree_on_sym; eauto). congruence.
        simpl. apply interp_arith_agree; apply agree_on_sym; eauto.
      * apply agree_on_remove_add; eauto.
    + destruct (interp_arith cond v2) eqn:Hc2.
      * exists (v2 $+ (x, interp_arith e2 v2)). split; [eapply EvalTraceCmovFalse; eauto | apply agree_on_dead_update_both; eauto].
      * exists (v2 $+ (x, interp_arith e1 v2)). split; [eapply EvalTraceCmovTrue; eauto | apply agree_on_dead_update_both; eauto].
  - destruct (VarSet.mem x out) eqn:Hx.
    + exists (v2 $+ (x, interp_arith e2 v1)). destruct_agree Hagree. split.
      * eapply EvalTraceCmovFalse; eauto. simpl. assert (interp_arith cond v2 = interp_arith cond v1) by (apply interp_arith_agree; apply agree_on_sym; eauto). congruence.
        simpl. apply interp_arith_agree; apply agree_on_sym; eauto.
      * unfold agree_on. intros. destruct (x ==v x0); [subst; repeat rewrite lookup_add_eq; reflexivity | eapply agree_on_update_both; [apply Hagree0|]; rewrite VarSetEqProps.remove_mem_2; eauto].
    + destruct (interp_arith cond v2) eqn:Hc2.
      * exists (v2 $+ (x, interp_arith e2 v2)). split; [eapply EvalTraceCmovFalse; eauto | apply agree_on_dead_update_both; eauto].
      * exists (v2 $+ (x, interp_arith e1 v2)). split; [eapply EvalTraceCmovTrue; eauto | apply agree_on_dead_update_both; eauto].
  - destruct_agree Hagree. exists (v2 $+ (x, a)). split.
    + econstructor; eauto. simpl. assert (interp_arith e1 v1 = interp_arith e1 v2 /\ interp_arith e2 v1 = interp_arith e2 v2) as [<- <-] by (split; apply interp_arith_agree; eauto). exact Heval.
    + apply agree_on_remove_add; eauto.
  - destruct ctx1 as [v_1 t_1].
    specialize (IHHeval1 _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) _ _ Hagree).
    destruct IHHeval1 as [v2_mid [IHHeval1 IHHagree1]].
    specialize (IHHeval2 _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) _ _ IHHagree1).
    destruct IHHeval2 as [v2_final [IHHeval2 IHHagree2]].
    exists v2_final. split; [econstructor|]; eauto.
  - destruct_agree Hagree. specialize (IHHeval _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) _ _ Hagree2).
    destruct IHHeval as [v2' [IHHeval IHHagree]].
    exists v2'. split; [eapply EvalTraceIfTrue|]; eauto.
    simpl. assert (interp_arith e v1 = interp_arith e v2) by (apply interp_arith_agree; eauto). congruence.
  - destruct_agree Hagree. specialize (IHHeval _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) _ _ Hagree3).
    destruct IHHeval as [v2' [IHHeval IHHagree]].
    exists v2'. split; [eapply EvalTraceIfFalse|]; eauto.
    simpl. assert (interp_arith e v1 = interp_arith e v2) by (apply interp_arith_agree; eauto). congruence.
  - destruct ctx' as [v_1 t_1].
    pose proof (liveness_while_body_closed body e out) as Hliveness_body.
    unfold liveness in Hliveness_body; fold liveness in Hliveness_body.
    pose proof (agree_on_subset _ _ _ _ Hliveness_body Hagree) as Hagree_body.
    specialize (IHHeval1 _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) _ _ Hagree_body).
    destruct IHHeval1 as [v2_mid [IHHeval1 IHHagree1]].
    specialize (IHHeval2 _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) _ _ IHHagree1).
    destruct IHHeval2 as [v2_final [IHHeval2 IHHagree2]].
    exists v2_final. split; [|exact IHHagree2].
    destruct_agree_while Hagree. eapply EvalTraceWhileTrue; eauto.
    simpl. assert (interp_arith e v1 = interp_arith e v2) by (apply interp_arith_agree; eauto). congruence.
  - destruct_agree_while Hagree.
    exists v2. split; [eapply EvalTraceWhileFalse|]; eauto.
    simpl. assert (interp_arith e v1' = interp_arith e v2) by (apply interp_arith_agree; eauto). congruence.
Qed.

Definition lifts_to (phi: function_env) (c: cmd) (out: var_set)
                     (ctx ctx_opt: context) : Prop :=
  exists ctx_out,
    eval_trace phi ctx c ctx_out /\
    trace_of ctx_out = trace_of ctx_opt /\
    agree_on out (val_of ctx_out) (val_of ctx_opt).

(* specific case of while completeness. original proof was not general enough *)
(* body is complete -> while loop is complete*)
Lemma safe_dse_while_complete : forall phi e c out secrets,
  (forall out' ctx ctx_opt,
     eval_trace phi ctx (safe_dse_helper c out' secrets) ctx_opt ->
     lifts_to phi c out' ctx ctx_opt) ->
  forall ctx ctx_opt,
    eval_trace phi ctx (While e (safe_dse_helper c (liveness (While e c) out) secrets)) ctx_opt ->
    lifts_to phi (While e c) out ctx ctx_opt.
Proof.
  intros phi e c out secrets Hbody ctx ctx_opt H.
  (* We remember what the command was (a while), because rocq doesnt. thten all other cases are removed*)
  remember (While e (safe_dse_helper c (liveness (While e c) out) secrets)) as w eqn:Hw.
  induction H; inversion Hw; subst; unfold lifts_to in *.
  - clear IHeval_trace1.
    specialize (Hbody _ _ _ H1). destruct Hbody as [ctx_mid [Heval_mid [Htrace_mid Hagree_mid]]].
    specialize (IHeval_trace2 Hw). destruct IHeval_trace2 as [ctx_final [Heval_final [Htrace_final Hagree_final]]].
    pose proof eval_trace_liveness_coincidence as Heval_coincide.
    apply agree_on_sym in Hagree_mid.
    destruct ctx, ctx', ctx'', ctx_mid, ctx_final.
    specialize (Heval_coincide _ _ _ _ _ _ _ _ Heval_final Hagree_mid).
    destruct Heval_coincide as [v2_coincide [Heval_coin Hagree_coin]].
    exists (v2_coincide, l3). split; eauto; simpl in *; subst.
    + eapply EvalTraceWhileTrue; eauto.
    + split; [reflexivity|].
      apply agree_on_sym in Hagree_coin.
      eapply agree_on_trans; eauto.
  - exists (ctx t++ Branch false).
    repeat split.
    constructor. exact H.
Qed. 


(* opt_dse doesn't modify the trace. well...
the trace is not modified. but the final valuation is.
so I need to be more precise:
*)

Lemma opt_safe_dse_helper_trace_complete : forall phi c out ctx ctx_opt secrets,
  eval_trace phi ctx (safe_dse_helper c out secrets) ctx_opt ->
  lifts_to phi c out ctx ctx_opt.
Proof.
  induction c as
      [| x e
       | x f e1 e2
       | x cond e1 e2
       | c1 IHc1 c2 IHc2
       | e thn IHthn els IHels
       | e body IHbody]; simpl; unfold lifts_to in *; intros.
  - subst; firstorder.
  - destruct (VarSet.mem x out) eqn:Hout; [inversion H; subst; firstorder|].
    destruct (sec_lookup secrets x) eqn:Hsecret;
      destruct (interp_sec e secrets) eqn:Hlevel;
      try (inversion H; subst; firstorder).
    destruct ctx_opt as [v_opt t_opt].
    exists (v_opt $+ (x, interp_arith e v_opt), t_opt).
    repeat split; simpl in *; [econstructor; eauto | apply agree_on_sym; eapply agree_on_update_out; eauto].
  - inversion H; subst; firstorder.
  - destruct (VarSet.mem x out) eqn:Hout; [inversion H; subst; firstorder|].
    destruct (sec_lookup secrets x) eqn:Hsecret;
      destruct (join_sec (interp_sec cond secrets)
        (join_sec (interp_sec e1 secrets) (interp_sec e2 secrets))) eqn:Hlevel;
      try (inversion H; subst; firstorder).
    destruct ctx_opt as [v_opt t_opt].
    destruct (interp_arith cond v_opt) eqn:Hinterp.
    + exists (v_opt $+ (x, interp_arith e2 v_opt), t_opt).
      repeat split; simpl; [eapply EvalTraceCmovFalse; eauto | apply agree_on_sym; eapply agree_on_update_out; eauto].
    + exists (v_opt $+ (x, interp_arith e1 v_opt), t_opt).
      repeat split; simpl; [eapply EvalTraceCmovTrue; eauto; discriminate | apply agree_on_sym; eapply agree_on_update_out; eauto].
  - inversion H; subst. specialize (IHc1 _ _ _ _ H3).
    destruct IHc1 as [ctx_out1 [Heval1 [Htrace1 Hagree1]]].
    specialize (IHc2 _ _ _ _ H5).
    destruct IHc2 as [ctx_out2 [Heval2 [Htrace2 Hagree2]]].
    pose proof eval_trace_liveness_coincidence as Heval_coincide.
    destruct ctx1 as [v_mid t_mid], ctx_out1 as [v_out1 t_out1], ctx_out2 as [v_out2 t_out2].
    simpl in *. subst t_out1.
    apply agree_on_sym in Hagree1.
    specialize (Heval_coincide _ _ _ _ _ _ _ _ Heval2 Hagree1).
    destruct Heval_coincide as [v_out_final [Heval_coincide Hagree_coin]].
    exists (v_out_final, t_out2).
    repeat split; [econstructor; [exact Heval1 | exact Heval_coincide] | exact Htrace2 |].
    simpl in *. apply agree_on_sym in Hagree_coin. eapply agree_on_trans; eauto.
  - inversion H; subst.
    + specialize (IHthn _ _ _ _ H7). destruct IHthn as [ctx_out [Heval [Htrace Hagree]]].
      exists ctx_out. repeat split; eauto. eapply EvalTraceIfTrue; eauto.
    + specialize (IHels _ _ _ _ H6). destruct IHels as [ctx_out [Heval [Htrace Hagree]]].
      exists ctx_out. repeat split; eauto. eapply EvalTraceIfFalse; eauto.
  - exists ctx_opt. repeat split; eauto.
Qed.


Lemma eval_trace_frame : forall phi ctx c ctx',
    eval_trace phi ctx c ctx' ->
    forall x,  ~ VarSet.In x (vars_in_cmd c) -> (val_of ctx') $? x = (val_of ctx) $? x.
Proof.
    induction 1; simpl in *; intros.
    all: try (destruct (x ==v x0); [VarSetDecide.fsetdec | apply lookup_add_ne; congruence]).
    all: try (apply IHeval_trace; VarSetDecide.fsetdec).
    all: try (rewrite IHeval_trace2 by VarSetDecide.fsetdec;
      apply IHeval_trace1; VarSetDecide.fsetdec).
    all: reflexivity.
Qed.
    


Lemma opt_safe_dse_helper_preserves_safe_pgm : forall phi p secrets,
    is_safe_pgm phi p secrets ->
    is_safe_pgm phi (opt_safe_dse p secrets) secrets.
Proof.
  unfold is_safe_pgm, opt_safe_dse in *.
  intros phi [c out] secrets [secrets' Hni].
  simpl in *.
  exists (VarSet.union secrets
    (vars_in_cmd (safe_dse_helper c (VarSet.union out (sec_post c secrets)) secrets))).
  unfold non_inference in *.
  intros v1 v2 t_in final_v1 final_v2 trace1 trace2 Hagree Hopt_eval1 Hopt_eval2.

  pose proof (opt_unskip_trace_complete phi
    (safe_dse_helper c (VarSet.union out (sec_post c secrets)) secrets)
    (v1, t_in) (final_v1, trace1) Hopt_eval1) as Hhelper_eval1.
  pose proof (opt_unskip_trace_complete phi
    (safe_dse_helper c (VarSet.union out (sec_post c secrets)) secrets)
    (v2, t_in) (final_v2, trace2) Hopt_eval2) as Hhelper_eval2.

  pose proof (opt_safe_dse_helper_trace_complete _ _ _ _ _ _ Hhelper_eval1)
    as Htrace_complete1.
  pose proof (opt_safe_dse_helper_trace_complete _ _ _ _ _ _ Hhelper_eval2)
    as Htrace_complete2.
  destruct Htrace_complete1 as [[v1_out trace1_out] [Heval1 [Htrace1 Hagree1]]].
  destruct Htrace_complete2 as [[v2_out trace2_out] [Heval2 [Htrace2 Hagree2]]].
  simpl in *.

  specialize (Hni v1 v2 t_in v1_out v2_out trace1_out trace2_out).
  specialize (Hni Hagree Heval1 Heval2).
  split.
  - destruct Hni as [Htrace_equal _].
    congruence.
  - unfold agree_on_public.
    intros x Hx.
    pose proof (eval_trace_frame _ _ _ _ Hhelper_eval1 x) as Hframe1.
    pose proof (eval_trace_frame _ _ _ _ Hhelper_eval2 x) as Hframe2.
    simpl in *.
    rewrite Hframe1.
    rewrite Hframe2.
    + apply Hagree.
      VarSetDecide.fsetdec.
    + VarSetDecide.fsetdec.
    + VarSetDecide.fsetdec.
Qed.
