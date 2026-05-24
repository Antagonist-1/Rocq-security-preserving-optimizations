Require Import Map.
Require Import VarSets.
Require Import Language.Main.
Require Import Language.Analysis.
Require Import Language.Optimizations.Safe.DSE.
Require Import Language.Optimizations.Safe.Unskip.
Require Import Proofs.SafeDSEProofs.
Require Import Proofs.EvalEquivalence.
Require Import Proofs.SecEnvProofs.
Require Import Proofs.UnskipProofs.
Require Import Proofs.UnsafeDSEProofs.
Require Import Proofs.SafeDSEAnalysisProofs.
Require Import Proofs.SecurityProofs.

Create HintDb dse_db.
Hint Constructors eval eval_trace eval_sec : dse_db.


(* Helper tactics *)

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

Ltac solve_interp_from_agree Heval Hagree :=
  rewrite <- Heval;
  apply interp_arith_agree;
  eapply agree_on_subset; [| apply agree_on_sym; exact Hagree];
  VarSetDecide.fsetdec.

Ltac finish_trace_same H :=
  eexists; split; [exact H | constructor; [reflexivity | apply agree_on_refl]].

Ltac finish_sec_same H :=
  eexists; split; [exact H | constructor; [intro y; reflexivity | reflexivity | apply agree_on_refl]].

(** * Records to define properties *) 
(* instead of using conjunctions, for better readability (avoid  repeated split) *)


(* Two context coincide if they have the same trace and they agree on the output variables. *) 
Record trace_coincide (out : var_set) (ctx_src ctx_opt : context) : Prop := {
  trace_coincide_trace : trace_of ctx_src = trace_of ctx_opt;
  trace_coincide_vals : agree_on out (val_of ctx_src) (val_of ctx_opt)
}.

(* Two sec_context coincide if : 1. their sec_env are the same, 2. their traces are the same, 3. they agree on the output variables. *)
Record sec_coincide (out : var_set) (ctx1 ctx2 : sec_context) : Prop := {
  sec_coincide_sec : forall x,
    sec_lookup (sec_of ctx1) x = sec_lookup (sec_of ctx2) x;
  sec_coincide_trace : sec_trace_of ctx1 = sec_trace_of ctx2;
  sec_coincide_vals : agree_on out (sec_val_of ctx1) (sec_val_of ctx2)
}.

Lemma sec_coincide_proj_trace : forall out ctx1 ctx2,
  sec_coincide out ctx1 ctx2 ->
  trace_coincide out
    (sec_val_of ctx1, sec_trace_of ctx1)
    (sec_val_of ctx2, sec_trace_of ctx2).
Proof.
  intros out ctx1 ctx2 Hcoin.
  destruct Hcoin as [_ Htrace Hagree].
  constructor; exact Htrace || exact Hagree.
Qed.




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

Definition opt_safe_dse_core (pgm: program) (secrets: sec_env) : program :=
  (safe_dse_helper (cmd_of pgm) (protected_out pgm secrets) secrets,
   output_of pgm).

(** * 3. Secret preservation (eval_sec) *)


Lemma sec_lookup_update_public_id : forall se x,
  sec_lookup se x = Public ->
  forall y, sec_lookup (update_sec se x Public) y = sec_lookup se y.
Proof.
  intros se x Hpub y.
  destruct (x ==v y).
  - subst. rewrite lookup_update_sec_eq. symmetry. exact Hpub.
  - rewrite lookup_update_sec_ne by congruence. reflexivity.
Qed.

Lemma agree_on_protected_out_implies_agree_on_secret : forall phi ctx c out ctx' v_opt,
  eval_sec phi ctx c ctx' ->
  agree_on (VarSet.union out (sec_post c (sec_of ctx))) (sec_val_of ctx') v_opt ->
  agree_on_secret (sec_of ctx') (sec_val_of ctx') v_opt.
Proof.
  intros phi ctx c out ctx' v_opt Heval Hagree.
  unfold agree_on_secret.
  intros x Hsecret.
  apply Hagree.
  rewrite VarSetEqProps.union_mem.
  apply Bool.orb_true_intro.
  right.
  apply mem_lookup_simpl_2.
  eapply sec_post_overapproximates_eval_sec; eauto.
Qed.


Lemma eval_sec_liveness_coincidence : forall phi c out ctx1 ctx2 ctx1_out,
  eval_sec phi ctx1 c ctx1_out ->
  (forall x, sec_lookup (sec_of ctx1) x = sec_lookup (sec_of ctx2) x) ->
  sec_trace_of ctx1 = sec_trace_of ctx2 ->
  agree_on (liveness c out) (sec_val_of ctx1) (sec_val_of ctx2) ->
  exists ctx2_out,
    eval_sec phi ctx2 c ctx2_out /\
    sec_coincide out ctx1_out ctx2_out.
Proof.
  intros phi c out ctx1 ctx2 ctx1_out Heval Hsec Htrace Hagree.
  revert out ctx2 Hsec Htrace Hagree.
  dependent induction Heval; simpl in *; intros.
  - exists ctx2.
    split; [constructor|].
    constructor; assumption.
  - destruct (VarSet.mem x out) eqn:Hx.
    + assert (Ha : interp_arith e (sec_val_of ctx2) = a).
      { solve_interp_from_agree H Hagree. }
      exists (((ctx2 sv$+ (x, a)) s$+ (x, interp_sec e (sec_of ctx2)))).
      split.
      * econstructor; eauto.
      * constructor.
        -- intro y. simpl.
           apply sec_lookup_update_agree; auto.
           rewrite <- H0.
           apply interp_sec_lookup_agree.
           exact Hsec.
        -- exact Htrace.
        -- apply agree_on_remove_add.
           eapply agree_on_subset; [| exact Hagree].
           VarSetDecide.fsetdec.
    + exists (((ctx2 sv$+ (x, interp_arith e (sec_val_of ctx2))) s$+ (x, interp_sec e (sec_of ctx2)))).
      split.
      * econstructor; eauto.
      * constructor.
        -- intro y. simpl.
           apply sec_lookup_update_agree; auto.
           rewrite <- H0.
           apply interp_sec_lookup_agree.
           exact Hsec.
        -- exact Htrace.
        -- apply agree_on_dead_update_both; auto.
  - destruct (VarSet.mem x out) eqn:Hx.
    + assert (Hcond : interp_arith cond (sec_val_of ctx2) = c).
      { solve_interp_from_agree H Hagree. }
      assert (Ha1 : interp_arith e1 (sec_val_of ctx2) = a1).
      { solve_interp_from_agree H1 Hagree. }
      assert (Ha2 : interp_arith e2 (sec_val_of ctx2) = a2).
      { solve_interp_from_agree H2 Hagree. }
      exists (((ctx2 sv$+ (x, a1)) s$+ (x,
        join_sec (interp_sec cond (sec_of ctx2))
          (join_sec (interp_sec e1 (sec_of ctx2)) (interp_sec e2 (sec_of ctx2)))))).
      split.
      * eapply EvalSecCmovTrue; eauto.
      * constructor.
        -- intro y. simpl.
           apply sec_lookup_update_agree; auto.
           rewrite <- H3.
           repeat rewrite (interp_sec_lookup_agree _ _ _ Hsec).
           reflexivity.
        -- exact Htrace.
        -- apply agree_on_remove_add.
           eapply agree_on_subset; [| exact Hagree].
           VarSetDecide.fsetdec.
    + destruct (interp_arith cond (sec_val_of ctx2)) eqn:Hc2.
      * exists (((ctx2 sv$+ (x, interp_arith e2 (sec_val_of ctx2))) s$+ (x,
          join_sec (interp_sec cond (sec_of ctx2))
            (join_sec (interp_sec e1 (sec_of ctx2)) (interp_sec e2 (sec_of ctx2)))))).
        split.
        -- eapply EvalSecCmovFalse; eauto.
        -- constructor.
           ++ intro y. simpl.
              apply sec_lookup_update_agree; auto.
              rewrite <- H3.
              repeat rewrite (interp_sec_lookup_agree _ _ _ Hsec).
              reflexivity.
           ++ exact Htrace.
           ++ apply agree_on_dead_update_both; auto.
      * exists (((ctx2 sv$+ (x, interp_arith e1 (sec_val_of ctx2))) s$+ (x,
          join_sec (interp_sec cond (sec_of ctx2))
            (join_sec (interp_sec e1 (sec_of ctx2)) (interp_sec e2 (sec_of ctx2)))))).
        split.
        -- eapply EvalSecCmovTrue; eauto.
        -- constructor.
           ++ intro y. simpl.
              apply sec_lookup_update_agree; auto.
              rewrite <- H3.
              repeat rewrite (interp_sec_lookup_agree _ _ _ Hsec).
              reflexivity.
           ++ exact Htrace.
           ++ apply agree_on_dead_update_both; auto.
  - destruct (VarSet.mem x out) eqn:Hx.
    + assert (Hcond : interp_arith cond (sec_val_of ctx2) = 0).
      { solve_interp_from_agree H Hagree. }
      assert (Ha1 : interp_arith e1 (sec_val_of ctx2) = a1).
      { solve_interp_from_agree H0 Hagree. }
      assert (Ha2 : interp_arith e2 (sec_val_of ctx2) = a2).
      { solve_interp_from_agree H1 Hagree. }
      exists (((ctx2 sv$+ (x, a2)) s$+ (x,
        join_sec (interp_sec cond (sec_of ctx2))
          (join_sec (interp_sec e1 (sec_of ctx2)) (interp_sec e2 (sec_of ctx2)))))).
      split.
      * eapply EvalSecCmovFalse; eauto.
      * constructor.
        -- intro y. simpl.
           apply sec_lookup_update_agree; auto.
           rewrite <- H2.
           repeat rewrite (interp_sec_lookup_agree _ _ _ Hsec).
           reflexivity.
        -- exact Htrace.
        -- apply agree_on_remove_add.
           eapply agree_on_subset; [| exact Hagree].
           VarSetDecide.fsetdec.
    + destruct (interp_arith cond (sec_val_of ctx2)) eqn:Hc2.
      * exists (((ctx2 sv$+ (x, interp_arith e2 (sec_val_of ctx2))) s$+ (x,
          join_sec (interp_sec cond (sec_of ctx2))
            (join_sec (interp_sec e1 (sec_of ctx2)) (interp_sec e2 (sec_of ctx2)))))).
        split.
        -- eapply EvalSecCmovFalse; eauto.
        -- constructor.
           ++ intro y. simpl.
              apply sec_lookup_update_agree; auto.
              rewrite <- H2.
              repeat rewrite (interp_sec_lookup_agree _ _ _ Hsec).
              reflexivity.
           ++ exact Htrace.
           ++ apply agree_on_dead_update_both; auto.
      * exists (((ctx2 sv$+ (x, interp_arith e1 (sec_val_of ctx2))) s$+ (x,
          join_sec (interp_sec cond (sec_of ctx2))
            (join_sec (interp_sec e1 (sec_of ctx2)) (interp_sec e2 (sec_of ctx2)))))).
        split.
        -- eapply EvalSecCmovTrue; eauto.
        -- constructor.
           ++ intro y. simpl.
              apply sec_lookup_update_agree; auto.
              rewrite <- H2.
              repeat rewrite (interp_sec_lookup_agree _ _ _ Hsec).
              reflexivity.
           ++ exact Htrace.
           ++ apply agree_on_dead_update_both; auto.
  - assert (Ha1 : interp_arith e1 (sec_val_of ctx2) = a1).
    { solve_interp_from_agree H0 Hagree. }
    assert (Ha2 : interp_arith e2 (sec_val_of ctx2) = a2).
    { solve_interp_from_agree H1 Hagree. }
    assert (Hl1 : interp_sec e1 (sec_of ctx2) = level1).
    {
      rewrite <- H2.
      symmetry.
      apply interp_sec_lookup_agree.
      exact Hsec.
    }
    assert (Hl2 : interp_sec e2 (sec_of ctx2) = level2).
    {
      rewrite <- H3.
      symmetry.
      apply interp_sec_lookup_agree.
      exact Hsec.
    }
    exists ((sec_val_of ctx2 $+ (x, a), update_sec (sec_of ctx2) x level, sec_trace_of ctx')).
    split.
    + eapply EvalSecAssignCall with (x1 := x1) (x2 := x2) (y := y) (body := body)
        (a1 := a1) (a2 := a2) (level1 := level1) (level2 := level2) (ctx' := ctx'); eauto.
      rewrite <- Htrace.
      exact Heval.
    + constructor.
      * intro z. simpl.
        apply sec_lookup_update_agree; auto.
      * reflexivity.
      * apply agree_on_remove_add.
        eapply agree_on_subset; [| exact Hagree].
        VarSetDecide.fsetdec.
  - destruct ctx1 as [[v_1 se_1] t_1].
    specialize (IHHeval1 (liveness c2 out) ctx0 Hsec Htrace Hagree).
    destruct IHHeval1 as [ctx2_mid [IHHeval1 Hcoin1]].
    destruct Hcoin1 as [IHsec1 IHtrace1 IHHagree1].
    specialize (IHHeval2 out ctx2_mid IHsec1 IHtrace1 IHHagree1).
    destruct IHHeval2 as [ctx2_final [IHHeval2 Hcoin2]].
    exists ctx2_final. split; [econstructor|exact Hcoin2]; eauto.
  - assert (Hcond : interp_arith e (sec_val_of ctx2) = c).
    { solve_interp_from_agree H Hagree. }
    assert (Hagree_thn : agree_on (liveness thn out) (sec_val_of ctx) (sec_val_of ctx2)).
    {
      eapply agree_on_subset; [| exact Hagree].
      VarSetDecide.fsetdec.
    }
    specialize (IHHeval out (ctx2 st++ Branch true) Hsec).
    assert (Htrace_thn : sec_trace_of (ctx st++ Branch true) = sec_trace_of (ctx2 st++ Branch true)).
    { simpl. rewrite Htrace. reflexivity. }
    specialize (IHHeval Htrace_thn Hagree_thn).
    destruct IHHeval as [ctx2' [IHHeval Hcoin]].
    exists ctx2'. split; [eapply EvalSecIfTrue|exact Hcoin]; eauto.
  - assert (Hcond : interp_arith e (sec_val_of ctx2) = 0).
    { solve_interp_from_agree H Hagree. }
    assert (Hagree_els : agree_on (liveness els out) (sec_val_of ctx) (sec_val_of ctx2)).
    {
      eapply agree_on_subset; [| exact Hagree].
      VarSetDecide.fsetdec.
    }
    specialize (IHHeval out (ctx2 st++ Branch false) Hsec).
    assert (Htrace_els : sec_trace_of (ctx st++ Branch false) = sec_trace_of (ctx2 st++ Branch false)).
    { simpl. rewrite Htrace. reflexivity. }
    specialize (IHHeval Htrace_els Hagree_els).
    destruct IHHeval as [ctx2' [IHHeval Hcoin]].
    exists ctx2'. split; [eapply EvalSecIfFalse|exact Hcoin]; eauto.
  - destruct ctx' as [[v_1 se_1] t_1].
    pose proof (liveness_while_body_closed body e out) as Hliveness_body.
    unfold liveness in Hliveness_body. fold liveness in Hliveness_body.
    pose proof (agree_on_subset _ _ _ _ Hliveness_body Hagree) as Hagree_body.
    specialize (IHHeval1 (liveness (While e body) out) (ctx2 st++ Branch true) Hsec).
    assert (Htrace_body : sec_trace_of (ctx st++ Branch true) = sec_trace_of (ctx2 st++ Branch true)).
    { simpl. rewrite Htrace. reflexivity. }
    specialize (IHHeval1 Htrace_body Hagree_body).
    destruct IHHeval1 as [ctx2_mid [IHHeval1 Hcoin1]].
    destruct Hcoin1 as [IHsec1 IHtrace1 IHHagree1].
    specialize (IHHeval2 out ctx2_mid IHsec1 IHtrace1 IHHagree1).
    destruct IHHeval2 as [ctx2_final [IHHeval2 Hcoin2]].
    exists ctx2_final. split.
    + destruct_agree_while Hagree.
      eapply EvalSecWhileTrue; eauto.
      simpl.
      assert (interp_arith e (sec_val_of ctx2) = c).
      { solve_interp_from_agree H Hagree_vars. }
      congruence.
    + exact Hcoin2.
  - destruct_agree_while Hagree.
    exists (ctx2 st++ Branch false). split.
    + eapply EvalSecWhileFalse.
      simpl.
      assert (interp_arith e (sec_val_of ctx2) = 0).
      { solve_interp_from_agree H Hagree_vars. }
      exact H0.
    + constructor.
      * exact Hsec.
      * simpl. rewrite Htrace. reflexivity.
      * exact Hagree_out.
Qed.

(* Any evaluation of the optimized program can be matched to an evaluation of the original program 
   that have : 1. same sec. labels, 2. same trace, 3. agree on the out variables. *)
Lemma safe_dse_helper_sec_complete : forall phi c out secrets ctx ctx_opt,
  sec_env_sub (sec_of ctx) secrets ->
  eval_sec phi ctx (safe_dse_helper c out secrets) ctx_opt ->
  exists ctx_src,
    eval_sec phi ctx c ctx_src /\
    sec_coincide out ctx_src ctx_opt.
Proof.
  intros phi c.
  induction c as
      [| x e
       | x f e1 e2
       | x cond e1 e2
       | c1 IHc1 c2 IHc2
       | e thn IHthn els IHels
       | e body IHbody];
    simpl; intros out secrets ctx ctx_opt Hsub Hopt.
  - finish_sec_same Hopt.
  - destruct (VarSet.mem x out) eqn:Hout.
    + finish_sec_same Hopt.
    + destruct (sec_lookup secrets x) eqn:Hsecret;
        destruct (interp_sec e secrets) eqn:Hlevel.
      * inversion Hopt; subst.
        pose proof (sec_env_sub_public _ _ _ Hsub Hsecret) as Hpub_actual.
        pose proof (interp_sec_public_under_sub e (sec_of ctx_opt) secrets Hsub Hlevel)
          as Hlevel_actual.
        exists ((ctx_opt sv$+ (x, interp_arith e (sec_val_of ctx_opt))) s$+ (x, Public)).
        split.
        -- econstructor; eauto.
        -- constructor.
           ++ intro y. simpl. apply sec_lookup_update_public_id. exact Hpub_actual.
           ++ reflexivity.
           ++ simpl. eapply agree_on_dead_update_left; eauto. apply agree_on_refl.
      * finish_sec_same Hopt.
      * finish_sec_same Hopt.
      * finish_sec_same Hopt.
  - finish_sec_same Hopt.
  - destruct (VarSet.mem x out) eqn:Hout.
    + finish_sec_same Hopt.
    + destruct (sec_lookup secrets x) eqn:Hsecret;
        destruct (join_sec (interp_sec cond secrets)
          (join_sec (interp_sec e1 secrets) (interp_sec e2 secrets))) eqn:Hlevel.
      * inversion Hopt; subst.
        pose proof (sec_env_sub_public _ _ _ Hsub Hsecret) as Hpub_actual.
        pose proof (cmov_level_public_under_sub cond e1 e2 (sec_of ctx_opt) secrets Hsub Hlevel)
          as Hlevel_actual.
        destruct (interp_arith cond (sec_val_of ctx_opt)) eqn:Hcond.
        -- exists ((ctx_opt sv$+ (x, interp_arith e2 (sec_val_of ctx_opt))) s$+ (x, Public)).
           split.
           ++ eapply EvalSecCmovFalse; eauto.
           ++ constructor.
              ** intro y. simpl. apply sec_lookup_update_public_id. exact Hpub_actual.
              ** reflexivity.
              ** simpl. eapply agree_on_dead_update_left; eauto. apply agree_on_refl.
        -- exists ((ctx_opt sv$+ (x, interp_arith e1 (sec_val_of ctx_opt))) s$+ (x, Public)).
           split.
           ++ eapply EvalSecCmovTrue; eauto.
           ++ constructor.
              ** intro y. simpl. apply sec_lookup_update_public_id. exact Hpub_actual.
              ** reflexivity.
              ** simpl. eapply agree_on_dead_update_left; eauto. apply agree_on_refl.
      * finish_sec_same Hopt.
      * finish_sec_same Hopt.
      * finish_sec_same Hopt.
  - inversion Hopt; subst.
    specialize (IHc1 (liveness c2 out) secrets ctx ctx1 Hsub H2).
    destruct IHc1 as [ctx1_src [Heval1_src Hcoin1]].
    destruct Hcoin1 as [Hsec_eq1 Htrace_eq1 Hagree1].
    assert (Hsub2 : sec_env_sub (sec_of ctx1) (sec_post c1 secrets)).
    {
      unfold sec_env_sub.
      intros y Hsecret_mid.
      pose proof (Hsec_eq1 y) as Hsec_eq1_y.
      rewrite <- Hsec_eq1_y in Hsecret_mid.
      eapply sec_env_sub_trans.
      - eapply sec_post_overapproximates_eval_sec_subset.
        exact Heval1_src.
      - eapply sec_post_monotone.
        exact Hsub.
      - exact Hsecret_mid.
    }
    specialize (IHc2 out (sec_post c1 secrets) ctx1 ctx_opt Hsub2 H4).
    destruct IHc2 as [ctx2_src_from_opt [Heval2_src_from_opt Hcoin2]].
    destruct Hcoin2 as [Hsec_eq2 Htrace_eq2 Hagree2].
    pose proof (eval_sec_liveness_coincidence phi c2 out ctx1 ctx1_src ctx2_src_from_opt
      Heval2_src_from_opt
      (fun y => eq_sym (Hsec_eq1 y))
      (eq_sym Htrace_eq1)
      (agree_on_sym _ _ _ Hagree1)) as Hcoincide.
    destruct Hcoincide as [ctx2_src [Heval2_src Hcoin]].
    destruct Hcoin as [Hsec_eq_coin Htrace_eq_coin Hagree_coin].
    exists ctx2_src.
    split.
    + econstructor; eauto.
    + constructor.
      * intro y. rewrite <- Hsec_eq_coin. apply Hsec_eq2.
      * rewrite <- Htrace_eq_coin. exact Htrace_eq2.
      * apply agree_on_sym in Hagree_coin.
        eapply agree_on_trans; eauto.
  - inversion Hopt; subst.
    + specialize (IHthn out secrets (ctx st++ Branch true) ctx_opt Hsub H6).
      destruct IHthn as [ctx_src [Heval_src Hcoin]].
      exists ctx_src.
      split; [eapply EvalSecIfTrue; eauto|exact Hcoin].
    + specialize (IHels out secrets (ctx st++ Branch false) ctx_opt Hsub H5).
      destruct IHels as [ctx_src [Heval_src Hcoin]].
      exists ctx_src.
      split; [eapply EvalSecIfFalse; eauto|exact Hcoin].
  - finish_sec_same Hopt.
Qed.

Lemma opt_safe_dse_core_keeps_secrets_secret :
  opt_keeps_secrets_secret opt_safe_dse_core.
Proof.
  unfold opt_keeps_secrets_secret, opt_safe_dse_core.
  intros sctx sctx' sctx'' pgm pgm' phi Hopt Hsrc Hopt_eval x.
  destruct pgm as [c out].
  destruct pgm' as [c' out'].
  simpl in Hopt.
  inversion Hopt; subst; clear Hopt.
  simpl in Hopt_eval.
  pose proof (safe_dse_helper_sec_complete phi c
    (VarSet.union out' (sec_post c (sec_of sctx)))
    (sec_of sctx) sctx sctx''
    (sec_env_sub_refl (sec_of sctx))
    Hopt_eval) as Hcomplete.
  destruct Hcomplete as [ctx_src [Hsrc_from_opt Hcoin_out]].
  destruct Hcoin_out as [Hsec_eq _ Hagree_out].
  pose proof (eval_sec_deterministic phi c sctx sctx' ctx_src Hsrc Hsrc_from_opt) as Hsame.
  subst ctx_src.
  split.
  - apply Hsec_eq.
  - eapply agree_on_protected_out_implies_agree_on_secret; eauto.
Qed.

Lemma opt_safe_dse_core_eval_sec_sound :
  opt_eval_sec_sound opt_safe_dse_core.
Proof.
  unfold opt_eval_sec_sound, opt_safe_dse_core.
  intros phi sctx sctx' [c out] Hsrc.
  destruct sctx as [[v se] t].
  destruct sctx' as [[v' se'] t'].
  simpl in *.
  pose proof (Eval_proj_sec_trace phi (v, se, t) c (v', se', t') Hsrc) as Heval.
  pose proof (safe_dse_helper_sound phi c
    (VarSet.union out (sec_post c se))
    v v v' se (agree_on_refl _ _) Heval) as Hsound.
  destruct Hsound as [v_opt [Hopt _]].
  destruct (Eval_lift_trace_sec phi v
    (safe_dse_helper c (VarSet.union out (sec_post c se)) se)
    v_opt Hopt se t) as [sec_opt [trace_opt Hsec_opt]].
  exists (v_opt, sec_opt, trace_opt).
  exact Hsec_opt.
Qed.

(** * 4. Trace Preservation (eval_trace / is_safe_pgm) *)

Lemma eval_trace_liveness_coincidence : forall phi c out v1 v2 t v1' t1,
  eval_trace phi (v1, t) c (v1', t1) ->
  agree_on (liveness c out) v1 v2 ->
  exists v2', eval_trace phi (v2, t) c (v2', t1) /\ agree_on out v1' v2'.
Proof.
  intros phi c out v1 v2 t v1' t1 Heval Hagree.
  destruct (Eval_lift_sec phi v1 t c v1' t1 Heval VarSet.empty)
    as [se1' Heval_sec].
  pose proof (eval_sec_liveness_coincidence phi c out
    (v1, VarSet.empty, t) (v2, VarSet.empty, t) (v1', se1', t1)
    Heval_sec (fun x => eq_refl _) eq_refl Hagree) as Hcoin.
  destruct Hcoin as [ctx2_out [Heval2_sec Hcoincide]].
  destruct Hcoincide as [_ Htrace Hagree_out].
  pose proof (Eval_proj_sec phi (v2, VarSet.empty, t) c ctx2_out Heval2_sec) as Heval2_trace.
  exists (sec_val_of ctx2_out).
  rewrite <- Htrace in Heval2_trace.
  split; [exact Heval2_trace | exact Hagree_out].
Qed.

(* opt_dse doesn't modify the trace. well...
   the trace is not modified. but the final valuation is.
   so I need to be more precise:
 *)

(* eval_trace only updated var that occur in the command. *) 
(* Variables not mentioned in the optimized command are unchanged,
   so public agreement for them follows from initial agreement. *)
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

(* Every traced execution of safe_dse_helper can be matched to an evaluation of the source program with
   the same trace and the same out *)
Lemma opt_safe_dse_helper_trace_complete : forall phi c out ctx ctx_opt secrets,
  eval_trace phi ctx (safe_dse_helper c out secrets) ctx_opt ->
  exists ctx_src,
    eval_trace phi ctx c ctx_src /\
    trace_coincide out ctx_src ctx_opt.
Proof.
  intros phi c out [v t] [v_opt t_opt] secrets Hopt.
  destruct (Eval_lift_sec phi v t (safe_dse_helper c out secrets) v_opt t_opt Hopt secrets)
    as [se_opt Hopt_sec].
  pose proof (safe_dse_helper_sec_complete phi c out secrets
    (v, secrets, t) (v_opt, se_opt, t_opt)
    (sec_env_sub_refl secrets) Hopt_sec) as Hcomplete.
  destruct Hcomplete as [ctx_src_sec [Hsrc_sec Hcoin_sec]].
  exists (sec_val_of ctx_src_sec, sec_trace_of ctx_src_sec).
  split.
  - exact (Eval_proj_sec phi (v, secrets, t) c ctx_src_sec Hsrc_sec).
  - destruct Hcoin_sec as [_ Htrace Hagree].
    constructor; simpl; exact Htrace || exact Hagree.
Qed.

(** ** Main theorem for non inference preservation *)
Lemma opt_safe_dse_core_preserves_safe_pgm : forall phi p secrets,
    is_safe_pgm phi p secrets ->
    is_safe_pgm phi (opt_safe_dse_core p secrets) secrets.
Proof.
  unfold is_safe_pgm, opt_safe_dse_core in *.
  intros phi [c out] secrets [secrets' Hni].
  simpl in *.
  exists (VarSet.union secrets
    (vars_in_cmd (safe_dse_helper c (VarSet.union out (sec_post c secrets)) secrets))).
  unfold non_inference in *.
  intros v1 v2 t_in final_v1 final_v2 trace1 trace2 Hagree Hopt_eval1 Hopt_eval2.

  pose proof (opt_safe_dse_helper_trace_complete _ _ _ _ _ _ Hopt_eval1)
    as Htrace_complete1.
  pose proof (opt_safe_dse_helper_trace_complete _ _ _ _ _ _ Hopt_eval2)
    as Htrace_complete2.
  destruct Htrace_complete1 as [[v1_out trace1_out] [Heval1 Hcoin1]].
  destruct Hcoin1 as [Htrace1 Hagree1].
  destruct Htrace_complete2 as [[v2_out trace2_out] [Heval2 Hcoin2]].
  destruct Hcoin2 as [Htrace2 Hagree2].
  simpl in *.

  specialize (Hni v1 v2 t_in v1_out v2_out trace1_out trace2_out).
  specialize (Hni Hagree Heval1 Heval2).
  split.
  - destruct Hni as [Htrace_equal _].
    congruence.
  - unfold agree_on_public.
    intros x Hx.
    pose proof (eval_trace_frame _ _ _ _ Hopt_eval1 x) as Hframe1.
    pose proof (eval_trace_frame _ _ _ _ Hopt_eval2 x) as Hframe2.
    simpl in *.
    rewrite Hframe1.
    rewrite Hframe2.
    + apply Hagree.
      VarSetDecide.fsetdec.
    + VarSetDecide.fsetdec.
    + VarSetDecide.fsetdec.
Qed.

(** * 5. Putting the Core Proof Together *)

Theorem opt_safe_dse_core_secure : forall phi,
  is_safe_opt phi opt_safe_dse_core.
Proof.
  intros phi.
  unfold is_safe_opt.
  split.
  - apply opt_safe_dse_core_preserves_safe_pgm.
  - apply opt_safe_dse_core_keeps_secrets_secret.
Qed.


(** * 6. Putting it all together to prove dse is secure *)

Theorem opt_safe_dse_secure : forall phi,
  is_safe_opt phi opt_safe_dse.
Proof.
  intros phi.
  change (is_safe_opt phi (compose_opt opt_unskip opt_safe_dse_core)).
  eapply is_safe_opt_compose.
  - apply opt_safe_dse_core_secure.
  - apply opt_unskip_secure.
  - apply opt_safe_dse_core_eval_sec_sound.
Qed.
