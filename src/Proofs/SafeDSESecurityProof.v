Require Import Map.
Require Import VarSets.
Require Import Language.Main.
Require Import Language.Analysis.
Require Import Language.Optimizations.Safe.DSE.
Require Import Proofs.UnskipProofs.
Require Import Proofs.UnsafeDSEProofs.
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
    + exists (v2 $+ (x, interp_arith e v1)). 
      destruct_agree Hagree. split.
      * constructor. simpl. apply interp_arith_agree; apply agree_on_sym; eauto.
      * apply agree_on_remove_add; eauto.
    + exists (v2 $+ (x, interp_arith e v2)).
      split.
      * constructor; eauto.
      * apply agree_on_dead_update_both; eauto.
  - destruct (VarSet.mem x out) eqn:Hx.
    + exists (v2 $+ (x, interp_arith e1 v1)).
      destruct_agree Hagree.
      split.
      * econstructor; eauto.
        simpl.
        assert (interp_arith cond v2 = interp_arith cond v1).
        {
          apply interp_arith_agree. apply agree_on_sym. assumption.
        }
        congruence.
        simpl.
        apply interp_arith_agree; apply agree_on_sym; eauto.
      * apply agree_on_remove_add; eauto.
    + destruct (interp_arith cond v2) eqn:Hc2. (* evaluated var not live, so we don't care about this other branch: both are fine*)
      * exists (v2 $+ (x, interp_arith e2 v2)).
        split; [ eapply EvalTraceCmovFalse; auto | ].
        apply agree_on_dead_update_both; eauto.
      * exists (v2 $+ (x, interp_arith e1 v2)).
        split; [ eapply EvalTraceCmovTrue; eauto| ].
        apply agree_on_dead_update_both; eauto.
  - destruct (VarSet.mem x out) eqn:Hx.
    + exists (v2 $+ (x, interp_arith e2 v1)).
      destruct_agree Hagree.
      split.
      * eapply EvalTraceCmovFalse; eauto.
        simpl.
        assert (interp_arith cond v2 = interp_arith cond v1).
        {
          apply interp_arith_agree. apply agree_on_sym. assumption.
        }
        congruence.
        simpl.
        apply interp_arith_agree; apply agree_on_sym; eauto.
      * unfold agree_on. intros.
        destruct (x ==v x0).
        -- subst. repeat rewrite lookup_add_eq; reflexivity.
        -- eapply agree_on_update_both; [apply Hagree0|]. rewrite VarSetEqProps.remove_mem_2; eauto.
    + destruct (interp_arith cond v2) eqn:Hc2. (* evaluated var not live, so we don't care about this other branch: both are fine*)
      * exists (v2 $+ (x, interp_arith e2 v2)).
        split; [ eapply EvalTraceCmovFalse; auto | ].
        apply agree_on_dead_update_both; eauto.
      * exists (v2 $+ (x, interp_arith e1 v2)).
        split; [ eapply EvalTraceCmovTrue; eauto| ].
        apply agree_on_dead_update_both; eauto.
  - destruct_agree Hagree.
    exists (v2 $+ (x, a)).
    split.
    + econstructor; eauto. simpl.
      assert (interp_arith e1 v1 = interp_arith e1 v2 /\ interp_arith e2 v1 = interp_arith e2 v2) as [<- <-].
      {
        split; apply interp_arith_agree; assumption.
      }
      exact Heval.
    + apply agree_on_remove_add; eauto.
  - destruct ctx1 as [v_1 t_1].
    specialize (IHHeval1 _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) _ _ Hagree).
    destruct IHHeval1 as [v2_mid [IHHeval1 IHHagree1]].
    specialize (IHHeval2 _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) _ _ IHHagree1).
    destruct IHHeval2 as [v2_final [IHHeval2 IHHagree2]].
    exists v2_final. split; [econstructor|]; eauto.
  - destruct_agree Hagree.
    specialize (IHHeval _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) _ _ Hagree2).
    destruct IHHeval as [v2' [IHHeval IHHagree]].
    exists v2'. split; [eapply EvalTraceIfTrue|]; eauto.
    simpl.
    assert (interp_arith e v1 = interp_arith e v2).
    {
      apply interp_arith_agree; eauto.
    }
    congruence.
  - destruct_agree Hagree.
    specialize (IHHeval _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) _ _ Hagree3).
    destruct IHHeval as [v2' [IHHeval IHHagree]].
    exists v2'. split; [eapply EvalTraceIfFalse|]; eauto.
    simpl.
    assert (interp_arith e v1 = interp_arith e v2).
    {
      apply interp_arith_agree; eauto.
    }
    congruence.
  - destruct ctx' as [v_1 t_1].
    pose proof (liveness_while_body_closed body e out) as Hliveness_body.
    unfold liveness in Hliveness_body.
    fold liveness in Hliveness_body.
    pose proof (agree_on_subset _ _ _ _ Hliveness_body Hagree) as Hagree_body.
    specialize (IHHeval1 _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) _ _ Hagree_body).
    destruct IHHeval1 as [v2_mid [IHHeval1 IHHagree1]].
    specialize (IHHeval2 _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) _ _ IHHagree1).
    destruct IHHeval2 as [v2_final [IHHeval2 IHHagree2]].
    exists v2_final. split; [|exact IHHagree2].
    destruct_agree_while Hagree.
    eapply EvalTraceWhileTrue; eauto.
    simpl.
    assert (interp_arith e v1 = interp_arith e v2)
      by (apply interp_arith_agree; eauto).
    congruence.

  - destruct_agree_while Hagree.
    exists v2. split; [eapply EvalTraceWhileFalse|]; eauto.
    + simpl.
      assert (interp_arith e v1' = interp_arith e v2).
      {
        apply interp_arith_agree; eauto.
      }
      congruence.
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
    induction c; simpl; unfold lifts_to in *; intros.
    - subst. firstorder. 
    - destruct (VarSet.mem s out) eqn:Hout.
      + inversion H; subst. firstorder.
      + destruct (sec_lookup secrets s) eqn:Hsecrets.
        * inversion H. subst. 
          destruct ctx_opt as [v_opt t_opt].
          exists (v_opt $+ (s, interp_arith e v_opt), t_opt).
          repeat split;
          simpl in *.
          econstructor; eauto.
          apply agree_on_sym;
          eapply agree_on_update_out; eauto.
        * firstorder.
    - firstorder.
    - destruct (VarSet.mem s out) eqn:Hout.
      + inversion H; subst; firstorder.
      + destruct (sec_lookup secrets s) eqn:Hsecrets.
        * inversion H. subst. 
          destruct ctx_opt as [v_opt t_opt].
          destruct (interp_arith e v_opt) eqn:Hinterp.
          -- exists (v_opt $+ (s, interp_arith e1 v_opt), t_opt).
             repeat split; simpl.
             eapply EvalTraceCmovFalse; eauto.
             all: apply agree_on_sym;
             eapply agree_on_update_out; eauto.
          -- exists (v_opt $+ (s, interp_arith e0 v_opt), t_opt).
             repeat split; simpl.
             eapply EvalTraceCmovTrue; eauto.
             all: apply agree_on_sym;
             eapply agree_on_update_out; eauto.
        * firstorder.
    - inversion H; subst. 
      specialize (IHc1 _ _ _ _ H3). destruct IHc1 as [ctx_out1 IHc1].
      specialize (IHc2 _ _ _ _ H5). destruct IHc2 as [ctx_out2 IHc2].
      intuition.
      rewrite <- H1.
      pose proof eval_trace_liveness_coincidence as Heval_coincide.
      destruct ctx1, ctx_out1, ctx_out2.
      apply agree_on_sym in H7.
      specialize (Heval_coincide _ _ _ _ _ _ _ _ H2 H7).
      destruct Heval_coincide as [v_out_final Heval_coincide].
      exists (v_out_final,l1).
      repeat split.
      econstructor.
      + apply H0.
      + intuition. simpl in H6. rewrite H6. apply H4.
      + simpl in *.
        destruct Heval_coincide.
        apply agree_on_sym in H9.
        eapply agree_on_trans; eauto.
    - inversion H; subst.
      + specialize (IHc1 _ _ _ _ H7).
        destruct IHc1 as [ctx_out IHc1].
        exists ctx_out. intuition.
        eapply EvalTraceIfTrue; eauto.
      + specialize (IHc2 _ _ _ _ H6).
        destruct IHc2 as [ctx_out [Heval [Htrace Hagree]]].
        exists ctx_out. 
        repeat split; eauto. 
        eapply EvalTraceIfFalse; eauto.
    - apply safe_dse_while_complete with (secrets := secrets).
        * intros. unfold lifts_to. eapply IHc. apply H0.
        * apply H.
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
    pose proof opt_unskip_preserves_safe_pgm as Hunskip.
    unfold is_safe_pgm, opt_safe_dse in *. 
    intros phi [c out] secrets [secrets' Hni].
    specialize (Hunskip phi ((safe_dse_helper c out secrets), out) secrets).
    destruct Hunskip as [secrets_unskip Hunskip]; eauto.
    simpl in *.
    (* We overestimate the new secrets to use all possible values that could be written*)
    (* This satisfies agree on secret and takes care of possible changes*)
    exists (VarSet.union secrets (vars_in_cmd (safe_dse_helper c out secrets))).
    unfold non_inference in *.
    intros v1 v2 t_in final_v1 final_v2 trace1 trace2 Hagree Hopt_eval1 Hopt_eval2.

    pose proof opt_safe_dse_helper_trace_complete as Htrace_complete1.
    pose proof Htrace_complete1 as Htrace_complete2.
    specialize (Htrace_complete1  _ _ _ _ _ _ Hopt_eval1).
    destruct Htrace_complete1 as [[v1_out trace1_out] [Heval1 [Htrace1 Hagree1]]].
    specialize (Htrace_complete2  _ _ _ _ _ _ Hopt_eval2).
    destruct Htrace_complete2 as [[v2_out trace2_out] [Heval2 [Htrace2 Hagree2]]].
    simpl in *.
    specialize (Hni v1 v2 t_in v1_out v2_out trace1_out trace2_out).
    specialize (Hni Hagree Heval1 Heval2).
    split.
    - destruct Hni as [Htrace_equal Hagree_out].
      congruence.
    - unfold agree_on_public.
      intros x Hx.
      pose proof eval_trace_frame as Hetf1.
      specialize (Hetf1 _ _  _ _ Hopt_eval1).
      pose proof eval_trace_frame as Hetf2.
      specialize (Hetf2 _ _  _ _ Hopt_eval2).  
      simpl in *.
      rewrite Hetf1.
      rewrite Hetf2.
      apply Hagree.
      all: VarSetDecide.fsetdec.
Qed.
