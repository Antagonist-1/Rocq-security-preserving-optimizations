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

Lemma eval_trace_liveness_coincidence : forall phi c out v1 v2 t v1' t1,
  eval_trace phi (v1, t) c (v1', t1) ->
  agree_on (liveness c out) v1 v2 ->
  exists v2', eval_trace phi (v2, t) c (v2', t1) /\ agree_on out v1' v2'.
Proof.
Admitted.

(* opt_dse doesn't modify the trace. well...
the trace is not modified. but the final valuation is.
so I need to be more precise:
*)

Lemma opt_safe_dse_helper_trace_complete : forall phi c out ctx ctx_opt secrets,
    eval_trace phi ctx (safe_dse_helper c out secrets) ctx_opt ->
    exists ctx_out,
        eval_trace phi ctx c ctx_out /\ 
        trace_of ctx_out = trace_of ctx_opt /\
        agree_on out (val_of ctx_out) (val_of ctx_opt).
Proof.
    induction c; simpl; intros.
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
        pose proof eval_trace_liveness_coincidence as Heval_coin.
        destruct ctx1, ctx_out1, ctx_out2.
        apply agree_on_sym in H7.
        specialize (Heval_coin _ _ _ _ _ _ _ _ H2 H7).
        destruct Heval_coin as [v_out_final Heval_coin].
        exists (v_out_final,l1).
        repeat split.
        econstructor.
        + apply H0.
        + intuition. simpl in H6. rewrite H6. apply H4.
        + simpl in *.
          destruct Heval_coin.
          apply agree_on_sym in H9.
          eapply agree_on_trans; eauto.
      - inversion H; subst.
    Admitted.
           
          
        
        

          
          



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
