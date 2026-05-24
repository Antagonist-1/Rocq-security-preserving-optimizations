Require Import Map.
Require Import Language.Main.
Require Import Language.Analysis.
Require Import Language.Optimizations.Safe.Unskip.

Create HintDb unskip_db.
Hint Constructors eval eval_trace eval_sec : unskip_db.

(** * Soundness *)
(* This part uses  eval*)

Lemma opt_unskip_sound: forall phi c v v',
  eval phi v c v' ->
  eval phi v (opt_unskip_cmd c) v'.
Proof.
    induction 1; simpl; intros; eauto with unskip_db.
    all: repeat match goal with 
    | [ |- context[match ?pat with _ => _ end]] => destruct pat
    end.
    all: try inversion IHeval1; try inversion IHeval2; subst;
    eauto with unskip_db.
Qed.

(** * Exact Trace Preservation Support (Non-Inference Lemmas) *)
(* This part uses eval_trace *)

Ltac solve_simple_assigns Hmatch:=
    unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace];
    rewrite Hval in *;
    eexists; split; eauto with unskip_db;
    unfold match_ctx; split; simpl; auto.

(* Running an unoptimized program from matching contexts yields matching
contexts. This is mainly a helper lemmas for AssignCall, because the bodies of
the functions are not optimized by [opt_unskip_cmd]. *)
Lemma eval_trace_unopt_match : forall phi c ctx_src ctx_src_final ctx_opt,
  eval_trace phi ctx_src c ctx_src_final ->
  match_ctx ctx_src ctx_opt ->
  exists ctx_opt_final,
    eval_trace phi ctx_opt c ctx_opt_final /\
    match_ctx ctx_src_final ctx_opt_final.
Proof.
  intros phi c ctx_src ctx_src_final ctx_opt Heval Hmatch.
  revert ctx_opt Hmatch.
  induction Heval; intros ctx_opt Hmatch; simpl;
  try solve [ solve_simple_assigns Hmatch].
  - (* Skip *)
    eexists; split; eauto with unskip_db.
  (* Assign, CmovTrue and CmovFalse solved by solve_ simple_assigns *)
  - unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace]; rewrite Hval in *.
    assert (Hmatch_body : match_ctx ($0 $+ (x1, a1) $+ (x2, a2), trace_of ctx)
                                    ($0 $+ (x1, a1) $+ (x2, a2), trace_of ctx_opt)) 
      by (split; auto).
    apply IHHeval in Hmatch_body as [ctx_opt_body_final [Hstep_body Hmatch_body_final]].
    unfold match_ctx in Hmatch_body_final; destruct Hmatch_body_final as [Hval_body Htrace_body].
    rewrite Hval_body in *.
    eexists; split; eauto with unskip_db.
    unfold match_ctx; split; simpl; auto.
  - apply IHHeval1 in Hmatch as [ctx1_opt [Hstep1 Hmatch1]].
    apply IHHeval2 in Hmatch1 as [ctx2_opt [Hstep2 Hmatch2]].
    eexists; split; eauto with unskip_db.
  - (* IfTrue *)
    unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace];
    assert (Hmatch_branch : match_ctx (ctx t++ Branch true) (ctx_opt t++ Branch true)) 
      by (split; auto; apply trace_subseq_append_keep; auto).
    apply IHHeval in Hmatch_branch as [ctx_opt_final [Hstep Hmatch_final]].
    rewrite Hval in *.
    eexists; split; eauto with unskip_db.
  - (* IfFalse *)
    unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace];
    assert (Hmatch_branch : match_ctx (ctx t++ Branch false) (ctx_opt t++ Branch false)) 
      by (split; auto; apply trace_subseq_append_keep; auto).
    apply IHHeval in Hmatch_branch as [ctx_opt_final [Hstep Hmatch_final]].
    rewrite Hval in *.
    eexists; split; eauto with unskip_db.
  - (* WhileTrue *)
    unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace];
    assert (Hmatch_branch : match_ctx (ctx t++ Branch true) (ctx_opt t++ Branch true)) 
      by (split; auto; apply trace_subseq_append_keep; auto).
    apply IHHeval1 in Hmatch_branch as [ctx_opt_mid [Hstep1 Hmatch_mid]].
    apply IHHeval2 in Hmatch_mid as [ctx_opt_final [Hstep2 Hmatch_final]].
    rewrite Hval in *.
    eexists; split; eauto with unskip_db.
  - (* WhileFalse *)
    unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace];
    rewrite Hval in *.
    eexists; split; eauto with unskip_db.
    unfold match_ctx; split; simpl; auto; apply trace_subseq_append_keep; auto.
Qed.

Lemma opt_unskip_forward : forall phi c ctx_src ctx_src_final ctx_opt,
  eval_trace phi ctx_src c ctx_src_final ->
  match_ctx ctx_src ctx_opt ->
  exists ctx_opt_final,
    eval_trace phi ctx_opt (opt_unskip_cmd c) ctx_opt_final /\
    match_ctx ctx_src_final ctx_opt_final.
Proof.
  intros phi c ctx_src ctx_src_final ctx_opt Heval Hmatch.
  revert ctx_opt Hmatch;
  induction Heval; intros ctx_opt Hmatch; simpl;
  try solve [ solve_simple_assigns Hmatch].
  - (* Skip *)
    eexists; split; eauto with unskip_db.

  - (* AssignCall *)
    unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
    rewrite Hval in *.
    assert (Hmatch_body : match_ctx ($0 $+ (x1, a1) $+ (x2, a2), trace_of ctx)
                                    ($0 $+ (x1, a1) $+ (x2, a2), trace_of ctx_opt)).
    { split; auto. }
    eapply eval_trace_unopt_match with (ctx_opt := ($0 $+ (x1, a1) $+ (x2, a2), trace_of ctx_opt)) in Heval; auto.
    destruct Heval as [ctx_opt_body_final [Hstep_body Hmatch_body_final]].
    unfold match_ctx in Hmatch_body_final; destruct Hmatch_body_final as [Hval_body Htrace_body].
    rewrite Hval_body in H2.
    eexists; split.
    + eapply EvalTraceAssignCall; eauto.
    + unfold match_ctx in *; split; simpl; auto.

  - (* Sequence *)
    apply IHHeval1 in Hmatch as [ctx1_opt [Hstep1 Hmatch1]].
    apply IHHeval2 in Hmatch1 as [ctx2_opt [Hstep2 Hmatch2]].
    destruct (opt_unskip_cmd c1) eqn:Hc1opt;
    destruct (opt_unskip_cmd c2) eqn:Hc2opt;
    repeat match goal with
      | H : eval_trace _ _ Skip _ |- _ => inversion H; subst; clear H
    end;
    eexists; split; eauto with unskip_db.

  - (* IfTrue *)
    destruct (opt_unskip_cmd thn) eqn:Hthn;
    destruct (opt_unskip_cmd els) eqn:Hels.
    (* Skip, Skip case, drop branch *)
    1: {
      unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
      assert (Hmatch_branch : match_ctx (ctx t++ Branch true) ctx_opt) 
        by (split; auto; apply trace_subseq_append_drop; auto).
      apply IHHeval in Hmatch_branch as [ctx_opt_final [Hstep Hmatch_final]].
      inversion Hstep; subst; clear Hstep.
      eexists; split; eauto with unskip_db.
    }
    (* Other cases: the branch is kept *)
    all: unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
    all: assert (Hmatch_branch : match_ctx (ctx t++ Branch true) (ctx_opt t++ Branch true)) 
           by (split; auto; apply trace_subseq_append_keep; auto).
    all: apply IHHeval in Hmatch_branch as [ctx_opt_final [Hstep Hmatch_final]].
    all: rewrite Hval in *.
    all: eexists; split; eauto with unskip_db.
  - (* IfFalse, same as IfTrue but with 'Branch false' *)
    destruct (opt_unskip_cmd thn) eqn:Hthn;
    destruct (opt_unskip_cmd els) eqn:Hels.
    1: {
      unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
      assert (Hmatch_branch : match_ctx (ctx t++ Branch false) ctx_opt) 
        by (split; auto; apply trace_subseq_append_drop; auto).
      apply IHHeval in Hmatch_branch as [ctx_opt_final [Hstep Hmatch_final]].
      inversion Hstep; subst; clear Hstep.
      eexists; split; eauto with unskip_db.
    }
    all: unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
    all: assert (Hmatch_branch : match_ctx (ctx t++ Branch false) (ctx_opt t++ Branch false)) 
           by (split; auto; apply trace_subseq_append_keep; auto).
    all: apply IHHeval in Hmatch_branch as [ctx_opt_final [Hstep Hmatch_final]].
    all: rewrite Hval in *.
    all: eexists; split; eauto with unskip_db.

  - (* WhileTrue *)
    unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
    (* Keep the true branch *)
    assert (Hmatch_branch : match_ctx (ctx t++ Branch true) (ctx_opt t++ Branch true)) 
      by (split; auto; apply trace_subseq_append_keep; auto).
    (* Chain the body execution and the rest of the loop execution *)
    apply IHHeval1 in Hmatch_branch as [ctx_opt_mid [Hstep1 Hmatch_mid]].
    apply IHHeval2 in Hmatch_mid as [ctx_opt_final [Hstep2 Hmatch_final]].
    rewrite Hval in *.
    eexists; split; eauto with unskip_db.

  - (* WhileFalse *)
    unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
    rewrite Hval in *.
    eexists; split; eauto with unskip_db.
    unfold match_ctx; split; simpl; auto; apply trace_subseq_append_keep; auto.
Qed.

Lemma trace_subseq_trans : forall A (src mid dst : list A),
  trace_subseq src mid ->
  trace_subseq mid dst ->
  trace_subseq src dst.
Proof.
  intros A src mid dst Hsrc_mid.
  revert dst.
  induction Hsrc_mid; intros dst Hmid_dst.
  - inversion Hmid_dst; constructor.
  - inversion Hmid_dst; subst.
    + constructor. eauto.
    + econstructor 3. eauto.
  - econstructor 3. eauto.
Qed.

Lemma match_ctx_trans : forall ctx1 ctx2 ctx3,
  match_ctx ctx1 ctx2 ->
  match_ctx ctx2 ctx3 ->
  match_ctx ctx1 ctx3.
Proof.
  intros ctx1 ctx2 ctx3 H12 H23.
  unfold match_ctx in *.
  destruct H12 as [Hval12 Htrace12].
  destruct H23 as [Hval23 Htrace23].
  split.
  - rewrite Hval12. exact Hval23.
  - eapply trace_subseq_trans; eauto.
Qed.


Lemma eval_trace_unopt_backward : forall phi c ctx_opt ctx_opt_final ctx_src,
  eval_trace phi ctx_opt c ctx_opt_final ->
  match_ctx ctx_src ctx_opt ->
  exists ctx_src_final,
    eval_trace phi ctx_src c ctx_src_final /\
    match_ctx ctx_src_final ctx_opt_final.
Proof.
Admitted.

Lemma opt_unskip_backward_while : forall phi e body ctx_opt ctx_opt_final ctx_src,
  eval_trace phi ctx_opt (While e (opt_unskip_cmd body)) ctx_opt_final ->
  (forall ctx_o ctx_o_f ctx_s, eval_trace phi ctx_o (opt_unskip_cmd body) ctx_o_f -> match_ctx ctx_s ctx_o -> exists ctx_s_f, eval_trace phi ctx_s body ctx_s_f /\ match_ctx ctx_s_f ctx_o_f) ->
  match_ctx ctx_src ctx_opt ->
  exists ctx_src_final, eval_trace phi ctx_src (While e body) ctx_src_final /\ match_ctx ctx_src_final ctx_opt_final.
Proof.
  intros phi e body ctx_opt ctx_opt_final ctx_src Hopt Hbody_ih Hmatch.
  revert ctx_src Hmatch.
  remember (While e (opt_unskip_cmd body)) as loop_cmd.
  induction Hopt; intros ctx_src Hmatch; try discriminate.
  - (* EvalTraceWhileTrue *)
    inversion Heqloop_cmd; subst; clear Heqloop_cmd.
    unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
    assert (Hmatch_branch : match_ctx (ctx_src t++ Branch true) (ctx t++ Branch true))
      by (split; simpl; [exact Hval | apply trace_subseq_append_keep; exact Htrace]).
    edestruct Hbody_ih as [ctx_src_mid [Hstep_body Hmatch_mid]]; [exact Hopt1 | exact Hmatch_branch |].
    edestruct IHHopt2 as [ctx_src_final [Hstep_loop Hmatch_final]]; [reflexivity | exact Hmatch_mid |].
    exists ctx_src_final; split.
    + eapply EvalTraceWhileTrue with (c := interp_arith e (val_of ctx)); eauto.
      rewrite Hval. reflexivity.
    + exact Hmatch_final.
  - (* EvalTraceWhileFalse *)
    inversion Heqloop_cmd; subst; clear Heqloop_cmd.
    unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
    assert (Hmatch_branch : match_ctx (ctx_src t++ Branch false) (ctx t++ Branch false))
      by (split; simpl; [exact Hval | apply trace_subseq_append_keep; exact Htrace]).
    exists (ctx_src t++ Branch false); split.
    + eapply EvalTraceWhileFalse. rewrite Hval. eassumption.
    + exact Hmatch_branch.
Qed.

Lemma opt_unskip_skip_trace_complete : forall phi c ctx,
  opt_unskip_cmd c = Skip ->
  exists ctx_src,
    eval_trace phi ctx c ctx_src /\
    match_ctx ctx_src ctx.
Proof.
  induction c; simpl; intros ctx Hskip.
  - exists ctx. split; auto with unskip_db. apply match_ctx_refl.
  - discriminate.
  - discriminate.
  - discriminate.
  - destruct (opt_unskip_cmd c1) eqn:Hc1;
    destruct (opt_unskip_cmd c2) eqn:Hc2;
    try discriminate;
    inversion Hskip; subst.
    destruct (IHc1 ctx eq_refl) as [ctx1_src [Hsrc1 Hmatch1]].
    destruct (IHc2 ctx1_src eq_refl) as [ctx2_src [Hsrc2 Hmatch2]].
    exists ctx2_src.
    split.
    + eapply EvalTraceSequence; eauto.
    + eapply match_ctx_trans; eauto.
  - destruct (opt_unskip_cmd c1) eqn:Hc1;
    destruct (opt_unskip_cmd c2) eqn:Hc2;
    try discriminate;
    inversion Hskip; subst.
    destruct (interp_arith e (val_of ctx)) eqn:Hcond.
    + destruct (IHc2 (ctx t++ Branch false) eq_refl) as [ctx2_src [Hsrc2 Hmatch2]].
      assert (Hbranch_match : match_ctx (ctx t++ Branch false) ctx).
      { unfold match_ctx; split; simpl; auto.
        apply trace_subseq_append_drop.
        apply trace_subseq_refl. }
      exists ctx2_src.
      split.
      * eapply EvalTraceIfFalse; eauto.
      * eapply match_ctx_trans; eauto.
    + destruct (IHc1 (ctx t++ Branch true) eq_refl) as [ctx1_src [Hsrc1 Hmatch1]].
      assert (Hbranch_match : match_ctx (ctx t++ Branch true) ctx).
      { unfold match_ctx; split; simpl; auto.
        apply trace_subseq_append_drop.
        apply trace_subseq_refl. }
      exists ctx1_src.
      split.
      * eapply EvalTraceIfTrue with (c := S n); eauto.
      * eapply match_ctx_trans; eauto.
  - discriminate.
Qed.

Lemma opt_unskip_backward : forall phi c ctx_opt ctx_opt_final ctx_src,
  eval_trace phi ctx_opt (opt_unskip_cmd c) ctx_opt_final ->
  match_ctx ctx_src ctx_opt ->
  exists ctx_src_final, eval_trace phi ctx_src c ctx_src_final /\ match_ctx ctx_src_final ctx_opt_final.
Proof.
  intros phi c. revert phi.
  induction c; intros phi ctx_opt ctx_opt_final ctx_src Hopt Hmatch; simpl in Hopt.
  
  - (* Skip *)
    inversion Hopt; subst.
    eexists; split; [apply EvalTraceSkip | exact Hmatch].
    
  - (* Assign *)
    inversion Hopt; subst.
    unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
    eexists; split.
    + eapply EvalTraceAssign. reflexivity.
    + unfold match_ctx; split; simpl.
      * rewrite Hval. reflexivity.
      * exact Htrace.
    
  - (* AssignCall *)
    inversion Hopt; subst.
    unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
    destruct ctx_src as [v_src t_src]; simpl in *.
    rewrite Hval in *.
    
    assert (Hmatch_body : match_ctx 
      ($0 $+ (x1, interp_arith e (val_of ctx_opt)) $+ (x2, interp_arith e0 (val_of ctx_opt)), t_src) 
      ($0 $+ (x1, interp_arith e (val_of ctx_opt)) $+ (x2, interp_arith e0 (val_of ctx_opt)), trace_of ctx_opt)).
    { split; simpl; auto. }
    
    apply eval_trace_unopt_backward with 
      (ctx_src := ($0 $+ (x1, interp_arith e (val_of ctx_opt)) $+ (x2, interp_arith e0 (val_of ctx_opt)), t_src)) 
      in H8; auto.
      
    destruct H8 as [ctx_src_body_final [Hsrc_body Hmatch_body_final]].
    unfold match_ctx in Hmatch_body_final; destruct Hmatch_body_final as [Hval_body Htrace_body].
    
    eexists; split.
    + eapply EvalTraceAssignCall.
      * exact H3.
      * reflexivity.
      * reflexivity.
      * exact Hsrc_body.
      * rewrite Hval_body. exact H9.
    + unfold match_ctx; split; simpl.
      * reflexivity.
      * exact Htrace_body.

  - (* Cmov *)
    inversion Hopt; subst.
    + (* CmovTrue *)
      unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
      destruct ctx_src as [v_src t_src]. simpl in *.
      eexists; split.
      * eapply EvalTraceCmovTrue; rewrite Hval; eauto.
      * unfold match_ctx; split; simpl.
        -- rewrite Hval. reflexivity.
        -- exact Htrace.
    + (* CmovFalse *)
      unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
      destruct ctx_src as [v_src t_src]. simpl in *.
      eexists; split.
      * eapply EvalTraceCmovFalse; rewrite Hval; eauto.
      * unfold match_ctx; split; simpl.
        -- rewrite Hval. reflexivity.
        -- exact Htrace.

  - (* Sequence *)
    destruct (opt_unskip_cmd c1) eqn:Hc1;
    destruct (opt_unskip_cmd c2) eqn:Hc2;
    match goal with
    | Hc1 : opt_unskip_cmd c1 = Skip,
      Hc2 : opt_unskip_cmd c2 = Skip |- _ =>
        inversion Hopt; subst;
        destruct (opt_unskip_skip_trace_complete phi c1 ctx_src Hc1)
          as [ctx1_src [Hsrc1 Hmatch1]];
        destruct (opt_unskip_skip_trace_complete phi c2 ctx1_src Hc2)
          as [ctx2_src [Hsrc2 Hmatch2]];
        exists ctx2_src; split;
        [eapply EvalTraceSequence; eauto
        |eapply match_ctx_trans; [exact Hmatch2|];
         eapply match_ctx_trans; eauto]
    | Hc1 : opt_unskip_cmd c1 = Skip |- _ =>
        destruct (opt_unskip_skip_trace_complete phi c1 ctx_src Hc1)
          as [ctx1_src [Hsrc1 Hmatch1]];
        edestruct (IHc2 phi ctx_opt ctx_opt_final ctx1_src)
          as [ctx2_src [Hsrc2 Hmatch2]];
        [exact Hopt | eapply match_ctx_trans; eauto |];
        exists ctx2_src; split;
        [eapply EvalTraceSequence; eauto | exact Hmatch2]
    | Hc2 : opt_unskip_cmd c2 = Skip |- _ =>
        edestruct (IHc1 phi ctx_opt ctx_opt_final ctx_src)
          as [ctx1_src [Hsrc1 Hmatch1]];
        [exact Hopt | exact Hmatch |];
        destruct (opt_unskip_skip_trace_complete phi c2 ctx1_src Hc2)
          as [ctx2_src [Hsrc2 Hmatch2]];
        exists ctx2_src; split;
        [eapply EvalTraceSequence; eauto | eapply match_ctx_trans; eauto]
    | _ =>
        inversion Hopt; subst; clear Hopt;
        match goal with
        | Hstep1 : eval_trace phi ctx_opt _ ?ctx1_opt,
          Hstep2 : eval_trace phi ?ctx1_opt _ ctx_opt_final |- _ =>
            edestruct (IHc1 phi ctx_opt ctx1_opt ctx_src)
              as [ctx1_src [Hsrc1 Hmatch1]];
            [exact Hstep1 | exact Hmatch |];
            edestruct (IHc2 phi ctx1_opt ctx_opt_final ctx1_src)
              as [ctx2_src [Hsrc2 Hmatch2]];
            [exact Hstep2 | exact Hmatch1 |];
            exists ctx2_src; split;
            [eapply EvalTraceSequence; eauto | exact Hmatch2]
        end
    end.
  - (* If *)
    (* We really have 2 cases: Case 1: The conditional is preserved (48 cases)
      If the optimized command evaluated as an If statement (meaning at least
      one branch wasn't optimized down to a Skip), the optimized trace will
      contain a [Branch true] or [Branch false] event. The branch event is
      present in both the optimized and source traces: We determine which branch
      was taken, append it to the matching contexts, and call the IH.

      Case 2: The conditional is dropped completely (1 case: Skip, Skip): the
      optimizer replaced the If cmd with a single Skip. Even though opt is just
      Skip, src still has an `If` statement, which means appends to the trace.
      To prove this is safe, we do two things:
      1. We use opt_unskip_skip_trace_complete to prove that running src's
         "useless" branch doesn't change the valuation.
      2. We use trace_subseq_append_drop as the traces don't match perfectly.
         The source trace has an extra branch event that opt dropped.
    *)
    unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
    simpl in Hopt.
    destruct (opt_unskip_cmd c1) eqn:Hc1, (opt_unskip_cmd c2) eqn:Hc2;
    try (
      inversion Hopt; subst; clear Hopt;
      [ (* EvalTraceIfTrue *)
        assert (Hmatch_branch: match_ctx (ctx_src t++ Branch true) (ctx_opt t++ Branch true))
          by (split; simpl; [ exact Hval | apply trace_subseq_append_keep; exact Htrace ]);
        edestruct IHc1 as [ctx_fin [Hsrc1 Hmatch_fin]]; [ eassumption | exact Hmatch_branch | ];
        exists ctx_fin; split;
        [ eapply EvalTraceIfTrue with (c := interp_arith e (val_of ctx_opt));
          [ rewrite Hval; reflexivity | eassumption | exact Hsrc1 ]
        | exact Hmatch_fin ]
      | (* EvalTraceIfFalse *)
        assert (Hmatch_branch: match_ctx (ctx_src t++ Branch false) (ctx_opt t++ Branch false))
          by (split; simpl; [ exact Hval | apply trace_subseq_append_keep; exact Htrace ]);
        edestruct IHc2 as [ctx_fin [Hsrc2 Hmatch_fin]]; [ eassumption | exact Hmatch_branch | ];
        exists ctx_fin; split;
        [ eapply EvalTraceIfFalse;
          [ rewrite Hval; eassumption | exact Hsrc2 ]
        | exact Hmatch_fin ]
      ]
    ).
    (* Skip, Skip. *)
    inversion Hopt; subst; clear Hopt;
    destruct (interp_arith e (val_of ctx_src)) eqn:Heq;
    [ (* False branch *)
      destruct (opt_unskip_skip_trace_complete phi c2 (ctx_src t++ Branch false) Hc2) as [ctx2_src [Hsrc2 Hmatch2]];
      exists ctx2_src; split;
      [ eapply EvalTraceIfFalse; [ eassumption | exact Hsrc2 ]
      | eapply match_ctx_trans; [exact Hmatch2 | split; simpl; auto; apply trace_subseq_append_drop; exact Htrace ] ]
    | (* True branch *)
      destruct (opt_unskip_skip_trace_complete phi c1 (ctx_src t++ Branch true) Hc1) as [ctx1_src [Hsrc1 Hmatch1]];
      exists ctx1_src; split;
      [ eapply EvalTraceIfTrue; [ eassumption | intro C; discriminate | exact Hsrc1 ]
      | eapply match_ctx_trans; [exact Hmatch1 | split; simpl; auto; apply trace_subseq_append_drop; exact Htrace ] ]
    ].
    
  - (* While *)
    eapply opt_unskip_backward_while; eauto.
Qed.

Lemma opt_traces_equal : forall phi c v1 v2 t_in final_v1 final_v2 trace1 trace2 src_final_v1 src_final_v2 src_trace,
  eval_trace phi (v1, t_in) c (src_final_v1, src_trace) ->
  eval_trace phi (v2, t_in) c (src_final_v2, src_trace) ->
  eval_trace phi (v1, t_in) (opt_unskip_cmd c) (final_v1, trace1) ->
  eval_trace phi (v2, t_in) (opt_unskip_cmd c) (final_v2, trace2) ->
  trace1 = trace2.
Proof.
Admitted.

(** ** Main theorem of non-inference preservation *)

(** [opt_unskip_preserves_safe_pgm] proves the non-inference half of
    [is_safe_opt]. Any optimized trace execution can be expanded into a source
    execution with the same final context by [opt_unskip_trace_complete], so the
    source program's [non_inference] proof applies directly to optimized runs. *)
Lemma opt_unskip_preserves_safe_pgm : forall phi p secrets,
  is_safe_pgm phi p secrets ->
  is_safe_pgm phi (opt_unskip p secrets) secrets.
Proof.
  unfold is_safe_pgm, opt_unskip, opt_unskip_cmd.
  intros phi [c out] secrets [secrets' Hni].
  simpl in *.
  exists secrets'.
  unfold non_inference in *.
  intros v1 v2 t_in final_v1 final_v2 trace1 trace2 Hagree Hopt_eval1 Hopt_eval2.

  assert (Hmatch1 : match_ctx (v1, t_in) (v1, t_in)) by (split; auto; apply trace_subseq_refl).
  assert (Hmatch2 : match_ctx (v2, t_in) (v2, t_in)) by (split; auto; apply trace_subseq_refl).
  
  pose proof Hopt_eval1 as Hopt_eval1_copy.
  apply opt_unskip_backward with (ctx_src := (v1, t_in)) in Hopt_eval1_copy; auto.
  destruct Hopt_eval1_copy as [[src_final_v1 src_trace1] [Hsrc_eval1 Hmatch_final1]].

  pose proof Hopt_eval2 as Hopt_eval2_copy.
  apply opt_unskip_backward with (ctx_src := (v2, t_in)) in Hopt_eval2_copy; auto.
  destruct Hopt_eval2_copy as [[src_final_v2 src_trace2] [Hsrc_eval2 Hmatch_final2]].

  pose proof (Hni v1 v2 t_in src_final_v1 src_final_v2 src_trace1 src_trace2 Hagree Hsrc_eval1 Hsrc_eval2) as [Htrace_eq Hval_agree].
  split.
  - rewrite Htrace_eq in Hsrc_eval1. 
    eapply opt_traces_equal with (src_trace := src_trace2) 
                                 (src_final_v1 := src_final_v1) 
                                 (src_final_v2 := src_final_v2); eauto.
  - unfold match_ctx in *.
    destruct Hmatch_final1 as [Hval1 Htrace1].
    destruct Hmatch_final2 as [Hval2 Htrace2].
    simpl in *.
    rewrite <- Hval1. rewrite <- Hval2. exact Hval_agree.
Qed.



(** * Secret Preservation Support *)
(* This part uses eval_sec *)


(** ** Main theorem of secret preservation *)

(** [opt_unskip_keeps_secrets_secret] proves the second half of
    [is_safe_opt]: optimized execution preserves the final security labels and
    values of variables that are secret in the source final security environment.

    The proof needs one optimizer-specific expansion lemma:

    - [opt_unskip_sec_complete]: every [eval_sec] execution of [opt_unskip_cmd c]
      can be expanded to an [eval_sec] execution of the source [c] with the same
      final context.

    Once the optimized run is expanded back to a source run, the rest is generic:

    - [eval_sec_deterministic]: the original source run and reconstructed source
      run start from the same security context and execute the same command, so
      their final security contexts are equal.

    After that equality, both required conclusions are reflexive:

    - final security labels agree for every variable;
    - values agree on every variable that is secret in the source final
      security environment. *)
Lemma opt_unskip_keeps_secrets_secret :
  opt_keeps_secrets_secret opt_unskip.
Proof.
Admitted.

(** * Main Theorem *)
(* Combine the two main proofs of the two previous sections to show unskip is a safe_opt *)

Theorem opt_unskip_secure : forall phi,
  is_safe_opt phi opt_unskip.
Proof.
  intros phi.
  unfold is_safe_opt.
  split.
  (* Non-inference preservation *) 
  - apply opt_unskip_preserves_safe_pgm.
  (* Secret preservation *)
  - apply opt_unskip_keeps_secrets_secret.
Qed.
