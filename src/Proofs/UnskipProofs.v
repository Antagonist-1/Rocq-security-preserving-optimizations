Require Import Map.
Require Import Language.Main.
Require Import Language.Analysis.
Require Import Language.Optimizations.Safe.Unskip.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

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
    rewrite Hval_body in *.
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
  intros phi c ctx_opt ctx_opt_final ctx_src Heval Hmatch.
  revert ctx_src Hmatch.
  induction Heval; intros ctx_src Hmatch.
  
  - (* Skip *)
    exists ctx_src; split; [apply EvalTraceSkip | exact Hmatch].
    
  - (* Assign *)
    unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
    exists (ctx_src v$+ (x, a)); split.
    + eapply EvalTraceAssign; rewrite Hval; eassumption.
    + unfold match_ctx; split; simpl; auto; rewrite Hval; auto.
    
  - (* CmovTrue *)
    unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
    exists (ctx_src v$+ (x, a1)); split.
    + eapply EvalTraceCmovTrue; destruct ctx_src as [v_src t_src]; simpl in *;
      rewrite Hval; eassumption.
    + unfold match_ctx; split; simpl; auto; rewrite Hval; auto.

  - (* CmovFalse *)
    unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
    exists (ctx_src v$+ (x, a2)); split.
    + eapply EvalTraceCmovFalse; destruct ctx_src as [v_src t_src]; simpl in *;
      rewrite Hval; eassumption.
    + unfold match_ctx; split; simpl; auto; rewrite Hval; auto.

  - (* AssignCall *)
    unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
    assert (Hmatch_body : match_ctx 
      ($0 $+ (x1, a1) $+ (x2, a2), trace_of ctx_src)
      ($0 $+ (x1, a1) $+ (x2, a2), trace_of ctx)).
    { split; simpl; auto. }
    edestruct IHHeval as [ctx_src_body_final [Hstep_body Hmatch_body_final]]; [exact Hmatch_body |].
    unfold match_ctx in Hmatch_body_final; destruct Hmatch_body_final as [Hval_body Htrace_body].
    exists (val_of ctx_src $+ (x, a), trace_of ctx_src_body_final); split.
    + eapply EvalTraceAssignCall.
      * eassumption.
      * rewrite Hval. eassumption.
      * rewrite Hval. eassumption.
      * exact Hstep_body.
      * rewrite Hval_body. eassumption.
    + unfold match_ctx; split; simpl; auto. rewrite Hval. reflexivity.

  - (* Sequence *)
    edestruct IHHeval1 as [ctx_src_mid [Hstep1 Hmatch1]]; [exact Hmatch |].
    edestruct IHHeval2 as [ctx_src_final [Hstep2 Hmatch_final]]; [exact Hmatch1 |].
    exists ctx_src_final; split.
    + eapply EvalTraceSequence; eassumption.
    + exact Hmatch_final.

  - (* IfTrue *)
    unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
    assert (Hmatch_branch : match_ctx (ctx_src t++ Branch true) (ctx t++ Branch true))
      by (split; simpl; auto; apply trace_subseq_append_keep; auto).
    edestruct IHHeval as [ctx_src_final [Hstep Hmatch_final]]; [exact Hmatch_branch |].
    exists ctx_src_final; split.
    + eapply EvalTraceIfTrue.
      * rewrite Hval. eassumption.
      * eassumption.
      * exact Hstep.
    + exact Hmatch_final.

  - (* IfFalse *)
    unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
    assert (Hmatch_branch : match_ctx (ctx_src t++ Branch false) (ctx t++ Branch false))
      by (split; simpl; auto; apply trace_subseq_append_keep; auto).
    edestruct IHHeval as [ctx_src_final [Hstep Hmatch_final]]; [exact Hmatch_branch |].
    exists ctx_src_final; split.
    + eapply EvalTraceIfFalse.
      * rewrite Hval. eassumption.
      * exact Hstep.
    + exact Hmatch_final.

  - (* WhileTrue *)
    unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
    assert (Hmatch_branch : match_ctx (ctx_src t++ Branch true) (ctx t++ Branch true))
      by (split; simpl; auto; apply trace_subseq_append_keep; auto).
    edestruct IHHeval1 as [ctx_src_mid [Hstep1 Hmatch1]]; [exact Hmatch_branch |].
    edestruct IHHeval2 as [ctx_src_final [Hstep2 Hmatch_final]]; [exact Hmatch1 |].
    exists ctx_src_final; split.
    + eapply EvalTraceWhileTrue.
      * rewrite Hval. eassumption.
      * eassumption.
      * exact Hstep1.
      * exact Hstep2.
    + exact Hmatch_final.

  - (* WhileFalse *)
    unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
    assert (Hmatch_branch : match_ctx (ctx_src t++ Branch false) (ctx t++ Branch false))
      by (split; simpl; auto; apply trace_subseq_append_keep; auto).
    exists (ctx_src t++ Branch false); split.
    + eapply EvalTraceWhileFalse. rewrite Hval. eassumption.
    + exact Hmatch_branch.
Qed.

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

Lemma eval_trace_sync : forall phi ctx1 c ctx1_out,
  eval_trace phi ctx1 c ctx1_out ->
  forall ctx2 ctx2_out tail1 tail2,
  eval_trace phi ctx2 c ctx2_out ->
  trace_of ctx1 = trace_of ctx2 ->
  trace_of ctx1_out ++ tail1 = trace_of ctx2_out ++ tail2 ->
  trace_of ctx1_out = trace_of ctx2_out.
Proof.
  intros phi ctx1 c ctx1_out Heval_1.
  induction Heval_1; intros ctxin_2 ctx2_out tail1 tail2 Heval_2 Hstart Heq;
  inversion Heval_2; subst; simpl in *.
  - (* Skip *) simpl in *. exact Hstart.
  - (* Assign *) exact Hstart.
  - (* CmovTrue / True *) exact Hstart.
  - (* CmovTrue / False *) exact Hstart.
  - (* CmovFalse / True *) exact Hstart.
  - (* CmovFalse / False *) exact Hstart.
  - (* AssignCall *)
    rewrite H in H7.
    inversion H7; subst.
    eapply IHHeval_1; [exact H12 | exact Hstart | exact Heq].
  - (* Sequence *)
    destruct (eval_trace_prefix _ _ _ _ Heval_1_2) as [diff1 Hdiff1].
    destruct (eval_trace_prefix _ _ _ _ H4) as [diff2 Hdiff2].
    assert (Hint_eq: trace_of ctx1 = trace_of ctx3).
    { eapply IHHeval_1_1; [exact H2 | exact Hstart | ].
      rewrite Hdiff1, Hdiff2 in Heq. 
      do 2 rewrite <- app_assoc in Heq. 
      exact Heq. }
    eapply IHHeval_1_2; [exact H4 | exact Hint_eq | exact Heq].

  - (* IfTrue / True *)
    eapply IHHeval_1; [exact H8 | | exact Heq].
    simpl. rewrite Hstart. reflexivity.

  - (* IfTrue / False Contradiction *)
    destruct (eval_trace_prefix _ _ _ _ Heval_1) as [diff1 Hdiff1];
    destruct (eval_trace_prefix _ _ _ _ H7) as [diff2 Hdiff2];
    simpl in *; rewrite Hdiff1, Hdiff2 in Heq; rewrite Hstart in Heq;
    repeat rewrite <- app_assoc in Heq; apply branch_contradiction in Heq; discriminate Heq.

  - (* IfFalse / True Contradiction *)
    destruct (eval_trace_prefix _ _ _ _ Heval_1) as [diff1 Hdiff1];
    destruct (eval_trace_prefix _ _ _ _ H7) as [diff2 Hdiff2];
    simpl in *; rewrite Hdiff1, Hdiff2 in Heq; rewrite Hstart in Heq;
    repeat rewrite <- app_assoc in Heq; apply branch_contradiction in Heq; discriminate Heq.

  - (* IfFalse / False *)
    eapply IHHeval_1; [exact H6 | | exact Heq];
    simpl; rewrite Hstart; reflexivity.

  - (* WhileTrue / True *)
    destruct (eval_trace_prefix _ _ _ _ Heval_1_2) as [diff1 Hdiff1].
    destruct (eval_trace_prefix _ _ _ _ H8) as [diff2 Hdiff2].
    assert (Hint_eq: trace_of ctx' = trace_of ctx'0).
    { eapply IHHeval_1_1; [exact H6 | | ].
      - simpl. rewrite Hstart. reflexivity.
      - rewrite Hdiff1, Hdiff2 in Heq. 
        do 2 rewrite <- app_assoc in Heq. 
        exact Heq. }
    eapply IHHeval_1_2; [exact H8 | exact Hint_eq | exact Heq].

  - (* WhileTrue / False Contradiction *)
    destruct (eval_trace_prefix _ _ _ _ Heval_1_1) as [diff_body Hdiff_body];
    destruct (eval_trace_prefix _ _ _ _ Heval_1_2) as [diff_loop Hdiff_loop];
    simpl in *; rewrite Hdiff_loop, Hdiff_body in Heq; rewrite Hstart in Heq;
    repeat rewrite <- app_assoc in Heq; apply branch_contradiction in Heq; discriminate Heq.

  - (* WhileFalse / True Contradiction *)
    destruct (eval_trace_prefix _ _ _ _ H5) as [diff_body Hdiff_body];
    destruct (eval_trace_prefix _ _ _ _ H7) as [diff_loop Hdiff_loop];
    simpl in *; rewrite Hdiff_loop, Hdiff_body in Heq; rewrite <- Hstart in Heq;
    repeat rewrite <- app_assoc in Heq; apply branch_contradiction in Heq; discriminate Heq.

  - (* WhileFalse / False *)
    rewrite Hstart. reflexivity.
Qed.

Lemma eval_trace_sequence_inv : forall phi ctx c1 c2 ctx_out,
  eval_trace phi ctx (Sequence c1 c2) ctx_out ->
  exists ctx_mid,
    eval_trace phi ctx c1 ctx_mid /\
    eval_trace phi ctx_mid c2 ctx_out.
Proof.
  intros phi ctx c1 c2 ctx_out Heval.
  inversion Heval; subst; eauto.
Qed.

Lemma eval_trace_rebase : forall phi ctx c ctx_out,
  eval_trace phi ctx c ctx_out ->
  forall t,
    exists suffix,
      trace_of ctx_out = trace_of ctx ++ suffix /\
      eval_trace phi (val_of ctx, t) c (val_of ctx_out, t ++ suffix).
Proof.
  intros phi ctx c ctx_out Heval.
  induction Heval; intros t0; simpl in *.
  - exists []. split; [rewrite app_nil_r; reflexivity |].
    rewrite app_nil_r. apply EvalTraceSkip.
  - exists []. split; [rewrite app_nil_r; reflexivity |].
    rewrite app_nil_r.
    change (eval_trace phi (val_of ctx, t0) (Assign x e)
      ((val_of ctx, t0) v$+ (x, a))).
    eapply EvalTraceAssign. exact H.
  - exists []. split; [rewrite app_nil_r; reflexivity |].
    rewrite app_nil_r.
    change (eval_trace phi (val_of ctx, t0) (Cmov x cond e1 e2)
      ((val_of ctx, t0) v$+ (x, a1))).
    eapply EvalTraceCmovTrue; eauto.
  - exists []. split; [rewrite app_nil_r; reflexivity |].
    rewrite app_nil_r.
    change (eval_trace phi (val_of ctx, t0) (Cmov x cond e1 e2)
      ((val_of ctx, t0) v$+ (x, a2))).
    eapply EvalTraceCmovFalse; eauto.
  - destruct (IHHeval t0) as [suffix [Hsuffix Hbody]].
    exists suffix. split; [exact Hsuffix |].
    eapply EvalTraceAssignCall with (ctx := (val_of ctx, t0))
      (ctx' := (val_of ctx', t0 ++ suffix));
      simpl; eauto.
  - destruct (IHHeval1 t0) as [suffix1 [Hsuffix1 Hstep1]].
    destruct (IHHeval2 (t0 ++ suffix1)) as [suffix2 [Hsuffix2 Hstep2]].
    exists (suffix1 ++ suffix2). split.
    + rewrite Hsuffix2, Hsuffix1, app_assoc. reflexivity.
    + rewrite app_assoc. eapply EvalTraceSequence; eauto.
  - destruct (IHHeval (t0 ++ [Branch true])) as [suffix [Hsuffix Hstep]].
    exists ([Branch true] ++ suffix). split.
    + rewrite Hsuffix. rewrite <- app_assoc. reflexivity.
    + eapply EvalTraceIfTrue; eauto.
      replace (t0 ++ ([Branch true] ++ suffix))
        with ((t0 ++ [Branch true]) ++ suffix)
        by (rewrite app_assoc; reflexivity).
      exact Hstep.
  - destruct (IHHeval (t0 ++ [Branch false])) as [suffix [Hsuffix Hstep]].
    exists ([Branch false] ++ suffix). split.
    + rewrite Hsuffix. rewrite <- app_assoc. reflexivity.
    + eapply EvalTraceIfFalse; eauto.
      replace (t0 ++ ([Branch false] ++ suffix))
        with ((t0 ++ [Branch false]) ++ suffix)
        by (rewrite app_assoc; reflexivity).
      exact Hstep.
  - destruct (IHHeval1 (t0 ++ [Branch true])) as [suffix1 [Hsuffix1 Hstep1]].
    destruct (IHHeval2 ((t0 ++ [Branch true]) ++ suffix1)) as [suffix2 [Hsuffix2 Hstep2]].
    exists ([Branch true] ++ suffix1 ++ suffix2). split.
    + rewrite Hsuffix2, Hsuffix1.
      do 2 rewrite <- app_assoc. reflexivity.
    + replace (t0 ++ (([Branch true] ++ suffix1) ++ suffix2))
        with (((t0 ++ [Branch true]) ++ suffix1) ++ suffix2)
        by (do 2 rewrite app_assoc; reflexivity).
      eapply EvalTraceWhileTrue with
        (ctx' := (val_of ctx', (t0 ++ [Branch true]) ++ suffix1))
        (c := c).
      * exact H.
      * exact H0.
      * exact Hstep1.
      * replace (t0 ++ [Branch true] ++ suffix1 ++ suffix2)
          with (((t0 ++ [Branch true]) ++ suffix1) ++ suffix2)
          by (repeat rewrite app_assoc; reflexivity).
        exact Hstep2.
  - exists [Branch false]. split; [reflexivity |].
    eapply EvalTraceWhileFalse. exact H.
Qed.

Lemma eval_trace_equal_rebased : forall phi c ctx_src1 ctx_src2 ctx_opt1 ctx_opt2
    ctx_src1_out ctx_src2_out ctx_opt1_out ctx_opt2_out,
  eval_trace phi ctx_src1 c ctx_src1_out ->
  eval_trace phi ctx_src2 c ctx_src2_out ->
  eval_trace phi ctx_opt1 c ctx_opt1_out ->
  eval_trace phi ctx_opt2 c ctx_opt2_out ->
  val_of ctx_src1 = val_of ctx_opt1 ->
  val_of ctx_src2 = val_of ctx_opt2 ->
  trace_of ctx_src1 = trace_of ctx_src2 ->
  trace_of ctx_opt1 = trace_of ctx_opt2 ->
  trace_of ctx_src1_out = trace_of ctx_src2_out ->
  trace_of ctx_opt1_out = trace_of ctx_opt2_out.
Proof.
  intros phi c ctx_src1 ctx_src2 ctx_opt1 ctx_opt2
    ctx_src1_out ctx_src2_out ctx_opt1_out ctx_opt2_out
    Hsrc1 Hsrc2 Hopt1 Hopt2 Hval1 Hval2 Hstart_src Hstart_opt Hout_src.
  destruct (eval_trace_rebase _ _ _ _ Hsrc1 (trace_of ctx_opt1))
    as [suffix1 [Hsuffix1 Hrebase1]].
  destruct (eval_trace_rebase _ _ _ _ Hsrc2 (trace_of ctx_opt2))
    as [suffix2 [Hsuffix2 Hrebase2]].
  destruct ctx_src1 as [v_src1 t_src1], ctx_src2 as [v_src2 t_src2].
  destruct ctx_opt1 as [v_opt1 t_opt1], ctx_opt2 as [v_opt2 t_opt2].
  simpl in *; subst v_opt1 v_opt2.
  assert (Heq1 : ctx_opt1_out = (val_of ctx_src1_out, t_opt1 ++ suffix1)).
  { eapply eval_trace_deterministic; eauto. }
  assert (Heq2 : ctx_opt2_out = (val_of ctx_src2_out, t_opt2 ++ suffix2)).
  { eapply eval_trace_deterministic; eauto. }
  rewrite Heq1, Heq2. simpl.
  rewrite Hsuffix1, Hsuffix2 in Hout_src.
  rewrite Hstart_src in Hout_src.
  apply app_inv_head in Hout_src.
  rewrite Hstart_opt, Hout_src. reflexivity.
Qed.

Ltac solve_unop :=
  match goal with
  | Hsrc1: eval_trace ?phi (?v1, ?t) ?c (?vf1, ?tr1),
    Hopt1: eval_trace ?phi (?v1, ?t) ?c (?vf1_opt, ?tr1_opt),
    Hsrc2: eval_trace ?phi (?v2, ?t) ?c (?vf2, ?tr2),
    Hopt2: eval_trace ?phi (?v2, ?t) ?c (?vf2_opt, ?tr2_opt) |- _ =>
    assert (Hdet1: (vf1_opt, tr1_opt) = (vf1, tr1)) by (eapply eval_trace_deterministic; [exact Hopt1 | exact Hsrc1]);
    assert (Hdet2: (vf2_opt, tr2_opt) = (vf2, tr2)) by (eapply eval_trace_deterministic; [exact Hopt2 | exact Hsrc2]);
    inversion Hdet1; inversion Hdet2; subst; reflexivity
  end.

Ltac contradict_branch_traces Hstep1 Hstep2 Hstart Hout :=
  let tail1 := fresh "tail1" in let Htail1 := fresh "Htail1" in
  let tail2 := fresh "tail2" in let Htail2 := fresh "Htail2" in
  destruct (eval_trace_prefix _ _ _ _ Hstep1) as [tail1 Htail1];
  destruct (eval_trace_prefix _ _ _ _ Hstep2) as [tail2 Htail2];
  simpl in *; rewrite Htail1, Htail2 in Hout; rewrite Hstart in Hout;
  repeat rewrite <- app_assoc in Hout; apply branch_contradiction in Hout; discriminate Hout.

Lemma opt_unskip_forward_match : forall phi c ctx ctx_out ctx_opt ctx_opt_out,
  eval_trace phi ctx c ctx_out ->
  eval_trace phi ctx_opt (opt_unskip_cmd c) ctx_opt_out ->
  match_ctx ctx ctx_opt ->
  match_ctx ctx_out ctx_opt_out.
Proof.
  intros phi c ctx ctx_out ctx_opt ctx_opt_out Hsrc Hopt Hmatch.
  destruct (opt_unskip_forward _ _ _ _ _ Hsrc Hmatch) as [ctx_fw [Hfw Hmatch_out]].
  replace ctx_opt_out with ctx_fw by (eapply eval_trace_deterministic; eauto).
  exact Hmatch_out.
Qed.

Lemma opt_traces_equal_gen : forall phi c ctx_src1 ctx_src2 ctx_opt1 ctx_opt2 ctx_src1_out ctx_src2_out ctx_opt1_out ctx_opt2_out,
  eval_trace phi ctx_src1 c ctx_src1_out ->
  eval_trace phi ctx_src2 c ctx_src2_out ->
  eval_trace phi ctx_opt1 (opt_unskip_cmd c) ctx_opt1_out ->
  eval_trace phi ctx_opt2 (opt_unskip_cmd c) ctx_opt2_out ->
  match_ctx ctx_src1 ctx_opt1 ->
  match_ctx ctx_src2 ctx_opt2 ->
  trace_of ctx_src1 = trace_of ctx_src2 ->
  trace_of ctx_opt1 = trace_of ctx_opt2 ->
  trace_of ctx_src1_out = trace_of ctx_src2_out ->
  trace_of ctx_opt1_out = trace_of ctx_opt2_out.
Proof.
  intros phi c ctx_src1 ctx_src2 ctx_opt1 ctx_opt2
    ctx_src1_out ctx_src2_out ctx_opt1_out ctx_opt2_out Hsrc1.
  revert ctx_src2 ctx_opt1 ctx_opt2 ctx_src2_out ctx_opt1_out ctx_opt2_out.
  induction Hsrc1; intros ctx_src2 ctx_opt1 ctx_opt2
    ctx_src2_out ctx_opt1_out ctx_opt2_out
    Hsrc2 Hopt1 Hopt2 Hmatch1 Hmatch2 Hstart_src Hstart_opt Hout_src;
    simpl in Hopt1, Hopt2.
  - (* Skip *)
    inversion Hopt1; inversion Hopt2; subst; exact Hstart_opt.
  - (* Assign *)
    inversion Hopt1; inversion Hopt2; subst; exact Hstart_opt.
  - (* CmovTrue *)
    inversion Hopt1; inversion Hopt2; subst; exact Hstart_opt.
  - (* CmovFalse *)
    inversion Hopt1; inversion Hopt2; subst; exact Hstart_opt.
  - (* AssignCall *)
    assert (Hsrc1_call :
      eval_trace phi ctx (AssignCall x f e1 e2)
        (val_of ctx $+ (x, a), trace_of ctx')).
    { eapply EvalTraceAssignCall; eauto. }
    unfold match_ctx in Hmatch1, Hmatch2.
    destruct Hmatch1 as [Hval1 _], Hmatch2 as [Hval2 _].
    eapply eval_trace_equal_rebased with
      (ctx_src1 := ctx) (ctx_src2 := ctx_src2)
      (ctx_opt1 := ctx_opt1) (ctx_opt2 := ctx_opt2).
    all: eassumption.
  - (* Sequence *)
    destruct (eval_trace_sequence_inv _ _ _ _ _ Hsrc2)
      as [ctx2_mid [Hsrc2_1 Hsrc2_2]].
    destruct (eval_trace_prefix _ _ _ _ Hsrc1_2) as [tail1 Htail1].
    destruct (eval_trace_prefix _ _ _ _ Hsrc2_2) as [tail2 Htail2].
    assert (Hsrc_mid : trace_of ctx1 = trace_of ctx2_mid).
    { eapply eval_trace_sync; [exact Hsrc1_1 | exact Hsrc2_1 | exact Hstart_src |].
      rewrite Htail1, Htail2 in Hout_src. exact Hout_src. }
    destruct (opt_unskip_cmd c1) eqn:Hc1;
    destruct (opt_unskip_cmd c2) eqn:Hc2;
    lazymatch type of Hc1 with
    | _ = Skip =>
      lazymatch type of Hc2 with
      | _ = Skip =>
        inversion Hopt1; inversion Hopt2; subst; exact Hstart_opt
      | _ =>
        assert (Hmatch1_mid : match_ctx ctx1 ctx_opt1)
          by (eapply opt_unskip_forward_match; [exact Hsrc1_1 | rewrite Hc1; constructor | exact Hmatch1]);
        assert (Hmatch2_mid : match_ctx ctx2_mid ctx_opt2)
          by (eapply opt_unskip_forward_match; [exact Hsrc2_1 | rewrite Hc1; constructor | exact Hmatch2]);
        eapply IHHsrc1_2 with
          (ctx_src2 := ctx2_mid) (ctx_opt1 := ctx_opt1) (ctx_opt2 := ctx_opt2);
        eassumption
      end
    | _ =>
      lazymatch type of Hc2 with
      | _ = Skip =>
        eapply IHHsrc1_1 with
          (ctx_src2 := ctx_src2) (ctx_opt1 := ctx_opt1) (ctx_opt2 := ctx_opt2);
        eassumption
      | _ =>
        destruct (eval_trace_sequence_inv _ _ _ _ _ Hopt1)
          as [ctx1_opt_mid [Hopt1_1 Hopt1_2]];
        destruct (eval_trace_sequence_inv _ _ _ _ _ Hopt2)
          as [ctx2_opt_mid [Hopt2_1 Hopt2_2]];
        assert (Hopt_mid : trace_of ctx1_opt_mid = trace_of ctx2_opt_mid)
          by (eapply IHHsrc1_1 with
            (ctx_src2 := ctx_src2) (ctx_opt1 := ctx_opt1) (ctx_opt2 := ctx_opt2);
            eassumption);
        assert (Hmatch1_mid : match_ctx ctx1 ctx1_opt_mid)
          by (eapply opt_unskip_forward_match; [exact Hsrc1_1 | rewrite Hc1; exact Hopt1_1 | exact Hmatch1]);
        assert (Hmatch2_mid : match_ctx ctx2_mid ctx2_opt_mid)
          by (eapply opt_unskip_forward_match; [exact Hsrc2_1 | rewrite Hc1; exact Hopt2_1 | exact Hmatch2]);
        eapply IHHsrc1_2 with
          (ctx_src2 := ctx2_mid) (ctx_opt1 := ctx1_opt_mid) (ctx_opt2 := ctx2_opt_mid);
        eassumption
      end
    end.
  - (* IfTrue *)
    assert (Hmatch1_branch :
      match_ctx (ctx t++ Branch true) (ctx_opt1 t++ Branch true)).
    { unfold match_ctx in *; destruct Hmatch1 as [Hval Htrace].
      split; simpl; [exact Hval | apply trace_subseq_append_keep; exact Htrace]. }
    assert (Hmatch2_branch :
      match_ctx (ctx_src2 t++ Branch true) (ctx_opt2 t++ Branch true)).
    { unfold match_ctx in *; destruct Hmatch2 as [Hval Htrace].
      split; simpl; [exact Hval | apply trace_subseq_append_keep; exact Htrace]. }
    assert (Hstart_src_branch :
      trace_of (ctx t++ Branch true) = trace_of (ctx_src2 t++ Branch true)).
    { simpl. rewrite Hstart_src. reflexivity. }
    assert (Hstart_opt_branch :
      trace_of (ctx_opt1 t++ Branch true) =
      trace_of (ctx_opt2 t++ Branch true)).
    { simpl. rewrite Hstart_opt. reflexivity. }
    dependent destruction Hsrc2.
    + destruct (opt_unskip_cmd thn) eqn:Hthn;
      destruct (opt_unskip_cmd els) eqn:Hels;
      lazymatch type of Hthn with
      | _ = Skip =>
        lazymatch type of Hels with
        | _ = Skip =>
          inversion Hopt1; inversion Hopt2; subst; exact Hstart_opt
        | _ =>
          unfold match_ctx in Hmatch1, Hmatch2;
          destruct Hmatch1 as [Hval1 _], Hmatch2 as [Hval2 _];
          inversion Hopt1; subst; try (rewrite Hval1 in *; lia);
          inversion Hopt2; subst; try (rewrite Hval2 in *; lia);
          eapply IHHsrc1; eauto
        end
      | _ =>
        unfold match_ctx in Hmatch1, Hmatch2;
        destruct Hmatch1 as [Hval1 _], Hmatch2 as [Hval2 _];
        inversion Hopt1; subst; try (rewrite Hval1 in *; lia);
        inversion Hopt2; subst; try (rewrite Hval2 in *; lia);
        eapply IHHsrc1; eauto
      end.
    + contradict_branch_traces Hsrc1 Hsrc2 Hstart_src Hout_src.
  - (* IfFalse *)
    assert (Hmatch1_branch :
      match_ctx (ctx t++ Branch false) (ctx_opt1 t++ Branch false)).
    { unfold match_ctx in *; destruct Hmatch1 as [Hval Htrace].
      split; simpl; [exact Hval | apply trace_subseq_append_keep; exact Htrace]. }
    assert (Hmatch2_branch :
      match_ctx (ctx_src2 t++ Branch false) (ctx_opt2 t++ Branch false)).
    { unfold match_ctx in *; destruct Hmatch2 as [Hval Htrace].
      split; simpl; [exact Hval | apply trace_subseq_append_keep; exact Htrace]. }
    assert (Hstart_src_branch :
      trace_of (ctx t++ Branch false) = trace_of (ctx_src2 t++ Branch false)).
    { simpl. rewrite Hstart_src. reflexivity. }
    assert (Hstart_opt_branch :
      trace_of (ctx_opt1 t++ Branch false) =
      trace_of (ctx_opt2 t++ Branch false)).
    { simpl. rewrite Hstart_opt. reflexivity. }
    dependent destruction Hsrc2.
    + contradict_branch_traces Hsrc1 Hsrc2 Hstart_src Hout_src.
    + destruct (opt_unskip_cmd thn) eqn:Hthn;
      destruct (opt_unskip_cmd els) eqn:Hels;
      lazymatch type of Hthn with
      | _ = Skip =>
        lazymatch type of Hels with
        | _ = Skip =>
          inversion Hopt1; inversion Hopt2; subst; exact Hstart_opt
        | _ =>
          unfold match_ctx in Hmatch1, Hmatch2;
          destruct Hmatch1 as [Hval1 _], Hmatch2 as [Hval2 _];
          inversion Hopt1; subst; try (rewrite Hval1 in *; lia);
          inversion Hopt2; subst; try (rewrite Hval2 in *; lia);
          eapply IHHsrc1; eauto
        end
      | _ =>
        unfold match_ctx in Hmatch1, Hmatch2;
        destruct Hmatch1 as [Hval1 _], Hmatch2 as [Hval2 _];
        inversion Hopt1; subst; try (rewrite Hval1 in *; lia);
        inversion Hopt2; subst; try (rewrite Hval2 in *; lia);
        eapply IHHsrc1; eauto
      end.
  - (* WhileTrue *)
    assert (Hmatch1_branch :
      match_ctx (ctx t++ Branch true) (ctx_opt1 t++ Branch true)).
    { unfold match_ctx in *; destruct Hmatch1 as [Hval Htrace].
      split; simpl; [exact Hval | apply trace_subseq_append_keep; exact Htrace]. }
    assert (Hmatch2_branch :
      match_ctx (ctx_src2 t++ Branch true) (ctx_opt2 t++ Branch true)).
    { unfold match_ctx in *; destruct Hmatch2 as [Hval Htrace].
      split; simpl; [exact Hval | apply trace_subseq_append_keep; exact Htrace]. }
    assert (Hstart_src_branch :
      trace_of (ctx t++ Branch true) = trace_of (ctx_src2 t++ Branch true)).
    { simpl. rewrite Hstart_src. reflexivity. }
    assert (Hstart_opt_branch :
      trace_of (ctx_opt1 t++ Branch true) =
      trace_of (ctx_opt2 t++ Branch true)).
    { simpl. rewrite Hstart_opt. reflexivity. }
    inversion Hsrc2; subst; clear Hsrc2.
    + (* Hsrc2 is WhileTrue *)
      unfold match_ctx in Hmatch1, Hmatch2;
      destruct Hmatch1 as [Hval1 _], Hmatch2 as [Hval2 _];
      inversion Hopt1; subst; clear Hopt1; try (rewrite <- Hval1 in *; lia);
      inversion Hopt2; subst; clear Hopt2; try (rewrite <- Hval2 in *; lia).
      match goal with
      | Hsrc2_1 : eval_trace phi (?ctx_src2 t++ Branch true) body ?ctx2_mid,
        Hsrc2_2 : eval_trace phi ?ctx2_mid (While e body) ctx_src2_out,
        Hopt1_1 : eval_trace phi (?ctx_opt1 t++ Branch true) (opt_unskip_cmd body) ?ctxopt1_mid,
        Hopt1_2 : eval_trace phi ?ctxopt1_mid (While e (opt_unskip_cmd body)) ctx_opt1_out,
        Hopt2_1 : eval_trace phi (?ctx_opt2 t++ Branch true) (opt_unskip_cmd body) ?ctxopt2_mid,
        Hopt2_2 : eval_trace phi ?ctxopt2_mid (While e (opt_unskip_cmd body)) ctx_opt2_out |- _ =>
          destruct (eval_trace_prefix _ _ _ _ Hsrc1_2) as [tail1 Htail1];
          destruct (eval_trace_prefix _ _ _ _ Hsrc2_2) as [tail2 Htail2];
          assert (Hsrc_mid : trace_of ctx' = trace_of ctx2_mid);
          [ eapply eval_trace_sync; [exact Hsrc1_1 | exact Hsrc2_1 | exact Hstart_src_branch | ];
            rewrite Htail1, Htail2 in Hout_src; exact Hout_src | ];
          assert (Hmatch1_mid : match_ctx ctx' ctxopt1_mid)
            by (eapply opt_unskip_forward_match; eauto);
          assert (Hmatch2_mid : match_ctx ctx2_mid ctxopt2_mid)
            by (eapply opt_unskip_forward_match; eauto);
          assert (Hopt_mid : trace_of ctxopt1_mid = trace_of ctxopt2_mid);
          [ eapply IHHsrc1_1; [exact Hsrc2_1 | exact Hopt1_1 | exact Hopt2_1 | exact Hmatch1_branch | exact Hmatch2_branch | exact Hstart_src_branch | exact Hstart_opt_branch | exact Hsrc_mid] | ];
          eapply IHHsrc1_2; [exact Hsrc2_2 | exact Hopt1_2 | exact Hopt2_2 | exact Hmatch1_mid | exact Hmatch2_mid | exact Hsrc_mid | exact Hopt_mid | exact Hout_src]
      end.
    + (* Hsrc2 is WhileFalse *)
      assert (Hsrc1_loop := @EvalTraceSequence phi _ _ _ _ _ Hsrc1_1 Hsrc1_2).
      contradict_branch_traces Hsrc1_loop (EvalTraceSkip phi (ctx_src2 t++ Branch false)) Hstart_src Hout_src.
  - (* WhileFalse *)
    inversion Hsrc2; subst; clear Hsrc2.
    + (* Hsrc2 is WhileTrue *)
      match goal with
      | Hsrc2_1 : eval_trace phi (?ctx_src2 t++ Branch true) body ?ctx2_mid,
        Hsrc2_2 : eval_trace phi ?ctx2_mid (While e body) ctx_src2_out |- _ =>
          assert (Hsrc2_loop := @EvalTraceSequence phi _ _ _ _ _ Hsrc2_1 Hsrc2_2);
          symmetry in Hstart_src, Hout_src;
          contradict_branch_traces Hsrc2_loop (EvalTraceSkip phi (ctx t++ Branch false)) Hstart_src Hout_src
      end.
    + (* Hsrc2 is WhileFalse *)
      unfold match_ctx in Hmatch1, Hmatch2;
      destruct Hmatch1 as [Hval1 _], Hmatch2 as [Hval2 _];
      inversion Hopt1; subst; clear Hopt1; try (rewrite <- Hval1 in *; lia);
      inversion Hopt2; subst; clear Hopt2; try (rewrite <- Hval2 in *; lia).
      simpl in *. rewrite Hstart_opt. reflexivity.
Qed.

Lemma opt_traces_equal : forall phi c v1 v2 t_in final_v1 final_v2 trace1 trace2 src_final_v1 src_final_v2 src_trace,
  eval_trace phi (v1, t_in) c (src_final_v1, src_trace) ->
  eval_trace phi (v2, t_in) c (src_final_v2, src_trace) ->
  eval_trace phi (v1, t_in) (opt_unskip_cmd c) (final_v1, trace1) ->
  eval_trace phi (v2, t_in) (opt_unskip_cmd c) (final_v2, trace2) ->
  trace1 = trace2.
Proof.
  intros phi c v1 v2 t_in final_v1 final_v2 trace1 trace2 src_final_v1 src_final_v2 src_trace
    Hsrc1 Hsrc2 Hopt1 Hopt2.
  pose proof (opt_traces_equal_gen phi c 
    (v1, t_in) (v2, t_in) 
    (v1, t_in) (v2, t_in) 
    (src_final_v1, src_trace) (src_final_v2, src_trace) 
    (final_v1, trace1) (final_v2, trace2) 
    Hsrc1 Hsrc2 Hopt1 Hopt2) as Hgen.
  apply Hgen; clear Hgen.
  - unfold match_ctx. split; simpl; [reflexivity | apply trace_subseq_refl].
  - unfold match_ctx. split; simpl; [reflexivity | apply trace_subseq_refl].
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

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

Lemma match_sec_ctx_refl : forall sctx,
  match_sec_ctx sctx sctx.
Proof.
  intros sctx.
  unfold match_sec_ctx.
  repeat split; try reflexivity.
  apply trace_subseq_refl.
Qed.

Lemma match_sec_ctx_trans : forall sctx1 sctx2 sctx3,
  match_sec_ctx sctx1 sctx2 ->
  match_sec_ctx sctx2 sctx3 ->
  match_sec_ctx sctx1 sctx3.
Proof.
  intros sctx1 sctx2 sctx3 H12 H23.
  unfold match_sec_ctx in *.
  destruct H12 as [Hval12 [Hsec12 Htrace12]].
  destruct H23 as [Hval23 [Hsec23 Htrace23]].
  repeat split.
  - rewrite Hval12. exact Hval23.
  - rewrite Hsec12. exact Hsec23.
  - eapply trace_subseq_trans; eauto.
Qed.

Lemma eval_sec_unopt_backward : forall phi c sctx_opt sctx_opt_out sctx_src,
  eval_sec phi sctx_opt c sctx_opt_out ->
  match_sec_ctx sctx_src sctx_opt ->
  exists sctx_src_out,
    eval_sec phi sctx_src c sctx_src_out /\
    match_sec_ctx sctx_src_out sctx_opt_out.
Proof.
  intros phi c sctx_opt sctx_opt_out sctx_src Heval.
  revert sctx_src.
  induction Heval; intros sctx_src Hmatch.
  - exists sctx_src. split; [constructor | exact Hmatch].
  - unfold match_sec_ctx in Hmatch.
    destruct Hmatch as [Hval [Hsec Htrace]].
    exists ((sctx_src sv$+ (x, a)) s$+ (x, level)).
    split.
    + eapply EvalSecAssign; [rewrite Hval; exact H | rewrite Hsec; exact H0].
    + unfold match_sec_ctx. simpl. repeat split.
      * rewrite Hval. reflexivity.
      * rewrite Hsec. reflexivity.
      * exact Htrace.
  - unfold match_sec_ctx in Hmatch.
    destruct Hmatch as [Hval [Hsec Htrace]].
    exists ((sctx_src sv$+ (x, a1)) s$+ (x, level)).
    split.
    + eapply EvalSecCmovTrue.
      * rewrite Hval. exact H.
      * exact H0.
      * rewrite Hval. exact H1.
      * rewrite Hval. exact H2.
      * rewrite Hsec. exact H3.
    + unfold match_sec_ctx. simpl. repeat split.
      * rewrite Hval. reflexivity.
      * rewrite Hsec. reflexivity.
      * exact Htrace.
  - unfold match_sec_ctx in Hmatch.
    destruct Hmatch as [Hval [Hsec Htrace]].
    exists ((sctx_src sv$+ (x, a2)) s$+ (x, level)).
    split.
    + eapply EvalSecCmovFalse.
      * rewrite Hval. exact H.
      * rewrite Hval. exact H0.
      * rewrite Hval. exact H1.
      * rewrite Hsec. exact H2.
    + unfold match_sec_ctx. simpl. repeat split.
      * rewrite Hval. reflexivity.
      * rewrite Hsec. reflexivity.
      * exact Htrace.
  - unfold match_sec_ctx in Hmatch.
    destruct Hmatch as [Hval [Hsec Htrace]].
    assert (Hmatch_body :
      match_sec_ctx
        (($0 $+ (x1, a1) $+ (x2, a2)), senv_mk2 x1 x2 level1 level2,
          sec_trace_of sctx_src)
        (($0 $+ (x1, a1) $+ (x2, a2)), senv_mk2 x1 x2 level1 level2,
          sec_trace_of ctx)).
    { unfold match_sec_ctx. simpl. repeat split; try reflexivity. exact Htrace. }
    destruct (IHHeval _ Hmatch_body)
      as [sctx_src_body [Hbody Hmatch_body_out]].
    unfold match_sec_ctx in Hmatch_body_out.
    destruct Hmatch_body_out as [Hbody_val [Hbody_sec Hbody_trace]].
    exists (sec_val_of sctx_src $+ (x, a), update_sec (sec_of sctx_src) x level,
      sec_trace_of sctx_src_body).
    split.
    + eapply EvalSecAssignCall.
      * exact H.
      * rewrite Hval. exact H0.
      * rewrite Hval. exact H1.
      * rewrite Hsec. exact H2.
      * rewrite Hsec. exact H3.
      * exact Hbody.
      * rewrite Hbody_val. exact H4.
      * rewrite Hbody_sec. exact H5.
    + unfold match_sec_ctx. simpl. repeat split.
      * rewrite Hval. reflexivity.
      * rewrite Hsec. reflexivity.
      * exact Hbody_trace.
  - destruct (IHHeval1 _ Hmatch) as [sctx_src_mid [Hstep1 Hmatch_mid]].
    destruct (IHHeval2 _ Hmatch_mid) as [sctx_src_out [Hstep2 Hmatch_out]].
    exists sctx_src_out. split; [eapply EvalSecSequence; eauto | exact Hmatch_out].
  - unfold match_sec_ctx in Hmatch.
    destruct Hmatch as [Hval [Hsec Htrace]].
    assert (Hmatch_branch :
      match_sec_ctx (sctx_src st++ Branch true) (ctx st++ Branch true)).
    { unfold match_sec_ctx. simpl. repeat split; try assumption.
      apply trace_subseq_append_keep. exact Htrace. }
    destruct (IHHeval _ Hmatch_branch) as [sctx_src_out [Hstep Hmatch_out]].
    exists sctx_src_out. split.
    + eapply EvalSecIfTrue; [rewrite Hval; exact H | exact H0 | exact Hstep].
    + exact Hmatch_out.
  - unfold match_sec_ctx in Hmatch.
    destruct Hmatch as [Hval [Hsec Htrace]].
    assert (Hmatch_branch :
      match_sec_ctx (sctx_src st++ Branch false) (ctx st++ Branch false)).
    { unfold match_sec_ctx. simpl. repeat split; try assumption.
      apply trace_subseq_append_keep. exact Htrace. }
    destruct (IHHeval _ Hmatch_branch) as [sctx_src_out [Hstep Hmatch_out]].
    exists sctx_src_out. split.
    + eapply EvalSecIfFalse; [rewrite Hval; exact H | exact Hstep].
    + exact Hmatch_out.
  - unfold match_sec_ctx in Hmatch.
    destruct Hmatch as [Hval [Hsec Htrace]].
    assert (Hmatch_branch :
      match_sec_ctx (sctx_src st++ Branch true) (ctx st++ Branch true)).
    { unfold match_sec_ctx. simpl. repeat split; try assumption.
      apply trace_subseq_append_keep. exact Htrace. }
    destruct (IHHeval1 _ Hmatch_branch) as [sctx_src_mid [Hstep1 Hmatch_mid]].
    destruct (IHHeval2 _ Hmatch_mid) as [sctx_src_out [Hstep2 Hmatch_out]].
    exists sctx_src_out. split.
    + eapply EvalSecWhileTrue; [rewrite Hval; exact H | exact H0 | exact Hstep1 | exact Hstep2].
    + exact Hmatch_out.
  - unfold match_sec_ctx in Hmatch.
    destruct Hmatch as [Hval [Hsec Htrace]].
    exists (sctx_src st++ Branch false). split.
    + eapply EvalSecWhileFalse. rewrite Hval. exact H.
    + unfold match_sec_ctx. simpl. repeat split; try assumption.
      apply trace_subseq_append_keep. exact Htrace.
Qed.

Lemma opt_unskip_skip_sec_complete : forall phi c sctx,
  opt_unskip_cmd c = Skip ->
  exists sctx_src_out,
    eval_sec phi sctx c sctx_src_out /\
    match_sec_ctx sctx_src_out sctx.
Proof.
  intros phi c.
  induction c; simpl; intros sctx Hskip.
  - exists sctx. split; [constructor | apply match_sec_ctx_refl].
  - discriminate.
  - discriminate.
  - discriminate.
  - destruct (opt_unskip_cmd c1) eqn:Hc1;
    destruct (opt_unskip_cmd c2) eqn:Hc2;
    try discriminate;
    inversion Hskip; subst.
    destruct (IHc1 sctx eq_refl) as [sctx1_src [Hsrc1 Hmatch1]].
    destruct (IHc2 sctx1_src eq_refl) as [sctx2_src [Hsrc2 Hmatch2]].
    exists sctx2_src. split.
    + eapply EvalSecSequence; eauto.
    + eapply match_sec_ctx_trans; eauto.
  - destruct (opt_unskip_cmd c1) eqn:Hc1;
    destruct (opt_unskip_cmd c2) eqn:Hc2;
    try discriminate;
    inversion Hskip; subst.
    destruct (interp_arith e (sec_val_of sctx)) eqn:Hcond.
    + destruct (IHc2 (sctx st++ Branch false) eq_refl)
        as [sctx_src_out [Hsrc Hmatch]].
      assert (Hbranch_match : match_sec_ctx (sctx st++ Branch false) sctx).
      { unfold match_sec_ctx. simpl. repeat split; try reflexivity.
        apply trace_subseq_append_drop. apply trace_subseq_refl. }
      exists sctx_src_out. split.
      * eapply EvalSecIfFalse; eauto.
      * eapply match_sec_ctx_trans; eauto.
    + destruct (IHc1 (sctx st++ Branch true) eq_refl)
        as [sctx_src_out [Hsrc Hmatch]].
      assert (Hbranch_match : match_sec_ctx (sctx st++ Branch true) sctx).
      { unfold match_sec_ctx. simpl. repeat split; try reflexivity.
        apply trace_subseq_append_drop. apply trace_subseq_refl. }
      exists sctx_src_out. split.
      * eapply EvalSecIfTrue with (c := S n); eauto.
      * eapply match_sec_ctx_trans; eauto.
  - discriminate.
Qed.

Lemma opt_unskip_sec_backward_while : forall phi e body sctx_opt sctx_opt_out sctx_src,
  eval_sec phi sctx_opt (While e (opt_unskip_cmd body)) sctx_opt_out ->
  (forall sctx_o sctx_o_out sctx_s,
    eval_sec phi sctx_o (opt_unskip_cmd body) sctx_o_out ->
    match_sec_ctx sctx_s sctx_o ->
    exists sctx_s_out,
      eval_sec phi sctx_s body sctx_s_out /\
      match_sec_ctx sctx_s_out sctx_o_out) ->
  match_sec_ctx sctx_src sctx_opt ->
  exists sctx_src_out,
    eval_sec phi sctx_src (While e body) sctx_src_out /\
    match_sec_ctx sctx_src_out sctx_opt_out.
Proof.
  intros phi e body sctx_opt sctx_opt_out sctx_src Hopt Hbody_ih Hmatch.
  revert sctx_src Hmatch.
  remember (While e (opt_unskip_cmd body)) as loop_cmd.
  induction Hopt; intros sctx_src Hmatch; try discriminate.
  - inversion Heqloop_cmd; subst; clear Heqloop_cmd.
    unfold match_sec_ctx in Hmatch.
    destruct Hmatch as [Hval [Hsec Htrace]].
    assert (Hmatch_branch :
      match_sec_ctx (sctx_src st++ Branch true) (ctx st++ Branch true)).
    { unfold match_sec_ctx. simpl. repeat split; try assumption.
      apply trace_subseq_append_keep. exact Htrace. }
    destruct (Hbody_ih _ _ _ Hopt1 Hmatch_branch)
      as [sctx_src_mid [Hsrc_body Hmatch_mid]].
    destruct (IHHopt2 eq_refl _ Hmatch_mid)
      as [sctx_src_out [Hsrc_loop Hmatch_out]].
    exists sctx_src_out. split.
    + eapply EvalSecWhileTrue with (c := interp_arith e (sec_val_of ctx)).
      * rewrite Hval. reflexivity.
      * exact H0.
      * exact Hsrc_body.
      * exact Hsrc_loop.
    + exact Hmatch_out.
  - inversion Heqloop_cmd; subst; clear Heqloop_cmd.
    unfold match_sec_ctx in Hmatch.
    destruct Hmatch as [Hval [Hsec Htrace]].
    assert (Hmatch_branch :
      match_sec_ctx (sctx_src st++ Branch false) (ctx st++ Branch false)).
    { unfold match_sec_ctx. simpl. repeat split; try assumption.
      apply trace_subseq_append_keep. exact Htrace. }
    exists (sctx_src st++ Branch false). split.
    + eapply EvalSecWhileFalse. rewrite Hval. exact H.
    + exact Hmatch_branch.
Qed.

Lemma opt_unskip_sec_complete : forall phi c sctx_opt sctx_opt_out sctx_src,
  eval_sec phi sctx_opt (opt_unskip_cmd c) sctx_opt_out ->
  match_sec_ctx sctx_src sctx_opt ->
  exists sctx_src_out,
    eval_sec phi sctx_src c sctx_src_out /\
    match_sec_ctx sctx_src_out sctx_opt_out.
Proof.
  intros phi c. revert phi.
  induction c; intros phi sctx_opt sctx_opt_out sctx_src Hopt Hmatch; simpl in Hopt.
  - eapply eval_sec_unopt_backward; eauto.
  - eapply eval_sec_unopt_backward; eauto.
  - eapply eval_sec_unopt_backward; eauto.
  - eapply eval_sec_unopt_backward; eauto.
  - destruct (opt_unskip_cmd c1) eqn:Hc1;
    destruct (opt_unskip_cmd c2) eqn:Hc2;
    lazymatch type of Hc1 with
    | _ = Skip =>
      lazymatch type of Hc2 with
      | _ = Skip =>
        inversion Hopt; subst;
        destruct (opt_unskip_skip_sec_complete phi c1 sctx_src Hc1)
          as [sctx1_src [Hsrc1 Hmatch1]];
        destruct (opt_unskip_skip_sec_complete phi c2 sctx1_src Hc2)
          as [sctx2_src [Hsrc2 Hmatch2]];
        exists sctx2_src; split;
        [ eapply EvalSecSequence; eauto
        | eapply match_sec_ctx_trans; [exact Hmatch2 |];
          eapply match_sec_ctx_trans; eauto ]
      | _ =>
        destruct (opt_unskip_skip_sec_complete phi c1 sctx_src Hc1)
          as [sctx1_src [Hsrc1 Hmatch1]];
        edestruct (IHc2 phi sctx_opt sctx_opt_out sctx1_src)
          as [sctx2_src [Hsrc2 Hmatch2]];
        [ exact Hopt | eapply match_sec_ctx_trans; eauto |];
        exists sctx2_src; split;
        [ eapply EvalSecSequence; eauto | exact Hmatch2 ]
      end
    | _ =>
      lazymatch type of Hc2 with
      | _ = Skip =>
        edestruct (IHc1 phi sctx_opt sctx_opt_out sctx_src)
          as [sctx1_src [Hsrc1 Hmatch1]];
        [ exact Hopt | exact Hmatch |];
        destruct (opt_unskip_skip_sec_complete phi c2 sctx1_src Hc2)
          as [sctx2_src [Hsrc2 Hmatch2]];
        exists sctx2_src; split;
        [ eapply EvalSecSequence; eauto | eapply match_sec_ctx_trans; eauto ]
      | _ =>
        inversion Hopt; subst; clear Hopt;
        match goal with
        | Hstep1 : eval_sec phi sctx_opt _ ?sctx1_opt,
          Hstep2 : eval_sec phi ?sctx1_opt _ sctx_opt_out |- _ =>
            edestruct (IHc1 phi sctx_opt sctx1_opt sctx_src)
              as [sctx1_src [Hsrc1 Hmatch1]];
            [ exact Hstep1 | exact Hmatch |];
            edestruct (IHc2 phi sctx1_opt sctx_opt_out sctx1_src)
              as [sctx2_src [Hsrc2 Hmatch2]];
            [ exact Hstep2 | exact Hmatch1 |];
            exists sctx2_src; split;
            [ eapply EvalSecSequence; eauto | exact Hmatch2 ]
        end
      end
    end.
  - unfold match_sec_ctx in Hmatch.
    destruct Hmatch as [Hval [Hsec Htrace]].
    destruct (opt_unskip_cmd c1) eqn:Hc1, (opt_unskip_cmd c2) eqn:Hc2;
    try (
      inversion Hopt; subst; clear Hopt;
      [ assert (Hmatch_branch :
          match_sec_ctx (sctx_src st++ Branch true) (sctx_opt st++ Branch true))
          by (unfold match_sec_ctx; simpl; repeat split; try assumption;
              apply trace_subseq_append_keep; exact Htrace);
        edestruct IHc1 as [sctx_src_out [Hsrc Hmatch_out]];
        [eassumption | exact Hmatch_branch |];
        exists sctx_src_out; split;
        [ eapply EvalSecIfTrue with (c := interp_arith e (sec_val_of sctx_opt));
          [rewrite Hval; reflexivity | eassumption | exact Hsrc]
        | exact Hmatch_out ]
      | assert (Hmatch_branch :
          match_sec_ctx (sctx_src st++ Branch false) (sctx_opt st++ Branch false))
          by (unfold match_sec_ctx; simpl; repeat split; try assumption;
              apply trace_subseq_append_keep; exact Htrace);
        edestruct IHc2 as [sctx_src_out [Hsrc Hmatch_out]];
        [eassumption | exact Hmatch_branch |];
        exists sctx_src_out; split;
        [ eapply EvalSecIfFalse; [rewrite Hval; eassumption | exact Hsrc]
        | exact Hmatch_out ]
      ]
    ).
    inversion Hopt; subst; clear Hopt.
    destruct (opt_unskip_skip_sec_complete phi (If e c1 c2) sctx_src)
      as [sctx_src_out [Hsrc Hmatch_src]].
    + simpl. rewrite Hc1, Hc2. reflexivity.
    + exists sctx_src_out. split; [exact Hsrc |].
      eapply match_sec_ctx_trans; [exact Hmatch_src |].
      unfold match_sec_ctx. repeat split; assumption.
  - eapply opt_unskip_sec_backward_while; eauto.
Qed.


(** ** Main theorem of secret preservation *)

(** [opt_unskip_keeps_secrets_secret] proves the second half of
    [is_safe_opt]: optimized execution preserves the final security labels and
    values of variables that are secret in the source final security environment.

    The proof needs one optimizer-specific expansion lemma:

    - [opt_unskip_sec_complete]: every [eval_sec] execution of [opt_unskip_cmd c]
      can be expanded to an [eval_sec] execution of the source [c] whose final
      context matches the optimized final context. Values and security labels
      are equal; optimized traces may omit removed branch events.

    Once the optimized run is expanded back to a source run, the rest is generic:

    - [eval_sec_deterministic]: the original source run and reconstructed source
      run start from the same security context and execute the same command, so
      their final security contexts are equal.

    The final [match_sec_ctx] relation then yields both required conclusions:

    - final security labels agree for every variable;
    - values agree on every variable that is secret in the source final
      security environment. *)
Lemma opt_unskip_keeps_secrets_secret :
  opt_keeps_secrets_secret opt_unskip.
Proof.
  unfold opt_keeps_secrets_secret, opt_unskip.
  intros sctx sctx' sctx'' [c out] [c' out'] phi Hopt Hsrc Hopt_eval x.
  simpl in Hopt.
  inversion Hopt; subst; clear Hopt.
  simpl in Hopt_eval.
  destruct (opt_unskip_sec_complete phi c sctx sctx'' sctx
    Hopt_eval (match_sec_ctx_refl sctx))
    as [sctx_src [Hsrc_from_opt Hmatch_out]].
  assert (Hsame : sctx' = sctx_src)
    by (eapply eval_sec_deterministic; eauto).
  subst sctx_src.
  unfold match_sec_ctx in Hmatch_out.
  destruct Hmatch_out as [Hval [Hsec _]].
  split.
  - rewrite Hsec. reflexivity.
  - unfold agree_on_secret.
    intros y Hsecret.
    rewrite Hval. reflexivity.
Qed.

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
