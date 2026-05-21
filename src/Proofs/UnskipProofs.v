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

(* Since [opt_unskip_cmd] no longer removes [If _ Skip Skip], a command can optimize
   to [Skip] only when it is operationally a no-op with exactly the same trace. *)
Lemma opt_unskip_skip_trace_complete : forall phi c ctx,
  opt_unskip_cmd c = Skip ->
  eval_trace phi ctx c ctx.
Proof.
  induction c; simpl; intros ctx Hskip.
  - constructor.
  - discriminate.
  - discriminate.
  - discriminate.
  - destruct (opt_unskip_cmd c1) eqn:Hc1;
    destruct (opt_unskip_cmd c2) eqn:Hc2;
    try discriminate;
    inversion Hskip; subst.
    pose proof (IHc1 ctx eq_refl) as Hsrc1.
    pose proof (IHc2 ctx eq_refl) as Hsrc2.
    eapply EvalTraceSequence with (ctx1 := ctx); eauto.
  - discriminate.
  - discriminate.
Qed.

(* Any optimized trace execution can be expanded into a source execution with
   exactly the same final context. This is true because [opt_unskip_cmd] only removes
   sequence-level [Skip] commands and keeps all branch-producing syntax. *)
Lemma opt_unskip_trace_complete : forall phi c ctx ctx_opt,
  eval_trace phi ctx (opt_unskip_cmd c) ctx_opt ->
  eval_trace phi ctx c ctx_opt.
Proof.
  induction c; simpl; intros ctx ctx_opt Hopt.
  - exact Hopt.
  - exact Hopt.
  - exact Hopt.
  - exact Hopt.
  - destruct (opt_unskip_cmd c1) eqn:Hc1;
    destruct (opt_unskip_cmd c2) eqn:Hc2;
    simpl in Hopt;
    try solve [
      pose proof (opt_unskip_skip_trace_complete phi c1 ctx Hc1) as Hsrc1;
      pose proof (IHc2 ctx ctx_opt Hopt) as Hsrc2;
      eapply EvalTraceSequence with (ctx1 := ctx); eauto
    ];
    try solve [
      pose proof (IHc1 ctx ctx_opt Hopt) as Hsrc1;
      pose proof (opt_unskip_skip_trace_complete phi c2 ctx_opt Hc2) as Hsrc2;
      eapply EvalTraceSequence with (ctx1 := ctx_opt); eauto
    ];
    inversion Hopt; subst;
    pose proof (IHc1 ctx ctx1 H2) as Hsrc1;
    pose proof (IHc2 ctx1 ctx_opt H4) as Hsrc2;
    eapply EvalTraceSequence; eauto.
  - inversion Hopt; subst.
    + eapply EvalTraceIfTrue; eauto.
    + eapply EvalTraceIfFalse; eauto.
  - remember (While e (opt_unskip_cmd c)) as copt eqn:Hcopt.
    induction Hopt; inversion Hcopt; subst.
    + pose proof (IHc (ctx t++ Branch true) ctx' Hopt1) as Hbody_src.
      pose proof (IHHopt2 eq_refl) as Hloop_src.
      eapply EvalTraceWhileTrue; eauto.
    + eapply EvalTraceWhileFalse; eauto.
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
  intros v1 v2 t_in final_v1 final_v2 trace1 trace2
    Hagree Hopt_eval1 Hopt_eval2.
  eapply Hni; eauto using opt_unskip_trace_complete.
Qed.



(** * Secret Preservation Support *)
(* This part uses eval_sec *)

Lemma opt_unskip_skip_sec_complete : forall phi c ctx,
  opt_unskip_cmd c = Skip ->
  eval_sec phi ctx c ctx.
Proof.
  induction c; simpl; intros ctx Hskip.
  - constructor.
  - discriminate.
  - discriminate.
  - discriminate.
  - destruct (opt_unskip_cmd c1) eqn:Hc1;
    destruct (opt_unskip_cmd c2) eqn:Hc2;
    try discriminate;
    inversion Hskip; subst.
    pose proof (IHc1 ctx eq_refl) as Hsrc1.
    pose proof (IHc2 ctx eq_refl) as Hsrc2.
    eapply EvalSecSequence with (ctx1 := ctx); eauto.
  - discriminate.
  - discriminate.
Qed.

(* Same expansion property for [eval_sec]: final valuation, security
   environment, and trace are preserved exactly. *)
Lemma opt_unskip_sec_complete : forall phi c ctx ctx_opt,
  eval_sec phi ctx (opt_unskip_cmd c) ctx_opt ->
  eval_sec phi ctx c ctx_opt.
Proof.
  induction c; simpl; intros ctx ctx_opt Hopt.
  - exact Hopt.
  - exact Hopt.
  - exact Hopt.
  - exact Hopt.
  - destruct (opt_unskip_cmd c1) eqn:Hc1;
    destruct (opt_unskip_cmd c2) eqn:Hc2;
    simpl in Hopt;
    try solve [
      pose proof (opt_unskip_skip_sec_complete phi c1 ctx Hc1) as Hsrc1;
      pose proof (IHc2 ctx ctx_opt Hopt) as Hsrc2;
      eapply EvalSecSequence with (ctx1 := ctx); eauto
    ];
    try solve [
      pose proof (IHc1 ctx ctx_opt Hopt) as Hsrc1;
      pose proof (opt_unskip_skip_sec_complete phi c2 ctx_opt Hc2) as Hsrc2;
      eapply EvalSecSequence with (ctx1 := ctx_opt); eauto
    ];
    inversion Hopt; subst;
    pose proof (IHc1 ctx ctx1 H2) as Hsrc1;
    pose proof (IHc2 ctx1 ctx_opt H4) as Hsrc2;
    eapply EvalSecSequence; eauto.
  - inversion Hopt; subst.
    + eapply EvalSecIfTrue; eauto.
    + eapply EvalSecIfFalse; eauto.
  - remember (While e (opt_unskip_cmd c)) as copt eqn:Hcopt.
    induction Hopt; inversion Hcopt; subst.
    + pose proof (IHc (ctx st++ Branch true) ctx' Hopt1) as Hbody_src.
      pose proof (IHHopt2 eq_refl) as Hloop_src.
      eapply EvalSecWhileTrue; eauto.
    + eapply EvalSecWhileFalse; eauto.
Qed.

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
  unfold opt_keeps_secrets_secret.
  intros sctx sctx' sctx'' pgm pgm' phi' Hopt Hsrc Hopt_eval x.
  unfold opt_unskip, opt_unskip_cmd in Hopt.
  destruct pgm as [c out].
  destruct pgm' as [c' out'].
  simpl in Hopt.
  inversion Hopt; subst; clear Hopt.
  simpl in Hopt_eval.
  pose proof (opt_unskip_sec_complete phi' c sctx sctx'' Hopt_eval)
    as Hsrc_from_opt.
  pose proof (eval_sec_deterministic phi' c sctx sctx'
    sctx''
    Hsrc Hsrc_from_opt) as Hsame.
  subst sctx''.
  split.
  - reflexivity.
  - unfold agree_on_secret.
    intros y _.
    reflexivity.
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
