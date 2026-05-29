Require Import Language.Main.

(* These theorems shows equivalence between the 3 eval inductives we created. It does so by either lifting them (by adding a trace or a sec_env to its context), or projecting them (by removing the trace or sec_env) *)


Create HintDb eval_db.
Hint Constructors eval eval_trace eval_sec : eval_db.

Ltac eval_simpl :=
  unfold val_of, trace_of, sec_val_of, sec_trace_of, sec_of in *; simpl in *.

(*
PROJECTING THEOREMS
*)

(* eval_trace -> eval *)
Theorem Eval_proj_trace : forall ctx c ctx',
    eval_trace ctx c ctx' -> 
    eval (val_of ctx) c (val_of ctx').
Proof.
  induction 1; eval_simpl; eauto with eval_db.
Qed.

(* eval_sec -> eval_trace *)
Theorem Eval_proj_sec : forall ctx c ctx',
    eval_sec ctx c ctx' ->
    eval_trace (sec_val_of ctx, sec_trace_of ctx) c (sec_val_of ctx', sec_trace_of ctx').

Proof.
  induction 1; eval_simpl; eauto with eval_db.
Qed.

(* eval_sec -> eval *)
Theorem Eval_proj_sec_trace : forall ctx c ctx',
    eval_sec ctx c ctx' ->
    eval (sec_val_of ctx) c (sec_val_of ctx').
Proof.
    intros.
    apply Eval_proj_sec in H.
    apply Eval_proj_trace in H.
    easy.
Qed.
    
(* 
LIFTING THEOREMS
*)


(* eval -> eval_trace *)
Theorem Eval_lift_trace : forall v c v',
    eval v c v' ->
    forall t, exists t',
    eval_trace (v, t) c (v',t').
Proof.
  induction 1; simpl; intros.
  - eexists. apply EvalTraceSkip.
  - eexists. eapply EvalTraceAssign; eauto.
  - eexists. eapply EvalTraceCmovTrue; eauto.
  - eexists. eapply EvalTraceCmovFalse; eauto.
  - specialize (IHeval1 t). destruct IHeval1 as [t1 Ht1].
    specialize (IHeval2 t1). destruct IHeval2 as [t2 Ht2].
    eexists. eapply EvalTraceSequence; eauto.
  - specialize (IHeval (t ++ Branch true :: nil)%list).
    destruct IHeval as [t' Ht'].
    eexists. eapply EvalTraceIfTrue; eauto.
  - specialize (IHeval (t ++ Branch false :: nil)%list).
    destruct IHeval as [t' Ht'].
    eexists. eapply EvalTraceIfFalse; eauto.
  - specialize (IHeval1 (t ++ Branch true :: nil)%list).
    destruct IHeval1 as [t1 Ht1].
    specialize (IHeval2 t1). destruct IHeval2 as [t2 Ht2].
    eexists. eapply EvalTraceWhileTrue; eauto.
  - eexists. apply EvalTraceWhileFalse; eauto.
Qed.

(* eval_trace -> eval_sec *)
Theorem Eval_lift_sec : forall v t c v' t',
    eval_trace (v, t) c (v', t') ->
    forall sec, exists sec',
    eval_sec (v, sec, t) c (v', sec', t').
Proof.
    intros v t c v' t' Heval.
    dependent induction Heval; simpl; intros.
    - do 2 econstructor.
    - do 2 econstructor; eauto.
    - eexists. eapply EvalSecCmovTrue; eauto.
    - eexists. eapply EvalSecCmovFalse; eauto.
    - destruct ctx1.
        specialize (IHHeval1 _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) sec).
        destruct IHHeval1 as [sec' Hsec'].
        specialize (IHHeval2 _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) sec').
        destruct IHHeval2 as [sec'' Hsec''].
        eexists.
        econstructor.
        eapply Hsec'.
        eapply Hsec''.
    - specialize (IHHeval _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) sec).
        destruct IHHeval as [sec' Hsec']. simpl in Hsec'.
        exists sec'.
        eapply EvalSecIfTrue; eauto.
    - specialize (IHHeval _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) sec).
        destruct IHHeval as [sec' Hsec']. simpl in Hsec'.
        exists sec'.
        eapply EvalSecIfFalse; eauto.
    - destruct ctx'.
        specialize (IHHeval1 _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) sec).
        destruct IHHeval1 as [sec' Hsec'].
        specialize (IHHeval2 _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) sec').
        destruct IHHeval2 as [sec'' Hsec''].
        eexists.
        eapply EvalSecWhileTrue; eauto.
    - eexists.
        eapply EvalSecWhileFalse; eauto.
Qed.


(* eval -> eval_sec *)
Theorem Eval_lift_trace_sec : forall v c v',
    eval v c v'->
    forall sec t, exists sec' t',
    eval_sec (v, sec, t) c (v', sec', t').
Proof.
    intros.
    eapply Eval_lift_trace in H.
    destruct H as [t' H].
    eapply Eval_lift_sec in H.
    destruct H as [sec' H].
    eauto.
Qed.
