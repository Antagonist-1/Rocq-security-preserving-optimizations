Require Import Map.
Require Import Language.Main.
Require Import proofs.SecEnvProofs.
Require Import Coq.Program.Equality.

(* If two valuations agree on public data, then running the same program on them
should produce the same trace.
Note 1: The initial trace has to be nonempty. This is necessary to prove the
sequence case, as the second statement won't always start with an empty trace.
Note 2: Also for the sequence proof, we have to strengthen the definition by
saying that the resulting context agrees on public variables, as in the sequence
case, the second statement doesn't start with the same context.
In both cases, we only strengthen the definition, so it is not a problem.
 *)
Definition non_inference (phi: function_env) (se: sec_env) (c: cmd) (se_out: sec_env) : Prop :=
  forall v1 v2 t_in final_v1 final_v2 trace1 trace2,
    agree_on_public se v1 v2 ->
    eval phi (v1, t_in) c (final_v1, trace1) ->
    eval phi (v2, t_in) c (final_v2, trace2) ->
    trace1 = trace2 /\ agree_on_public se_out final_v1 final_v2.


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
    unfold agree_on_public in Hagree.
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
  join_sec_env se se_inv = se_inv ->
  agree_on_public se v1 v2 ->
  agree_on_public se_inv v1 v2.
Proof.
  intros se se_inv v1 v2 Hjoin Hagree.
  unfold agree_on_public in *. intros x Hpub.
  apply Hagree.
  apply join_sec_public_thn with se_inv.
  rewrite Hjoin. exact Hpub.
Qed.
(* If two valuations agree on the output of the body of a loop, then they
agree on the loop invariant environment (se_inv) *)
Lemma agree_on_public_body_inv : forall se_inv se_body v1 v2,
  join_sec_env se_inv se_body = se_inv ->
  agree_on_public se_body v1 v2 ->
  agree_on_public se_inv v1 v2.
Proof.
  intros se_inv se_body v1 v2 Hjoin Hagree.
  unfold agree_on_public in *. intros x Hpub.
  apply Hagree.
  apply join_sec_public_els with se_inv.
  rewrite Hjoin. exact Hpub.
Qed.


(* A program that is constant time according to our definition should satisfy
non-inference. *)
Theorem ct_cmd_soundness : forall phi se c se_out,
  ct_cmd phi se c se_out ->
  non_inference phi se c se_out.
Proof.
  Ltac invert_evals :=
    inversion Heval1; inversion Heval2; subst.

  Ltac resolve_maps :=
    unfold agree_on_public, sec_lookup in *; intros param Hparam;
    autorewrite with core in *; cbn in *.


  intros phi se c se_out Hct.
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
        eapply interp_sec_public_agree; eauto.
      + destruct (x ==v param); [ congruence | ].
        autorewrite with core in *. apply Hagree. exact Hparam.
  - (* AssignCall*)
    (* Unify duplicated function environments and extract contexts. *)
    invert_evals. rewrite H in H10, H22; inversion H10; inversion H22; subst; clear H10 H22.
    destruct ctx' as [fv1 t1], ctx'0 as [fv2 t2]. cbn in *.
    (* Verify trace-independence of function arguments. *)
    assert (Hargs: agree_on_public ($0 $+ (x6, interp_sec e1 se) $+ (x7, interp_sec e2 se))
           ($0 $+ (x6, interp_arith e1 v1) $+ (x7, interp_arith e2 v1))
           ($0 $+ (x6, interp_arith e1 v2) $+ (x7, interp_arith e2 v2))).
    { resolve_maps. destruct (x7 ==v param); destruct (x6 ==v param);
      subst; autorewrite with core in *; try reflexivity;
      apply f_equal; eapply interp_sec_public_agree; eauto. }
    (* Extract caller trace/memory safety and verify return variable assignment. *)
    edestruct IHHct as [Htrace Hbody]; eauto.
    split; [exact Htrace |].
    resolve_maps. destruct (x ==v param).
    + subst. autorewrite with core in *.
      assert (Hpub: fv1 $? y1 = fv2 $? y1) by (apply Hbody; exact Hparam).
      rewrite H14, H26 in Hpub. inversion Hpub. reflexivity.
    + (* Any other variable *)
      autorewrite with core in *. apply Hagree. exact Hparam.
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
      eapply join_sec_public_thn. exact Hpub.
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
      eapply join_sec_public_els. exact Hpub.
  - (* While *)
    (* The initial valuations agree on the loop invariant environment *)
    assert (Hagree_inv: agree_on_public se_inv v1 v2).
    { eapply agree_on_public_inv; eauto. }
    clear Hagree.

    revert v2 final_v2 trace2 Hagree_inv Heval2.
    dependent induction Heval1.

    + (* EvalWhileTrue *)
      intros v2 final_v2 trace2 Hagree_inv Heval2.
      inversion Heval2; subst; clear Heval2.
      * (* Case 1: Both take True branch *)
        cbn in *.
        destruct ctx' as [v1' t1'].
        match goal with
        | H : eval phi _ body ?ctx2' |- _ => destruct ctx2' as [v2' t2']
        end.

        edestruct IHHct as [Htrace_body Hmem_body]; eauto.
        subst t2'.

        assert (Hagree_inv_after: agree_on_public se_inv v1' v2').
        { eapply agree_on_public_body_inv; eauto. }
        eauto.

      * (* Case 2: Contradiction - v1 True, v2 False *)
        cbn in *.
        (* inversion unified v2 with final_v2 because EvalWhileFalse doesn't change the valuation *)
        assert (Hcond: interp_arith e v1 = interp_arith e final_v2).
        {eapply interp_sec_public_agree; eauto. }
        congruence.

    + (* EvalWhileFalse *)
      intros v2 final_v2 trace2 Hagree_inv Heval2.
      inversion Heval2; subst; clear Heval2.
      * (* Case 3: Contradiction - v1 False, v2 True *)
        cbn in *.
        (* inversion unified v1 with final_v1 because EvalWhileFalse doesn't change the valuation *)
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

(* If two dynamic environments agree on statically public variables, then they
   will compute the exact same dynamic label for any statically public
   expression. *)
Lemma interp_sec_dynamic_agree : forall e se se_dyn1 se_dyn2,
  (forall x, sec_lookup se x = Public -> sec_lookup se_dyn1 x = sec_lookup se_dyn2 x) ->
  interp_sec e se = Public ->
  interp_sec e se_dyn1 = interp_sec e se_dyn2.
Proof.
  induction e; intros se se_dyn1 se_dyn2 Hagree Hpub; cbn in *.
  - (* Const *) reflexivity.
  - (* Var *) apply Hagree. exact Hpub.
  - (* Binop *)
    destruct (interp_sec e1 se) eqn:He1;
    destruct (interp_sec e2 se) eqn:He2;
    cbn in Hpub; try discriminate.
    rewrite (IHe1 se se_dyn1 se_dyn2 Hagree eq_refl).
    rewrite (IHe2 se se_dyn1 se_dyn2 Hagree eq_refl).
    reflexivity.
Qed.


Definition non_inference_sec (phi: function_env) (se_static: sec_env) (c: cmd) (se_static_out: sec_env) : Prop :=
  forall ctx1_in ctx2_in ctx1_out ctx2_out,
    (* If the initial contexts agree on public data and labels... *)
    agree_on_public_sec_ctx se_static ctx1_in ctx2_in ->
    (* ...and they start with identical traces... *)
    sec_trace_of ctx1_in = sec_trace_of ctx2_in ->
    (* ...and they both evaluate the command... *)
    eval_sec phi ctx1_in c ctx1_out ->
    eval_sec phi ctx2_in c ctx2_out ->
    (* ...then their output traces must be identical... *)
    sec_trace_of ctx1_out = sec_trace_of ctx2_out /\ 
    (* ...and their output contexts must still agree on public data and labels. *)
    agree_on_public_sec_ctx se_static_out ctx1_out ctx2_out.

    Theorem ct_cmd_soundness_sec : forall phi se c se_out,
  ct_cmd phi se c se_out ->
  non_inference_sec phi se c se_out.
  Proof.
  Admitted.