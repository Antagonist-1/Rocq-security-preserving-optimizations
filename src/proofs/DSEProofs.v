Require Import Map.
Require Import VarSets.
Require Import Language.Main.
Require Import Language.Optimizations.

(* ================================================================= *)
(* agree_on: two valuations agree on all variables in a set          *)
(* ================================================================= *)

Definition agree_on (S: var_set) (v1 v2: valuation) : Prop :=
  forall x, VarSet.mem x S = true -> v1 $? x = v2 $? x.

(* ================================================================= *)
(* Step 1: Basic agree_on lemmas                                      *)
(* ================================================================= *)

Lemma agree_on_refl: forall S v,
  agree_on S v v.
Proof. 
  unfold agree_on.
  reflexivity.
Qed.


Lemma agree_on_sym: forall S v1 v2,
  agree_on S v1 v2 -> agree_on S v2 v1.
Proof.
  unfold agree_on.
  intros.
  apply eq_sym.
  firstorder.
Qed.

Lemma agree_on_subset: forall S S' v1 v2,
  VarSet.Subset S' S ->
  agree_on S v1 v2 ->
  agree_on S' v1 v2.
Proof.
  unfold agree_on, VarSet.Subset.
  intros.
  apply H0.
  apply VarSet.mem_spec.
  apply VarSet.mem_spec in H1.
  apply H.
  apply H1.
Qed.

(* x is not in S, so updating x doesn't affect agreement on S *)
Lemma agree_on_update_out: forall S v x a,
  VarSet.mem x S = false ->
  agree_on S v (v $+ (x, a)).
Proof.
  unfold agree_on.
  intros.
  destruct (VarSetProps.FM.eq_dec x x0).
  - subst.
    rewrite H in H0.
    discriminate.
  - rewrite lookup_add_ne.
    + reflexivity.
    + auto.
Qed.

(* Updating the same key on both sides preserves agreement *)
Lemma agree_on_update_both: forall S v1 v2 x a,
  agree_on S v1 v2 ->
  agree_on S (v1 $+ (x, a)) (v2 $+ (x, a)).
Proof.
  unfold agree_on.
  intros.
  destruct (VarSetProps.FM.eq_dec x x0).
  - repeat rewrite lookup_add_eq; [reflexivity | assumption | assumption].
  - repeat rewrite lookup_add_ne.
    1: apply H; exact H0.
    1,2 : auto.
Qed.


Lemma agree_on_remove_both: forall S v1 v2 x,
  agree_on S v1 v2 ->
  agree_on (VarSet.remove x S) v1 v2.
Proof.
  unfold agree_on.
  intros.
  destruct (VarSetProps.FM.eq_dec x x0).
  - subst.
    exfalso.
    rewrite VarSet.mem_spec in H0.
    rewrite VarSet.remove_spec in H0.
    tauto.
  - apply H.
    rewrite VarSet.mem_spec in *.
    rewrite VarSet.remove_spec in H0.
    tauto.
Qed.

(* ================================================================= *)
(* Step 2: interp_arith only depends on vars_in_expr                 *)
(* ================================================================= *)

Lemma interp_arith_agree: forall e v1 v2,
  agree_on (vars_in_expr e) v1 v2 ->
  interp_arith e v1 = interp_arith e v2.
Proof. Admitted.

(* ================================================================= *)
(* Step 3: Liveness monotonicity and variable bound                  *)
(* ================================================================= *)

(* Larger live-out set => larger live-in set *)
Lemma liveness_monotone: forall c out1 out2,
  VarSet.Subset out1 out2 ->
  VarSet.Subset (liveness c out1) (liveness c out2).
Proof. Admitted.

(* liveness can only introduce variables already in out or in vars_in_cmd c *)
Lemma liveness_vars_bound: forall c out,
  VarSet.Subset (liveness c out) (VarSet.union out (vars_in_cmd c)).
Proof. Admitted.

(* ================================================================= *)
(* Step 4: while_fixpoint properties                                  *)
(* ================================================================= *)

(* The result always contains the initial out *)
Lemma while_fixpoint_contains_out: forall f cond_vars out fuel,
  VarSet.Subset out (while_fixpoint f cond_vars out fuel).
Proof. Admitted.

(* The result always contains cond_vars *)
Lemma while_fixpoint_contains_cond_vars: forall f cond_vars out fuel,
  VarSet.Subset cond_vars (while_fixpoint f cond_vars out fuel).
Proof. Admitted.

(* KEY LEMMA: with enough fuel the result is a genuine fixpoint.
   Enough fuel = cardinal of variables that can ever be added
   = cardinal (vars_in_cmd (While e body)).
   The fixpoint fp satisfies: fp ⊇ fp ∪ cond_vars ∪ f(fp), i.e. it is
   a post-fixpoint of the iteration step. *)
Lemma while_fixpoint_is_fixpoint: forall body e out n,
  VarSet.cardinal (VarSet.union (vars_in_expr e) (vars_in_cmd body)) <= n ->
  let fp := while_fixpoint (liveness body) (vars_in_expr e) out n in
  VarSet.Subset
    (VarSet.union (VarSet.union fp (vars_in_expr e)) (liveness body fp))
    fp.
Proof. Admitted.

(* ================================================================= *)
(* Step 5: dse_helper soundness (main inductive lemma)               *)
(* ================================================================= *)

(* Given:
   - eval phi ctx1 c ctx1'         (original terminates)
   - ctx2 agrees with ctx1 on liveness c out  (same live vars at entry)
   - ctx1 and ctx2 have the same trace
   Conclude:
   - dse_helper c out terminates from ctx2, producing ctx2'
   - ctx1' and ctx2' agree on out
   - ctx1' and ctx2' have the same trace

   Proved by induction on the eval derivation.
   Uses: interp_arith_agree, while_fixpoint_is_fixpoint,
         while_fixpoint_contains_cond_vars, agree_on lemmas. *)
Lemma dse_helper_sound: forall phi c out ctx1 ctx1',
  eval phi ctx1 c ctx1' ->
  forall ctx2,
    agree_on (liveness c out) (val_of ctx1) (val_of ctx2) ->
    trace_of ctx1 = trace_of ctx2 ->
    exists ctx2',
      eval phi ctx2 (dse_helper c out) ctx2' /\
      agree_on out (val_of ctx1') (val_of ctx2') /\
      trace_of ctx1' = trace_of ctx2'.
Proof. Admitted.

(* ================================================================= *)
(* Step 6: opt_unskip soundness                                       *)
(* ================================================================= *)

(* opt_unskip preserves the final valuation.
   Traces may differ: "If Skip Skip" becomes "Skip" (no Branch event).
   We do not claim trace equality. *)
Lemma opt_unskip_sound: forall phi c ctx ctx',
  eval phi ctx c ctx' ->
  exists ctx_opt,
    eval phi ctx (opt_unskip c) ctx_opt /\
    val_of ctx' = val_of ctx_opt.
Proof. Admitted.

(* ================================================================= *)
(* Step 7: Main theorem                                               *)
(* ================================================================= *)

(* opt_dse is a wrapper: opt_unskip (dse_helper c out).
   The optimized program produces the same values on all output variables. *)
Theorem opt_dse_sound: forall phi (pgm: program) ctx ctx',
  eval phi ctx (cmd_of pgm) ctx' ->
  exists ctx_opt,
    eval phi ctx (opt_dse pgm) ctx_opt /\
    agree_on (output_of pgm) (val_of ctx') (val_of ctx_opt). (*all output vars are the same*)
Proof.
  intros phi pgm ctx ctx' Heval.
  unfold opt_dse.
  (* Step 1: apply dse_helper_sound with ctx1 = ctx2 = ctx *)
  assert (H_dse: exists ctx_dse,
    eval phi ctx (dse_helper (cmd_of pgm) (output_of pgm)) ctx_dse /\
    agree_on (output_of pgm) (val_of ctx') (val_of ctx_dse) /\
    trace_of ctx' = trace_of ctx_dse).
  {
    apply dse_helper_sound with (ctx1 := ctx).
    - exact Heval.
    - apply agree_on_refl.
    - reflexivity.
  }
  destruct H_dse as [ctx_dse [Hdse_eval [Hdse_agree _]]].
  (* Step 2: apply opt_unskip_sound to ctx_dse *)
  apply opt_unskip_sound in Hdse_eval.
  destruct Hdse_eval as [ctx_opt [Hunskip_eval Hunskip_val]].
  exists ctx_opt.
  split.
  - exact Hunskip_eval.
  - rewrite <- Hunskip_val. exact Hdse_agree.
Qed.
