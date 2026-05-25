Require Import Map.
Require Import VarSets.
Require Import Language.Main.
Require Import Language.Analysis.
Require Import Proofs.VarSetAgreement.

From Stdlib Require Import Lia.


Lemma interp_arith_agree: forall e v1 v2,
  agree_on (vars_in_expr e) v1 v2 ->
  interp_arith e v1 = interp_arith e v2.
Proof.
  unfold agree_on.
  induction e; simpl; intros.
  - reflexivity.
  - rewrite H.
    reflexivity.
    rewrite VarSet.mem_spec.
    rewrite VarSet.singleton_spec.
    reflexivity.
  - erewrite IHe1.
    erewrite IHe2.
    1: reflexivity.
    1,2: intros;
      apply H;
      rewrite VarSet.mem_spec in *;
      rewrite VarSet.union_spec.
    + right. assumption.
    + left. assumption.
Qed.

Ltac solve_dse_cmov_interp H_agree :=
  match goal with
  | [ H : interp_arith ?e ?v1 = ?c |- interp_arith ?e ?v2 = ?c ] =>
      rewrite <- H; apply interp_arith_agree;
      eapply agree_on_subset; [| apply agree_on_sym; exact H_agree]; VarSetDecide.fsetdec
  end.

Lemma while_fixpoint_contains_out: forall f cond_vars out fuel,
  VarSet.Subset out (while_fixpoint f cond_vars out fuel).
Proof.
  intros f cond_vars out fuel.
  revert out.
  induction fuel; simpl; intros out.
  - apply vsp.subset_refl.
  - destruct (VarSet.equal out (VarSet.union (VarSet.union out cond_vars) (f out))) eqn:H.
    + apply vsp.subset_refl.
    + apply vsp.subset_trans with (VarSet.union (VarSet.union out cond_vars) (f out)).
      * eapply vsp.subset_trans; [apply vsp.union_subset_1|].
        apply vsp.union_subset_1.
      * apply IHfuel.
Qed.

Lemma while_fixpoint_at_fixpoint: forall f cond_vars out fuel,
  VarSet.equal out (VarSet.union (VarSet.union out cond_vars) (f out)) = true ->
  while_fixpoint f cond_vars out fuel = out.
Proof.
  induction fuel; simpl; intros H.
  - reflexivity.
  - rewrite H. reflexivity.
Qed.

Lemma while_fixpoint_monotone: forall f cond_vars out1 out2 fuel,
  (forall s1 s2, VarSet.Subset s1 s2 -> VarSet.Subset (f s1) (f s2)) ->
  VarSet.Subset out1 out2 ->
  VarSet.Subset (while_fixpoint f cond_vars out1 fuel) (while_fixpoint f cond_vars out2 fuel).
Proof.
  intros f cond_vars out1 out2 fuel Hf.
  revert out1 out2.
  induction fuel; simpl; intros out1 out2 H0.
  - assumption.
  - assert (H_in: VarSet.Subset
        (VarSet.union (VarSet.union out1 cond_vars) (f out1))
        (VarSet.union (VarSet.union out2 cond_vars) (f out2))).
    { apply vsp.union_subset_3.
      - apply vsp.union_subset_3.
        + eapply vsp.subset_trans; [exact H0|].
          eapply vsp.subset_trans; [apply vsp.union_subset_1|].
          apply vsp.union_subset_1.
        + eapply vsp.subset_trans; [apply vsp.union_subset_2|].
          apply vsp.union_subset_1.
      - eapply vsp.subset_trans; [apply Hf; exact H0|].
        apply vsp.union_subset_2.
    }
    destruct (VarSet.equal out1 (VarSet.union (VarSet.union out1 cond_vars) (f out1))) eqn:Hout1,
             (VarSet.equal out2 (VarSet.union (VarSet.union out2 cond_vars) (f out2))) eqn:Hout2.
    + assumption.
    + apply vsp.subset_trans with out2; [assumption|].
      apply vsp.subset_trans with (VarSet.union (VarSet.union out2 cond_vars) (f out2)).
      * eapply vsp.subset_trans; [apply vsp.union_subset_1|].
        apply vsp.union_subset_1.
      * apply while_fixpoint_contains_out.
    + assert (H_in2_out2: VarSet.Subset
          (VarSet.union (VarSet.union out2 cond_vars) (f out2)) out2).
      { apply vsp.subset_equal.
        apply vsp.equal_sym.
        apply VarSet.equal_spec.
        exact Hout2. }
      apply vsp.subset_trans with (while_fixpoint f cond_vars out2 fuel).
      * apply IHfuel.
        eapply vsp.subset_trans; [exact H_in | exact H_in2_out2].
      * rewrite while_fixpoint_at_fixpoint by exact Hout2.
        apply vsp.subset_refl.
    + apply IHfuel. exact H_in.
Qed.

Lemma while_fixpoint_vars_bound: forall f cond_vars out fuel universe,
  VarSet.Subset out universe ->
  VarSet.Subset cond_vars universe ->
  (forall s, VarSet.Subset s universe -> VarSet.Subset (f s) universe) ->
  VarSet.Subset (while_fixpoint f cond_vars out fuel) universe.
Proof.
  intros f cond_vars out fuel universe H0 H1 H2.
  generalize out H0.
  induction fuel; simpl; intros.
  - assumption.
  - destruct (VarSet.equal out0 (VarSet.union (VarSet.union out0 cond_vars) (f out0))).
    + assumption.
    + rewrite IHfuel.
      * VarSetDecide.fsetdec.
      * rewrite H2.
        2: assumption.
        rewrite H3.
        rewrite H1.
        VarSetDecide.fsetdec.
Qed.

Lemma liveness_vars_bound: forall c out,
  VarSet.Subset (liveness c out) (VarSet.union out (vars_in_cmd c)).
Proof.
  induction c; simpl; intros.
  - VarSetDecide.fsetdec.
  - destruct (VarSet.mem s out) eqn:Hs.
    all: VarSetDecide.fsetdec.
  - VarSetDecide.fsetdec.
  - destruct (VarSet.mem s out) eqn:Hs.
    all: VarSetDecide.fsetdec.
  - eapply vsp.subset_trans.
    apply IHc1.
    rewrite IHc2.
    VarSetDecide.fsetdec.
  - rewrite IHc1.
    rewrite IHc2.
    VarSetDecide.fsetdec.
  - apply while_fixpoint_vars_bound.
    + VarSetDecide.fsetdec.
    + VarSetDecide.fsetdec.
    + intros.
      rewrite IHc.
      VarSetDecide.fsetdec.
Qed.

Lemma while_fixpoint_contains_cond_vars: forall f cond_vars out fuel,
    fuel > 0 ->
  VarSet.Subset cond_vars (while_fixpoint f cond_vars out fuel).
Proof.
  intros f cond_vars out fuel.
  revert out.
  induction fuel; simpl; intros.
  - lia.
  - destruct (VarSet.equal out (VarSet.union (VarSet.union out cond_vars) (f out))) eqn:Hout.
    apply VarSet.equal_spec in Hout.
    rewrite Hout.
    VarSetDecide.fsetdec.
    destruct fuel as [|n].
    + simpl.
      VarSetDecide.fsetdec.
    + apply IHfuel.
      lia.
Qed.

Lemma liveness_while_cond_subset : forall body e out,
  VarSet.Subset (vars_in_expr e) (liveness (While e body) out).
Proof.
  intros body e out. simpl.
  destruct (VarSet.cardinal (VarSet.union (vars_in_expr e) (vars_in_cmd body))) eqn:Hfuel.
  - apply vsp.cardinal_Empty in Hfuel. VarSetDecide.fsetdec.
  - apply while_fixpoint_contains_cond_vars. lia.
Qed.

Lemma cardinal_diff_with_witness : forall universe out _in x,
  VarSet.In x universe ->
  VarSet.In x _in ->
  ~ VarSet.In x out ->
  VarSet.Subset out _in ->
  VarSet.cardinal (VarSet.diff universe _in) < VarSet.cardinal (VarSet.diff universe out).
Proof.
  intros. apply vsp.subset_cardinal_lt with x; VarSetDecide.fsetdec.
Qed.

Lemma while_fixpoint_is_fixpoint: forall body e out n,
  VarSet.cardinal (VarSet.diff (VarSet.union (vars_in_expr e) (vars_in_cmd body)) out) <= n ->
  let fp := while_fixpoint (liveness body) (vars_in_expr e) out n in
  VarSet.Equal (VarSet.union (VarSet.union fp (vars_in_expr e)) (liveness body fp)) fp.
Proof.
  intros body e out n. revert body e out.
  induction n; simpl; intros body e out H.
  - apply Nat.le_0_r, vsp.cardinal_Empty in H.
    pose proof (liveness_vars_bound body out). VarSetDecide.fsetdec.
  - set (universe := VarSet.union (vars_in_expr e) (vars_in_cmd body)).
    set (_in := VarSet.union (VarSet.union out (vars_in_expr e)) (liveness body out)).
    destruct (VarSet.equal out _in) eqn:Heq.
    + apply VarSet.equal_spec in Heq. VarSetDecide.fsetdec.
    + apply IHn. fold universe in H.
      destruct (VarSet.choose (VarSet.diff _in out)) as [x|] eqn:Hchoose.
      * apply VarSet.choose_spec1, VarSet.diff_spec in Hchoose as [Hxin Hxout].
        assert (Hxuniv: VarSet.In x universe).
        { unfold _in in Hxin. rewrite !VarSet.union_spec in Hxin.
          destruct Hxin as [[Hxo|Hxe]|Hxl].
          - contradiction.
          - unfold universe. VarSetDecide.fsetdec.
          - assert (VarSet.In x (VarSet.union out (vars_in_cmd body)))
              by (apply liveness_vars_bound; exact Hxl).
            unfold universe. VarSetDecide.fsetdec. }
        assert (VarSet.cardinal (VarSet.diff universe _in) <
                VarSet.cardinal (VarSet.diff universe out))
          by (apply cardinal_diff_with_witness with x;
              [exact Hxuniv | exact Hxin | exact Hxout | VarSetDecide.fsetdec]).
        fold universe.
        lia.
      * exfalso. apply VarSet.choose_spec2 in Hchoose.
        assert (VarSet.equal out _in = true)
          by (apply VarSet.equal_spec; VarSetDecide.fsetdec).
        congruence.
Qed.

Lemma liveness_while_body_closed : forall body e out,
  VarSet.Subset (liveness body (liveness (While e body) out)) (liveness (While e body) out).
Proof.
  intros body e out.
  assert (Hbound: VarSet.cardinal (VarSet.diff (VarSet.union (vars_in_expr e) (vars_in_cmd body)) out) <=
          VarSet.cardinal (VarSet.union (vars_in_expr e) (vars_in_cmd body)))
    by (apply vsp.subset_cardinal; VarSetDecide.fsetdec).
  pose proof while_fixpoint_is_fixpoint body e out _ Hbound as Heq.
  simpl in Heq. VarSetDecide.fsetdec.
Qed.
