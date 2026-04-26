Require Import Map.
Require Import Language.Main.

Lemma lookup_join_env : forall se1 se2 x,
  sec_lookup (join_sec_env se1 se2) x = join_sec (sec_lookup se1 x) (sec_lookup se2 x).
Proof.
  intros se1 se2 x.
  unfold sec_lookup, join_sec_env.
  rewrite lookup_merge.
  destruct (se1 $? x) as [l1|] eqn:H1;
  destruct (se2 $? x) as [l2|] eqn:H2;
  cbn; try reflexivity.
  - destruct l1; reflexivity.
  - destruct l2; reflexivity.
Qed.


Lemma join_sec_public:
  forall se1 se2 x,
  sec_lookup (join_sec_env se1 se2) x = Public ->
  sec_lookup se1 x = Public /\ sec_lookup se2 x = Public.
Proof.
  intros se1 se2 x Hjoin.
  rewrite lookup_join_env in Hjoin.
  destruct (sec_lookup se1 x) eqn:H1;
  destruct (sec_lookup se2 x) eqn:H2;
  cbn in Hjoin; try discriminate; split; reflexivity.
Qed.

Lemma join_sec_public_thn:
  forall se1 se2 x,
  sec_lookup (join_sec_env se1 se2) x = Public ->
  sec_lookup se1 x = Public.
Proof. intros. apply join_sec_public in H. destruct H. assumption. Qed.

Lemma join_sec_public_els:
  forall se1 se2 x,
  sec_lookup (join_sec_env se1 se2) x = Public ->
  sec_lookup se2 x = Public.
Proof. intros. apply join_sec_public in H. destruct H. assumption. Qed.