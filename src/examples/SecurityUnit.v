Require Import Map.
Require Import Language.Main.
Require Import examples.Programs.
From Stdlib Require Import List.
Import ListNotations.

Ltac crush_security :=
  unfold interp_sec, sec_lookup;
  cbn; autorewrite with core; reflexivity.

(* `eval_sec`: copying a secret value taints the destination as `Secret`. *)
Example eval_sec_secret_copy_taints_x :
  eval_sec $0
    (($0 $+ ("secret", 7)), ($0 $+ ("secret", Secret)), nil)
    secret_copy
    (($0 $+ ("secret", 7) $+ ("x", 7)), ($0 $+ ("secret", Secret) $+ ("x", Secret)), nil).
Proof.
  econstructor; crush_security.
Qed.

(* `eval_sec`: when the source has no security label, the destination defaults to `Public`. *)
Example eval_sec_secret_copy_defaults_to_public :
  eval_sec $0
    (($0 $+ ("secret", 7)), $0, nil)
    secret_copy
    (($0 $+ ("secret", 7) $+ ("x", 7)), ($0 $+ ("x", Public)), nil).
Proof.
  econstructor; crush_security.
Qed.

(* `ct_cmd`: branching on a public guard is accepted by the constant-time checker. *)
Example ct_public_guard_program_ok :
  exists se',
    ct_cmd $0
      ($0 $+ ("flag", Public))
      public_guard_program
      se'.
Proof.
  eexists.
  repeat econstructor; crush_security.
Qed.

(* `ct_cmd`: branching on a secret guard is rejected by the constant-time checker. *)
Example ct_secret_guard_program_rejected :
  ~ exists se',
      ct_cmd $0
        ($0 $+ ("secret", Secret))
        secret_guard_program
        se'.
Proof.
  intros [se' Hct].
  inversion Hct; subst.
  unfold interp_sec, sec_lookup in H2.
  cbn in H2.
  autorewrite with core in H2.
  discriminate.
Qed.

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

(* `ct_cmd`: a public branch may be constant-time, but joining branch labels
still taints `x` as `Secret`. *)
Example ct_branch_join_marks_x_secret :
  exists se',
    ct_cmd $0
      ($0 $+ ("flag", Public) $+ ("secret", Secret))
      branch_join_program
      se'
    /\ sec_lookup se' "x" = Secret
    /\ sec_lookup se' "flag" = Public.
Proof.
  eexists.
  split.
  - repeat econstructor; crush_security.
  - split; rewrite lookup_join_env; crush_security.
Qed.
