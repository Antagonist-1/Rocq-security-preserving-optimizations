Require Import Map.
Require Import Language.Main.
Require Import examples.Programs.
From Stdlib Require Import List.
Import ListNotations.

Example eval_sec_secret_copy_taints_x :
  eval_sec $0
    (($0 $+ ("secret", 7)), ($0 $+ ("secret", Secret)), nil)
    secret_copy
    (($0 $+ ("secret", 7) $+ ("x", 7)), ($0 $+ ("secret", Secret) $+ ("x", Secret)), nil).
Proof.
  econstructor.
  cbn. autorewrite with core. reflexivity.
  unfold interp_sec, sec_lookup.
  cbn. autorewrite with core. reflexivity.
Qed.

Example eval_sec_secret_copy_defaults_to_public :
  eval_sec $0
    (($0 $+ ("secret", 7)), $0, nil)
    secret_copy
    (($0 $+ ("secret", 7) $+ ("x", 7)), ($0 $+ ("x", Public)), nil).
Proof.
  econstructor.
  cbn. autorewrite with core. reflexivity.
  unfold interp_sec, sec_lookup.
  cbn. autorewrite with core. reflexivity.
Qed.

Example ct_public_guard_program_ok :
  exists se',
    ct_cmd $0
      ($0 $+ ("flag", Public))
      public_guard_program
      se'.
Proof.
  eexists.
  econstructor.
  unfold interp_sec, sec_lookup.
  cbn. autorewrite with core. reflexivity.
  econstructor.
  econstructor.
Qed.

Example ct_secret_guard_program_rejected :
  ~ exists se',
      ct_cmd $0
        ($0 $+ ("secret", Secret))
        secret_guard_program
        se'.
Proof.
  intros [se' Hct].
  inversion Hct; subst.
  unfold interp_sec, sec_lookup in H3.
  cbn in H3.
  autorewrite with core in H3.
  discriminate.
Qed.

Example ct_branch_join_marks_x_secret :
  exists se',
    ct_cmd $0
      ($0 $+ ("flag", Public) $+ ("secret", Secret))
      (when "flag" then
         "x" <- "secret"
       else
         "x" <- 0
       done)
      se'
    /\ sec_lookup se' "x" = Secret
    /\ sec_lookup se' "flag" = Public.
Proof. Admitted.
