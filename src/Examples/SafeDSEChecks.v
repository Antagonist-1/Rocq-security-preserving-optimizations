Require Import Map.
Require Import Language.Main.
Require Import Examples.Programs.
Require Import Language.Optimizations.Safe.DSE.


Definition secret_write_body :=
  "x" <- Var "secret".

Definition secret_write_p := single_out_pgm secret_write_body "y".

Definition secret_write_secrets := senv_mk1 "secret" Secret.

(* After the forward secret analysis is threaded through safe DSE, this write
   must stay because it turns [x] into a maybe-secret variable, even though [x]
   is not in the ordinary output set. *)
Eval compute in protected_out secret_write_p secret_write_secrets.
Eval compute in opt_safe_dse secret_write_p secret_write_secrets.

Goal opt_safe_dse secret_write_p secret_write_secrets = secret_write_p.
Proof.
  reflexivity.
Qed.


Definition public_write_body :=
  "x" <- Var "pub".

Definition public_write_p := single_out_pgm public_write_body "y".

(* This one should still optimize away: [x] is dead and the assignment stays
   public. *)
Eval compute in protected_out public_write_p secret_write_secrets.
Eval compute in opt_safe_dse public_write_p secret_write_secrets.

Goal opt_safe_dse public_write_p secret_write_secrets = single_out_pgm Skip "y".
Proof.
  reflexivity.
Qed.
