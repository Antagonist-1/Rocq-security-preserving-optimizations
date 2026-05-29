Require Import Language.Main.
Require Import Language.Optimizations.Safe.Unskip.
Require Import Proofs.unskip.Noninference.
Require Import Proofs.unskip.SecretPreservation.


Theorem opt_unskip_secure :
  is_safe_opt opt_unskip.
Proof.
  unfold is_safe_opt.
  split.
  - apply opt_unskip_preserves_safe_pgm.
  - apply opt_unskip_keeps_secrets_secret.
Qed.
