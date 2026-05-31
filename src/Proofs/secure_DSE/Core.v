Require Import Language.Main.
Require Import Language.Optimizations.Secure.DSE.
Require Import Language.Optimizations.Secure.Unskip.
Require Import Proofs.secure_DSE.Defs.
Require Import Proofs.secure_DSE.SecretPreservation.
Require Import Proofs.secure_DSE.Soundness.
Require Import Proofs.secure_DSE.Noninference.
Require Import Proofs.unskip.Core.


Theorem opt_secure_DSE_core_secure :
  is_secure_opt opt_secure_DSE_core.
Proof.
  unfold is_secure_opt.
  split.
  - apply opt_secure_DSE_core_preserves_secure_pgm.
  - apply opt_secure_DSE_core_keeps_secrets_secret.
Qed.

Theorem opt_secure_DSE_secure :
  is_secure_opt opt_secure_DSE.
Proof.
  change (is_secure_opt (compose_opt opt_unskip opt_secure_DSE_core)).
  eapply is_secure_opt_compose.
  - apply opt_secure_DSE_core_secure.
  - apply opt_unskip_secure.
  - apply opt_secure_DSE_core_eval_sec_sound.
Qed.
