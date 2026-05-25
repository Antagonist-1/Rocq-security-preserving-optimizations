Require Import Language.Main.
Require Import Language.Optimizations.Safe.DSE.
Require Import Language.Optimizations.Safe.Unskip.
Require Import Proofs.DSE.Defs.
Require Import Proofs.DSE.SecretPreservation.
Require Import Proofs.DSE.Soundness.
Require Import Proofs.DSE.Noninference.
Require Import Proofs.UnskipProofs.


Theorem opt_safe_dse_core_secure : forall phi,
  is_safe_opt phi opt_safe_dse_core.
Proof.
  intros phi.
  unfold is_safe_opt.
  split.
  - apply opt_safe_dse_core_preserves_safe_pgm.
  - apply opt_safe_dse_core_keeps_secrets_secret.
Qed.

Theorem opt_safe_dse_secure : forall phi,
  is_safe_opt phi opt_safe_dse.
Proof.
  intros phi.
  change (is_safe_opt phi (compose_opt opt_unskip opt_safe_dse_core)).
  eapply is_safe_opt_compose.
  - apply opt_safe_dse_core_secure.
  - apply opt_unskip_secure.
  - apply opt_safe_dse_core_eval_sec_sound.
Qed.
