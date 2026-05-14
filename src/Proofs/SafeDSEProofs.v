Require Import Map.
Require Import VarSets.
Require Import Language.Main.
Require Import Language.Analysis.
Require Import Language.Optimizations.Safe.DSE.

Lemma opt_safe_dse_sound : forall phi pgm secrets ctx ctx',
  eval phi ctx (cmd_of pgm) ctx' ->
  exists ctx_opt,
    eval phi ctx (cmd_of (opt_safe_dse pgm secrets)) ctx_opt /\
    agree_on_public (output_of pgm) (val_of ctx') (val_of ctx_opt).
Proof.
  Admitted.
