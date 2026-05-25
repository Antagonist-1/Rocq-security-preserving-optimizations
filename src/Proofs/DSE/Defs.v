Require Import Language.Main.
Require Import Language.Analysis.
Require Import Language.Optimizations.Safe.DSE.


Definition opt_safe_dse_core (pgm: program) (secrets: sec_env) : program :=
  (safe_dse_helper (cmd_of pgm) (protected_out pgm secrets) secrets,
   output_of pgm).
