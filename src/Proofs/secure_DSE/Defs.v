Require Import Language.Main.
Require Import Language.Analysis.
Require Import Language.Optimizations.Secure.DSE.


Definition opt_secure_DSE_core (pgm: program) (secrets: sec_env) : program :=
  (secure_DSE_helper (cmd_of pgm) (protected_out pgm secrets) secrets,
   output_of pgm).
