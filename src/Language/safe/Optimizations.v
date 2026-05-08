Require Import Map.
Require Import Language.Syntax.
Require Import Language.Semantics.
Require Import VarSets.
Require Import Language.Optimizations.
Require Import Language.Security.


Fixpoint safe_dse_helper (c: cmd) (out: var_set) (secrets: sec_env): cmd :=
  match c with
  | Skip => Skip
  | Assign x e =>
      match (VarSet.mem x out), (secrets $? x) with
      | false, None | false, Some Public => Skip (*not live, remove this assignment*)
      | _, _ => Assign x e (*used later. keep it*)
      end
        (*keep assigncalls for now, but they could be removed as in simple Assign*)
  | AssignCall x f e1 e2 => AssignCall x f e1 e2
  | Sequence c1 c2 =>
      Sequence (safe_dse_helper c1 (liveness c2 out) secrets) (safe_dse_helper c2 out secrets)
  | If e thenC elseC =>
      If e (safe_dse_helper thenC out secrets) (safe_dse_helper elseC out secrets)
  | While e body =>
      While e (safe_dse_helper body (liveness c out) secrets)
  end.

Definition opt_safe_dse (pgm: program) (secrets: sec_env): program :=
  (opt_unskip (safe_dse_helper (cmd_of pgm) (output_of pgm) secrets), output_of pgm).

