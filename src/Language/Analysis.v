Require Import Map.
Require Import Language.Syntax.
Require Import VarSets.

Definition program := (cmd * var_set)%type.

Definition cmd_of (pgm: program) := fst pgm.
Definition output_of (pgm: program) := snd pgm.


  (* All vars used in an expr *)
Fixpoint vars_in_expr (e: expr) : var_set :=
  match e with
  | Const n => VarSet.empty
  | Var x => VarSet.singleton x
  | Binop b e1 e2 => VarSet.union (vars_in_expr e1) (vars_in_expr e2)
  end.

  (* All vars used in a cmd *)
Fixpoint vars_in_cmd (c: cmd) : var_set :=
  match c with
  | Skip => VarSet.empty
  | Assign x e => VarSet.add x (vars_in_expr e)
  | Cmov x cond e1 e2 => VarSet.add x (VarSet.union (vars_in_expr cond) (VarSet.union (vars_in_expr e1) (vars_in_expr e2)))
  | AssignCall x f e1 e2 => VarSet.add x (VarSet.union (vars_in_expr e1) (vars_in_expr e2))
  | Sequence c1 c2 => VarSet.union (vars_in_cmd c1) (vars_in_cmd c2)
  | If e c1 c2 => VarSet.union (vars_in_expr e) (VarSet.union (vars_in_cmd c1) (vars_in_cmd c2))
  | While e body => VarSet.union (vars_in_expr e) (vars_in_cmd body)
  end.

  (* Fixpoint algorithm, perform f until no change (max fuel iterations) *)
Fixpoint while_fixpoint  (f: var_set -> var_set) (cond_vars: var_set) (out: var_set) (fuel: nat): var_set :=
  match fuel with
  | 0 => out
  | S n =>
      let _in := VarSet.union (VarSet.union out cond_vars) (f out) in
      if VarSet.equal out _in
      then out
      else while_fixpoint f cond_vars _in n
  end.

(*note: When computing liveness of variables in a while loop, n_vars iterations is enough: 
because f is strictly monotonous, and there are a bound number of variables.*)

(* liveness computes live variables before command, given live variables after command *)
(* The analysis goes backwards. *)
(* formula: live_in = live_out + 'vars used in command' - 'vars overwritten in command' *)

(*More details about formula: https://cs420.epfl.ch/c/06_dataflow.html*)
Fixpoint liveness (c: cmd) (out: var_set) {struct c}: var_set :=
  match c with
  | Skip => out
  | Assign x e =>
      (* if the assigned value is not live, the values used dont become live
      -> propagates backwards 'unuse' of variables *)
      if VarSet.mem x out
      then VarSet.union (VarSet.remove x out) (vars_in_expr e)
      else out
  | Cmov x cond e1 e2 =>
      if VarSet.mem x out
      then VarSet.union (VarSet.remove x out) (VarSet.union (vars_in_expr cond) (VarSet.union (vars_in_expr e1) (vars_in_expr e2)))
      else out
  (*Body of functions cant access outer functions, no need to care about it*)
  | AssignCall x f e1 e2 =>
      VarSet.union (VarSet.remove x out) (VarSet.union (vars_in_expr e1) (vars_in_expr e2))
  | Sequence c1 c2 =>
      liveness c1 (liveness c2 out)
  | If e thenC elseC =>
       VarSet.union (vars_in_expr e) (VarSet.union (liveness thenC out) (liveness elseC out))
  | While e body =>
        while_fixpoint (liveness body) (vars_in_expr e) out (VarSet.cardinal (vars_in_cmd c))
  end.