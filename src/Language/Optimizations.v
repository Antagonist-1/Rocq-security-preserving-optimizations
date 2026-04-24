Require Import Map.
Require Import Language.Syntax.
Require Import Language.Semantics.
Require Import examples.Programs.

Require Import Stdlib.Structures.OrderedTypeEx.
Require Import Stdlib.Structures.OrdersAlt.
Require Import Stdlib.MSets.MSetWeakList.
Require Import Stdlib.MSets.MSetFacts.
Require Import Stdlib.MSets.MSetProperties.

(* clean programs by removing skips after DSE *)
Fixpoint opt_unskip (c: cmd) :  cmd :=
  match c with
  | Sequence c1 c2 => match (opt_unskip c1), (opt_unskip c2) with
                       | Skip, c2' => c2'
                       | c1', Skip => c1'
                       | c1', c2' => c1' ;; c2'
                     end
  | If cond thenC elseC => match opt_unskip thenC, opt_unskip elseC with
                          | Skip, Skip => Skip
                          | thenC', elseC' => If cond thenC' elseC'
                          end
  (* We can't simplify the body because it might be non-terminating *)
  | While cond body => While cond (opt_unskip body)
  | _ => c
  end.

(* VarSet represents sets of strings*)
Module StringOT := Update_OT String_as_OT.
Module VarSet := MSetWeakList.Make StringOT.
Module VarSetFacts := MSetFacts.Facts VarSet.
Module VarSetProps := MSetProperties.Properties VarSet.

(*
VarSet API:
(* membership *)
VarSet.mem x s        (* returns bool *)

(* add/remove *)
VarSet.add x s
VarSet.remove x s

(* union *)
VarSet.union s1 s2

VarSet.equal s1 s2    (* returns bool *)

(* size *)
VarSet.cardinal s
 *)

Definition var_set := VarSet.t.

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
  | AssignCall x f e1 e2 => VarSet.add x (VarSet.union (vars_in_expr e1) (vars_in_expr e2))
  | Sequence c1 c2 => VarSet.union (vars_in_cmd c1) (vars_in_cmd c2)
  | If e c1 c2 => VarSet.union (vars_in_expr e) (VarSet.union (vars_in_cmd c1) (vars_in_cmd c2))
  | While e body => VarSet.union (vars_in_expr e) (vars_in_cmd body)
  end.

  (* Fixpoint algorithm, perform f until no change (max: fuel iterations) *)
Fixpoint fixpoint  (f: var_set -> var_set) (x: var_set) (fuel: nat): var_set :=
  match fuel with
  | 0 => x
  | S n =>
      let x' := f x in
      if VarSet.equal x x'
      then x
      else fixpoint f x' n
  end.

(*note: n_vars is enough to iterate. because f is monotonous, and there are a bound number of variables.*)

(*Set of all vars stored by some program*) (*This is unused for now. We need it if we do While loop elimination *)
(* Fixpoint written_vars (c: cmd) : var_set := *)
(*   match c with *)
(*   | Skip => VarSet.empty *)
(*   | Assign x _ => VarSet.singleton x *)
(*   | AssignCall x _ _ _ => VarSet.singleton x *)
(*   | Sequence c1 c2 => VarSet.union (written_vars c1) (written_vars c2) *)
(*   | If _ thenC elseC => VarSet.union (written_vars thenC) (written_vars elseC) *)
(*   | While _ body => written_vars body *)
(*   end. *)


(* compute live variables, given live variables from after command *)
(* The analysis goes backwards. *)
(* formula: live_in = live_out + vars used in command - vars overwritten in command *)
Fixpoint liveness (c: cmd) (out: var_set) {struct c}: var_set :=
  match c with 
  | Skip => out
  | Assign x e =>
      (* if the assigned value is not live, the values used dont become live 
      -> propagates backwardsunuse of variables *)
      if VarSet.mem x out
      then VarSet.union (VarSet.remove x out) (vars_in_expr e)
      else out
  (*Body of functions cant access outer functions, no need to care about it*)
  | AssignCall x f e1 e2 =>
      VarSet.union (VarSet.remove x out) (VarSet.union (vars_in_expr e1) (vars_in_expr e2))
  | Sequence c1 c2 =>
      liveness c1 (liveness c2 out)
  | If e thenC elseC =>
       VarSet.union (vars_in_expr e) (VarSet.union (liveness thenC out) (liveness elseC out))
  | While e body =>
      let seed := VarSet.union out (vars_in_expr e) in
        fixpoint (liveness body) seed (VarSet.cardinal (vars_in_cmd c))
  end.


Fixpoint dse_helper (c: cmd) (out: var_set) : cmd :=
  match c with
  | Skip => Skip
  | Assign x e =>
      match VarSet.mem x out with
      | false => Skip (*not live, remove this assignment*)
      | true => Assign x e (*used later. keep it*)
      end
        (*keep assigncalls for now, but they could be removed as in simple Assign*)
  | AssignCall x f e1 e2 => AssignCall x f e1 e2
  | Sequence c1 c2 =>
      Sequence (dse_helper c1 (liveness c2 out)) (dse_helper c2 out)
  | If e thenC elseC =>
      If e (dse_helper thenC out) (dse_helper elseC out)
  | While e body =>
      While e (dse_helper body (liveness c out))
  end.

Definition opt_dse (c: cmd) (result: var): cmd :=
  opt_unskip (dse_helper c (VarSet.singleton result)).

