Require Import Map.
Require Import Language.Syntax.
Require Import Language.Semantics.
Require Import examples.Programs.


(** Constant folding  - from lab08 *)
Definition opt_binop_fold (b: BinopName) (e1 e2: expr) : expr :=
  match b with
  | Plus =>
    match e1 with
    | Const 0 => e2
    | _ =>
      match e2 with
      | Const 0 => e1
      | _ => Binop b e1 e2
      end
    end
  | Times =>
    match e1 with
    | Const 0 => Const 0
    | _ =>
      match e2 with
      | Const 0 => Const 0
      | _ => Binop b e1 e2
      end
    end
  | Divide =>
    match e2 with
    | Const 1 => e1
    | _ => Binop b e1 e2
    end
  | _ => Binop b e1 e2
  end.
Arguments opt_binop_fold !_ !_ !_ /. (* Coq magic *)

(** Precomputation *)
Definition opt_binop_precompute (b: BinopName) (e1 e2: expr) : expr :=
  match e1, e2 with
  | Const n1, Const n2 => Const (interp_binop b n1 n2)
  | _, _ => Binop b e1 e2
  end.
Arguments opt_binop_precompute !_ !_ !_ /. (* Coq magic *)

(** The overall arithmetic optimizer *)
Fixpoint opt_arith (e: expr) : expr :=
  match e with
  | Binop b e1 e2 =>
    match opt_binop_precompute b (opt_arith e1) (opt_arith e2) with
    | Binop b' e1' e2' =>
      opt_binop_fold b (opt_arith e1) (opt_arith e2)
    | e' => e'
    end
  | _ => e
  end.
Arguments opt_arith !e /. (* Coq magic *)

Fixpoint opt_remove_branch (c : cmd) : cmd :=
match c with
| Skip => Skip
| Assign _ _ => c
| Sequence c1 c2 => Sequence (opt_remove_branch c1) (opt_remove_branch c2)
| AssignCall x f e1 e2 => AssignCall x f e1 e2
| If cond thn els => match (opt_arith cond) with
                    | Const n => match n with
                                | 0 => (opt_remove_branch els)
                                | _ => (opt_remove_branch thn)
                                end
                    | optim => If optim (opt_remove_branch thn) (opt_remove_branch els)
                    end
| While cond body => match (opt_arith cond) with
                    | Const n => match n with
                                | 0 => Skip
                                | _ => While 1 (opt_remove_branch body)
                                end
                    | optim => While optim (opt_remove_branch body)
                    end
end.


(* set of live variable *)
Definition live_set := fmap var unit.

Fixpoint vars_in_expr (e: expr) : live_set :=
  match e with
  | Const n => $0
  | Var x => $0 $+ (x, tt)
  | Binop b e1 e2 => join (vars_in_expr e1) (vars_in_expr e2)
  end.

(* Admitted. recurse over binop and collect vars *)

(*basic, unsafe DSE*)


(* compute liveness, given liveness at next point *)
Fixpoint liveness (c: cmd) (out: live_set): live_set :=
  match c with 
  | Skip => out
  | Assign x e =>
      join (remove out x) (vars_in_expr e)
  (*Body of functions cant access outer functions, no need to care about it*)
  | AssignCall x f e1 e2 =>
      join (remove out x) (join (vars_in_expr e1) (vars_in_expr e2))
  | Sequence c1 c2 =>
      liveness c1 (liveness c2 out)
  | If e thenC elseC =>
      join (vars_in_expr e) (join (liveness thenC out) (liveness elseC out))
  (*simplification. we need a fixpoint algorithm (bounded (fueled) to amount of variables)*)
  | While e body =>
      join (vars_in_expr e) (join out (liveness body out))
  end.

Fixpoint dse_helper (c: cmd) (out: live_set) : cmd :=
  match c with
  | Skip => Skip
  | Assign x e =>
      match out $? x with
      | None => Skip (*not live, remove this assignment*)
      | _ => Assign x e (*used later. keep it*)
      end
        (*keep assigncalls for now*)
  | AssignCall x f e1 e2 => AssignCall x f e1 e2
  | Sequence c1 c2 =>
      Sequence (dse_helper c1 (liveness c2 out)) (dse_helper c2 out)
  | If e thenC elseC =>
      If e (dse_helper thenC out) (dse_helper elseC out)
         (*while body, just use simplification from liveness*)
  | While e body =>
      While e (dse_helper body (liveness c out))
            end.


Definition opt_dead_store_elim (c: cmd): cmd :=
  dse_helper c $0.

  (* ("f" <- 2;; *)
  (* "g" <- 2;; *)
  (* when "f" == 0 then *)
  (*    "g" <-  *)
  (*  else *)
  (*    Skip *)
  (*      done *)
  (* ). *)

Goal opt_dead_store_elim simple_assign = Skip.
Proof.
  compute.
  rewrite lookup_empty.
  reflexivity.
Qed.

Goal


(* when seeing an assign, we look later in the program if it is used*)
(* how can we do that well?
good question. I might need small step to consider how the program is after the assign.

lets say i have
assign x<-e;;
do that;;
do this;;
assert 1
assign x <- e'

is x accessed ? before beeing overwritten otherwise, we can remove the first assign.
without smallstep: I can check the value




 *)
