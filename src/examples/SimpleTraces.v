Require Import Map.
Require Import Language.Main.
Require Import examples.Programs.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Lia.

Hint Constructors eval : eval.

Ltac crush_eval_step :=
  let rec go :=
    cbn [empty_context interp_arith interp_binop] in *;
    autorewrite with core in *;
    lazymatch goal with
    | |- _ <> 0 => discriminate || congruence || lia
    | |- _ = _ => cbn; autorewrite with core; reflexivity
    | |- exists _ : valuation, _ => eexists
    | |- eval _ _ _ _ => econstructor; go
    end
  in go.
Ltac crush_eval := crush_eval_step.

Print simple_assign.

  Example simple_assign_empty_trace :
    eval $0
      empty_context
      simple_assign
      ($0 $+ ("x", 5), nil).
  Proof. unfold simple_assign. crush_eval. Qed.

  Print two_assigns.

  Example two_assigns_empty_trace :
    eval $0
      empty_context
      two_assigns
      ($0 $+ ("x", 5) $+ ("y", 10), nil).
  Proof.
    unfold two_assigns. crush_eval.
  Qed.

  Print simple_if.

  Example simple_if_true_branch :
    eval $0
      empty_context
      simple_if
      ($0 $+ ("x", 42), Branch true :: nil).
  Proof.
    unfold simple_if. crush_eval.
  Qed.

  Print simple_sequence.

  Example simple_sequence_true_false_branch :
    eval $0
      empty_context
      simple_sequence
      ($0 $+ ("x", 0) $+ ("y", 0), Branch true :: Branch false :: nil).
  Proof.
    unfold simple_sequence. crush_eval.
  Qed.

  Print nested_if.

  Example nested_if_true_false_branch :
    eval $0
      empty_context
      nested_if
      ($0 $+ ("x", 0), Branch true :: Branch false :: nil).
  Proof.
    unfold nested_if. crush_eval.
  Qed.

  Print simple_while.

  Example simple_while_true_false_branch :
    eval $0
      ($0 $+ ("x", 1), nil)
      simple_while
      ((($0 $+ ("x", 1)) $+ ("x", 0)), Branch true :: Branch false :: nil).
  Proof.
    unfold simple_while. crush_eval.
  Qed.

  (* Final Boss: Example from Lab05 *)
  Print the_answer_is_42.
  (* The trace will depend on the initial valuation, in particular on the value
    of "oops".
    For example, with oops = 0 the trace will be [Branch false; Branch true],
    while with oops = 1 the trace will be [Branch true; Branch true].
  *)

  (*
  Rewritten with easy-to-read syntax:
  x := oops;
  if x then
    tmp := x + x       // nonzero as x is nonzero in the then branch
  else
    tmp := 1;          // also nonzero, as 1 is nonzero
  if tmp then          // will always be true as tmp is nonzero no matter what
    answer := 42       // <= We will always take this branch
  else
    answer := 24.
  *)

  Definition oopsZeroValuation : valuation :=
    $0 $+ ("oops", 0).
  Definition traceWithZero : list trace_event :=
    Branch false :: Branch true :: nil.
  Definition oopsNonZeroValuation : valuation :=
    $0 $+ ("oops", 1).
  Definition traceWithNonZero : list trace_event :=
    Branch true :: Branch true :: nil.

  Example trace_with_zero_inside :
    eval $0
      ($0 $+ ("oops", 0) $+ ("x", 0), nil)
      (Sequence
        (If (Var "x")
            (Assign "tmp" (Binop Plus (Var "x") (Var "x")))
            (Assign "tmp" (Const 1)))
        (If (Var "tmp")
            (Assign "answer" (Const 42))
            (Assign "answer" (Const 24))))
      (($0 $+ ("oops", 0) $+ ("x", 0) $+ ("tmp", 1) $+ ("answer", 42)),
         Branch false :: Branch true :: nil).
  Proof.
    crush_eval.
  Qed.

  Example trace_with_zero :
    eval $0
      (oopsZeroValuation, nil)
      the_answer_is_42
      (oopsZeroValuation $+ ("x", 0) $+ ("tmp", 1) $+ ("answer", 42), traceWithZero).
  Proof.
    unfold the_answer_is_42, oopsZeroValuation, traceWithZero.
    crush_eval.
  Qed.

  Example trace_with_nonzero_inside :
    eval $0
      ($0 $+ ("oops", 1) $+ ("x", 1), nil)
      (Sequence
        (If (Var "x")
            (Assign "tmp" (Binop Plus (Var "x") (Var "x")))
            (Assign "tmp" (Const 1)))
        (If (Var "tmp")
            (Assign "answer" (Const 42))
            (Assign "answer" (Const 24))))
      (($0 $+ ("oops", 1) $+ ("x", 1) $+ ("tmp", 2) $+ ("answer", 42)),
         Branch true :: Branch true :: nil).
  Proof.
    crush_eval.
  Qed.

  Example trace_with_nonzero :
    eval $0
      (oopsNonZeroValuation, nil)
      the_answer_is_42
      (oopsNonZeroValuation $+ ("x", 1) $+ ("tmp", 2) $+ ("answer", 42), traceWithNonZero).
  Proof.
    unfold the_answer_is_42, oopsNonZeroValuation, traceWithNonZero.
    crush_eval.
  Qed.
