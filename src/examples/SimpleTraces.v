Require Import Map.
Require Import Language.Main.
Require Import Lia.

  Definition simple_assign := Assign "x" (Const 5).

  Example simple_assign_empty_trace :
    eval $0
      empty_context
      simple_assign
      {| val := $0 $+ ("x", 5); trace := nil |}.
  Proof. econstructor. reflexivity. Qed.

  Definition two_assigns := Sequence (Assign "x" (Const 5)) (Assign "y" (Const 10)).
  Example two_assigns_empty_trace :
    eval $0
      empty_context
      two_assigns
      {| val := $0 $+ ("x", 5) $+ ("y", 10); trace := nil |}.
  Proof.
    unfold two_assigns. econstructor.
    - apply EvalAssign; unfold interp_arith; reflexivity.
    - apply EvalAssign; unfold interp_arith; reflexivity.
  Qed.

  Definition simple_if := If (Const 1) (Assign "x" (Const 42)) (Assign "x" (Const 0)).
  Example simple_if_true_branch :
    eval $0
      empty_context
      simple_if
      {| val := $0 $+ ("x", 42); trace := Branch true :: nil |}.
  Proof.
    unfold simple_if.
    eapply EvalIfTrue with (ctx' := {| val := $0 $+ ("x", 42); trace := nil |}).
    - (* Prove: interp_arith (Const 1) $0 = 1 *)
      unfold interp_arith. reflexivity.
    - (* Prove: 1 <> 0 *) lia.
    - (* Prove the assignment *)
      apply EvalAssign.
      unfold interp_arith.
      reflexivity.
  Qed.

  Definition simple_sequence :=
    Sequence
    (If (Const 1) (Assign "x" (Const 0)) (Assign "x" (Const 0)))
    (If (Const 0) (Assign "y" (Const 0)) (Assign "y" (Const 0))).

  Example simple_sequence_true_false_branch :
    eval $0
      empty_context
      simple_sequence
      {| val := $0 $+ ("x", 0) $+ ("y", 0); trace := Branch true :: Branch false :: nil |}.
  Proof.
  Admitted.

  Definition nested_if :=
    If (Const 1)
      (If (Const 0)
        (Assign "x" (Const 0))
        (Assign "x" (Const 0)))
      (Assign "x" (Const 0)).

  Example nested_if_true_false_branch :
    eval $0
      empty_context
      nested_if
      {| val := $0 $+ ("x", 0); trace := Branch true :: Branch false :: nil |}.
  Proof.
  Admitted.

  (* Final Boss: Example from Lab05 *)
  Definition the_answer_is_42 :=
      Sequence
        (Assign "x" (Var "oops"))
        (Sequence
          (If (Var "x")
              (Assign "tmp" (Binop Plus (Var "x") (Var "x")))
              (Assign "tmp" (Const 1)))
          (If (Var "tmp")
              (Assign "answer" (Const 42))
              (Assign "answer" (Const 24)))).
  (* The trace will depend on the initial valuation, in particular on the value
    of "oops".
    For example, with oops = 0 the trace will be [Branch true; Branch false],
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
    Branch true :: Branch false :: nil.
  Definition oopsNonZeroValuation : valuation :=
    $0 $+ ("oops", 1).
  Definition traceWithNonZero : list trace_event :=
    Branch true :: Branch true :: nil.

  Example trace_with_zero_inside :
    eval $0
      {| val := $0 $+ ("oops", 0) $+ ("x", 0); trace := nil |}
      (Sequence
        (If (Var "x")
            (Assign "tmp" (Binop Plus (Var "x") (Var "x")))
            (Assign "tmp" (Const 1)))
        (If (Var "tmp")
            (Assign "answer" (Const 42))
            (Assign "answer" (Const 24))))
      {| val := $0 $+ ("oops", 0) $+ ("x", 0) $+ ("tmp", 1) $+ ("answer", 42);
         trace := Branch true :: Branch false :: nil |}.
  Proof.
  Admitted.

  Example trace_with_zero :
    eval $0
      {| val := oopsZeroValuation; trace := nil |}
      the_answer_is_42
      {| val := oopsZeroValuation $+ ("x", 0) $+ ("tmp", 1) $+ ("answer", 42); trace := traceWithZero |}.
  Proof.
  Admitted.

  Example trace_with_nonzero_inside :
    eval $0
      {| val := $0 $+ ("oops", 1) $+ ("x", 1); trace := nil |}
      (Sequence
        (If (Var "x")
            (Assign "tmp" (Binop Plus (Var "x") (Var "x")))
            (Assign "tmp" (Const 1)))
        (If (Var "tmp")
            (Assign "answer" (Const 42))
            (Assign "answer" (Const 24))))
      {| val := $0 $+ ("oops", 1) $+ ("x", 1) $+ ("tmp", 2) $+ ("answer", 42);
         trace := Branch true :: Branch true :: nil |}.
  Proof.
  Admitted.

  Example trace_with_nonzero :
    eval $0
      {| val := oopsNonZeroValuation; trace := nil |}
      the_answer_is_42
      {| val := oopsNonZeroValuation $+ ("x", 1) $+ ("tmp", 2) $+ ("answer", 42); trace := traceWithNonZero |}.
  Proof.
  Admitted.