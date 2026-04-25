Require Import Map.
Require Import Language.Main.

Example Times3Plus1Body :=
  ("n" <- "n" * 3 + 1).

Example FactBody :=
  ("f" <- 1;;
    while "n" loop
      "f" <- "f" * "n";;
      "n" <- "n" - 1
    done).

Example FactRecBody :=
  (when "n" == 1 then
      "f" <- 1
    else
      "f" <- call1 "fact_r" ("n" - 1);;
      "f" <- "f" * "n"
    done).

Example FactTailRecBody :=
  (when "n" == 1 then
      "f" <- "acc"
    else
      "f" <- call2 "fact_tr" ("n" - 1) ("acc" * "n")
    done).

Example CollatzBody :=
  (when ("start" == 1) then
      Skip
    else when ("start" mod 2 == 0) then
          "start" <- "start" / 2
        else
          (* `call1 f arg` is short for `call2 f arg 0` *)
          "start" <- call1 "times3plus1" ("start" + 0)
        done;;
        "flight" <- call2 "collatz" "start" ("flight" + 1)
    done).

Notation TimesThreePlus1_signature := (("n", ""), "n", Times3Plus1Body).
Notation Fact_signature := (("n", ""), "f", FactBody).
Notation FactRec_signature := (("n", ""), "f", FactRecBody).
Notation FactTailRec_signature := (("n", "acc"), "f", FactTailRecBody).
Notation Collatz_signature := (("start", "flight"), "flight", CollatzBody).

Notation Collatz_env :=
($0
  $+ ("collatz", Collatz_signature)
  $+ ("times3plus1", TimesThreePlus1_signature)).

Notation Fact_env :=
  ($0
    $+ ("fact", Fact_signature)
    $+ ("fact_r", FactRec_signature)
    $+ ("fact_tr", FactTailRec_signature)).

Definition simple_assign :=
  Assign "x" (Const 5).

Definition two_assigns :=
  Sequence (Assign "x" (Const 5)) (Assign "y" (Const 10)).

Definition simple_if :=
  If (Const 1) (Assign "x" (Const 42)) (Assign "x" (Const 0)).

Definition simple_sequence :=
  Sequence
    (If (Const 1) (Assign "x" (Const 0)) (Assign "x" (Const 0)))
    (If (Const 0) (Assign "y" (Const 0)) (Assign "y" (Const 0))).

Definition nested_if :=
  If (Const 1)
    (If (Const 0)
      (Assign "x" (Const 0))
      (Assign "x" (Const 0)))
    (Assign "x" (Const 0)).

Definition simple_while :=
  While (Var "x")
    (Assign "x" (Const 0)).

Definition secret_copy :=
  Assign "x" (Var "secret").

Definition secret_overwritten_with_const :=
  Assign "x" (Const 0).

Definition secret_overwritten_with_public_var :=
  Assign "x" (Var "flag").

Definition public_guard_program :=
  If (Var "flag")
    (Assign "x" (Const 1))
    (Assign "x" (Const 0)).

Definition secret_guard_program :=
  If (Var "secret")
    (Assign "x" (Const 1))
    (Assign "x" (Const 0)).

Definition branch_join_program :=
  If (Var "flag")
    (Assign "x" (Var "secret"))
    (Assign "x" (Const 0)).

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


(* Simple DSE programs *)

Definition dead_assign :=
  ("x" <- 5;;
   "x" <- 10).

Definition live_assign :=
  ("x" <- 5;;
    "y" <- Var "x";;
    "x" <- 10).


Definition live_in_condition :=
  ("x" <- 5;;
   when (Var "x") then
     "y" <- 1
   else
     "y" <- 0
   done).

Definition dead_before_if :=
  ("x" <- 5;;
   when (Var "cond") then
     "x" <- 1
   else
     "x" <- 2
   done).

Definition dead_in_loop :=
  ("tmp" <- 0;;
   while (Var "n") loop
     "tmp" <- Var "n";;
     "n" <- Var "n" - 1
   done).

Definition chained_dead :=
  ("x" <- 1;;
   "x" <- 2;;
   "x" <- 3;;
   "y" <- Var "x").

(*Variables in while condition should be live and propagate their liveness inside the while's body*)
Definition while_issue1 :=
  ("x" <- 1;;
   while "y" loop
     "y" <- "x"
             done).

Definition while_issue2 :=
  (while "x" loop
     "x" <- "y";;
     "y" <- "y" - 1
   done).

Definition while_issue3 :=
  (while "x" loop
      "x" <- 5
    done).

Definition while_issue4 :=
  ("y" <- 10;;
  while "x" loop
    "y" <- "5";;
    "x" <- "x" - 1
  done).