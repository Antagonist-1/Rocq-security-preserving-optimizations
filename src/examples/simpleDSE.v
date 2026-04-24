Require Import examples.Programs.
Require Import Language.Optimizations.
Require Import Language.Main.


Goal opt_dse simple_assign "x" = simple_assign.
Proof.
  reflexivity.
Qed.

Goal opt_dse simple_assign "y" = Skip.
Proof.
  reflexivity.
Qed.

Goal opt_dse dead_assign "x" = ("x" <- 10).
  reflexivity.
Qed.

Goal opt_dse  live_assign "y" =
  ("x" <- 5;;
   "y" <- Var "x").
  reflexivity.
Qed.

Goal opt_dse  live_assign "z" =
       Skip.
  reflexivity.
Qed.


Goal opt_dse  live_assign "x" =
   ("x" <- 10).
  reflexivity.
Qed.

Goal opt_dse  live_in_condition "y" =
  ("x" <- 5;;
   when (Var "x") then
     "y" <- 1
   else
     "y" <- 0
   done).
  reflexivity.
Qed.

Goal opt_dse  dead_before_if "x" =
  (
   when (Var "cond") then
     "x" <- 1
   else
     "x" <- 2
   done).
  reflexivity.
Qed.

Goal opt_dse  dead_in_loop "n" =
  (
   while (Var "n") loop
     "n" <- Var "n" - 1
   done).
  reflexivity.
Qed.

Goal opt_dse  chained_dead "y" =
  (
   "x" <- 3;;
   "y" <- Var "x").
  reflexivity.
Qed.


Goal opt_dse while_issue1 "z" = while_issue1.
  reflexivity.
Qed.

Goal opt_dse while_issue2 "z" = while_issue2.
  reflexivity.
Qed.

Goal opt_dse while_issue3 "z" = while_issue3.
  reflexivity.
Qed.

Goal opt_dse while_issue4 "y" = while_issue4.
  reflexivity.
Qed.

(*We could possibly make DSE stronger, by detecting non-infinite, useless loops.
but that seems a lot of work for not much result.
 *)
Compute opt_dse FactBody "smth_else".
