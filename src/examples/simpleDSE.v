Require Import examples.Programs.
Require Import Language.Optimizations.
Require Import Language.Main.


Goal opt_dse simple_assign_p1 = simple_assign.
Proof.
  reflexivity.
Qed.

Goal opt_dse simple_assign_p2 = Skip.
Proof.
  reflexivity.
Qed.

Goal opt_dse dead_assign_p = ("x" <- 10).
  reflexivity.
Qed.

Goal opt_dse live_assign_p1 =
  ("x" <- 5;;
   "y" <- Var "x").
  reflexivity.
Qed.

Goal opt_dse live_assign_p2 =
       Skip.
  reflexivity.
Qed.

Goal opt_dse live_assign_p3 =
   ("x" <- 10).
  reflexivity.
Qed.

Goal opt_dse live_in_condition_p =
  ("x" <- 5;;
   when (Var "x") then
     "y" <- 1
   else
     "y" <- 0
   done).
  reflexivity.
Qed.

Goal opt_dse dead_before_if_p =
  (
   when (Var "cond") then
     "x" <- 1
   else
     "x" <- 2
   done).
  reflexivity.
Qed.

Goal opt_dse dead_in_loop_p =
  (
   while (Var "n") loop
     "n" <- Var "n" - 1
   done).
  reflexivity.
Qed.

Goal opt_dse chained_dead_p =
  (
   "x" <- 3;;
   "y" <- Var "x").
  reflexivity.
Qed.


Goal opt_dse while_issue1_p = while_issue1_body.
  reflexivity.
Qed.

Goal opt_dse while_issue2_p = while_issue2_body.
  reflexivity.
Qed.

Goal opt_dse while_issue3_p = while_issue3_body.
  reflexivity.
Qed.

Goal opt_dse while_issue4_p = while_issue4_body.
  reflexivity.
Qed.

(*We could possibly make DSE stronger, by detecting non-infinite, useless loops.
but that seems a lot of work for not much result.
 *)
Compute opt_dse (single_out_pgm FactBody "smth_else").
