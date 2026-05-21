Require Import Language.Syntax.
Require Import Language.Analysis.

(* clean programs by removing useless sequence of skips *)
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
  (* We can't simplify the loop because it might be non-terminating *)
  | While cond body => While cond (opt_unskip body)
  | _ => c
  end.

Definition opt_unskip_pgm (pgm: program) : program :=
  (opt_unskip (cmd_of pgm), output_of pgm).
