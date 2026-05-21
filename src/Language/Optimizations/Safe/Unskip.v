Require Import Language.Syntax.
Require Import Language.Analysis.
Require Import Language.Security.

(* clean programs by removing useless sequence of skips *)
Fixpoint opt_unskip_cmd (c: cmd) :  cmd :=
  match c with
  | Sequence c1 c2 => match (opt_unskip_cmd c1), (opt_unskip_cmd c2) with
                       | Skip, c2' => c2'
                       | c1', Skip => c1'
                       | c1', c2' => c1' ;; c2'
                     end
  | If cond thenC elseC => If cond (opt_unskip_cmd thenC) (opt_unskip_cmd elseC)
  (* Original definition that removed [If cond skip skip] :  
    | If cond thenC elseC => match opt_unskip thenC, opt_unskip elseC with
                          | Skip, Skip => Skip
                          | thenC', elseC' => If cond thenC' elseC'
                          end

  *)
  (* We can't simplify the loop because it might be non-terminating *)
  | While cond body => While cond (opt_unskip_cmd body)
  | _ => c
  end.

Definition opt_unskip (pgm: program) (_: sec_env) : program :=
  (opt_unskip_cmd (cmd_of pgm), output_of pgm).
