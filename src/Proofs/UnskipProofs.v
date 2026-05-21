Require Import Map.
Require Import VarSets.
Require Import Language.Main.
Require Import Language.Analysis.
Require Import Language.Properties.
Require Import Language.Semantics.
Require Import Language.Optimizations.Safe.Unskip.


From Stdlib Require Import Lia.

Create HintDb unskip_db.
Hint Constructors eval eval_trace eval_sec : unskip_db.

Ltac invert_skip_trace :=
  repeat match goal with
  | [ H: eval_trace _ _ Skip _ |- _ ] => inversion H; subst; clear H
  | [ H: eval_sec _ _ Skip _ |- _ ] => inversion H; subst; clear H
  end.

Lemma opt_unskip_sound: forall phi c v v',
  eval phi v c v' ->
  eval phi v (opt_unskip c) v'.
Proof.
    induction 1; simpl; intros; eauto with unskip_db.
    all: repeat match goal with 
    | [ |- context[match ?pat with _ => _ end]] => destruct pat
    end.
    all: try inversion IHeval1; try inversion IHeval2; subst;
    eauto with unskip_db.
Qed.


