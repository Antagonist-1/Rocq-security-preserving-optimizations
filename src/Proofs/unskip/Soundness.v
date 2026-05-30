Require Import Map.
Require Import Language.Main.
Require Import Language.Analysis.
Require Import Language.Optimizations.Safe.Unskip.
Require Import Proofs.unskip.UnskipHints.

Lemma opt_unskip_sound: forall c v v',
  eval v c v' ->
  eval v (opt_unskip_cmd c) v'.
Proof.
    induction 1; simpl; intros; eauto with unskip_db.
    all: repeat match goal with
    | [ |- context[match ?pat with _ => _ end]] => destruct pat
    end.
    all: try inversion IHeval1; try inversion IHeval2; subst;
    eauto with unskip_db.
Qed.
