Require Import Map.
Require Import Language.Syntax.
Require Import Language.Semantics.

Definition secrets := fmap var unit. (*store secrets in a set*)
Definition is_secret (s: secrets) (x: var) := s $? x = Some tt.

(*2 programs agree on public variables, with potentially different secrets
necessary to check*)
Definition agree_on_public (s: secrets) (v1 v2 : valuation) : Prop :=
  forall x, not (is_secret s x) -> v1 $? x = v2 $? x.
