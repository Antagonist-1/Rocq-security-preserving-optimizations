Require Import examples.Programs.
Require Import Language.Semantics.
Require Import Map.
Require Import Language.Main.


Example unsafe1 := single_out_pgm secret_guard_program "x".

Example senv := $0 $+ ("secret", Secret).

Goal ~ (is_safe_pgm unsafe1 senv).
Proof.  
    intros H.
    destruct (H $0) as [? Hct].
    inversion Hct.
    unfold senv, interp_sec, sec_lookup in *.
    rewrite lookup_add_eq in H3 by reflexivity.
    discriminate.
Qed.


