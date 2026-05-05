Require Import examples.Programs.
Require Import Language.Semantics.
Require Import Map.
Require Import Language.Main.
Require Import Language.Optimizations.


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

Example safe1 := single_out_pgm public_guard_program "x".

Goal is_safe_pgm safe1 senv.
Proof.  
    unfold is_safe_pgm. intro.
    eexists.
    unfold safe1, public_guard_program. simpl.
    econstructor.
    2,3: econstructor.
    all: unfold senv, interp_sec, sec_lookup in *.
    rewrite lookup_add_ne by congruence.
    rewrite lookup_empty. 
    all: reflexivity. 
Qed.

Example senv' := $0 $+ ("x", Secret).

Example unsafe2 := single_out_pgm secret_overwritten_with_const "y".

Example sctx: sec_context := ($0 $+ ("x", 123), $0 $+ ("x", Secret), nil).
Example sctx': sec_context := ($0 $+ ("x", 123) $+ ("x", 0), $0 $+ ("x", Secret) $+ ("x", Public), nil).
Example sctx'' := sctx. (* secret untouched after opt dse!*)

Theorem unsafeDSE_unsafe : ~ is_safe_opt (opt_dse).
Proof.
  unfold is_safe_opt.
  intro.
  destruct H.
  clear H.
  unfold opt_keeps_secrets_secret in H0.
  specialize (H0 sctx sctx' sctx'' unsafe2 (single_out_pgm Skip "y") $0).
  unfold unsafe2, secret_overwritten_with_const, opt_dse in H0.
  simpl in H0.
  assert (Hpre1 : eval_sec $0 sctx ("x" <- 0) sctx') by (constructor; reflexivity).
  assert (Hpre2 : eval_sec $0 sctx Skip sctx'') by constructor.
  specialize (H0 eq_refl Hpre1 Hpre2 "x").
  (* Here both sides of H0 are wrong. x doesnt have the same level AND the same value *)
  destruct H0.
  (*it seems easier to prove the left side wrong*)
  unfold sctx', sctx'' in H.
  unfold sec_of in H. (* for some reason simpl needs an extra help*)
  simpl in H.
  do 2 rewrite lookup_add_eq in H by reflexivity.
  congruence.
Qed.
