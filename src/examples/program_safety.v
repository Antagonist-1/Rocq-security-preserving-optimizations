Require Import examples.Programs.
Require Import Language.Semantics.
Require Import Map.
Require Import Language.Main.
Require Import Language.Optimizations.
Require Import proofs.SecurityProofs.

From Stdlib Require Import Lia.

Print secret_guard_program.

Example unsafe1 := single_out_pgm secret_guard_program "x".

Example senv := $0 $+ ("secret", Secret).

Example v1 := $0 $+ ("secret", 1).
Example v2 := $0 $+ ("secret", 0).



Goal ~ (is_safe_pgm $0 unsafe1 senv).
Proof.  
    intros H.
    destruct H as [? Hct].
    unfold non_inference, unsafe1 in Hct; simpl in Hct.
    specialize (Hct v1 v2 nil (v1 $+ ("x",1)) (v2 $+ ("x", 0)) (cons (Branch true)  nil) (cons (Branch false) nil)).
    assert (Hpre1 :  agree_on_public senv v1 v2).
    {
     unfold agree_on_public, v1, v2.
     intros.
     unfold sec_lookup, senv in H.
     destruct (var_eq x0 "secret") eqn:Hsecret; subst.
     +  rewrite lookup_add_eq in H by reflexivity.
        discriminate.
     +  repeat rewrite lookup_add_ne by congruence.
        reflexivity.
    }
    assert (Hpre2 : eval $0 (v1, nil) secret_guard_program
            (v1 $+ ("x", 1), (Branch true :: nil)%list)).
    {
        eapply EvalIfTrue.
        simpl.
        unfold v1.
        rewrite lookup_add_eq; reflexivity.
        lia.
        constructor.
        reflexivity.
    }
    assert (Hpre3 : eval $0 (v2, nil) secret_guard_program
            (v2 $+ ("x", 0), (Branch false :: nil)%list)).
    {
        eapply EvalIfFalse.
        simpl.
        unfold v2.
        rewrite lookup_add_eq; reflexivity.
        constructor.
        reflexivity.
    }
    specialize (Hct Hpre1 Hpre2 Hpre3).
    easy.
Qed.

Example safe1 := single_out_pgm public_guard_program "x".

Goal is_safe_pgm $0 safe1 senv.
Proof.  
    unfold is_safe_pgm.
    eexists.
    eassert (Hct : ct_cmd $0 senv public_guard_program _).
    {
        unfold safe1, public_guard_program. simpl.
        econstructor.
        2,3: econstructor.
        all: unfold senv, interp_sec, sec_lookup in *.
        rewrite lookup_add_ne by congruence.
        rewrite lookup_empty. 
        all: reflexivity. 
    }
    apply ct_cmd_soundness in Hct.
    apply Hct.
Qed.

Example senv' := $0 $+ ("x", Secret).

Example unsafe2 := single_out_pgm secret_overwritten_with_const "y".

Example sctx: sec_context := ($0 $+ ("x", 123), $0 $+ ("x", Secret), nil).
Example sctx': sec_context := ($0 $+ ("x", 123) $+ ("x", 0), $0 $+ ("x", Secret) $+ ("x", Public), nil).
Example sctx'' := sctx. (* secret untouched after opt dse!*)

Theorem unsafeDSE_unsafe : forall phi,  ~ is_safe_opt phi (opt_dse).
Proof.
  unfold is_safe_opt.
  intros phi H.
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
