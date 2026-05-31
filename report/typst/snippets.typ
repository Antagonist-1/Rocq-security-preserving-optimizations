#import "@preview/codelst:2.0.2": sourcecode


#set raw(syntaxes: "rocq.sublime-syntax")


#sourcecode()[
```rocq
Theorem Eval_lift_sec : forall phi v t c v' t',
    eval_trace phi (v, t) c (v', t') ->
    forall sec, exists sec',
    eval_sec phi (v, sec, t) c (v', sec', t').
Proof.
    intros phi v t c v' t' Heval.
    dependent induction Heval; simpl; intros.
    - do 2 econstructor.
    - do 2 econstructor; eauto.
    - eexists. eapply EvalSecCmovTrue; eauto.
    - eexists. eapply EvalSecCmovFalse; eauto.
    - destruct ctx'. simpl in *.
        specialize (IHHeval _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) (senv_mk2 x1 x2 (interp_sec e1 sec) (interp_sec e2 sec))).


```
]

#sourcecode(
  highlighted: (5,6,7,10),
)[
  ```rocq
Fixpoint liveness (c: cmd) (out: var_set) : var_set :=
  match c with
  | Skip => out
  | Assign x e =>
      if VarSet.mem x out
      then VarSet.union (VarSet.remove x out) (vars_in_expr e)
      else out
  ...
  | Sequence c1 c2 =>
      liveness c1 (liveness c2 out)
  ...
end.
```
]


#sourcecode(
  highlighted: (6,7,8,12),
)[
  ```rocq

Fixpoint dse_helper (c: cmd) (out: var_set) : cmd :=
  match c with
  | Skip => Skip
  | Assign x e =>
      match VarSet.mem x out with
      | false => Skip (*not live, remove this assignment*)
      | true => Assign x e (*used later. keep it*)
      end
  ...
  | Sequence c1 c2 =>
      Sequence (dse_helper c1 (liveness c2 out)) (dse_helper c2 out)
  ...
  end.
```
]


#sourcecode(
  highlighted: (6,12,13,14),
)[
  ```rocq

Fixpoint safe_dse_helper (c: cmd) (out: var_set) (secrets: sec_env): cmd :=
  match c with
  | Skip => Skip
  | Assign x e =>
      match (VarSet.mem x out), (sec_lookup secrets x), (interp_sec e secrets) with
      | false, Public, Public => Skip
      | _, _, _ => Assign x e
      end
  ...
  | Sequence c1 c2 =>
      let secrets_mid := sec_post c1 secrets in
      Sequence (safe_dse_helper c1 (liveness c2 out) secrets)
        (safe_dse_helper c2 out secrets_mid)
  ...
  end.
```
]

```rocq
1. VarSet.mem x out = false
2. sec_lookup secrets x = Public
3. interp_sec e secrets = Public
```
