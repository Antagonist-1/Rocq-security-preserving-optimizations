## Goal

Refactor safe DSE so that it can satisfy the full theorem
`opt_keeps_secrets_secret opt_safe_dse`, not just the non-inference side.

The current optimizer only checks:

- backward liveness
- whether the destination variable is secret in the original input secret set

This is too weak. A variable can start `Public`, become `Secret` mid-program,
and then be incorrectly optimized away. The canonical bad shape is `x := s` when
`s` is secret and `x` is dead in the plain output set.

The fix is to combine:

- a forward static secret analysis that over-approximates dynamic secret propagation
- the existing backward liveness analysis

Whenever exact treatment is hard, we conservatively treat the result as `Secret`.

## Fixed Design Decisions

These decisions are intentional and should not be revisited during the first implementation.

### 1. Keep the theorem target unchanged

We still want to prove:

- `opt_keeps_secrets_secret opt_safe_dse`

We are fixing the optimizer and proofs, not weakening the property.

### 2. Use a static forward analysis, not `eval_sec`, inside the optimizer

`eval_sec` remains the semantic reference model.
The optimizer will instead use a computable forward transfer function that
approximates how secrets propagate.

### 3. Be conservative whenever information is hard to compute exactly

If a command may make a variable secret and we cannot prove otherwise, we mark it `Secret`.

### 4. Protect final secrets, not just program outputs

The backward pass must preserve:

- ordinary output variables
- variables that may be secret in the final state

So the optimizer will run with a protected set of the form:

- `protected_out := VarSet.union (output_of pgm) (sec_post (cmd_of pgm) secrets)`

### 5. Keep `AssignCall` conservative in v1

We will not try to eliminate `AssignCall` in the first version.
If we need a post-secret summary for it, we conservatively mark its destination as `Secret`.

### 6. Start with straight-line plus branching, then finish loops

Loops are the hardest part because they need a stable security invariant.
The implementation should still keep loop syntax supported, but the work should be staged:

- first get `Assign`, `Cmov`, `Sequence`, and `If` correct
- then add the loop fixpoint and loop proofs

## High-Level Strategy

### Current behavior

Current safe DSE removes a dead assignment or `Cmov` when:

- the destination variable is not live in `out`
- the destination variable is `Public` in the original input secret set

This ignores:
- secrets introduced by earlier statements
- secrets introduced by the right-hand side expression itself
- the need to preserve values of finally-secret variables even if they are not outputs

### New behavior

The new safe DSE will optimize with two pieces of information at each program point:

- a backward set of variables whose values must be preserved
- a forward secret environment describing which variables may currently be secret

For a dead write to be removed, we must know both:

- the old value/label of the destination is irrelevant to the protected set
- the write itself does not turn the destination secret

## Planned New Definitions

### 1. Forward secret transfer function

Add a computable function in `src/Language/Optimizations/Safe/DSE.v`:

```coq
Fixpoint sec_post (c : cmd) (se : sec_env) : sec_env := ...
```

Intended meaning:

- `sec_post c se` is a conservative approximation of the final dynamic secret environment
  after running `c` from an initial secret environment `se`

It is a may-analysis:

- `Public` means definitely public
- `Secret` means may be secret

#### Transfer rules

Use these rules in v1:

- `Skip`
  - `sec_post Skip se = se`
- `Assign x e`
  - `sec_post (Assign x e) se = update_sec se x (interp_sec e se)`
- `Cmov x cond e1 e2`
  - `sec_post (Cmov x cond e1 e2) se = update_sec se x (join_sec (interp_sec cond se) (join_sec (interp_sec e1 se) (interp_sec e2 se)))`
- `AssignCall x f e1 e2`
  - conservative v1: `update_sec se x Secret`
- `Sequence c1 c2`
  - `sec_post c2 (sec_post c1 se)`
- `If e c1 c2`
  - `join_sec_env (sec_post c1 se) (sec_post c2 se)`
- `While e body`
  - use a security fixpoint / invariant, conservative if necessary

### 2. Security fixpoint for `While`

Add a loop helper in the same style as the existing liveness fixpoint.

Recommended shape:

```coq
Fixpoint sec_while_fixpoint (body_post : sec_env -> sec_env) (inv : sec_env) (fuel : nat) : sec_env := ...
```

Target intuition:

- start from the incoming secret env
- repeatedly close it under one body iteration
- use `join_sec_env` to accumulate anything that may become secret

Conservative rule:

- if exact loop reasoning becomes awkward at any step, join more secrets rather than fewer

### 3. Protected output set

Add a helper definition:

```coq
Definition protected_out (pgm : program) (secrets : sec_env) : var_set :=
  VarSet.union (output_of pgm) (sec_post (cmd_of pgm) secrets).
```

This is the backward set that DSE must preserve at the top level.

## Optimizer Refactor Plan

## Chunk 1: Refactor `safe_dse_helper` to thread forward secrets

File:

- `src/Language/Optimizations/Safe/DSE.v`

Tasks:

1. Add `sec_post`.
2. Update `safe_dse_helper` so that its `secrets` argument means the incoming
   static secret environment at the current program point.
3. Change the `Sequence` case to thread the forward secret env:
   - optimize `c1` under `se`
   - compute `se_mid := sec_post c1 se`
   - optimize `c2` under `se_mid`
4. Keep `If` branches under the same incoming `se`.
5. Add a conservative `While` treatment.
6. Change `opt_safe_dse` to use `protected_out`, not just `output_of pgm`.

### New removal rule for `Assign`

Remove `Assign x e` only if all of the following hold:

- `VarSet.mem x out = false`
- `sec_lookup se x = Public`
- `interp_sec e se = Public`

Otherwise keep it.

### New removal rule for `Cmov`

Remove `Cmov x cond e1 e2` only if all of the following hold:

- `VarSet.mem x out = false`
- `sec_lookup se x = Public`
- `join_sec (interp_sec cond se) (join_sec (interp_sec e1 se) (interp_sec e2 se)) = Public`

Otherwise keep it.

### Conservative `AssignCall` policy

In v1:

- keep `AssignCall` unchanged
- let `sec_post` mark its destination `Secret`

This avoids unsoundness from unknown callee effects.

### Conservative `While` policy

In v1:

- compute a secret invariant using a join-based fixpoint
- optimize the body under that invariant

If this proof becomes too hard immediately, an acceptable temporary checkpoint is:

- keep loop bodies unoptimized
- still compute a conservative post-secret env for the whole loop

That checkpoint is conservative and keeps the theorem direction viable.

### Done condition

After this chunk:

- `x := s` is no longer removable when `s` may be secret
- top-level DSE protects maybe-final-secret variables
- the optimizer interface remains `program -> sec_env -> program`

## Chunk 2: Prove basic soundness of the forward secret analysis

Files:

- likely `src/Proofs/SecEnvProofs.v`
- likely `src/Proofs/SecurityProofs.v`
- optionally a new dedicated proof file if this grows too much

Tasks:

1. Add helper lemmas about `update_sec`, `join_sec_env`, and `interp_sec` as needed.
2. Add monotonicity lemmas for `sec_post` if the loop fixpoint needs them.
3. Prove a core analysis soundness theorem of this flavor:

```coq
eval_sec phi sctx c sctx' ->
forall x, sec_lookup (sec_of sctx') x = Secret -> sec_lookup (sec_post c (sec_of sctx)) x = Secret.
```

This theorem says the static post-secret env over-approximates every dynamic final secret.

4. Prove the theorem first for:
   - `Skip`
   - `Assign`
   - `Cmov`
   - `Sequence`
   - `If`
5. Extend to `AssignCall` with the conservative destination-secret rule.
6. Extend to `While` once the loop invariant is in place.

### Done condition

After this chunk, the forward analysis is justified as a safe approximation of `eval_sec`.

## Chunk 3: Adapt plain semantic soundness of safe DSE

File:

- `src/Proofs/SafeDSEProofs.v`

Main target:

- repair `safe_dse_helper_sound`
- repair `opt_safe_dse_sound`

Tasks:

1. Thread the new incoming secret env through `safe_dse_helper_sound`.
2. Update the induction hypotheses so that `Sequence` passes `sec_post c1 se`
   into the proof for `c2`.
3. Replace old cases that only destructed `sec_lookup secrets x` with new cases that inspect:
   - liveness of `x`
   - old label of `x`
   - new label of the assignment / cmov result
4. Keep `AssignCall` unchanged so its case stays close to the current one.
5. Make sure the agreement theorem preserves `protected_out`, not just raw outputs.

### Expected proof shape

The proof should remain an induction on source `eval`, not a redesign.
The key difference is that the optimizer is now more selective, so removed-write
cases become stronger and better aligned with the secret theorem.

### Done condition

After this chunk:

- `opt_safe_dse_sound` still proves plain `eval` soundness
- all updated files compile

## Chunk 4: Adapt trace lifting and non-inference preservation

File:

- `src/Proofs/SafeDSESecurityProof.v`

Main targets:

- repair `opt_safe_dse_helper_trace_complete`
- repair `opt_safe_dse_helper_preserves_safe_pgm`

Tasks:

1. Thread the new incoming secret env through the helper lemmas.
2. Update the `Assign` and `Cmov` trace-completeness cases to use the stronger
   removal rule.
3. Update the `Sequence` case to thread `sec_post c1 se` into the proof of `c2`.
4. Update the `While` case once the loop invariant is available.
5. Keep the non-inference proof conservative if needed.

### Conservative theorem strategy

It is acceptable if the existential secret set used by
`opt_safe_dse_helper_preserves_safe_pgm` remains an over-approximation during the
first pass, as long as the theorem stays true and compiles.

### Done condition

After this chunk:

- the non-inference half of `is_safe_opt` still holds for the refactored optimizer

## Chunk 5: Prove helper-level secret preservation for safe DSE

File:

- `src/Proofs/SafeDSESecurityProof.v` or a new dedicated file if this becomes too large

Main target:

- a new `eval_sec` simulation lemma for `safe_dse_helper`

This is the crucial new proof. It replaces the unskip-style exact completeness argument.

### Recommended theorem shape

Prove something of the form:

```coq
Lemma safe_dse_helper_keeps_secrets_secret :
  forall phi c out se_in sctx sctx_src,
    sec_of sctx = se_in ->
    eval_sec phi sctx c sctx_src ->
    exists sctx_dse,
      eval_sec phi sctx (safe_dse_helper c out se_in) sctx_dse /\
      (forall x,
         sec_lookup (sec_of sctx_src) x = sec_lookup (sec_of sctx_dse) x) /\
      agree_on_secret (sec_of sctx_src) (sec_val_of sctx_src) (sec_val_of sctx_dse).
```

The exact statement can be adjusted, but it should directly expose:

- final secret-env equality
- final value agreement on finally-secret variables

### Proof strategy

Induct on the source `eval_sec` derivation.

#### Kept-write cases

When the optimizer keeps the source command:

- reconstruct the same `eval_sec` rule
- conclude by induction or reflexive agreement

#### Removed `Assign` case

Use the new removal rule to show:

- `x` was not protected by the backward set
- `x` was public before the assignment
- `x` stays public after the assignment

Therefore replacing the assignment by `Skip` cannot:

- change the final secret set at `x`
- change the value of any finally-secret variable

#### Removed `Cmov` case

Same idea as `Assign`, but use the joined label proof.

#### Sequence case

Compose the first induction result into the second one.
This is likely the technically hardest non-loop case.

#### If case

The static env is the same on both branches, so this should be manageable once
the branch cases are in place.

#### While case

Use the loop security invariant from the forward analysis.
Expect this to be the hardest case overall.

### Done condition

After this chunk, there is a helper-level theorem that directly states safe DSE
preserves final secret labels and values on final secrets.

## Chunk 6: Compose safe DSE with unskip for the final theorem

File:

- `src/Proofs/SafeDSESecurityProof.v`

Main target:

- prove `opt_keeps_secrets_secret opt_safe_dse`

### Composition plan

1. Start from an optimized `eval_sec` run of `opt_safe_dse`.
2. Expand the `opt_unskip_cmd` part using:
   - `opt_unskip_sec_complete`
3. This reduces the goal to the helper command `safe_dse_helper ...`.
4. Apply the new helper-level secret preservation theorem from Chunk 5.
5. If there are two helper executions to compare, use:
   - `eval_sec_deterministic`
6. Conclude:
   - final secret labels agree for all variables
   - final values agree on every source-final-secret variable

### Important note

Unlike the unskip proof, the safe DSE proof should not try to prove exact final
context equality. The correct target is:

- equal final secret environments
- agreement on values of finally-secret variables

### Done condition

After this chunk:

- the second half of `is_safe_opt` is proved for `opt_safe_dse`

## Chunk 7: Finish loop precision if any temporary fallback remains

This chunk only exists if earlier chunks used a temporary conservative fallback.

Tasks:

1. Replace any temporary “do not optimize loop bodies” behavior with the real
   invariant-driven body optimization.
2. Strengthen `sec_post` for loops if the first version was intentionally coarse.
3. Extend the helper-level secret theorem to the final loop implementation.
4. Re-run all downstream proofs.

### Done condition

After this chunk, the final optimizer behavior matches the intended design,
including loops.

## Suggested Implementation Order

Follow this order strictly.

1. Add `sec_post` and `protected_out`.
2. Refactor `safe_dse_helper` to thread the incoming static secret env.
3. Recompile the optimizer file.
4. Repair `safe_dse_helper_sound` and `opt_safe_dse_sound`.
5. Repair trace lifting and non-inference preservation.
6. Prove the helper-level `eval_sec` secret-preservation theorem.
7. Compose with `opt_unskip_sec_complete` to prove `opt_keeps_secrets_secret`.
8. Finish loop precision if a temporary fallback was used.
9. Run `make rocq`.

## File-by-File Impact

### `src/Language/Optimizations/Safe/DSE.v`

- add `sec_post`
- add loop secret fixpoint helper if needed
- refactor `safe_dse_helper`
- update `opt_safe_dse`

### `src/Proofs/SafeDSEProofs.v`

- adapt `safe_dse_helper_sound`
- adapt `opt_safe_dse_sound`

### `src/Proofs/SafeDSESecurityProof.v`

- adapt trace completeness / lifting lemmas
- adapt non-inference preservation theorem
- add helper-level secret-preservation theorem
- prove final `opt_keeps_secrets_secret` result

### `src/Proofs/SecEnvProofs.v`

- add set / lookup / update lemmas needed by `sec_post`

### `src/Proofs/SecurityProofs.v`

- add any semantic soundness lemmas linking `eval_sec` and `sec_post`
- possibly add loop-invariant helper lemmas

## Verification Plan

### Local checkpoints

Compile after each chunk, not only at the end.

Recommended checkpoints:

1. `rocq compile -R src "" src/Language/Optimizations/Safe/DSE.v`
2. `rocq compile -R src "" src/Proofs/SafeDSEProofs.v`
3. `rocq compile -R src "" src/Proofs/SafeDSESecurityProof.v`

### Final verification

Run:

```sh
make rocq
```

## Expected Risks

### 1. Loop invariants may dominate the proof effort

This is expected. That is why loops are explicitly staged late and conservative
fallbacks are allowed temporarily.

### 2. `Sequence` proofs will become more technical

This is also expected because they now thread both:

- backward liveness / protected sets
- forward secret environments

### 3. Over-approximation may reduce optimization power

This is acceptable in v1. The goal is to recover soundness and the secret-preservation theorem first.

## Success Criteria

The refactor is complete when all of the following hold:

1. `opt_safe_dse` no longer removes commands like `x := s` when `s` may be secret.
2. Plain `eval` soundness still holds.
3. The non-inference side of `is_safe_opt` still holds.
4. The full theorem `opt_keeps_secrets_secret opt_safe_dse` is proved.
5. The project compiles with `make rocq`.
