## Goal

This week we will extend the semantics to track secrecy. Next week we do proof of trace non-interference for the constant-time checker. 
_(Non interference is the technical term for the property that changes to secret inputs are not reflected , which in our setting means that secret inputs do not affect the trace.)_

Extend the language and semantics so that:

- secrecy is tracked in a second semantics via a `sec_env` (instead of changing the existing `eval` immediately)
- secrecy propagates through assignments and expressions via `interp_sec`
- `eval` remains exactly the plain execution semantics used today, so colleagues can work in parallel on the language without rebasing onto a semantics refactor
- a second evaluator / judgment threads secrecy information alongside execution
- a second judgment checks constant-time style trace safety (this blocks programs with secret guards, but does not affect execution semantics)

## Design Summary
a minimal *Jasmin-inspired* model:

- security lattice: `Public | Secret` (instead of just having true/false for whether an expression is secret/or public)
- security environment: `fmap var sec_level` (`previously fmap var unit`)
- runtime context for the secrecy-aware semantics: valuation * security environment * trace
- expression security interpreter: `interp_sec` (return the sec_level of an expression given a `sec_env`)
- keep the current `eval` context unchanged and introduce a separate secrecy-aware evaluation relation (for example `eval_sec`)
- separate constant-time checker: (Build proof tree of secure commands, rejecting secret guards)
  - `if` and `while` guards (conditions) must be `Public`

## Scope

To implement this week : 

- `sec_level`
- `sec_env`
- a second secrecy-aware `context`
- `interp_sec`
- secrecy propagation in the second evaluator
- constant-time checker judgment
- examples and small proof update

Next week 
- Add the theorem layer on top.
 if two initial valuations agree on all public variables
 and they may differ on secret ones
and the command passes the constant-time checker
 then any two evaluations produce the same trace

For later (after we prove non-interference next week):


- declassification?
- safe DSE integration

## File-by-File Plan

### 1. `src/Language/Security.v`

Refactor this file into the home for the security model.

Add:

- `Inductive sec_level := Public | Secret.`
- `Definition sec_env := fmap var sec_level.`
- `Definition join_sec : sec_level -> sec_level -> sec_level.` (Just an OR operator where `Secret` dominates `Public`)
- `Definition sec_lookup (se : sec_env) (x : var) : sec_level` 
  - default to `Public` when absent

Replace the current `secrets := fmap var unit` API with:

- predicates based on `sec_env`
- `is_secret se x := sec_lookup se x = Secret`

Keep or redefine:

- public agreement on valuations  ( public variables have the same values but secret variables may differ )
- low-equivalence based on a `sec_env`

Recommended shape:
- `agree_on_public (se : sec_env) (v1 v2 : valuation) : Prop := ...`
This is a standard entry point for non-interference proofs:  For all agree_on_public (same public variables) we have the same trace.
### 2. `src/Language/Semantics.v`

Keep the current runtime state for `eval` unchanged.
Add a second runtime state / evaluator for secrecy-aware execution.

Current:

- `context := valuation * list trace_event`

Planned:

- keep `context := valuation * list trace_event` for the existing `eval`
- add a second context, for example `sec_context := valuation * sec_env * list trace_event`

Add accessors:

- `val_of`
- `sec_of`
- `trace_of`

Update notations:

- trace append notation
- valuation update notation
- add a security update notation if useful

Update or add `empty_context` constructors:

- keep the current empty context for `eval`
- add an empty secrecy-aware context with:
  - empty valuation
  - empty security env
  - empty trace

Add:

- `Fixpoint interp_sec (e : expr) (se : sec_env) : sec_level`
Compute the security level of an expression given a security environment.
Rules:

- `Const _ => Public`
- `Var x => sec_lookup se x`
- `Binop _ e1 e2 => join_sec (interp_sec e1 se) (interp_sec e2 se)`

### 3. `src/Language/Syntax.v`

Keep syntax mostly unchanged.

Only change this file if needed for function metadata.

Recommended minimal approach:

- keep `cmd` and `expr` unchanged
- keep `function_env` mostly unchanged at first

If function-entry secrecy must become explicit in the source model, introduce a small function metadata record later, but this is optional for the first implementation.

### 4. Function Inputs / Initial Secrecy

Use function parameters as the intended source of secrecy.

Implementation choice for now:

- at call time, the callee security environment is initialized from the secrecy of actual arguments
- secrecy is not introduced by assignment syntax

For the current two-argument function model:

- compute `interp_sec e1 (sec_of ctx)`
- compute `interp_sec e2 (sec_of ctx)`
- initialize callee parameter security env with those levels
- run body
- copy result value and result secrecy back into caller variable

This avoids needing a separate source syntax for secrets.

## Semantics Changes

### 5. Keep `eval` As Is

Keep `eval` executable and permissive.
`eval` only cares about correctness of execution, not about security.
Do not change its context or rules in this step.

Reason for this split:

- colleagues can keep working on the core language and existing proofs without immediately rebasing onto the secrecy refactor
- we reduce merge pressure on the operational semantics already in use
- secrecy and constant-time reasoning can be developed in parallel as an additional layer

### 6. Add a Secrecy-Aware Evaluator

Add a second evaluator, for example `eval_sec`, which mirrors `eval` operationally but threads `sec_env`.
This evaluator is where secrecy propagation lives.

#### `EvalSecAssign`

Current effect:

- update valuation only

Planned effect:

- update valuation with `interp_arith`
- update security env with `interp_sec`

Meaning:

- after `x <- e`, the security of `x` becomes the security of `e`

#### `EvalSecAssignCall`

Current effect:

- initialize fresh callee valuation
- keep trace
- run body
- return result value

Planned effect:

- initialize fresh callee valuation from argument values
- initialize fresh callee security env from argument secrecy
- keep caller trace as today
- run body
- return both:
  - result value
  - result security level

This is the key place where secrecy enters execution modularly.

#### `EvalSecSequence`

- thread full context

#### `EvalSecIfTrue` / `EvalSecIfFalse`

- same operational behavior
- thread full context including `sec_env`

#### `EvalSecWhileTrue` / `EvalSecWhileFalse`

- same operational behavior
- thread full context including `sec_env`

## Constant-Time Checker

### 7. Add a Second Judgment

Add a separate judgment, likely in `Security.v` or a new file if it grows.

Suggested name:

- `ct_cmd`
- or `secure_cmd`

Purpose:

- certify that control-flow does not depend on secret data

Core rules:

- `Skip` is allowed
- `Assign` is allowed
- `Sequence c1 c2` requires both subcommands allowed
- `AssignCall` requires called body/function to satisfy the checker
- `If e c1 c2` requires:
  - `interp_sec e se = Public`
  - both branches checked
- `While e body` requires:
  - `interp_sec e se = Public`
  - body checked

## Theorem Layer (For next week)

### 8. Restate Non-Interference For Traces

Target theorem shape:

- if two initial valuations agree on all public variables
- and they may differ on secret ones
- and the command passes the constant-time checker
- then any two evaluations produce the same trace

This will require:

- low-equivalence definition on initial states
- lemmas showing:
  - public expressions evaluate equally in low-equivalent states
  - checked guards evaluate to the same branch outcome
  - traces therefore stay aligned

### 9. Supporting Lemmas

Expect to need:

- `interp_sec_public_agree`
  - if `interp_sec e se = Public` and two valuations agree on public vars, then `interp_arith e v1 = interp_arith e v2`
- preservation lemmas for assignments
- call lemmas for passing low-equivalence through function calls

## Examples And Proof Updates

### 10. `src/examples/SimpleTraces.v`

Update examples so that the plain `eval` examples can stay on the existing context shape, while secrecy-aware examples use the new context.

Current plain-eval examples use:

- `(v, trace)`

Planned secrecy-aware examples use:

- `(v, se, trace)`

Add examples for:

- assignment tainting:
  - secret input makes assigned variable secret
- public branch accepted
- secret branch rejected by the checker
- same trace under different secret inputs for accepted programs

### 11. `src/examples/Programs.v`

Likely minimal updates only.

Possible additions:

- tiny examples specifically for secrecy propagation and branch safety

## Suggested Implementation Order
This week:

1. Add `sec_level`, `sec_env`, `join_sec`, `sec_lookup`
2. Add a separate secrecy-aware `context` and helper projections
3. Add `interp_sec`
4. Add a second evaluator that threads secrecy without changing the existing `eval`
5. Update secrecy-aware `AssignCall` to initialize callee secrecy from actual arguments
6. Repair or extend examples/proofs for the secrecy-aware context while keeping existing plain-eval examples stable where possible
7. Add constant-time checker judgment
8. Add small checker examples
NExt week:
9. State and begin proving the trace non-interference theorem

## Expected Friction Points

### Function calls
The biggest proof/design hotspot will be `AssignCall`, because secrecy must move correctly across caller/callee boundaries.

### Existing proof scripts
`SimpleTraces.v` uses automation that assumes contexts are pairs. Keeping `eval` unchanged reduces churn there, but secrecy-aware examples and lemmas will still need small updates.

### Separation of concerns
Keep clear separation between:

- execution semantics
- secrecy-aware execution semantics
- secrecy propagation
- constant-time admissibility

Do not fold all three into `eval`.

## Parallel Work Note

To support parallel work on the language, prefer the following short-term split:

- keep the current `eval` untouched
- add a second evaluator (`eval_sec`, or similar) for secrecy propagation
- add the constant-time checker as a separate judgment on top

If this layering works well, we can later decide whether the two evaluators should stay separate permanently or be refactored behind a shared abstraction.


## One Small Design Recommendation

We Don't change the object-language syntax to add secret declarations, as I naïvely thought, instead:
- treat secrecy as part of the semantic interface of function inputs
- initialize it at call boundaries from actual arguments

