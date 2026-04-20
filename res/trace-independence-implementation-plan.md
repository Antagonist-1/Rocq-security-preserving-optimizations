**Implementation Plan**

## Goal

Extend the language and semantics so that:

- secrecy is tracked during execution via a `sec_env`
- secrecy propagates through assignments and expressions via `interp_sec`
- `eval` remains a plain execution semantics
- a second judgment checks constant-time style trace safety
- initial secrecy comes from function inputs, not from ad hoc assignments

## Design Summary

Use a minimal Jasmin-inspired model:

- security lattice: `Public | Secret` (instead of just having true/false for whether an expression is secret/or public)
- security environment: `fmap var sec_level` (`previously fmap var unit`)
- runtime context: valuation + security environment + trace
- expression security interpreter: `interp_sec` (return the sec_level of an expression given a `sec_env`)
- separate constant-time checker: (Build proof tree of secure commands, rejecting secret guards)
  - `if` and `while` guards (conditions) must be `Public`

## Scope

To implement this week : 

- `sec_level`
- `sec_env`
- extended `context`
- `interp_sec`
- secrecy propagation in `eval`
- constant-time checker judgment
- examples and small proof update

For later:

- source syntax for `secret`
- declassification
- safe DSE integration
- full Jasmin-style polymorphic security contracts

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

Extend the runtime state.

Current:

- `context := valuation * list trace_event`

Planned:

- `context := valuation * sec_env * list trace_event`

Add accessors:

- `val_of`
- `sec_of`
- `trace_of`

Update notations:

- trace append notation
- valuation update notation
- add a security update notation if useful

Update `empty_context`:

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

### 5.  `eval` Rules

Keep `eval` executable and permissive.
Eval only cares about correctness of execution, not about security.

#### `EvalAssign`

Current effect:

- update valuation only

Planned effect:

- update valuation with `interp_arith`
- update security env with `interp_sec`

Meaning:

- after `x <- e`, the security of `x` becomes the security of `e`

#### `EvalAssignCall`

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

#### `EvalSequence`

- thread full context

#### `EvalIfTrue` / `EvalIfFalse`

- same operational behavior
- thread full context including `sec_env`

#### `EvalWhileTrue` / `EvalWhileFalse`

- same operational behavior
- thread full context including `sec_env`

## Constant-Time Checker

### 6. Add a Second Judgment

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

Update all examples to the new context shape.

Current examples use:

- `(v, trace)`

Planned examples use:

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
2. Extend `context` and update helpers/notions
3. Add `interp_sec`
4. Update `eval` rules to thread secrecy
5. Update `AssignCall` to initialize callee secrecy from actual arguments
6. Repair existing examples/proofs to new context shape
7. Add constant-time checker judgment
8. Add small checker examples
NExt week:
9. State and begin proving the trace non-interference theorem

## Expected Friction Points

### Function calls
The biggest proof/design hotspot will be `AssignCall`, because secrecy must move correctly across caller/callee boundaries.

### Existing proof scripts
`SimpleTraces.v` uses automation that assumes contexts are pairs. That automation will need small updates.

### Separation of concerns
Keep clear separation between:

- execution semantics
- secrecy propagation
- constant-time admissibility

Do not fold all three into `eval`.


## One Small Design Recommendation

Do **not** change the object-language syntax to add secret declarations.

Instead:

- treat secrecy as part of the semantic interface of function inputs
- initialize it at call boundaries from actual arguments

That keeps the implementation small and aligned with the direction you prefer.

