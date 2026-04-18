# Agent Notes

## Build And Verification
- This repo is a small Rocq project. the main verification step is compilation.
- Run `make rocq` to verify the full project. It compiles `src/Map.v`, then `src/Language/Syntax.v`, `src/Language/Semantics.v`, `src/Language/Security.v`, `src/Language/Main.v`, and `src/examples/Programs.v`.
- Run `make clean` to remove generated Rocq artifacts from `src/` and its subdirectories.
- For focused checks, use `rocq compile -R src "" src/Map.v`, `rocq compile -R src "" src/Language/Syntax.v`, `rocq compile -R src "" src/Language/Semantics.v`, `rocq compile -R src "" src/Language/Security.v`, `rocq compile -R src "" src/Language/Main.v`, or `rocq compile -R src "" src/examples/Programs.v`.
- Keep the `-R src ""` flag when compiling manually; imports assume `src/` is registered as the logical root.
- `make rocq` prints output because of various `Print`. Non-empty stdout from that command is normal.

## Repo Structure
- `_RocqProject` and `Makefile` are the sources of truth for what is built.
- `src/Map.v` defines the reusable finite-map interface and implementation used by the rest of the project.
- `src/Language/Syntax.v` defines the core language interface: variables, operators, syntax, notations, and `function_env`.
- `src/Language/Semantics.v` defines traces, contexts, interpreters, and big-step evaluation.
- `src/Language/Security.v` defines secrets and public-agreement predicates.
- `src/Language/Main.v` is the convenient re-export surface for the core language modules.
- `src/examples/Programs.v` holds the example programs, signatures, and example function environments.
- `src/optimizations/` and `src/proofs/` exist for future optimization passes and proofs.
- `res/` and `ITP-proposal/` are reference/proposal material, not part of the build.

## Project Goal
- The project extends the Software Foundations-style `IMP` language with optimizations and machine-checked security properties, not just semantic preservation.
- Two target security properties drive the design: preserving deliberate sensitive-memory clears against dead-store elimination, and preserving constant-time behavior by keeping execution traces independent of secret inputs.
- Expected optimization work includes a modified DSE plus standard AST passes like constant folding/evaluation; changes should be evaluated against both semantics and these security goals.
- `src/Language/Semantics.v` and `src/Language/Security.v` already include scaffolding for the constant-time direction: trace events, big-step semantics over traces, secrets, and public-agreement.

## Editing Gotchas
- Generated Rocq files (`*.vo`, `*.vos`, `*.vok`, `*.glob`, `*.aux`) live in `src/` and its subdirectories and are ignored by Git. Do not edit them.
- Keep imports one-way: `Map -> Language/* -> examples/optimizations -> proofs`.
- `Language/*` must not import from `examples/`, `optimizations/`, or `proofs/`.
- If you change any `src/Language/*.v` file, re-run full compilation instead of only compiling that file when the change could affect downstream imports or `Map` assumptions.
