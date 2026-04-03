| Reference | Why cited | What we reuse concretely | Limitation for our project |
|---|---|---|---|
| *Dead Store Elimination (Still) Considered Harmful* | Justifies the primary objective by showing that normal compiler DSE can remove secure memory clearing. | The attacker/failure model for zeroization, and the reason a normal dead-store proof is not enough for security. | Mostly motivation and empirical analysis; it does not give a Rocq/IMP-style verified design you can directly implement. |
| *High-assurance zeroization* | Closest paper to your secure-erasure goal. | The idea of a compiler-aware zeroization mechanism and a theorem that erasure survives compilation. | Its design is function-level/compiler-inserted zeroization in Jasmin, not your proposed variable-level `Sensitive`-aware DSE over `IMP`. |
| *CT-Wasm: Type-Driven Secure Cryptography for the Web Ecosystem* | Strong justification for the extension objective. | The `Public`/`Secret` style typing discipline and the idea that type systems can enforce constant-time security constraints. | It is a WebAssembly language design, not a verified optimization pass over `IMP`. |
| *Formal Verification of a Constant-Time Preserving C Compiler* | Shows that constant-time can be a compiler preservation theorem, not just a source-language property. | The theorem shape for your extension: prove an optimization preserves constant-time behavior. | Technically heavier than your setting; it is more a proof-model reference than an implementation blueprint. |
| *Jasmin: High-Assurance and High-Speed Cryptography* | Best reference for the overall project philosophy. | The high-level idea that cryptographic code should combine efficiency, verification, and side-channel awareness in one framework. | Broad design inspiration rather than a step-by-step recipe for your `IMP` development. |
| *The Jasmin Compiler Preserves Cryptographic Security* | Supports your framing that compiler correctness should include security preservation. | The overall claim that verified compilation for crypto should preserve security properties, not just semantics. | Too high-level for your concrete mechanisms; not the main blueprint for DSE or type-system implementation. |
| *A Study of Compiler-Introduced Security Bugs* | Broader background showing that compilers can introduce security problems. | General motivation for the “correctness-security gap” framing in your introduction. | Useful context, but not a direct guide for your proofs or implementation. |
| *Software Foundations* | Best practical blueprint for how to structure the actual Rocq development. | The `IMP` semantics, liveness/optimization proof style, inductive relations, and semantic-preservation proof patterns you will directly adapt. | It is a textbook/course source rather than a security paper, so it provides method more than security-specific design. |

Short takeaway:

- **Main blueprint for implementation style:** `Software Foundations`
- **Main blueprint for secure erasure design:** `High-assurance zeroization`
- **Main blueprint for the type system:** `CT-Wasm`
- **Main blueprint for the constant-time preservation theorem:** `Formal Verification of a Constant-Time Preserving C Compiler`
