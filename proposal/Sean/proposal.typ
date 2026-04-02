

#set page(paper: "a4")
#set text(font: "Libertinus Serif", size: 11pt)
#set heading(numbering: "1.1")

#align(center)[
  #text(size: 16pt, weight: "bold")[Bridging the Correctness-Security Gap:]

  #text(size: 14pt)[A Formally Verified, Security-Aware Compiler Pipeline in Rocq]
]
#set par(justify: true)
#v(2em)

= Motivation
Mainstream compilers (e.g., GCC, Clang) optimize code under the assumption that functional correctness is the only required property, and that all data behaves equally. In cryptographic and secure software, this approach fails: mathematically correct optimizations routinely delete critical security mechanisms (such as explicit memory clearing) via Dead Store Elimination (DSE) or introduce timing side-channels by converting constant-time arithmetic into faster conditional branches. This is known as the "Correctness-Security Gap."

Drawing inspiration from the high-assurance cryptographic Domain Specific langage *Jasmin*, this project explores how a compiler's optimization phase can be mathematically constrained to respect security properties.

= Project Scope & Methodology
This project extends the `IMP` language and frameworks provided in the _Software Foundations_ series to build a multi-pass, security-aware compiler pipeline. The development is divided into two distinct objectives, each demonstrating a different technique for preventing *optimization-induced vulnerabilities*.

== Objective 1: Safe Memory Clearing via Dead Store Elimination
The first objective tackles data persistence vulnerabilities.
- *Implementation:* The `IMP` language will be extended to support explicit `Sensitive` variable markers. We will implement a Liveness Analysis and a subsequent Dead Store Elimination (DSE) pass. Liveness analysis remains necessary to identify and safely eliminate non-sensitive dead variables for performance. However, our DSE will implement an explicit exception to retain sensitive data manipulations.
- *Verification:* The optimizer will be proven to satisfy standard functional correctness. Crucially, we will formulate and prove a *Security Preservation Theorem*: the optimizer is statically restricted from eliminating dead stores if the target variable is marked sensitive, effectively proving the compiler safely preserves intentional memory clearing operations.

== Objective 2: Secure Optimization of Constant-Time Branching
The second objective tackles the preservation of constant-time execution, heavily inspired by Jasmin's approach to information flow.
- *Implementation:* We will introduce a static Information Flow Type System tagging variables as `Secret` or `Public`. We will also extend `IMP` with a `CMOV` (Conditional Move) instruction. In hardware and cryptography, a `CMOV` evaluates a condition and performs an assignment in strictly constant time without generating a control-flow branch, preventing timing side-channels.
- *Optimization Pass:* We will implement a type-directed optimizer. Compilers typically try to convert `CMOV` instructions into `IF` branches because branching is faster (assuming correct branch prediction). Our compiler will execute this performance conversion *only* when the condition variable is statically typed as `Public`. `Secret` conditions will be strictly preserved as constant-time `CMOV` instructions.
- *Verification:* We will prove that execution time trace equivalence is preserved with respect to `Secret` variables, ensuring the optimizer improves performance for public data while mathematically guaranteeing it never introduces a timing side-channel for secrets.

= Feasibility & Timeline ( $~$ 100h)
This project is strategically scoped. By leveraging the existing `IMP` semantics, Maps, and foundational Liveness proofs from *Software Foundations (Vol 1 & 2)*, the project avoids the heavy infrastructure cost of defining full compiler semantics from scratch. This allows the ~100 hours to be focused entirely on the novel aspects: implementing the security type systems, modifying the optimizers, and conducting the "Correctness vs. Security" proofs in Rocq.
