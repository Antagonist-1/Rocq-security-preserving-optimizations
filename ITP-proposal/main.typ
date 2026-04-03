#import "@preview/codelst:2.0.2": sourcecode
#import "@preview/wordometer:0.1.5": word-count, total-words

#set page("a4", margin: (x: 1.25in, y: 1.25in))
#set text(font: "Libertinus Serif", size: 11pt)
#set par(justify: true, leading: 0.8em, first-line-indent: 1.2em, spacing: 1.5em)
#set heading(numbering: "1.")
#set bibliography(style: "association-for-computing-machinery")

#align(left)[Carraux Guillaume, Bennani Maria, Perazzolo Sean]

#show list: set block(spacing: 1.5em)
#show list: set list(indent: 1em, body-indent: 0.6em)

// Title
#align(center)[
  #text(size: 18pt, weight: "bold", tracking: 0.05em)[TITLé]
  #v(-1em)
  #text(size: 14pt, weight: "bold", style: "italic")[Verifying security of optimizations in a simple language]
  #v(2.5em)
]
#show: word-count
= Introduction / problem statement

Standard optimization tools assume functional correctness is the only required property. However, this approach can introduce security vulnerabilities. For example, most optimizers would eliminate a `memset` on a region not accessed later. @yang2017

#sourcecode(
  numbers-start: 1,
  highlighted: (5,),
)[```c
  static void invert_key(u16 *ek, u16 dk[IDEA_KEYLEN]) {
    u16 temp[IDEA_KEYLEN]; // Allocated on stack to hold inverted key 
     ...
    memcpy(dk, temp, sizeof(temp));
    memset(temp, 0, sizeof(temp)); // Clear the value from memory
  }
```]

While functionally redundant, this `memset` is necessary from a security perspective, to explicitly erase the value from memory and prevent memory-dump attacks.

// TOoOD: Cite the correc tsource
*This project intends to explore this issue commonly known as the _Correctness-Security Gap_ * @xu2023 by formally verifying that specific optimization passes on a toy language maintain designated security properties. 


= Proposal
We focus on preserving two distinct security properties. To prove them we will extend the `IMP`  language from the _Software Foundations_ course @SoftwareFoundations with custom optimizations phases, formally verifying they do not add vulnerabilities to the program.

*Security properties*, inspired by the cryptography-centered language *Jasmin*. @almeida2017 @olmos2025

- *Safe Memory Clearing:* Address the DSE issue illustrated above by ensuring the optimizer cannot erase deliberate clears.

  _All sensitive assignments from the original program remain in the optimized program_ 

- #par(first-line-indent: 0em)[

*Preservation of Constant-Time Execution:* Address timing-side channels by ensuring control flow remains independent of sensitive data
// The second one tackles constant time programming, preventing side channel timing attacks.
]

  _The execution trace of a programs *P* is identical under all possible inputs of secret variables._ 

#pagebreak()
*AST Optimizations*

Apart from implementing a modified version of DSE, we will also add other, more standards optimizations, such constant folding, constant evaluation, etc.

One possible challenge we expect to face is the propagation of use of secrets, that we need to follow in order to determine if the program branches depending on a secret.

If time allows, we will focus on new possible optimizations, such as _Constant Subexpression Elimination_. Another possible attack to study is a _side channel timing attack caused by memory access_.

= Timeline and responsibilities

Since the `IMP` language is already defined in depth @SoftwareFoundations, we already have a solid starting point. Here is our expected timeline, with parallelizable points

- W8: define and formalize the language (extend `IMP`s arith and command type as needed)

- W9-10: formalize optimizations and security properties _(in parallel)_

- W11-12: prove correctness and security of transformations _(in parallel)_

- W13-14: finalization, cleaning the code, preparing presentation, writing final report

#bibliography("./ref.bib", full: false)

#total-words words