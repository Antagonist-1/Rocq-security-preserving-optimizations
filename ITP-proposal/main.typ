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
  #text(size: 18pt, weight: "bold", tracking: 0.05em)[Security-Preserving Optimizations]
  #v(-1em)
  #text(size: 14pt, weight: "bold", style: "italic")[Formal verification of secure compiler passes in a simple language]
  #v(2.5em)
]
#show: word-count
= Introduction / problem statement

Standard optimization tools assume functional correctness is the only required property. However, this approach can introduce security vulnerabilities. For instance, most optimizers would eliminate a `memset` on a region not accessed later, illustrated in this example~@yang2017:

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

*This project intends to explore this issue commonly known as the _Correctness-Security Gap_  @xu2023*  by formally verifying that specific optimization passes on a toy language maintain designated security properties. 


= Proposal
We focus on preserving two distinct security properties. To prove them we will extend the `IMP`  language from the _Software Foundations_ course @SoftwareFoundations with custom optimizations phases, formally verifying they do not add vulnerabilities to the program.

*Security properties*, inspired by the cryptography-centered language *Jasmin*~@almeida2017 @olmos2025:

- *Safe Memory Clearing:* Address the _Dead Store Elimination (DSE)_ issue illustrated above by ensuring the optimizer cannot erase deliberate clears.

  _All sensitive assignments from the original program remain in the optimized program_ 

- #par(first-line-indent: 0em)[

*Preservation of Constant-Time Execution:* Address timing-side channels by ensuring control flow remains independent of sensitive data
// The second one tackles constant time programming, preventing side channel timing attacks.
]

  _The execution trace of a program *P* is identical under all possible inputs of secret variables._ 

#pagebreak()
*AST Optimizations*

Apart from implementing a modified version of DSE, we will also include standard optimizations such as constant folding and constant evaluation among others, and prove that the security properties are preserved under these transformations.

One primary challenge will be tracking security labels propagation throughout the AST, which is essential to ensure that the program control flow remains independent of secret information.

If time allows, we will explore further optimizations, such as _Common Subexpression Elimination_. Another potential area of research is the one of _Timing Side-Channel Attacks_, which exploit memory access latencies.

= Timeline

Since the `IMP` language is already defined in depth @SoftwareFoundations, we already have a solid starting point. Here is our expected timeline, with parallelizable points

- Week 8: Define and formalize the language (extend `IMP`s `arith` and `command` type as needed)

- Weeks 9–10: Formalize optimizations and security properties _(in parallel)_

- Weeks 11–12: Prove correctness and security of transformations _(in parallel)_

- Weeks 13–14: Finalization, clean the code, prepare the presentation and the final report

#bibliography("./ref.bib", full: false)
