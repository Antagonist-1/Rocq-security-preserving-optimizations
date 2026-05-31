---
title: |
  {TITLE}
subtitle: |
  CS-{428/642} project report
author:
  - "{Name 1}"
  - "{Name 2}"
  - "{Name 3}"
date: "{2025-06-31}"

documentclass: scrartcl
classoption: a4paper, twocolumn, DIV=calc
mainfont: "Libertinus Serif"
sansfont: "Libertinus Sans"
mathfont: "Libertinus Math"
monofont: "Fira Code"
---

# How to use this template

1. Rename this template to `<Your group id> - <Your project title>.md`.

2. Make sure that this document compiles without errors with `pandoc <your document>.txt --pdf-engine=lualatex -o template.pdf`.

3. Replace all `{}` blocks in this template with your own content.  Use `[@citation_id]` syntax for citations (for example~[@rocq91]), and `[^footnote]` syntax for footnotes (for example[^foo]).

4. Delete this section.

[^foo]: Here's a footnote!

# Abstract

{ABSTRACT}

**Keywords:** {course technique 1, course technique 2, concept 1, concept 2…}

# Introduction

{INTRODUCTION}

# Approach

{APPROACH}

# Results

{RESULTS}

# Timeline

{TIMELINE}

# Related work

{RELATED WORK}

#  Future work

{FUTURE WORK}

# Conclusion

{CONCLUSION}

# AI use disclosure

{AI USE DISCLOSURE}

# References

---
references:
  - id: rocq91
    DOI: 10.5281/zenodo.17473943
    title: "The Rocq Prover"
    author:
      - literal: "The Rocq Development Team"
    issued:
      date-parts: [[2025, 09, 15]]
    publisher: Zenodo
    type: software
    version: 9.1.0
---

