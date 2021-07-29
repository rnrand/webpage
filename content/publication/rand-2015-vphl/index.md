---
# Documentation: https://wowchemy.com/docs/managing-content/

title: 'VPHL: A Verified Partial-Correctness Logic for Probabilistic Programs'
subtitle: ''
summary: ''
authors:
- Robert Rand
- Steve Zdancewic
tags:
- '"Hoare Logic"'
- '"Formal Verification"'
- '"Coq"'
- '"Probabilistic Programming"'
- '"Non-termination"'
categories: []
date: '2015-01-01'
lastmod: 2021-07-26T16:34:19-05:00
featured: false
draft: false

# Featured image
# To use, add an image named `featured.jpg/png` to your page's folder.
# Focal points: Smart, Center, TopLeft, Top, TopRight, Left, Right, BottomLeft, Bottom, BottomRight.
image:
  caption: ''
  focal_point: ''
  preview_only: false

# Projects (optional).
#   Associate this post with one or more of your projects.
#   Simply enter your project's folder or file name without extension.
#   E.g. `projects = ["internal-project"]` references `content/project/deep-learning/index.md`.
#   Otherwise, set `projects = []`.
projects: []
publishDate: '2021-07-26T21:34:18.905386Z'
publication_types:
- '1'
abstract: We introduce a Hoare-style logic for probabilistic programs, called VPHL,
  that has been formally verified in the Coq proof assistant. VPHL features propositional,
  rather than additive, assertions and a simple set of rules for reasoning about these
  assertions using the standard axioms of probability theory. VPHL's assertions are
  partial correctness assertions, meaning that their conclusions are dependent upon
  (deterministic) program termination. The underlying simple probabilistic imperative
  language, PrImp, includes a probabilistic toss operator, probabilistic guards and
  potentially-non-terminating while loops.
publication: '*Mathematical Foundations of Programming Semantics (MFPS 2015)*'
doi: https://doi.org/10.1016/j.entcs.2015.12.021
url_pdf: files/mfps_2015_expanded.pdf
url_slides: files/mfps_2015_slides.pdf
---
