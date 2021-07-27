---
# Documentation: https://wowchemy.com/docs/managing-content/

title: Formally Verified Quantum Programming
subtitle: ''
summary: ''
authors:
- Robert Rand
tags: []
categories: []
date: '2018-01-01'
lastmod: 2021-07-26T16:34:20-05:00
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
publishDate: '2021-07-26T21:34:20.056688Z'
publication_types:
- '7'
abstract: 'The field of quantum mechanics predates computer science by at least ten years, the time between the publication of the Schrödinger equation and the Church-Turing thesis. It took another fifty years for Feynman to recognize that harnessing quantum mechanics is necessary to efficiently simulate physics and for David Deutsch to propose the quantum Turing machine. After thirty more years, we are finally getting close to the first general-purpose quantum computers based upon prototypes by IBM, Intel, Google and others. 

While physicists and engineers have worked on building scalable quantum computers, theoretical computer scientists have made their own advances. Complexity theorists introduced quantum complexity classes like BQP and QMA; Shor and Grover developed their famous algorithms for factoring and unstructured search. Programming languages researchers pursued two main research directions: Small-scale languages like QPL and the quantum λ-calculi for reasoning about quantum computation and large-scale languages like Quipper and Q# for industrial-scale quantum software development. This thesis aims to unify these two threads while adding a third one: formal verification.

We argue that quantum programs demand machine-checkable proofs of correctness. We justify this on the basis of the complexity of programs manipulating quantum states, the expense of running quantum programs, and the inapplicability of traditional debugging techniques to programs whose states cannot be examined. We further argue that the existing mathematical models of quantum computation make this an easier task than one could reasonably expect. In light of these observations we introduce QWIRE, a tool for writing verifiable, large scale quantum programs.

QWIRE is not merely a language for writing and verifying quantum circuits: it is a verified circuit description language. This means that the semantics of QWIRE circuits are verified in the Coq proof assistant. We also implement verified abstractions, like ancilla management and reversible circuit compilation. Finally, we turn QWIRE and Coq’s abilities outwards, towards verifying popular quantum algorithms like quantum teleportation. We argue that this tool provides a solid foundation for research into quantum programming languages and formal verification going forward.'
publication: ''
url_pdf: thesis.pdf
---
