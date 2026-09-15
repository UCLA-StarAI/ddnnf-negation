# Negation of d-DNNF in Lean

[![Verify Lean proof](https://github.com/UCLA-StarAI/ddnnf-negation/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/UCLA-StarAI/ddnnf-negation/actions/workflows/lean.yml)

**[Read the paper (PDF)](negation-of-ddnnf.pdf).** This repository formalizes the proof
that d-DNNF is not polynomially closed under negation and its circuit,
grammar, and automaton corollaries.

Start with the [formal statement](src/DDNNFNegation/TrustBoundary.lean),
follow the [proof modules](src/DDNNFNegation.lean), or browse the
[corollaries](src/DDNNFNegationCorollaries/README.md).

With [elan](https://github.com/leanprover/elan) installed, run:

```sh
lake exe cache get
lake build DDNNFNegation DDNNFNegationCorollaries DDNNFNegationTests
lake env lean scripts/Check.lean
lake env lean scripts/CheckCorollaries.lean
```

Lean and Mathlib versions are pinned. CI builds the proof and corollaries
and checks their axiom dependencies. Code: [Apache 2.0](LICENSE).
