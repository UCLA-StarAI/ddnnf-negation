# Formalized corollaries

This library proves the six corollaries in [the paper](https://ucla-starai.github.io/ddnnf-negation/negation-of-ddnnf.pdf).
Each theorem is tagged with its paper label and links from the corresponding
box in the PDF. The core nonclosure proof does not import this library.

| Paper result | Module | Theorem |
|---|---|---|
| d-D versus DNNF | [InternalNegation](InternalNegation.lean) | `internal_negation_separation` |
| Negating unambiguous OBDDs | [UnambiguousOBDD](UnambiguousOBDD.lean) | `unambiguous_obdd_separation` |
| Missing monomials | [MissingMonomials](MissingMonomials.lean) | `missing_monomials` |
| Probabilistic circuit subtraction | [ProbabilisticSubtraction](ProbabilisticSubtraction.lean) | `probabilistic_subtraction` |
| Grammar complementation | [GrammarComplementation](GrammarComplementation.lean) | `grammar_complementation` |
| Deterministic pushdown automata | [PushdownAutomata](PushdownAutomata.lean) | `dpda_size_separation` |

The statements use explicit bounds in the construction parameter `n`.
The paper sets `m = 2^(c*n)` for a sufficiently large fixed `c` to express
these as an `O(m)` upper bound and an `m^{Ω(log m)}` lower bound.
Input length is `N = 60*n²`. Circuit size counts edges plus one; auxiliary gate counts are named
`nodeCount`. Grammar size counts productions and right-hand-side symbols;
automata and branching programs use their stated description measures.

## Reading the statements

The circuit models include semantics and support with equations fixing their
meaning. Each module defines its representation, proves the relevant
translation, and packages the upper and lower bounds in the tagged theorem.

* **Internal negation:** `DDCircuit` has explicit NOT gates; `POG` uses signed
  edges. Both receive the lower bound against arbitrary DNNFs.
* **Unambiguous OBDDs:** one hard function has a small unambiguous program in
  every variable order. The complement is hard for every DNNF.
* **Missing monomials:** `ArithCircuit` has nonnegative constants on the
  monotone side. The lower bound depends only on monomial support and allows
  any positive coefficients; the small circuit is syntactically multilinear.
* **Probabilistic subtraction:** the upper circuit is a monotone
  set-multilinear arithmetic circuit evaluated at Boolean literal indicators.
  It is right-linear in one variable order, hence structured-decomposable.
  Subtracting its value from one and normalizing gives the uniform complement
  distribution. The lower bound covers general nonnegative decomposable
  `ProbCircuit`s.
* **Grammars:** `descriptionSize` counts productions and right-hand-side
  occurrences. The complement grammar is constrained only on words of length
  `N`, and may be ambiguous. The positive right-linear grammar has unique
  parses.
* **Pushdown automata:** `Pushdown.DPDA` has one-way input, epsilon moves, and
  final-state acceptance. The small unambiguous automaton is presented as its
  right-linear grammar. `DPDA.complementCFG` directly constructs a complement
  grammar using run summaries, with a polynomial bound on its size.

Definitions and reusable translations live in
[Supporting](Supporting/README.md).

## Verification

```sh
lake build DDNNFNegationCorollaries
lake env lean scripts/CheckCorollaries.lean
```

The check verifies all six tagged endpoints and their axiom dependencies.
