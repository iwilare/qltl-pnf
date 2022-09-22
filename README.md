## Positive normal forms for counterpart-based temporal logics

This repository contains the Agda definitions and proofs to present a positive normal form for a quantified linear temporal logic QLTL based on counterpart semantics in the sense of Lewis. Two counterpart flavours are defined here, one with partial functions and one with standard relations.

## Remarks

Formulas use a representation based on de Bruijn indices to ensure well-scopedness[^1]. Each formula is typed with a number `n : ℕ`, indicating the size of the underlying context in which the formula is defined. This is such that `n` is greater than the cardinality of the set of free variables of the formula, and is thus sufficient to ensure that the formula is well-scoped by construction. For example, in PNF the formula `∃x. x = y` is represented as:
```agda
-- The formula has type `QLTL 1` since y appears free, the context has at least 1 variable
example : QLTL 1
example = ∃<> zero == suc zero
       -- ∃x. x == y
```

[^1]: https://plfa.github.io/DeBruijn/

## Requirements

No external libraries have been used. The files are tested using Agda 2.6.2.
