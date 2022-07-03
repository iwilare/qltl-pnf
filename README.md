## Positive normal forms for counterpart-based temporal logics

This repository contains the Agda definitions and proofs presented in the paper "Positive normal forms for counterpart-based temporal logics" (Gadducci, Laretto, Trotta 2022).

For simplicity, only the extended versions of QLTL and its positive normal form are formalized here, since the constructions for the standard case trivially follow. However, the proofs still closely mirror our work and the new operators are introduced with the same pace of the paper.

## Remarks

Formulas use a representation based on de Bruijn indices to ensure well-scopedness[^1]. Each formula is typed with a number `n : ℕ`, indicating the size of the underlying context in which the formula is defined. This is such that `n` is greater than the cardinality of the set of free variables of the formula, and is thus sufficient to ensure that the formula is well-scoped by construction. For example, in PNF the formula `∃x. x = y` is represented as:
```agda
-- The formula has type `QLTL 1` since y appears free, the context has at least 1 variable
example : QLTL 1
example = ∃<> zero == suc zero
       -- ∃x. x == y
```

[^1]: https://plfa.github.io/DeBruijn/

### Files description

- `QLTL.agda`: syntax and semantics of extended QLTL.
- `PNF.agda`: syntax and semantics for the positive normal form of extended QLTL.
- `Full.agda`: syntax and semantics of QLTL with all additional operators, used to show the main theorems.
- `Counterpart.agda`: core definitions for traces, counterpart models, counterpart functions and their negations.
- `Predicates.agda`: shorthands for the standard predicates of LTL.
- `Negation.agda`: classical notions of negations used in the proofs.
- `PNF/Conversion.agda`: conversion and equi-expressiveness of extended QLTL and its positive normal form. The translation function is indicated with `^`.

- `QLTL/*.agda`: equivalences and results for QLTL.
- `PNF/*.agda`: equivalences and results for the positive normal form.

- `QLTL/Ext/Negation.agda`: negation for QLTL extended with weak until.
- `QLTL/Negation/AlwaysEventually.agda`: negation for the derived operators of QLTL.
- `PNF/Negation/AlwaysEventually.agda`: negation for the additional derived operators of PNF.

- `Alternative/`: positive normal form results for the alternative definition of the `then` operator.
- `All/`: collection of all results for ease of retrieval.

## Requirements

No external libraries have been used. The files are tested using Agda 2.6.2.
