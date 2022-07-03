## Positive normal forms for counterpart-based temporal logics

This repository contains the Agda definitions and proofs presented in the paper "Positive normal forms for counterpart-based temporal logics" (Gadducci, Laretto, Trotta 2022).

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

## Remarks

Formulas are represented using de Bruijn indices to ensure well-scopedness. Each formula is typed with a number `n : ℕ` indicating the size of the context.
