{-# OPTIONS --guardedness #-}

{-
  Negation for the additional temporal operators in non-extended PNF.
-}
module PNF.Negation where

open import Data.Product

open import Counterpart
open import Predicates
open import Negation
open import Full

A-negation : ∀ {n} {ϕ : Full n} → ! (A ϕ) ≣ ◯ (! ϕ)
A-negation {σ = σ} {μ = μ} = (λ x → ¬∀C→∃C¬ {x = ↑ (C≤ 1 σ) μ} x)
                           , (λ x → ¬∀C←∃C¬ {x = ↑ (C≤ 1 σ) μ} x)

T-negation : ∀ {n} {ϕ₁ ϕ₂ : Full n} → ! (ϕ₁ T ϕ₂) ≣ (! ϕ₂) U (! ϕ₁ ∧ ! ϕ₂)
T-negation {σ = σ} {μ = μ} =
  (λ x → congUntil (λ {i} → ¬∀C→∃C¬ {x = ↑ (C≤ i σ) μ})
                       (λ {i} (p1 , p2) → conjunct∃ {x = ↑ (C≤ i σ) μ} (¬∀C→∃C¬ {x = ↑ (C≤ i σ) μ} p1)
                                                                       (¬∀C→∃C¬ {x = ↑ (C≤ i σ) μ} p2))
                       (¬weakUntil→until x)) ,
  (λ x → ¬weakUntil←until (congUntil (λ {i} → ¬∀C←∃C¬ {x = ↑ (C≤ i σ) μ})
                                         (λ {i} x → let a , b = (disjunct∃ {x = ↑ (C≤ i σ) μ} x) in ¬∀C←∃C¬ {x = ↑ (C≤ i σ) μ} a , ¬∀C←∃C¬ {x = ↑ (C≤ i σ) μ} b)
                                         x))
