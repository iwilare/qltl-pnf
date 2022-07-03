{-# OPTIONS --guardedness #-}

{-
  Negation for the temporal operators in non-extended QLTL.
-}
module QLTL.Negation where

open import Data.Product

open import Counterpart
open import Predicates
open import Negation
open import Full

◯-negation : ∀ {n} {ϕ : Full n} → ! (◯ ϕ) ≣ A (! ϕ)
◯-negation {σ = σ} {μ = μ} = (λ x → ¬∃C→∀C¬ {x = ↑ (C≤ 1 σ) μ} x)
                           , (λ x → ¬∃C←∀C¬ {x = ↑ (C≤ 1 σ) μ} x)

U-negation : ∀ {n} {ϕ₁ ϕ₂ : Full n} → ! (ϕ₁ U ϕ₂) ≣ ! ϕ₂ T (! ϕ₁ ∧ ! ϕ₂)
U-negation {σ = σ} {μ = μ} =
  (λ x → congWeakUntil (λ {i} → ¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ})
                       (λ {i} (p1 , p2) → conjunct∀ {x = ↑ (C≤ i σ) μ} (¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ} p1)
                                                                       (¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ} p2))
                       (¬until→weakUntil x)) ,
  (λ x → ¬until←weakUntil (congWeakUntil (λ {i} → ¬∃C←∀C¬ {x = ↑ (C≤ i σ) μ})
                                         (λ {i} x → let a , b = (disjunct∀ {x = ↑ (C≤ i σ) μ} x) in ¬∃C←∀C¬ {x = ↑ (C≤ i σ) μ} a , ¬∃C←∀C¬ {x = ↑ (C≤ i σ) μ} b)
                                         x))
