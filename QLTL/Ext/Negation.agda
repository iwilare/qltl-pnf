{-# OPTIONS --guardedness #-}

{-
  Negation for the additional temporal operators in extended QLTL and extended PNF.
-}
module QLTL.Ext.Negation where

open import Data.Product

open import Counterpart
open import Predicates
open import Negation
open import Full

W-negation : ∀ {n} {ϕ₁ ϕ₂ : Full n} → ! (ϕ₁ W ϕ₂) ≣ (! ϕ₂) F (! ϕ₁ ∧ ! ϕ₂)
W-negation {σ = σ} {μ = μ} =
  (λ x → congUntil (λ {i} → ¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ})
                       (λ {i} (p1 , p2) → conjunct∀ {x = ↑ (C≤ i σ) μ} (¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ} p1)
                                                                       (¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ} p2))
                       (¬weakUntil→until x)) ,
  (λ x → ¬weakUntil←until (congUntil (λ {i} → ¬∃C←∀C¬ {x = ↑ (C≤ i σ) μ})
                                         (λ {i} x → let a , b = (disjunct∀ {x = ↑ (C≤ i σ) μ} x) in ¬∃C←∀C¬ {x = ↑ (C≤ i σ) μ} a , ¬∃C←∀C¬ {x = ↑ (C≤ i σ) μ} b)
                                         x))

F-negation : ∀ {n} {ϕ₁ ϕ₂ : Full n} → ! (ϕ₁ F ϕ₂) ≣ (! ϕ₂) W (! ϕ₁ ∧ ! ϕ₂)
F-negation {σ = σ} {μ = μ} =
  (λ x → congWeakUntil (λ {i} → ¬∀C→∃C¬ {x = ↑ (C≤ i σ) μ})
                       (λ {i} (p1 , p2) → conjunct∃ {x = ↑ (C≤ i σ) μ} (¬∀C→∃C¬ {x = ↑ (C≤ i σ) μ} p1)
                                                                       (¬∀C→∃C¬ {x = ↑ (C≤ i σ) μ} p2))
                       (¬until→weakUntil x)) ,
  (λ x → ¬until←weakUntil (congWeakUntil (λ {i} → ¬∀C←∃C¬ {x = ↑ (C≤ i σ) μ})
                                         (λ {i} x → let a , b = (disjunct∃ {x = ↑ (C≤ i σ) μ} x) in ¬∀C←∃C¬ {x = ↑ (C≤ i σ) μ} a , ¬∀C←∃C¬ {x = ↑ (C≤ i σ) μ} b)
                                         x))
