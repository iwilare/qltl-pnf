{-# OPTIONS --guardedness #-}

module QLTL.Negation where

open import Data.Empty
open import Data.Fin using (Fin)
open import Data.Maybe
open import Data.Nat using (ℕ; _∸_; _+_; _<_; _≤_; suc; zero; _<′_; _<‴_; _≤‴_)
open import Data.Nat.Induction
open import Data.Nat.Properties using (≤⇒≤′; ≤⇒≤‴; <-transˡ; <-trans; <⇒≤; <-cmp; ≤-<-connex)
open import Data.Product
open import Data.Sum
open import Data.Unit hiding (_≤_)
open import Function using (_∘_)
open import Function using (id)
open import Level using (0ℓ; Level)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality using (subst; inspect; refl; sym) renaming (_≡_ to _≣_; [_] to ≣:)
open import Relation.Nullary
open import Relation.Nullary.Negation using (¬∃⟶∀¬; contraposition)

open import Counterpart
open import Predicates
open import Negation
open import Full

◯∃-negation : ∀ {n} {ϕ : Full n} → ! (◯∃ ϕ) ≡ (◯∀ (! ϕ))
◯∃-negation {σ = σ} {μ = μ} = (λ x → ¬∃C→∀C¬ {x = ↑ (C≤ 1 σ) μ} x)
                            , (λ x → ¬∃C←∀C¬ {x = ↑ (C≤ 1 σ) μ} x)

U∃-negation : ∀ {n} {ϕ₁ ϕ₂ : Full n} → ! (ϕ₁ U∃ ϕ₂) ≡ ((! ϕ₂) W∀ (! ϕ₁ ∧ ! ϕ₂))
U∃-negation {σ = σ} {μ = μ} =
  (λ x → congWeakUntil (λ {i} → ¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ})
                       (λ {i} (p1 , p2) → conjunct∀ {x = ↑ (C≤ i σ) μ} (¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ} p1)
                                                                       (¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ} p2))
                       (¬until→weakUntil x)) ,
  (λ x → ¬until←weakUntil (congWeakUntil (λ {i} → ¬∃C←∀C¬ {x = ↑ (C≤ i σ) μ})
                                         (λ {i} x → let a , b = (disjunct∀ {x = ↑ (C≤ i σ) μ} x) in ¬∃C←∀C¬ {x = ↑ (C≤ i σ) μ} a , ¬∃C←∀C¬ {x = ↑ (C≤ i σ) μ} b)
                                         x))
