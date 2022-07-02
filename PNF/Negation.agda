{-# OPTIONS --guardedness #-}

module PNF.Negation where

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

A-negation : ∀ {n} {ϕ : Full n} → ! (A ϕ) ≡ (◯ (! ϕ))
A-negation {σ = σ} {μ = μ} = (λ x → ¬∀C→∃C¬ {x = ↑ (C≤ 1 σ) μ} x)
                            , (λ x → ¬∀C←∃C¬ {x = ↑ (C≤ 1 σ) μ} x)

T-negation : ∀ {n} {ϕ₁ ϕ₂ : Full n} → ! (ϕ₁ T ϕ₂) ≡ ((! ϕ₂) U (! ϕ₁ ∧ ! ϕ₂))
T-negation {σ = σ} {μ = μ} =
  (λ x → congUntil (λ {i} → ¬∀C→∃C¬ {x = ↑ (C≤ i σ) μ})
                       (λ {i} (p1 , p2) → conjunct∃ {x = ↑ (C≤ i σ) μ} (¬∀C→∃C¬ {x = ↑ (C≤ i σ) μ} p1)
                                                                       (¬∀C→∃C¬ {x = ↑ (C≤ i σ) μ} p2))
                       (¬weakUntil→until x)) ,
  (λ x → ¬weakUntil←until (congUntil (λ {i} → ¬∀C←∃C¬ {x = ↑ (C≤ i σ) μ})
                                         (λ {i} x → let a , b = (disjunct∃ {x = ↑ (C≤ i σ) μ} x) in ¬∀C←∃C¬ {x = ↑ (C≤ i σ) μ} a , ¬∀C←∃C¬ {x = ↑ (C≤ i σ) μ} b)
                                         x))
