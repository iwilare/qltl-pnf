{-# OPTIONS --guardedness #-}

module QLTL.Negation.AlwaysEventually where

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

open import PNF.Negation
open import QLTL.Negation
open import QLTL.Ext.Negation

□-negation : ∀ {n} {ϕ : Full n} → ! (□ ϕ) ≡ ♢* (! ϕ)
□-negation {_} {ϕ} {σ = σ} {μ = μ} = ⇒ , ⇐
   where
     ⇒ : μ , σ ⊨ ! (□ ϕ) → μ , σ ⊨ ♢* (! ϕ)
     ⇒ = congUntil (λ {i} → imply∀ {x = ↑ (C≤ i σ) μ} λ _ → tt)
                   ((λ {i} → imply∀ {x = ↑ (C≤ i σ) μ} proj₁))
       ∘ proj₁ (W-negation {ϕ₁ = ϕ} {ϕ₂ = false} {σ = σ} {μ = μ})

     ⇐ : μ , σ ⊨ ♢* (! ϕ) → μ , σ ⊨ ! (□ ϕ)
     ⇐ = proj₂ (W-negation {ϕ₁ = ϕ} {ϕ₂ = false} {σ = σ} {μ = μ})
       ∘ congUntil ((λ {i} → imply∀ {x = ↑ (C≤ i σ) μ} λ _ z → z))
                   ((λ {i} → imply∀ {x = ↑ (C≤ i σ) μ} λ z → z , (λ x → x)))

♢-negation : ∀ {n} {ϕ : Full n} → ! (♢* ϕ) ≡ □ (! ϕ)
♢-negation {_} {ϕ} {σ = σ} {μ = μ} = ⇒ , ⇐
   where
     ⇒ : μ , σ ⊨ ! (♢* ϕ) → μ , σ ⊨ □ (! ϕ)
     ⇒ = congWeakUntil (λ {i} → imply∃ {x = ↑ (C≤ i σ) μ} λ z → z)
                       ((λ {i} → imply∃ {x = ↑ (C≤ i σ) μ} λ z → proj₁ z tt))
       ∘ proj₁ (F-negation {ϕ₁ = true} {ϕ₂ = ϕ} {σ = σ} {μ = μ})

     ⇐ : μ , σ ⊨ □ (! ϕ) → μ , σ ⊨ ! (♢* ϕ)
     ⇐ = proj₂ (F-negation {ϕ₁ = true} {ϕ₂ = ϕ} {σ = σ} {μ = μ})
       ∘ congWeakUntil ((λ {i} → imply∃ {x = ↑ (C≤ i σ) μ} λ z → z))
                       ((λ {i} → imply∃ {x = ↑ (C≤ i σ) μ} λ z → (λ x → z) , (λ x → z)))
