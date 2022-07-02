{-# OPTIONS --guardedness #-}

module QLTL.Equivalences where

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

open import Predicates
open import Counterpart
open import Full

U-equivalence : ∀ {n} {ϕ₁ ϕ₂ : Full n} → (ϕ₁ U ϕ₂) ≡ ((ϕ₁ W ϕ₂) ∧ ♢ ϕ₂)
U-equivalence {_} {ϕ₁} {ϕ₂} {_} {σ} {μ} = ⇒ , ⇐
  where

    ⇒ : μ , σ ⊨ (ϕ₁ U ϕ₂) → μ , σ ⊨ (ϕ₁ W ϕ₂) ∧ ♢ ϕ₂
    ⇒ (n , ϕ₁<i , ϕ₂n) = inj₁ (n , ϕ₁<i , ϕ₂n) , n , true-before-n , ϕ₂n
      where
        true-before-n : at∃ μ σ true before n
        true-before-n i x with ↑ (C≤ i σ) μ | ϕ₁<i i x
        ... | just μ | _ = tt

    ⇐ : μ , σ ⊨ (ϕ₁ W ϕ₂) ∧ ♢ ϕ₂ → μ , σ ⊨ (ϕ₁ U ϕ₂)
    ⇐ (inj₁ u , _) = u
    ⇐ (inj₂ a , n , _ , ϕ₂n) = n , (λ i _ → a i) , ϕ₂n

W-equivalence : ∀ {n} {ϕ₁ ϕ₂ : Full n} → (ϕ₁ W ϕ₂) ≡ ((ϕ₁ U ϕ₂) ∨ □ ϕ₁)
W-equivalence {_} {ϕ₁} {ϕ₂} {_} {σ} {μ} = ⇒ , ⇐
  where
    ⇒ : μ , σ ⊨ (ϕ₁ W ϕ₂) → μ , σ ⊨ (ϕ₁ U ϕ₂) ∨ □ ϕ₁
    ⇒ (inj₁ x) = inj₁ x
    ⇒ (inj₂ y) = inj₂ (inj₂ y)

    ⇐ : μ , σ ⊨ (ϕ₁ U ϕ₂) ∨ □ ϕ₁ → μ , σ ⊨ ϕ₁ W ϕ₂
    ⇐ (inj₁ x) = inj₁ x
    ⇐ (inj₂ (inj₁ (n , ϕ₁<i , ϕ₂n))) with ↑ (C≤ n σ) μ
    ⇐ (inj₂ (inj₁ (n , ϕ₁<i , ()))) | just x
    ⇐ (inj₂ (inj₁ (n , ϕ₁<i , ()))) | nothing
    ⇐ (inj₂ (inj₂ y)) = inj₂ y
