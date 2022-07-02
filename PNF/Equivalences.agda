{-# OPTIONS --guardedness #-}

module PNF.Equivalences where

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
open import PNF

F-equivalence : ∀ {n} {ϕ₁ ϕ₂ : PNF n} → (ϕ₁ F ϕ₂) ≡ ((ϕ₁ T ϕ₂) ∧ ♢* ϕ₂)
F-equivalence {_} {ϕ₁} {ϕ₂} {_} {σ} {μ} = ⇒ , ⇐
  where

    ⇒ : μ , σ ⊨ (ϕ₁ F ϕ₂) → μ , σ ⊨ (ϕ₁ T ϕ₂) ∧ ♢* ϕ₂
    ⇒ (n , ϕ₁<i , ϕ₂n) = inj₁ (n , ϕ₁<i , ϕ₂n) , n , true-before-n , ϕ₂n
      where
        true-before-n : at∀ μ σ true before n
        true-before-n i x with ↑ (C≤ i σ) μ
        ... | nothing = tt
        ... | just μ = tt

    ⇐ : μ , σ ⊨ (ϕ₁ T ϕ₂) ∧ ♢* ϕ₂ → μ , σ ⊨ ϕ₁ F ϕ₂
    ⇐ (inj₁ u , _) = u
    ⇐ (inj₂ a , n , _ , ϕ₂n) = n , (λ i _ → a i) , ϕ₂n

T-equivalence : ∀ {n} {ϕ₁ ϕ₂ : PNF n} → (ϕ₁ T ϕ₂) ≡ ((ϕ₁ F ϕ₂) ∨ □* ϕ₁)
T-equivalence {_} {ϕ₁} {ϕ₂} {_} {σ} {μ} = ⇒ , ⇐
  where
    ⇒ : μ , σ ⊨ (ϕ₁ T ϕ₂) → μ , σ ⊨ (ϕ₁ F ϕ₂) ∨ □* ϕ₁
    ⇒ (inj₁ x) = inj₁ x
    ⇒ (inj₂ y) = inj₂ (inj₂ y)

    ⇐ : μ , σ ⊨ (ϕ₁ F ϕ₂) ∨ □* ϕ₁ → μ , σ ⊨ ϕ₁ T ϕ₂
    ⇐ (inj₁ x) = inj₁ x
    ⇐ (inj₂ (inj₁ (n , ϕ₁<i , ϕ₂n))) with ↑ (C≤ n σ) μ | inspect (↑ (C≤ n σ)) μ
    ... | nothing | ≣: eq = inj₁ (n , ϕ₁<i , ∀ϕ₂)
       where ∀ϕ₂ : ∀C∈ ↑ (C≤ n σ) μ ⇒ (_, s n σ ⊨ ϕ₂)
             ∀ϕ₂ rewrite eq = tt
    ⇐ (inj₂ (inj₂ y)) = inj₂ y
