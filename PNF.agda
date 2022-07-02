{-# OPTIONS --guardedness #-}

module PNF where

open import Axiom.DoubleNegationElimination
open import Axiom.ExcludedMiddle
open import Axiom.Extensionality.Propositional
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

data PNF : ℕ → Set where
    true  : ∀ {n} → PNF n
    false : ∀ {n} → PNF n
    _∧_   : ∀ {n} → PNF n → PNF n → PNF n
    _∨_   : ∀ {n} → PNF n → PNF n → PNF n
    ∃<>_  : ∀ {n} → PNF (suc n) → PNF n
    ∀<>_  : ∀ {n} → PNF (suc n) → PNF n
    ◯_   : ∀ {n} → PNF n → PNF n
    A_   : ∀ {n} → PNF n → PNF n
    _U_  : ∀ {n} → PNF n → PNF n → PNF n
    _W_  : ∀ {n} → PNF n → PNF n → PNF n
    _F_  : ∀ {n} → PNF n → PNF n → PNF n
    _T_  : ∀ {n} → PNF n → PNF n → PNF n

♢ : ∀ {n} → PNF n → PNF n
♢ ϕ = true U ϕ
□ : ∀ {n} → PNF n → PNF n
□ ϕ = ϕ W false
♢* : ∀ {n} → PNF n → PNF n
♢* ϕ = true F ϕ
□* : ∀ {n} → PNF n → PNF n
□* ϕ = ϕ T false

infix 10 _,_⊨_

interleaved mutual
  _,_⊨_ : ∀ {A : Set} {n} → Elements n A → CounterpartTrace A → PNF n → Set
  at∃ : ∀ {A : Set} {n} → Elements n A → CounterpartTrace A → PNF n → ℕ → Set
  at∀ : ∀ {A : Set} {n} → Elements n A → CounterpartTrace A → PNF n → ℕ → Set

  at∃ μ σ ϕ i = ∃C∈ ↑ (C≤ i σ) μ ⇒ (_, s i σ ⊨ ϕ)
  at∀ μ σ ϕ i = ∀C∈ ↑ (C≤ i σ) μ ⇒ (_, s i σ ⊨ ϕ)

  μ , σ ⊨ true = ⊤
  μ , σ ⊨ false = ⊥
  μ , σ ⊨ (ϕ₁ ∧ ϕ₂) = μ , σ ⊨ ϕ₁ × μ , σ ⊨ ϕ₂
  μ , σ ⊨ (ϕ₁ ∨ ϕ₂) = μ , σ ⊨ ϕ₁ ⊎ μ , σ ⊨ ϕ₂
  μ , σ ⊨ (∃<> ϕ) = ∃[ x ] (x , μ) , σ ⊨ ϕ
  μ , σ ⊨ (∀<> ϕ) = ∀ x → (x , μ) , σ ⊨ ϕ
  μ , σ ⊨ (◯ ϕ) = at∃ μ σ ϕ 1
  μ , σ ⊨ (A ϕ) = at∀ μ σ ϕ 1
  μ , σ ⊨ (ϕ₁ U ϕ₂) = at∃ μ σ ϕ₁ until     at∃ μ σ ϕ₂
  μ , σ ⊨ (ϕ₁ W ϕ₂) = at∃ μ σ ϕ₁ weakUntil at∃ μ σ ϕ₂
  μ , σ ⊨ (ϕ₁ F ϕ₂) = at∀ μ σ ϕ₁ until     at∀ μ σ ϕ₂
  μ , σ ⊨ (ϕ₁ T ϕ₂) = at∀ μ σ ϕ₁ weakUntil at∀ μ σ ϕ₂

_≡_ : ∀ {n} → PNF n → PNF n → Set₁
ϕ₁ ≡ ϕ₂ = ∀ {A} {σ : CounterpartTrace A} {μ} → (μ , σ ⊨ ϕ₁ → μ , σ ⊨ ϕ₂) × (μ , σ ⊨ ϕ₂ → μ , σ ⊨ ϕ₁)
