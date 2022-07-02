{-# OPTIONS --guardedness #-}

module Full where

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

data Full : ℕ → Set where
    true  : ∀ {n} → Full n
    false : ∀ {n} → Full n
    !_    : ∀ {n} → Full n → Full n
    _∧_   : ∀ {n} → Full n → Full n → Full n
    _∨_   : ∀ {n} → Full n → Full n → Full n
    ∃<>_  : ∀ {n} → Full (suc n) → Full n
    ∀<>_  : ∀ {n} → Full (suc n) → Full n
    ◯_   : ∀ {n} → Full n → Full n
    A_   : ∀ {n} → Full n → Full n
    _U_  : ∀ {n} → Full n → Full n → Full n
    _W_  : ∀ {n} → Full n → Full n → Full n
    _F_  : ∀ {n} → Full n → Full n → Full n
    _T_  : ∀ {n} → Full n → Full n → Full n

♢ : ∀ {n} → Full n → Full n
♢ ϕ = true U ϕ
□ : ∀ {n} → Full n → Full n
□ ϕ = ϕ W false
♢* : ∀ {n} → Full n → Full n
♢* ϕ = true F ϕ
□* : ∀ {n} → Full n → Full n
□* ϕ = ϕ T false

infix 10 _,_⊨_
infix 30 !_

interleaved mutual
  _,_⊨_ : ∀ {A : Set} {n} → Elements n A → CounterpartTrace A → Full n → Set
  at∃ : ∀ {A : Set} {n} → Elements n A → CounterpartTrace A → Full n → ℕ → Set
  at∀ : ∀ {A : Set} {n} → Elements n A → CounterpartTrace A → Full n → ℕ → Set

  at∃ μ σ ϕ i = ∃C∈ ↑ (C≤ i σ) μ ⇒ (_, s i σ ⊨ ϕ)
  at∀ μ σ ϕ i = ∀C∈ ↑ (C≤ i σ) μ ⇒ (_, s i σ ⊨ ϕ)

  μ , σ ⊨ true = ⊤
  μ , σ ⊨ false = ⊥
  μ , σ ⊨ ! ϕ = ¬ μ , σ ⊨ ϕ
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

_≡_ : ∀ {n} → Full n → Full n → Set₁
ϕ₁ ≡ ϕ₂ = ∀ {A} {σ : CounterpartTrace A} {μ} → (μ , σ ⊨ ϕ₁ → μ , σ ⊨ ϕ₂) × (μ , σ ⊨ ϕ₂ → μ , σ ⊨ ϕ₁)
