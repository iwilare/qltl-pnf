{-# OPTIONS --guardedness #-}

module Alternative.QLTL where

open import Data.Empty
open import Data.Fin using (Fin)
open import Data.Maybe
open import Data.Nat
open import Data.Nat.Induction
open import Data.Nat.Properties using (≤⇒≤′; <-transˡ; <-trans; <⇒≤; <-cmp; ≤-<-connex)
open import Data.Product
open import Data.Sum
open import Data.Unit hiding (_≤_)
open import Function using (id)
open import Level using (0ℓ; Level)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality using (refl) renaming (_≡_ to _≣_)
open import Relation.Nullary
open import Relation.Nullary.Negation using (¬∃⟶∀¬; contraposition)

open import Counterpart

data QLTL : ℕ → Set where
    true  : ∀ {n} → QLTL n
    false : ∀ {n} → QLTL n
    !_    : ∀ {n} → QLTL n → QLTL n
    _∧_   : ∀ {n} → QLTL n → QLTL n → QLTL n
    _∨_   : ∀ {n} → QLTL n → QLTL n → QLTL n
    ∃<>_  : ∀ {n} → QLTL (suc n) → QLTL n
    ∀<>_  : ∀ {n} → QLTL (suc n) → QLTL n
    A_   : ∀ {n} → QLTL n → QLTL n
    ◯_   : ∀ {n} → QLTL n → QLTL n
    _F_  : ∀ {n} → QLTL n → QLTL n → QLTL n
    _U_  : ∀ {n} → QLTL n → QLTL n → QLTL n
    _T_  : ∀ {n} → QLTL n → QLTL n → QLTL n
    _W_  : ∀ {n} → QLTL n → QLTL n → QLTL n

♢* : ∀ {n} → QLTL n → QLTL n
♢* ϕ = true F ϕ
♢ : ∀ {n} → QLTL n → QLTL n
♢ ϕ = true U ϕ
□* : ∀ {n} → QLTL n → QLTL n
□* ϕ = ϕ T false
□ : ∀ {n} → QLTL n → QLTL n
□ ϕ = ϕ W false

infix 30 !_
infix 10 _,_⊨_

interleaved mutual
  _,_⊨_ : ∀ {A : Set} {n} → Elements n A → CounterpartTrace A → QLTL n → Set
  at∀ : ∀ {A : Set} {n} → Elements n A → CounterpartTrace A → QLTL n → ℕ → Set
  at∃ : ∀ {A : Set} {n} → Elements n A → CounterpartTrace A → QLTL n → ℕ → Set

  at∀ μ σ ϕ i = ∀C∈ ↑ (C≤ i σ) μ ⇒ (_, s i σ ⊨ ϕ)
  at∃ μ σ ϕ i = ∃C∈ ↑ (C≤ i σ) μ ⇒ (_, s i σ ⊨ ϕ)

  μ , σ ⊨ true = ⊤
  μ , σ ⊨ false = ⊥
  μ , σ ⊨ ! ϕ = ¬ μ , σ ⊨ ϕ
  μ , σ ⊨ (ϕ₁ ∧ ϕ₂) = μ , σ ⊨ ϕ₁ × μ , σ ⊨ ϕ₂
  μ , σ ⊨ (ϕ₁ ∨ ϕ₂) = μ , σ ⊨ ϕ₁ ⊎ μ , σ ⊨ ϕ₂
  μ , σ ⊨ (∃<> ϕ) = ∃[ x ] (x , μ) , σ ⊨ ϕ
  μ , σ ⊨ (∀<> ϕ) = ∀ x → (x , μ) , σ ⊨ ϕ
  μ , σ ⊨ (A ϕ) = at∀ μ σ ϕ 1
  μ , σ ⊨ (◯ ϕ) = at∃ μ σ ϕ 1
  μ , σ ⊨ (ϕ₁ U ϕ₂) = ∃[ n ] ((∀ i → i < n → at∃ μ σ ϕ₁ i) × at∃ μ σ ϕ₂ n)
  μ , σ ⊨ (ϕ₁ F ϕ₂) = ∃[ n ] ((∀ i → i < n → at∃ μ σ ϕ₁ i) × at∀ μ σ ϕ₂ n)
  μ , σ ⊨ (ϕ₁ T ϕ₂) =(∃[ n ] ((∀ i → i < n → at∃ μ σ ϕ₁ i) × at∀ μ σ ϕ₂ n)) ⊎ (∀ i → at∀ μ σ ϕ₁ i)
  μ , σ ⊨ (ϕ₁ W ϕ₂) =(∃[ n ] ((∀ i → i < n → at∃ μ σ ϕ₁ i) × at∃ μ σ ϕ₂ n)) ⊎ (∀ i → at∃ μ σ ϕ₁ i)

_≡_ : ∀ {n} → QLTL n → QLTL n → Set₁
ϕ₁ ≡ ϕ₂ = ∀ {A} {σ : CounterpartTrace A} {μ} → (μ , σ ⊨ ϕ₁ → μ , σ ⊨ ϕ₂) × (μ , σ ⊨ ϕ₂ → μ , σ ⊨ ϕ₁)
