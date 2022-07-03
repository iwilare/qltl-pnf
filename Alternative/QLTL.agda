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
  _,_⊨_ : ∀ {A : Set} {n} → CounterpartTrace A → Assignment n A → QLTL n → Set
  at∀ : ∀ {A : Set} {n} → CounterpartTrace A → Assignment n A → QLTL n → ℕ → Set
  at∃ : ∀ {A : Set} {n} → CounterpartTrace A → Assignment n A → QLTL n → ℕ → Set

  at∀ σ μ ϕ i = ∀C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ)
  at∃ σ μ ϕ i = ∃C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ)

  σ , μ ⊨ true = ⊤
  σ , μ ⊨ false = ⊥
  σ , μ ⊨ ! ϕ = ¬ σ , μ ⊨ ϕ
  σ , μ ⊨ (ϕ₁ ∧ ϕ₂) = σ , μ ⊨ ϕ₁ × σ , μ ⊨ ϕ₂
  σ , μ ⊨ (ϕ₁ ∨ ϕ₂) = σ , μ ⊨ ϕ₁ ⊎ σ , μ ⊨ ϕ₂
  σ , μ ⊨ (∃<> ϕ) = ∃[ x ] σ , (x , μ) ⊨ ϕ
  σ , μ ⊨ (∀<> ϕ) = ∀ x → σ , (x , μ) ⊨ ϕ
  σ , μ ⊨ (A ϕ) = at∀ σ μ ϕ 1
  σ , μ ⊨ (◯ ϕ) = at∃ σ μ ϕ 1
  σ , μ ⊨ (ϕ₁ U ϕ₂) = ∃[ n ] ((∀ i → i < n → at∃ σ μ ϕ₁ i) × at∃ σ μ ϕ₂ n)
  σ , μ ⊨ (ϕ₁ F ϕ₂) = ∃[ n ] ((∀ i → i < n → at∃ σ μ ϕ₁ i) × at∀ σ μ ϕ₂ n)
  σ , μ ⊨ (ϕ₁ T ϕ₂) =(∃[ n ] ((∀ i → i < n → at∃ σ μ ϕ₁ i) × at∀ σ μ ϕ₂ n)) ⊎ (∀ i → at∀ σ μ ϕ₁ i)
  σ , μ ⊨ (ϕ₁ W ϕ₂) =(∃[ n ] ((∀ i → i < n → at∃ σ μ ϕ₁ i) × at∃ σ μ ϕ₂ n)) ⊎ (∀ i → at∃ σ μ ϕ₁ i)

_≡_ : ∀ {n} → QLTL n → QLTL n → Set₁
ϕ₁ ≡ ϕ₂ = ∀ {A} {σ : CounterpartTrace A} {μ} → (σ , μ ⊨ ϕ₁ → σ , μ ⊨ ϕ₂) × (σ , μ ⊨ ϕ₂ → σ , μ ⊨ ϕ₁)
