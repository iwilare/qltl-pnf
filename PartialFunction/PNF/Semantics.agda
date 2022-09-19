{-# OPTIONS --guardedness #-}

module PartialFunction.PNF.Semantics where

open import Data.Empty
open import Data.Maybe
open import Data.Nat using (ℕ; suc)
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Relation.Nullary
open import Data.Fin
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Relation.Counterpart
open import Predicates
open import Negation
open import PNF

-- Counterpart semantics of extended PNF
infix 10 _,_⊨_

interleaved mutual
  _,_⊨_ : ∀ {A : Set} {n} → CounterpartTrace A → Assignment n A → PNF n → Set
  at∃ : ∀ {A : Set} {n} → CounterpartTrace A → Assignment n A → PNF n → ℕ → Set
  at∀ : ∀ {A : Set} {n} → CounterpartTrace A → Assignment n A → PNF n → ℕ → Set

  -- Shorthand expressing: "There exists a counterpart for μ in σ after i steps that satisfies ϕ"
  at∃ σ μ ϕ i = ∃C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ)

  -- Shorthand expressing: "All counterparts for μ in σ after i steps satisfy ϕ"
  at∀ σ μ ϕ i = ∀C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ)

  σ , μ ⊨ true = ⊤
  σ , μ ⊨ false = ⊥
  σ , μ ⊨ x == y = μ [ x ] ≡ μ [ y ]
  σ , μ ⊨ x != y = μ [ x ] ≢ μ [ y ]
  σ , μ ⊨ (ϕ₁ ∧ ϕ₂) = σ , μ ⊨ ϕ₁ × σ , μ ⊨ ϕ₂
  σ , μ ⊨ (ϕ₁ ∨ ϕ₂) = σ , μ ⊨ ϕ₁ ⊎ σ , μ ⊨ ϕ₂
  σ , μ ⊨ (∃<> ϕ) = ∃[ x ] σ , (x , μ) ⊨ ϕ
  σ , μ ⊨ (∀<> ϕ) = ∀ x → σ , (x , μ) ⊨ ϕ
  σ , μ ⊨ (◯ ϕ) = at∃ σ μ ϕ 1
  σ , μ ⊨ (A ϕ) = at∀ σ μ ϕ 1
  σ , μ ⊨ (ϕ₁ U ϕ₂) = at∃ σ μ ϕ₁ until     at∃ σ μ ϕ₂
  σ , μ ⊨ (ϕ₁ W ϕ₂) = at∃ σ μ ϕ₁ weakUntil at∃ σ μ ϕ₂
  σ , μ ⊨ (ϕ₁ F ϕ₂) = at∀ σ μ ϕ₁ until     at∀ σ μ ϕ₂
  σ , μ ⊨ (ϕ₁ T ϕ₂) = at∀ σ μ ϕ₁ weakUntil at∀ σ μ ϕ₂

_≣_ : ∀ {n} → PNF n → PNF n → Set₁
ϕ₁ ≣ ϕ₂ = ∀ {A} {σ : CounterpartTrace A} {μ} → (σ , μ ⊨ ϕ₁ → σ , μ ⊨ ϕ₂) × (σ , μ ⊨ ϕ₂ → σ , μ ⊨ ϕ₁)
