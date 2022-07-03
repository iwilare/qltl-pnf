{-# OPTIONS --guardedness #-}

{-
  Syntax and semantics of extended QLTL.
-}
module QLTL where

open import Data.Empty
open import Data.Maybe
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit
open import Data.Fin
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Counterpart
open import Predicates
open import Negation

-- Syntax of extended QLTL
data QLTL : ℕ → Set where
    true  : ∀ {n} → QLTL n
    _==_  : ∀ {n} → Fin n → Fin n → QLTL n
    !_    : ∀ {n} → QLTL n → QLTL n
    _∨_   : ∀ {n} → QLTL n → QLTL n → QLTL n
    ∃<>_  : ∀ {n} → QLTL (suc n) → QLTL n
    ◯_   : ∀ {n} → QLTL n → QLTL n
    _U_  : ∀ {n} → QLTL n → QLTL n → QLTL n
    _W_  : ∀ {n} → QLTL n → QLTL n → QLTL n

infix 25 _∧_ _∨_
infix 30 _U_ _W_
infix 35 ∃<>_
infix 40 ◯_ ♢_ □_
infix 45 !_
infix 50 _==_

-- Syntactically defined shorthands
false : ∀ {n} → QLTL n
false = ! true

♢_ : ∀ {n} → QLTL n → QLTL n
♢ ϕ = true U ϕ

□_ : ∀ {n} → QLTL n → QLTL n
□ ϕ = ϕ W ! true

_∧_ : ∀ {n} → QLTL n → QLTL n → QLTL n
ϕ₁ ∧ ϕ₂ = ! (! ϕ₁ ∨ ! ϕ₂)

-- Counterpart semantics of extended QLTL
infix 10 _,_⊨_

interleaved mutual
  _,_⊨_ : ∀ {A : Set} {n} → CounterpartTrace A → Assignment n A → QLTL n → Set
  at∃ : ∀ {A : Set} {n} → CounterpartTrace A → Assignment n A → QLTL n → ℕ → Set

  -- Shorthand expressing: "There exists a counterpart for μ in σ after i steps that satisfies ϕ"
  at∃ σ μ ϕ i = ∃C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ)

  -- Satisfiability relation
  σ , μ ⊨ true = ⊤
  σ , μ ⊨ ! ϕ = σ , μ ⊨ ϕ → ⊥
  σ , μ ⊨ x == y = μ [ x ] ≡ μ [ y ]
  σ , μ ⊨ (ϕ₁ ∨ ϕ₂) = σ , μ ⊨ ϕ₁ ⊎ σ , μ ⊨ ϕ₂
  σ , μ ⊨ (∃<> ϕ) = ∃[ x ] σ , (x , μ) ⊨ ϕ
  σ , μ ⊨ (◯ ϕ) = at∃ σ μ ϕ 1
  σ , μ ⊨ (ϕ₁ U ϕ₂) = at∃ σ μ ϕ₁ until     at∃ σ μ ϕ₂
  σ , μ ⊨ (ϕ₁ W ϕ₂) = at∃ σ μ ϕ₁ weakUntil at∃ σ μ ϕ₂

-- Extended QLTL equivalence
_≣_ : ∀ {n} → QLTL n → QLTL n → Set₁
ϕ₁ ≣ ϕ₂ = ∀ {A} {σ : CounterpartTrace A} {μ} → (σ , μ ⊨ ϕ₁ → σ , μ ⊨ ϕ₂) × (σ , μ ⊨ ϕ₂ → σ , μ ⊨ ϕ₁)
