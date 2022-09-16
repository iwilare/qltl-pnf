{-# OPTIONS --guardedness #-}

{-
  Syntax and semantics of the positive normal form for extended QLTL.
-}
module PNF where

open import Data.Empty
open import Data.Maybe
open import Data.Nat using (ℕ; suc)
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Relation.Nullary
open import Data.Fin
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Counterpart
open import Predicates
open import Negation

-- Syntax of extended PNF
data PNF : ℕ → Set where
    true  : ∀ {n} → PNF n
    false : ∀ {n} → PNF n
    _∧_   : ∀ {n} → PNF n → PNF n → PNF n
    _∨_   : ∀ {n} → PNF n → PNF n → PNF n
    _==_  : ∀ {n} → Fin n → Fin n → PNF n
    _!=_  : ∀ {n} → Fin n → Fin n → PNF n
    ∃<>_  : ∀ {n} → PNF (suc n) → PNF n
    ∀<>_  : ∀ {n} → PNF (suc n) → PNF n
    ◯_    : ∀ {n} → PNF n → PNF n
    A_    : ∀ {n} → PNF n → PNF n
    _U_   : ∀ {n} → PNF n → PNF n → PNF n
    _W_   : ∀ {n} → PNF n → PNF n → PNF n
    _F_   : ∀ {n} → PNF n → PNF n → PNF n
    _T_   : ∀ {n} → PNF n → PNF n → PNF n

infix 25 _∧_ _∨_
infix 30 _U_ _W_ _F_ _T_
infix 35 ∃<>_ ∀<>_
infix 40 ◯_ A_ ♢_ □_ ♢*_ □*_
infix 50 _==_ _!=_

-- Syntactically defined shorthands
♢_ : ∀ {n} → PNF n → PNF n
♢ ϕ = true U ϕ

□_ : ∀ {n} → PNF n → PNF n
□ ϕ = ϕ W false

♢*_ : ∀ {n} → PNF n → PNF n
♢* ϕ = true F ϕ

□*_ : ∀ {n} → PNF n → PNF n
□* ϕ = ϕ T false

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
