{-# OPTIONS --guardedness #-}

{-
  Syntax and semantics for QLTL with negation and all derived operators.
-}
module QLTL where

open import Data.Empty
open import Data.Maybe
open import Data.Nat using (ℕ; suc)
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Relation.Nullary
open import Data.Fin
open import Relation.Unary hiding (U)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Counterpart
open import Predicates
open import Negation

-- Syntax of full QLTL
data QLTL : ℕ → Set where
    true  : ∀ {n} → QLTL n
    false : ∀ {n} → QLTL n
    !_    : ∀ {n} → QLTL n → QLTL n
    _∧_   : ∀ {n} → QLTL n → QLTL n → QLTL n
    _∨_   : ∀ {n} → QLTL n → QLTL n → QLTL n
    _==_  : ∀ {n} → Fin n  → Fin n  → QLTL n
    _!=_  : ∀ {n} → Fin n  → Fin n  → QLTL n
    ∃<>_  : ∀ {n} → QLTL (suc n) → QLTL n
    ∀<>_  : ∀ {n} → QLTL (suc n) → QLTL n
    ◯_   : ∀ {n} → QLTL n → QLTL n
    A_   : ∀ {n} → QLTL n → QLTL n
    _U_  : ∀ {n} → QLTL n → QLTL n → QLTL n
    _F_  : ∀ {n} → QLTL n → QLTL n → QLTL n
    _W_  : ∀ {n} → QLTL n → QLTL n → QLTL n
    _T_  : ∀ {n} → QLTL n → QLTL n → QLTL n
    _UD_  : ∀ {n} → QLTL n → QLTL n → QLTL n
    _FD_  : ∀ {n} → QLTL n → QLTL n → QLTL n
    _WD_  : ∀ {n} → QLTL n → QLTL n → QLTL n
    _TD_  : ∀ {n} → QLTL n → QLTL n → QLTL n

infix 25 _∧_ _∨_
infix 30 _U_ _F_ _W_ _T_ _UD_ _FD_ _WD_ _TD_
infix 35 ∃<>_ ∀<>_
infix 40 ◯_ A_ ♢_ □_ ♢*_ □*_
infix 45 !_
infix 50 _==_ _!=_

-- Syntactically defined shorthands
♢_ : ∀ {n} → QLTL n → QLTL n
♢ ϕ = true U ϕ

□_ : ∀ {n} → QLTL n → QLTL n
□ ϕ = ϕ T false

♢*_ : ∀ {n} → QLTL n → QLTL n
♢* ϕ = true F ϕ

□*_ : ∀ {n} → QLTL n → QLTL n
□* ϕ = ϕ T false

-- Counterpart semantics of extended QLTL with all derived operators
infix 10 _,_⊨_

_,_⊨_ : ∀ {A : Set} {n} → CounterpartTrace A → Assignment n A → QLTL n → Set
σ , μ ⊨ true = ⊤
σ , μ ⊨ false = ⊥
σ , μ ⊨ ! ϕ = ¬ σ , μ ⊨ ϕ
σ , μ ⊨ x == y = μ [ x ] ≡ μ [ y ]
σ , μ ⊨ x != y = μ [ x ] ≢ μ [ y ]
σ , μ ⊨ (ϕ₁ ∧ ϕ₂) = σ , μ ⊨ ϕ₁ × σ , μ ⊨ ϕ₂
σ , μ ⊨ (ϕ₁ ∨ ϕ₂) = σ , μ ⊨ ϕ₁ ⊎ σ , μ ⊨ ϕ₂
σ , μ ⊨ (∃<> ϕ) = ∃[ x ] σ , (x , μ) ⊨ ϕ
σ , μ ⊨ (∀<> ϕ) = ∀ x → σ , (x , μ) ⊨ ϕ
σ , μ ⊨ (◯ ϕ) = ∃C∈ ↑ (C≤ 1 σ) μ ⇒ (s 1 σ ,_⊨ ϕ)
σ , μ ⊨ (A ϕ) = ∀C∈ ↑ (C≤ 1 σ) μ ⇒ (s 1 σ ,_⊨ ϕ)
σ , μ ⊨ (ϕ₁ U ϕ₂)  = (λ i → ∃C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₁)) until     (λ i → ∃C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₂))
σ , μ ⊨ (ϕ₁ F ϕ₂)  = (λ i → ∀C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₁)) until     (λ i → ∀C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₂))
σ , μ ⊨ (ϕ₁ UD ϕ₂) = (λ i → ∃C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₁)) until     (λ i → ∃C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₁) × ∃C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₂))
σ , μ ⊨ (ϕ₁ FD ϕ₂) = (λ i → ∀C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₁)) until     (λ i → ∀C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₁) ⊎ ∀C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₂))
σ , μ ⊨ (ϕ₁ W ϕ₂)  = (λ i → ∃C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₁)) weakUntil (λ i → ∃C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₂)) 
σ , μ ⊨ (ϕ₁ T ϕ₂)  = (λ i → ∀C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₁)) weakUntil (λ i → ∀C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₂))
σ , μ ⊨ (ϕ₁ WD ϕ₂) = (λ i → ∃C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₁)) weakUntil (λ i → ∃C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₁) × ∃C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₂))
σ , μ ⊨ (ϕ₁ TD ϕ₂) = (λ i → ∀C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₁)) weakUntil (λ i → ∀C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₁) ⊎ ∀C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₂))

_≣_ : ∀ {n} → QLTL n → QLTL n → Set₁
ϕ₁ ≣ ϕ₂ = ∀ {A} {σ : CounterpartTrace A} {μ} → (σ , μ ⊨ ϕ₁ → σ , μ ⊨ ϕ₂) × (σ , μ ⊨ ϕ₂ → σ , μ ⊨ ϕ₁)