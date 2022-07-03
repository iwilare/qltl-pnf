{-# OPTIONS --guardedness #-}

{-
  Syntax and semantics for QLTL with negation and all derived operators, using
  the alternative definitions for the then and until-forall operators.
  The proof of their equivalence is shown in Alternative.Negation.
-}
module Alternative.QLTL where

open import Data.Empty
open import Data.Maybe
open import Data.Nat using (ℕ; suc; _<_)
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Relation.Nullary
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Counterpart
open import Predicates
open import Negation

-- Syntax of full QLTL
data QLTL-alt : ℕ → Set where
    true  : ∀ {n} → QLTL-alt n
    false : ∀ {n} → QLTL-alt n
    !_    : ∀ {n} → QLTL-alt n → QLTL-alt n
    _∧_   : ∀ {n} → QLTL-alt n → QLTL-alt n → QLTL-alt n
    _∨_   : ∀ {n} → QLTL-alt n → QLTL-alt n → QLTL-alt n
    _==_  : ∀ {n} → Fin n  → Fin n  → QLTL-alt n
    _!=_  : ∀ {n} → Fin n  → Fin n  → QLTL-alt n
    ∃<>_  : ∀ {n} → QLTL-alt (suc n) → QLTL-alt n
    ∀<>_  : ∀ {n} → QLTL-alt (suc n) → QLTL-alt n
    ◯_   : ∀ {n} → QLTL-alt n → QLTL-alt n
    A_   : ∀ {n} → QLTL-alt n → QLTL-alt n
    _U_  : ∀ {n} → QLTL-alt n → QLTL-alt n → QLTL-alt n
    _W_  : ∀ {n} → QLTL-alt n → QLTL-alt n → QLTL-alt n
    _F_  : ∀ {n} → QLTL-alt n → QLTL-alt n → QLTL-alt n
    _T_  : ∀ {n} → QLTL-alt n → QLTL-alt n → QLTL-alt n
    _F′_  : ∀ {n} → QLTL-alt n → QLTL-alt n → QLTL-alt n
    _T′_  : ∀ {n} → QLTL-alt n → QLTL-alt n → QLTL-alt n

infix 25 _∧_ _∨_
infix 30 _U_ _W_ _F_ _T_ _F′_ _T′_
infix 35 ∃<>_ ∀<>_
infix 40 ◯_ A_ ♢_ □_ ♢*_ □*_ ♢′*_ □′*_
infix 45 !_
infix 50 _==_ _!=_

-- Syntactically defined shorthands
♢_ : ∀ {n} → QLTL-alt n → QLTL-alt n
♢ ϕ = true U ϕ

□_ : ∀ {n} → QLTL-alt n → QLTL-alt n
□ ϕ = ϕ W false

♢*_ : ∀ {n} → QLTL-alt n → QLTL-alt n
♢* ϕ = true F ϕ

□*_ : ∀ {n} → QLTL-alt n → QLTL-alt n
□* ϕ = ϕ T false

♢′*_ : ∀ {n} → QLTL-alt n → QLTL-alt n
♢′* ϕ = true F′ ϕ

□′*_ : ∀ {n} → QLTL-alt n → QLTL-alt n
□′* ϕ = ϕ T′ false

-- Counterpart semantics of extended QLTL with all derived operators
infix 10 _,_⊨_

interleaved mutual
  _,_⊨_ : ∀ {A : Set} {n} → CounterpartTrace A → Assignment n A → QLTL-alt n → Set
  at∃ : ∀ {A : Set} {n} → CounterpartTrace A → Assignment n A → QLTL-alt n → ℕ → Set
  at∀ : ∀ {A : Set} {n} → CounterpartTrace A → Assignment n A → QLTL-alt n → ℕ → Set

  -- Shorthand expressing: "A counterpart for μ in σ after i steps is defined and satisfies ϕ"
  at∃ σ μ ϕ i = ∃C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ)
  -- Shorthand expressing: "If a counterpart for μ in σ after i steps is defined then it satisfies ϕ"
  at∀ σ μ ϕ i = ∀C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ)

  σ , μ ⊨ true = ⊤
  σ , μ ⊨ false = ⊥
  σ , μ ⊨ ! ϕ = ¬ σ , μ ⊨ ϕ
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
  -- Alternative definitions, using existential quantification in the intermediate and always part.
  σ , μ ⊨ (ϕ₁ F′ ϕ₂) = at∃ σ μ ϕ₁ until     at∀ σ μ ϕ₂
  σ , μ ⊨ (ϕ₁ T′ ϕ₂) = at∃ σ μ ϕ₁ weakUntil at∀ σ μ ϕ₂

_≣_ : ∀ {n} → QLTL-alt n → QLTL-alt n → Set₁
ϕ₁ ≣ ϕ₂ = ∀ {A} {σ : CounterpartTrace A} {μ} → (σ , μ ⊨ ϕ₁ → σ , μ ⊨ ϕ₂) × (σ , μ ⊨ ϕ₂ → σ , μ ⊨ ϕ₁)
