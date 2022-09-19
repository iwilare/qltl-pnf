{-# OPTIONS --guardedness #-}

{-
  Equivalences for the temporal operators in QLTL.
-}
module Relation.QLTL.Equivalences where

open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.Unit

open import Relation.Counterpart
open import Relation.QLTL.Semantics
open import Predicates
open import QLTL

infixl 20 _≣_

_≣_ : ∀ {n} → QLTL n → QLTL n → Set₁
ϕ₁ ≣ ϕ₂ = ∀ {A} {σ : CounterpartTrace A} {μ} → (σ , μ ⊨ ϕ₁ → σ , μ ⊨ ϕ₂) × (σ , μ ⊨ ϕ₂ → σ , μ ⊨ ϕ₁)

{-
U-equivalence : ∀ {n} {ϕ₁ ϕ₂ : QLTL n} → (ϕ₁ U ϕ₂) ≣ (ϕ₁ W ϕ₂) ∧ (♢ ϕ₂)
U-equivalence {_} {ϕ₁} {ϕ₂} {_} {σ} {μ} = ⇒ , ⇐
  where

    ⇒ : σ , μ ⊨ ϕ₁ U ϕ₂ → σ , μ ⊨ ϕ₁ W ϕ₂ ∧ ♢ ϕ₂
    ⇒ (n , ϕ₁<i , ϕ₂n) = ?

    ⇐ : σ , μ ⊨ ϕ₁ W ϕ₂ ∧ ♢ ϕ₂ → σ , μ ⊨ ϕ₁ U ϕ₂
    ⇐ = ?
-}

W-equivalence : ∀ {n} {ϕ₁ ϕ₂ : QLTL n} → ϕ₁ W ϕ₂ ≣ ϕ₁ U ϕ₂ ∨ □ ϕ₁
W-equivalence {_} {ϕ₁} {ϕ₂} {_} {σ} {μ} = ⇒ , ⇐
  where
    ⇒ : σ , μ ⊨ ϕ₁ W ϕ₂ → σ , μ ⊨ ϕ₁ U ϕ₂ ∨ □ ϕ₁
    ⇒ = {!   !}

    ⇐ : σ , μ ⊨ ϕ₁ U ϕ₂ ∨ □ ϕ₁ → σ , μ ⊨ ϕ₁ W ϕ₂
    ⇐ = {!   !}