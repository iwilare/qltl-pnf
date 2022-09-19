{-# OPTIONS --guardedness #-}

{-
  Equivalences for the temporal operators in PNF.
-}
module Relation.PNF.Equivalences where

open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.Unit

open import Relation.Counterpart
open import Relation.PNF.Semantics
open import Predicates
open import PNF

infixl 20 _≣_

_≣_ : ∀ {n} → PNF n → PNF n → Set₁
ϕ₁ ≣ ϕ₂ = ∀ {A} {σ : CounterpartTrace A} {μ} → (σ , μ ⊨ ϕ₁ → σ , μ ⊨ ϕ₂) × (σ , μ ⊨ ϕ₂ → σ , μ ⊨ ϕ₁)

T-equivalence : ∀ {n} {ϕ₁ ϕ₂ : PNF n} → ϕ₁ T ϕ₂ ≣ ϕ₁ F ϕ₂ ∨ □* ϕ₁
T-equivalence {_} {ϕ₁} {ϕ₂} {_} {σ} {μ} = ⇒ , ⇐
  where
    ⇒ : σ , μ ⊨ ϕ₁ T ϕ₂ → σ , μ ⊨ ϕ₁ F ϕ₂ ∨ □* ϕ₁
    ⇒ = {!   !}

    ⇐ : σ , μ ⊨ ϕ₁ F ϕ₂ ∨ □* ϕ₁ → σ , μ ⊨ ϕ₁ T ϕ₂
    ⇐ = {!   !}

F-equivalence : ∀ {n} {ϕ₁ ϕ₂ : PNF n} → ϕ₁ F ϕ₂ ≣ ϕ₁ T ϕ₂ ∧ ♢* ϕ₂
F-equivalence {_} {ϕ₁} {ϕ₂} {_} {σ} {μ} = ⇒ , ⇐
  where

    ⇒ : σ , μ ⊨ ϕ₁ F ϕ₂ → σ , μ ⊨ ϕ₁ T ϕ₂ ∧ ♢* ϕ₂
    ⇒ = {!   !}

    ⇐ : σ , μ ⊨ ϕ₁ T ϕ₂ ∧ ♢* ϕ₂ → σ , μ ⊨ ϕ₁ F ϕ₂
    ⇐ = {!   !}