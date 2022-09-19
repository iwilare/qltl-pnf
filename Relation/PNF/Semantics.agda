{-# OPTIONS --guardedness #-}

module Relation.PNF.Semantics where

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

open import PNF public
open import Relation.Counterpart
open import VecT
open import Predicates

-- Counterpart semantics of extended PNF with all derived operators
infix 10 _,_⊨_

_,_⊨_ : ∀ {A : Set} {n} → CounterpartTrace A → Assignment n A → PNF n → Set
σ , μ ⊨ true = ⊤
σ , μ ⊨ false = ⊥
σ , μ ⊨ x == y = μ [ x ] ≡ μ [ y ]
σ , μ ⊨ x != y = μ [ x ] ≢ μ [ y ]
σ , μ ⊨ (ϕ₁ ∧ ϕ₂) = σ , μ ⊨ ϕ₁ × σ , μ ⊨ ϕ₂
σ , μ ⊨ (ϕ₁ ∨ ϕ₂) = σ , μ ⊨ ϕ₁ ⊎ σ , μ ⊨ ϕ₂
σ , μ ⊨ (∃<> ϕ) = ∃[ x ] σ , (x , μ) ⊨ ϕ
σ , μ ⊨ (∀<> ϕ) = ∀ x → σ , (x , μ) ⊨ ϕ
σ , μ ⊨ (◯ ϕ) = ∃C∈ VecT.zip (C≤ 1 σ) μ ⇒ (s 1 σ ,_⊨ ϕ)
σ , μ ⊨ (A ϕ) = ∀C∈ VecT.zip (C≤ 1 σ) μ ⇒ (s 1 σ ,_⊨ ϕ)
σ , μ ⊨ (ϕ₁ U ϕ₂)  = (λ i → ∃C∈ VecT.zip (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₁)) until     (λ i → ∃C∈ VecT.zip (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₂))
σ , μ ⊨ (ϕ₁ F ϕ₂)  = (λ i → ∀C∈ VecT.zip (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₁)) until     (λ i → ∀C∈ VecT.zip (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₂))
σ , μ ⊨ (ϕ₁ W ϕ₂)  = (λ i → ∃C∈ VecT.zip (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₁)) weakUntil (λ i → ∃C∈ VecT.zip (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₂)) 
σ , μ ⊨ (ϕ₁ T ϕ₂)  = (λ i → ∀C∈ VecT.zip (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₁)) weakUntil (λ i → ∀C∈ VecT.zip (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₂))