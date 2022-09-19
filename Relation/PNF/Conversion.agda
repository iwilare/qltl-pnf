{-# OPTIONS --guardedness #-}

{-
  Equi-expressiveness between extended QLTL and its extended positive normal form PNF.
  The translation function is defined as ^ and split into two definitions ^ and ^¬
  to show to Agda that the procedure terminates in a finite number of steps.
-}
module Relation.PNF.Conversion where

open import Data.Product
open import Data.Sum
open import Data.Unit
open import Function using (_∘_)
open import Relation.Nullary.Negation using (¬∃⟶∀¬)

open import Predicates
open import Relation.Counterpart
open import Negation
open import Relation.QLTL.Semantics renaming (_,_⊨_ to _,_⊨QLTL_)
open import Relation.PNF.Semantics renaming (_,_⊨_ to _,_⊨PNF_)

-- Iff between satisfiability in QLTL and PNF for two formulas
_≣_ : ∀ {n} → QLTL n → PNF n → Set₁
ϕ₁ ≣ ϕ₂ = ∀ {A} {σ : CounterpartTrace A} {μ} → (σ , μ ⊨QLTL ϕ₁ → σ , μ ⊨PNF ϕ₂) × (σ , μ ⊨PNF ϕ₂ → σ , μ ⊨QLTL ϕ₁)

interleaved mutual

  ^¬ : ∀ {n} → QLTL n → PNF n
  ^  : ∀ {n} → QLTL n → PNF n

  -- Translation function with no negation
  ^ true      = true
  ^ (x == y)  = x == y
  ^ (! ϕ)     = ^¬ ϕ
  ^ (∃<> ϕ)   = ∃<> ^ ϕ
  ^ (◯ ϕ)     = ◯ ^ ϕ
  ^ (ϕ₁ ∨ ϕ₂) = ^ ϕ₁ ∨ ^ ϕ₂
  ^ (ϕ₁ U ϕ₂) = ^ ϕ₁ U ^ ϕ₂
  ^ (ϕ₁ W ϕ₂) = ^ ϕ₁ W ^ ϕ₂

  -- Translation function implicitly carrying a negation
  ^¬ true      = false
  ^¬ (x == y)  = x != y
  ^¬ (! ϕ)     = ^ ϕ
  ^¬ (∃<> ϕ)   = ∀<> (^¬ ϕ)
  ^¬ (◯ ϕ)     = A (^¬ ϕ)
  ^¬ (ϕ₁ ∨ ϕ₂) = ^¬ ϕ₁ ∧ ^¬ ϕ₂
  ^¬ (ϕ₁ U ϕ₂) = (^¬ ϕ₂) T (^¬ ϕ₁ ∧ ^¬ ϕ₂)
  ^¬ (ϕ₁ W ϕ₂) = (^¬ ϕ₂) F (^¬ ϕ₁ ∧ ^¬ ϕ₂)

interleaved mutual

  -- Main theorems:
  -- Given a QLTL formula ϕ, ^ ϕ in PNF is equisatisfiable with the original formula ϕ.
  ^-equivalence : ∀ {n} (ϕ : QLTL n) →     ϕ ≣ ^ ϕ
  -- Dually, ^¬ ϕ in PNF is equisatisfiable with the negation of the original formula.
  ^¬-negation   : ∀ {n} (ϕ : QLTL n) → (! ϕ) ≣ ^¬ ϕ

  -- The proofs are similar to QLTL.Negation and PNF.Negation; however, here
  -- we need to apply the inductive hypotheses on subformulas, and reusing the previously
  -- shown theorem becomes non-trivial.

  -- Show that ^ produces an equivalent formula:
  ^-equivalence (! ϕ) = ^¬-negation ϕ
  ^-equivalence true = (λ x → tt) , (λ x → tt)
  ^-equivalence (x == y) = (λ z → z) , λ z → z
  ^-equivalence (ϕ₁ ∨ ϕ₂) = [ inj₁ ∘ proj₁ (^-equivalence ϕ₁) , inj₂ ∘ proj₁ (^-equivalence ϕ₂) ]
                          , [ inj₁ ∘ proj₂ (^-equivalence ϕ₁) , inj₂ ∘ proj₂ (^-equivalence ϕ₂) ]
  ^-equivalence (∃<> ϕ) = (λ (s , p) → s , proj₁ (^-equivalence ϕ) p)
                        , (λ (s , p) → s , proj₂ (^-equivalence ϕ) p)
  ^-equivalence (◯ ϕ) {σ = σ} {μ = μ} = (λ x → {!   !})
                                      , (λ x → {!   !})
  ^-equivalence (ϕ₁ U ϕ₂) {σ = σ} {μ = μ} = {!   !}
  ^-equivalence (ϕ₁ W ϕ₂)  {σ = σ} {μ = μ} = {!   !}

  -- Show that ^¬ negates the formula:
  ^¬-negation true = (λ x → x tt) , (λ x x₁ → x)
  ^¬-negation (x == y) = (λ x → x) , (λ x → x)
  ^¬-negation (! ϕ) {σ = σ} {μ = μ} with ^-equivalence ϕ {σ = σ} {μ = μ}
  ... | ⇒ , ⇐ = (λ x → ⇒ (DNE x)) , (λ x → λ z → z (⇐ x)) -- Go back to standard equivalence using DNE
  ^¬-negation (ϕ₁ U ϕ₂) {σ = σ} {μ = μ} = {!   !}
  ^¬-negation (ϕ₁ W ϕ₂) {σ = σ} {μ = μ} = {!   !}
  ^¬-negation (ϕ₁ ∨ ϕ₂) = (λ x → let a , b = ¬⊎→¬×¬ x in proj₁ (^¬-negation ϕ₁) a , proj₁ (^¬-negation ϕ₂) b)
                        , λ { (a , b) (inj₁ x) → proj₂ (^¬-negation ϕ₁) a x
                            ; (a , b) (inj₂ y) → proj₂ (^¬-negation ϕ₂) b y
                            }
  ^¬-negation (∃<> ϕ) = (λ x → λ i → proj₁ (^¬-negation ϕ) ((¬∃⟶∀¬ x) i))
                      , (λ x → λ (a , b) → (proj₂ (^¬-negation ϕ)) (x a) b)
  ^¬-negation (◯ ϕ){σ = σ} {μ = μ} = {!   !}