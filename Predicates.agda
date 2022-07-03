{-# OPTIONS --guardedness #-}

{-
  Shorthand predicates of standard LTL, defining temporal until, always, eventually, weak until.
-}
module Predicates where

open import Data.Nat using (ℕ; _<_)
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Relation.Unary

-- A holds for all i strictly before n steps
_before_ : ∀ (A : ℕ → Set) → ℕ → Set
A before n = ∀ i → i < n → A i

-- A holds until B is satisfied
_until_ : ∀ (A B : ℕ → Set) → Set
A until B = ∃[ n ] (A before n × B n)

-- A is always satisfied at each step
always : ∀ (A : ℕ → Set) → Set
always A = ∀ i → A i

-- There exists a step after which A is satisfied
eventually : ∀ (A : ℕ → Set) → Set
eventually A = ∃[ i ] A i

-- Either until or always hold
_weakUntil_ : ∀ (A B : ℕ → Set) → Set
A weakUntil B = A until B ⊎ always A

-- Implication congruences for until and weak until
congUntil : ∀ {A B A′ B′ : ℕ → Set}
          → (∀ {x} → A x → A′ x)
          → (∀ {x} → B x → B′ x)
          → A until B → A′ until B′
congUntil G F = λ (n , b , t) → n , (λ i x → G (b i x)) , F t

congWeakUntil : ∀ {A B A′ B′ : ℕ → Set}
              → (∀ {x} → A x → A′ x)
              → (∀ {x} → B x → B′ x)
              → A weakUntil B → A′ weakUntil B′
congWeakUntil G F = [ (λ x → inj₁ (congUntil G F x)) , (λ x → inj₂ (λ y → G (x y))) ]
