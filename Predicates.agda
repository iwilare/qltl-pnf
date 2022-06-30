{-# OPTIONS --guardedness #-}

module Predicates where

open import Axiom.DoubleNegationElimination
open import Axiom.ExcludedMiddle
open import Axiom.Extensionality.Propositional
open import Data.Empty
open import Data.Fin using (Fin)
open import Data.Maybe
open import Data.Nat using (ℕ; _∸_; _+_; _<_; _≤_; suc; zero; _<′_; _<‴_; _≤‴_)
open import Data.Nat.Induction
open import Data.Nat.Properties using (≤⇒≤′; ≤⇒≤‴; <-transˡ; <-trans; <⇒≤; <-cmp; ≤-<-connex)
open import Data.Product
open import Data.Sum
open import Data.Unit hiding (_≤_)
open import Function using (_∘_)
open import Function using (id)
open import Level using (0ℓ; Level)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality using (subst; inspect; refl; sym) renaming (_≡_ to _≣_; [_] to ≣:)
open import Relation.Nullary
open import Relation.Nullary.Negation using (¬∃⟶∀¬; contraposition)

_before_ : ∀ (A : ℕ → Set) → ℕ → Set
A before n = ∀ i → i < n → A i

_until_ : ∀ (A B : ℕ → Set) → Set
A until B = ∃[ n ] (A before n × B n)

always : ∀ (A : ℕ → Set) → Set
always A = ∀ i → A i

eventually : ∀ (A : ℕ → Set) → Set
eventually A = ∃[ i ] A i

¬′ : ∀  (A : ℕ → Set) → ℕ → Set
¬′ A = λ x → ¬ A x

_∧′_ : ∀ (A B : ℕ → Set) → ℕ → Set
A ∧′ B = λ x → A x × B x

_∨′_ : ∀ (A B : ℕ → Set) → ℕ → Set
A ∨′ B = λ x → A x ⊎ B x

_weakUntil_ : ∀ (A B : ℕ → Set) → Set
A weakUntil B = A until B ⊎ always A

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
