{-# OPTIONS --guardedness #-}

module Counterpart where

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

record CounterpartTrace (A : Set) : Set₁ where
  constructor _∷_
  coinductive
  field
    {B}    : Set
    rel    : A → Maybe B
    tail   : CounterpartTrace B

open CounterpartTrace public

wi : ∀ {A : Set} → ℕ → CounterpartTrace A → Set
wi {A} zero T = A
wi (suc n) T = wi n (tail T)

s : ∀ {A} → (n : ℕ) → (σ : CounterpartTrace A) → CounterpartTrace (wi n σ)
s zero T = T
s (suc n) T = s n (tail T)

relAt : ∀ {A : Set} → (n : ℕ) → (σ : CounterpartTrace A) → (wi n σ → Maybe (wi (suc n) σ))
relAt zero σ = rel σ
relAt (suc n) σ = relAt n (tail σ)

_>=>_ : ∀ {A B C : Set} → (A → Maybe B) → (B → Maybe C) → A → Maybe C
_>=>_ f g = λ x → f x >>= g

<*,*> : ∀ {A B C D : Set} → (A → Maybe C) → (B → Maybe D) → A → B → Maybe (C × D)
<*,*> f g a b with f a | g b
... | just x | just y = just (x , y)
... | _ | _ = nothing

monad-law1 : ∀ {A B} {f : A → Maybe B} x
           → (f >=> just) x ≣ f x
monad-law1 {f = f} x with f x
... | just x₁ = refl
... | nothing = refl

monad-law2 : ∀ {A B C D} {f : A → Maybe B} {g : B → Maybe C} {h : C → Maybe D} x
           → ((f >=> g) >=> h) x ≣ (f >=> (g >=> h)) x
monad-law2 {f = f} x with f x
... | just x₁ = refl
... | nothing = refl

C≤′ : ∀ {A} → (n : ℕ) → (σ : CounterpartTrace A) → A → Maybe (wi n σ)
C≤′ zero σ = just
C≤′ (suc n) σ = C≤′ n σ >=> relAt n σ

C≤ : ∀ {A} → (n : ℕ) → (σ : CounterpartTrace A) → A → Maybe (wi n σ)
C≤ zero σ = just
C≤ (suc n) σ = rel σ >=> C≤ n (tail σ)

Elements : ℕ → Set → Set
Elements zero A = ⊤
Elements (suc n) A = A × Elements n A

↑ : ∀ {n} {A B : Set} → (A → Maybe B) → Elements n A → Maybe (Elements n B)
↑ {n = zero} f tt = just tt
↑ {n = suc n} f (x , e) = <*,*> f (↑ f) x e

postulate
  sorry : ∀ {a : Set} → a

CRUCIAL-LEMMA : ∀ {A B C} {f : A → Maybe B} {g : B → Maybe C} {n} (μ : Elements n A)
              → ↑ (f >=> g) μ ≣ (↑ f >=> ↑ g) μ
CRUCIAL-LEMMA {n = zero} μ = refl
CRUCIAL-LEMMA {f = f} {g = g} {n = suc n} (x , e) rewrite CRUCIAL-LEMMA {f = f} {g = g} {n = n} e = sorry

↑-ext-cong : ∀ {n} {A B : Set} {f g : A → Maybe B} {μ : Elements n A}
           → (∀ x → f x ≣ g x)
           → ↑ f μ ≣ ↑ g μ
↑-ext-cong {zero} x = refl
↑-ext-cong {suc n} {μ = a , b} x rewrite ↑-ext-cong {μ = b} x | x a = refl

lift-unit : ∀ {n} {A : Set} {μ : Elements n A} → ↑ just μ ≣ just μ
lift-unit {zero} {μ = tt} = refl
lift-unit {suc n} {μ = a , μ} rewrite lift-unit {n} {μ = μ} = refl

thm : ∀ {k} {A} {σ : CounterpartTrace A} {n} {μ : Elements k _} {μ′}
    → ↑ (C≤ 1 σ) μ ≣ just μ′
    → ↑ (C≤ n (tail σ)) μ′
    ≣ ↑ (C≤ (suc n) σ) μ
thm {_} {_} {σ} {n} {μ} eq rewrite ↑-ext-cong {μ = μ} (monad-law1 {f = rel σ})
                      | CRUCIAL-LEMMA {f = rel σ} {g = C≤ n (tail σ)} μ
                      | eq = refl

thm-n : ∀ {k} {A} {σ : CounterpartTrace A} {n} {μ : Elements k _}
    → ↑ (C≤ 1 σ) μ ≣ nothing
    → ↑ (C≤ (suc n) σ) μ ≣ nothing
thm-n {_} {_} {σ} {n} {μ} eq rewrite ↑-ext-cong {μ = μ} (monad-law1 {f = rel σ})
                    | CRUCIAL-LEMMA {f = rel σ} {g = C≤ n (tail σ)} μ
                    | eq = refl

∀C∈_⇒_ : ∀ {A : Set} → Maybe A → (A → Set) → Set
∀C∈ nothing ⇒ P = ⊤
∀C∈ just x ⇒ P = P x

∃C∈_⇒_ : ∀ {A : Set} → Maybe A → (A → Set) → Set
∃C∈ nothing ⇒ P = ⊥
∃C∈ just x ⇒ P = P x

¬∃C←∀C¬ : ∀ {A : Set} → {P : A → Set} → {x : Maybe A} → ∀C∈ x ⇒ (λ x → ¬ P x) → ¬ (∃C∈ x ⇒ P)
¬∃C←∀C¬ {x = nothing} e = λ z → z
¬∃C←∀C¬ {x = just x} e = e

¬∀C←∃C¬ : ∀ {A : Set} → {P : A → Set} → {x : Maybe A} → ∃C∈ x ⇒ (λ x → ¬ P x) → ¬ (∀C∈ x ⇒ P)
¬∀C←∃C¬ {x = nothing} e = λ _ → e
¬∀C←∃C¬ {x = just x} e = e

¬∃C→∀C¬ : ∀ {A : Set} → {P : A → Set} → {x : Maybe A} → ¬ (∃C∈ x ⇒ P) → ∀C∈ x ⇒ (λ x → ¬ P x)
¬∃C→∀C¬ {x = nothing} e = tt
¬∃C→∀C¬ {x = just x} e = e

¬∀C→∃C¬ : ∀ {A : Set} → {P : A → Set} → {x : Maybe A} → ¬ (∀C∈ x ⇒ P) → ∃C∈ x ⇒ (λ x → ¬ P x)
¬∀C→∃C¬ {x = nothing} e = e tt
¬∀C→∃C¬ {x = just x} e = e

conjunct∀ : ∀ {S : Set} → {A B : S → Set} → {x : Maybe S} → (∀C∈ x ⇒ A) → (∀C∈ x ⇒ B) → (∀C∈ x ⇒ (λ x → A x × B x))
conjunct∀ {x = just x} = _,_
conjunct∀ {x = nothing} = λ _ _ → tt

conjunct∃ : ∀ {S : Set} → {A B : S → Set} → {x : Maybe S} → (∃C∈ x ⇒ A) → (∃C∈ x ⇒ B) → (∃C∈ x ⇒ (λ x → A x × B x))
conjunct∃ {x = just x} = _,_
conjunct∃ {x = nothing} = λ _ z → z

disjunct∀ : ∀ {S : Set} → {A B : S → Set} → {x : Maybe S} → (∀C∈ x ⇒ (λ x → A x × B x)) → (∀C∈ x ⇒ A) × (∀C∈ x ⇒ B)
disjunct∀ {x = just x} = λ z → z
disjunct∀ {x = nothing} = λ _ → tt , tt

disjunct∃ : ∀ {S : Set} → {A B : S → Set} → {x : Maybe S} → (∃C∈ x ⇒ (λ x → A x × B x)) → (∃C∈ x ⇒ A) × (∃C∈ x ⇒ B)
disjunct∃ {x = just x} = λ z → z
disjunct∃ {x = nothing} = λ z → z , z

lift-exists : ∀ {n} {A} {μ : Elements n A} {P}
     → P μ
     → ∃C∈ ↑ just μ ⇒ P
lift-exists {μ = μ} x rewrite lift-unit {μ = μ} = x

lift-exists′ : ∀ {n} {A} {μ : Elements n A} {P}
     → ∃C∈ ↑ just μ ⇒ P
     → P μ
lift-exists′ {μ = μ} x rewrite lift-unit {μ = μ} = x

lift-forall : ∀ {n} {A} {μ : Elements n A} {P}
     → P μ
     → ∀C∈ ↑ just μ ⇒ P
lift-forall {μ = μ} x rewrite lift-unit {μ = μ} = x

lift-nothing : ∀ {A} {P : A → Set}
             → ∀C∈ nothing ⇒ P
lift-nothing = tt