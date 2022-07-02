{-# OPTIONS --guardedness #-}

module Negation where

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

open import Predicates

private
  variable
    ℓ : Level

postulate
  LEM : ExcludedMiddle ℓ
  DNE : DoubleNegationElimination ℓ
  Ext : Extensionality ℓ ℓ

¬×→¬⊎¬ : ∀ {A B : Set ℓ} → ¬ (A × B) → (¬ A ⊎ ¬ B)
¬×→¬⊎¬ {ℓ} {A} neg with LEM {ℓ} {A}
... | yes p = inj₂ λ x → neg (p , x)
... | no ¬p = inj₁ ¬p

¬⊎→¬×¬ : ∀ {A B : Set ℓ} → ¬ (A ⊎ B) → (¬ A × ¬ B)
¬⊎→¬×¬ {ℓ} {A} neg with LEM {ℓ} {A}
... | yes p = (λ x → neg (inj₁ x)) , (λ x → neg (inj₁ p))
... | no ¬p = ¬p , (λ x → neg (inj₂ x))

¬∀¬⟶∃ : ∀ {A : Set ℓ} {P : A → Set ℓ} → ¬ (∀ x → ¬ P x) → (∃[ n ] P n)
¬∀¬⟶∃ x = DNE λ z → x (λ x z₁ → z (x , z₁))

¬∀⟶∃¬ : ∀ {A : Set ℓ} {P : A → Set ℓ} → ¬ (∀ x → P x) → (∃[ n ] ¬ P n)
¬∀⟶∃¬ {P = P} x = ¬∀¬⟶∃ {P = λ x → ¬ P x} λ x₁ → x λ x₂ → DNE (x₁ x₂)

_¬until_ : ∀ (A B : ℕ → Set) → Set
A ¬until B = ∀ n → ((∃[ i ] i < n × A i) ⊎ B n)

_¬untilLeft_ : ∀ (A B : ℕ → Set) → Set
A ¬untilLeft B = ∀ n → (A before n → B n)

_¬weakUntil_ : ∀ (A B : ℕ → Set) → Set
A ¬weakUntil B = A ¬until B × eventually A

_¬weakUntilLeft_ : ∀ (A B : ℕ → Set) → Set
A ¬weakUntilLeft B = A ¬untilLeft B × eventually A

u¬u : ∀ {A B} → ¬ A until B → (¬′ A) ¬until (¬′ B)
u¬u nu = λ i → [ (λ x → inj₁ let a , b = ¬∀⟶∃¬ x in a , let b , c = ¬∀⟶∃¬ x in ¬∀⟶∃¬ c) , (λ x → inj₂ x) ] (¬×→¬⊎¬ ((¬∃⟶∀¬ nu) i))

u¬ul : ∀ {A B} → ¬ A until B → A ¬untilLeft (¬′ B)
u¬ul nu = λ i → [ (λ x → λ z _ → x z) , (λ x → λ _ → x) ] (¬×→¬⊎¬ ((¬∃⟶∀¬ nu) i))

a→e : ∀ {A} → ¬ always A → eventually (¬′ A)
a→e = ¬∀⟶∃¬

e→a : ∀ {A} → ¬ eventually A → always (¬′ A)
e→a = λ z i z₁ → z (i , z₁)

wu¬wu : ∀ {A B} → ¬ A weakUntil B → (¬′ A) ¬weakUntil (¬′ B)
wu¬wu nu = < (λ x → u¬u (proj₁ x)) , (λ x → a→e (proj₂ x)) > (¬⊎→¬×¬ nu)

wu¬wul : ∀ {A B} → ¬ A weakUntil B → A ¬untilLeft (¬′ B) × eventually (¬′ A)
wu¬wul nu = < (λ x → u¬ul (proj₁ x)) , (λ x → a→e (proj₂ x)) > (¬⊎→¬×¬ nu)

strong-prefix-lem : ∀ {A} → A until (¬′ A) ⊎ always A
strong-prefix-lem {A} with LEM {P = A until (¬′ A)}
... | yes y = inj₁ y
... | no n = inj₂ (λ i → wow i (<′-wellFounded i))
    where
      wow : ∀ i → Acc _<′_ i → A i
      wow i (acc rs) with u¬u n i
      ... | inj₂ y = DNE y
      ... | inj₁ (n′ , n′<i , all) = ⊥-elim (all (wow n′ (rs n′ (≤⇒≤′ n′<i))))

¬until→weakUntil : ∀ {A B} → ¬ A until B → (¬′ B) weakUntil (¬′ A ∧′ ¬′ B)
¬until→weakUntil {A} nu =
    [ (λ (n , Ai<n , !An) →
      inj₁ (n ,
            (λ k k<n → u¬ul nu k λ i i<k → Ai<n i (<-trans i<k k<n))
            , !An , u¬ul nu n λ i i<k → Ai<n i i<k))
    , (λ Ai → inj₂ λ i x → u¬ul nu i (λ k k<i → Ai k) x)
    ]′ (strong-prefix-lem {A})

¬until←weakUntil : ∀ {A B} → (¬′ B) weakUntil (¬′ A ∧′ ¬′ B) → ¬ A until B
¬until←weakUntil (inj₁ (m , !Bi<m , !Am , !Bm)) (n , Ai<n , Bn) with <-cmp m n
... | tri< m<n _ _ = !Am (Ai<n m m<n)
... | tri≈ _ refl _ = !Bm Bn
... | tri> _ _ n<m = !Bi<m n n<m Bn
¬until←weakUntil (inj₂ !Bi) (n , Ai<n , Bn) = !Bi n Bn

¬weakUntil→until : ∀ {A B} → ¬ A weakUntil B → (¬′ B) until (¬′ A ∧′ ¬′ B)
¬weakUntil→until {A} nu with wu¬wul nu
... | then , (n , !An) with strong-prefix-lem {A}
... | inj₁ (n , Ai<n , !An) =
       n , (λ k k<n → then k λ i i<k → Ai<n i (<-trans i<k k<n)) , !An , then n Ai<n
... | inj₂ Ai = ⊥-elim (!An (Ai n))

¬weakUntil←until : ∀ {A B} → (¬′ B) until (¬′ A ∧′ ¬′ B) → ¬ A weakUntil B
¬weakUntil←until (n , !Bi<n , !An , !Bn) (inj₁ (m , Ai<m , Bm)) with <-cmp m n
... | tri< m<n _ _ = !Bi<n m m<n Bm
... | tri≈ _ refl _ = !Bn Bm
... | tri> _ _ n<m = !An (Ai<m n n<m)
¬weakUntil←until (n , !Bi<n , !An , !Bn) (inj₂ Ai) = !An (Ai n)
