{-# OPTIONS --guardedness #-}

module Alternative.Negation where

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

open import Counterpart
open import Alternative.QLTL

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

postulate
  ¬∀⟶∃¬ : ∀ {P : ℕ → Set ℓ} → ¬ (∀ x → P x) → (∃[ n ] ¬ P n)
  ¬∀⟶∃¬< : ∀ {n} {P : ℕ → Set ℓ} → ¬ (∀ z → z < n → P z) → (∃[ z ] (z < n × ¬ P z))

raise-exists : ∀ {S : Set} → {A B : S → Set} → {x : Maybe S} → (∃C∈ x ⇒ B) → (∀C∈ x ⇒ A) → (∃C∈ x ⇒ A)
raise-exists {x = just x} _ a = a

clash∃ : ∀ {S : Set} → {P : S → Set} → {x : Maybe S} → (∃C∈ x ⇒ P) → (∃C∈ x ⇒ (λ x → ¬ P x)) → ⊥
clash∃ {x = just x} x₁ x₂ = x₂ x₁
clash∃ {x = nothing} x x₁ = x₁

decrease-chain : ∀ {P : ℕ → Set} {n n′} → n′ ≤ n → (∀ i → i < n → P i) → (∀ i → i < n′ → P i)
decrease-chain n′≤n P = λ i i<n′ → P i (<-transˡ i<n′ n′≤n)

thm1 : ∀ {n} {ϕ₁ ϕ₂ : QLTL n} → ! (ϕ₁ U ϕ₂) ≡ ((! ϕ₂) T (! ϕ₁ ∧ ! ϕ₂))
thm1 {n} {ϕ₁} {ϕ₂} {A} {σ} {μ} = ⇒ , ⇐
  where

    att∀ : ℕ → QLTL n → Set
    att∀ i ϕ = ∀C∈ ↑ (C≤ i σ) μ ⇒ (_, s i σ ⊨ ϕ)

    att∃ : ℕ → QLTL n → Set
    att∃ i ϕ = ∃C∈ ↑ (C≤ i σ) μ ⇒ (_, s i σ ⊨ ϕ)

    before∃ : ℕ → QLTL n → Set
    before∃ n ϕ = ∀ i → i < n → att∃ i ϕ

    ¬before∃ : ℕ → QLTL n → Set
    ¬before∃ n ϕ = ∃[ i ] (i < n × att∀ i (! ϕ))

    max-prefix : QLTL n → Set
    max-prefix ϕ = ∃[ n ] (before∃ n ϕ × att∀ n (! ϕ))

    ¬max-prefix : QLTL n → Set
    ¬max-prefix ϕ = ∀ n → (¬before∃ n ϕ ⊎ att∃ n ϕ)

    strong-always : QLTL n → Set
    strong-always ϕ = ∀ i → att∃ i ϕ

    ¬mp : ∀ ϕ → ¬ max-prefix ϕ → ¬max-prefix ϕ
    ¬mp ϕ a = λ i →
      [ (λ x → inj₁ let i , i<n , x = ¬∀⟶∃¬< x in i , i<n , ¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ} x)
      , (λ x → inj₂ (imply∃ {x = ↑ (C≤ i σ) μ} (λ {x} → DNE {P = x , s i σ ⊨ ϕ}) (¬∀C→∃C¬ {x = ↑ (C≤ i σ) μ} x)))
      ]′ (¬×→¬⊎¬ (¬∃⟶∀¬ a i))

    max-prefix⊎strong-always : ∀ ϕ → max-prefix ϕ ⊎ strong-always ϕ
    max-prefix⊎strong-always ϕ with LEM {P = max-prefix ϕ}
    ... | yes y = inj₁ y
    ... | no n = inj₂ (λ i → wow i (<′-wellFounded i))
      where
        wow : ∀ i → Acc _<′_ i → att∃ i ϕ
        wow i (acc rs) with ¬mp ϕ n i
        ... | inj₂ y = y
        ... | inj₁ (n′ , n′<i , all) with wow n′ (rs n′ (≤⇒≤′ n′<i))
        ... | p with ↑ (C≤ n′ σ) μ
        ... | just x = ⊥-elim (all p)

    then : μ , σ ⊨ ! (ϕ₁ U ϕ₂)
         → ∀ n → before∃ n ϕ₁ → att∀ n (! ϕ₂)
    then a n i<n|∃ϕ₁ = ¬∃C→∀C¬ {x = ↑ (C≤ n σ) μ} (λ x → a (n , i<n|∃ϕ₁ , x))

    ⇒ : μ , σ ⊨ ! (ϕ₁ U ϕ₂) → μ , σ ⊨ ((! ϕ₂) T (! ϕ₁ ∧ ! ϕ₂))
    ⇒ a with max-prefix⊎strong-always ϕ₁
    ... | inj₁ (n , i<n|∃ϕ₁ , n|∀¬ϕ₁) =
             inj₁ (n , (λ i i<n → raise-exists {x = ↑ (C≤ i σ) μ}
                                              (i<n|∃ϕ₁ i i<n)
                                              (then a i (decrease-chain (<⇒≤ i<n) i<n|∃ϕ₁)))
                     , conjunct∀ {x = ↑ (C≤ n σ) μ} n|∀¬ϕ₁ (then a n i<n|∃ϕ₁))
    ... | inj₂ strong-always = inj₂ λ i → then a i λ i′ i′<i → strong-always i′

    ⇐ : μ , σ ⊨ ((! ϕ₂) T (! ϕ₁ ∧ ! ϕ₂)) → μ , σ ⊨ ! (ϕ₁ U ϕ₂)
    ⇐ (inj₂ ∀i|∀ϕ₁∧¬ϕ₂) (n , i<n|∃ϕ₁ , n|∃ϕ₂) with ↑ (C≤ n σ) μ | ∀i|∀ϕ₁∧¬ϕ₂ n
    ... | just μn | un|¬ϕ₂ = un|¬ϕ₂ n|∃ϕ₂
    ⇐ (inj₁ (m , i<m|∃¬ϕ₂ , m|∀¬ϕ₁∧¬ϕ₂)) (n , i<n|∃ϕ₁ , n|∃ϕ₂) with <-cmp m n
    ... | tri< m<n _ _ with ↑ (C≤ m σ) μ | i<n|∃ϕ₁ m m<n | m|∀¬ϕ₁∧¬ϕ₂
    ...                   | just x | m|ϕ₁ | m|¬ϕ₁ , _ = m|¬ϕ₁ m|ϕ₁
    ⇐ (inj₁ (m , i<m|∃¬ϕ₂ , m|∀¬ϕ₁∧¬ϕ₂)) (n , i<n|∃ϕ₁ , n|∃ϕ₂)
        | tri> _ _ n<m with ↑ (C≤ n σ) μ | i<m|∃¬ϕ₂ n n<m
    ...                   | just x | n|¬ϕ₂ = n|¬ϕ₂ n|∃ϕ₂
    ⇐ (inj₁ (m , i<m|∃¬ϕ₂ , m|∀¬ϕ₁∧¬ϕ₂)) (n , i<n|∃ϕ₁ , n|∃ϕ₂)
        | tri≈ _ refl _ with ↑ (C≤ n σ) μ | m|∀¬ϕ₁∧¬ϕ₂
    ...                   | just x | _ , m|¬ϕ₂ = m|¬ϕ₂ n|∃ϕ₂

thm2 : ∀ {n} {ϕ₁ ϕ₂ : QLTL n} → ! (ϕ₁ T ϕ₂) ≡ ((! ϕ₂) U (! ϕ₁ ∧ ! ϕ₂))
thm2 {n} {ϕ₁} {ϕ₂} {A} {σ} {μ} = ⇒ , ⇐
  where

    att∀ : ℕ → QLTL n → Set
    att∀ i ϕ = ∀C∈ ↑ (C≤ i σ) μ ⇒ (_, s i σ ⊨ ϕ)

    att∃ : ℕ → QLTL n → Set
    att∃ i ϕ = ∃C∈ ↑ (C≤ i σ) μ ⇒ (_, s i σ ⊨ ϕ)

    before∃ : ℕ → QLTL n → Set
    before∃ n ϕ = ∀ i → i < n → att∃ i ϕ

    ¬before∃ : ℕ → QLTL n → Set
    ¬before∃ n ϕ = ∃[ i ] (i < n × att∀ i (! ϕ))

    max-prefix : QLTL n → Set
    max-prefix ϕ = ∃[ n ] (before∃ n ϕ × att∀ n (! ϕ))

    ¬max-prefix : QLTL n → Set
    ¬max-prefix ϕ = ∀ n → (¬before∃ n ϕ ⊎ att∃ n ϕ)

    strong-always : QLTL n → Set
    strong-always ϕ = ∀ i → att∃ i ϕ

    ¬mp : ∀ ϕ → ¬ max-prefix ϕ → ¬max-prefix ϕ
    ¬mp ϕ a = λ i →
      [ (λ x → inj₁ let i , i<n , x = ¬∀⟶∃¬< x in i , i<n , ¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ} x)
      , (λ x → inj₂ (imply∃ {x = ↑ (C≤ i σ) μ} (λ {x} → DNE {P = x , s i σ ⊨ ϕ}) (¬∀C→∃C¬ {x = ↑ (C≤ i σ) μ} x)))
      ]′ (¬×→¬⊎¬ (¬∃⟶∀¬ a i))

    max-prefix⊎strong-always : ∀ ϕ → max-prefix ϕ ⊎ strong-always ϕ
    max-prefix⊎strong-always ϕ with LEM {P = max-prefix ϕ}
    ... | yes y = inj₁ y
    ... | no n = inj₂ (λ i → wow i (<′-wellFounded i))
      where
        wow : ∀ i → Acc _<′_ i → att∃ i ϕ
        wow i (acc rs) with ¬mp ϕ n i
        ... | inj₂ y = y
        ... | inj₁ (n′ , n′<i , all) with wow n′ (rs n′ (≤⇒≤′ n′<i))
        ... | p with ↑ (C≤ n′ σ) μ
        ... | just x = ⊥-elim (all p)

    useful-negation : μ , σ ⊨ ! (ϕ₁ T ϕ₂)
                  → ∃[ n ] (att∃ n (! ϕ₁)
                         × (∀ i → (∀ k → k < i → att∃ k ϕ₁) → att∃ i (! ϕ₂)))
    useful-negation a =
      let a , b = ¬⊎→¬×¬ a in
      let n , b = ¬∀⟶∃¬ b in
      n , ¬∀C→∃C¬ {x = ↑ (C≤ n σ) μ} b
        , λ i x → [ (λ x₁ → ⊥-elim (x₁ x))
                  , ¬∀C→∃C¬ {x = ↑ (C≤ i σ) μ}
                  ] (¬×→¬⊎¬ (¬∃⟶∀¬ a i))

    ⇒ : μ , σ ⊨ ! (ϕ₁ T ϕ₂) → μ , σ ⊨ ((! ϕ₂) U (! ϕ₁ ∧ ! ϕ₂))
    ⇒ a with useful-negation a
    ... | m , m|¬ϕ₁ , then with max-prefix⊎strong-always ϕ₁
    ... | inj₁ (n , i<n|∃ϕ₁ , n|∀¬ϕ₁) with ≤-<-connex n m
    ... | inj₁ n≤m = n , (λ i i<n → then i λ k k<i → i<n|∃ϕ₁ k (<-trans k<i i<n))
                        , conjunct∃ {x = ↑ (C≤ n σ) μ} (raise-exists {x = ↑ (C≤ n σ) μ} (then n i<n|∃ϕ₁) n|∀¬ϕ₁) (then n i<n|∃ϕ₁)
    ... | inj₂ m<n = ⊥-elim (clash∃ {x = ↑ (C≤ m σ) μ} (i<n|∃ϕ₁ m m<n) m|¬ϕ₁)
    ⇒ a | m , m|¬ϕ₁ , then | inj₂ strong-always with ↑ (C≤ m σ) μ | strong-always m
    ... | just x | m|ϕ₁ = ⊥-elim (m|¬ϕ₁ m|ϕ₁)

    ⇐ : μ , σ ⊨ ((! ϕ₂) U (! ϕ₁ ∧ ! ϕ₂)) → μ , σ ⊨ ! (ϕ₁ T ϕ₂)
    ⇐ (n , i<n|∃¬ϕ₂ , n|∃¬ϕ₁∧¬ϕ₂) (inj₂ ∀i|¬ϕ₂) with ↑ (C≤ n σ) μ | ∀i|¬ϕ₂ n
    ⇐ (n , i<n|∃¬ϕ₂ , (n|∃¬ϕ₁ , n|¬ϕ₂)) (inj₂ ∀i|¬ϕ₂) | just x | b = n|∃¬ϕ₁ b
    ⇐ (n , i<n|∃¬ϕ₂ , n|∃¬ϕ₁∧¬ϕ₂) (inj₁ (m , i<m|∃ϕ₁ , m|∀ϕ₂)) with <-cmp m n
    ... | tri< m<n _ _ with ↑ (C≤ m σ) μ | i<n|∃¬ϕ₂ m m<n
    ...                   | just x  | m|∃¬ϕ₂ = m|∃¬ϕ₂ m|∀ϕ₂
    ...                   | nothing | m|∃¬ϕ₂ = m|∃¬ϕ₂
    ⇐ (n , i<n|∃¬ϕ₂ , n|∃¬ϕ₁∧¬ϕ₂) (inj₁ (m , i<m|∃ϕ₁ , m|∀ϕ₂))
        | tri> _ _ n<m  with ↑ (C≤ n σ) μ | i<m|∃ϕ₁ n n<m
    ⇐ (n , i<n|∃¬ϕ₂ , (n|∃¬ϕ₁ , n|¬ϕ₂)) (inj₁ (m , i<m|∃ϕ₁ , m|∀ϕ₂)) | tri> _ _ n<m | just x | n|∃ϕ₁ = n|∃¬ϕ₁ n|∃ϕ₁
    ⇐ (n , i<n|∃¬ϕ₂ , n|∃¬ϕ₁∧¬ϕ₂) (inj₁ (m , i<m|∃ϕ₁ , m|∀ϕ₂))
        | tri≈ _ refl _ with ↑ (C≤ m σ) μ
    ⇐ (n , i<n|∃¬ϕ₂ , (n|∃¬ϕ₁ , n|¬ϕ₂)) (inj₁ (m , i<m|∃ϕ₁ , m|∀ϕ₂)) | tri≈ _ refl _ | just x = n|¬ϕ₂ m|∀ϕ₂
