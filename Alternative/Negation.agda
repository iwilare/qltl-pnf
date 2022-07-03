{-# OPTIONS --guardedness #-}

{-
  Negation for the then and until-forall operators using
  the alternative existential definitions.
  We show here how the two definitions of the then and
  until-forall operators actually coincide.
-}
module Alternative.Negation where

open import Data.Product
open import Data.Sum
open import Data.Unit using (tt)
open import Data.Maybe
open import Data.Empty
open import Relation.Binary.Definitions
open import Data.Nat using (ℕ; _∸_; _+_; _<_; _≤_; suc; zero; _<′_; _<‴_; _≤‴_)
open import Data.Nat.Properties using (≤⇒≤′; ≤⇒≤‴; <-transˡ; <-trans; <⇒≤; <-cmp; ≤-<-connex)
open import Relation.Binary.PropositionalEquality using (refl; inspect) renaming ([_] to ≣:)

open import Counterpart
open import Predicates
open import Negation
open import Alternative.QLTL

degrade : ∀ {S : Set} → {A : S → Set} → {x : Maybe S} → (∃C∈ x ⇒ A) → (∀C∈ x ⇒ A)
degrade {x = just x} a = a

T-equiv : ∀ {n} {ϕ₁ ϕ₂ : QLTL-alt n} → ϕ₁ T ϕ₂ ≣ ϕ₁ T′ ϕ₂
T-equiv {n} {ϕ₁} {ϕ₂} {A} {σ} {μ} = ⇒ , ⇐
  where
    ⇒ : σ , μ ⊨ ϕ₁ T ϕ₂ → σ , μ ⊨ ϕ₁ T′ ϕ₂
    ⇒ (inj₁ (n , i<n|∀ϕ₁ , i<n|∀ϕ₂)) with strong-prefix-lem {A = at∃ σ μ ϕ₁}
    ... | inj₂ always = inj₂ always
    ... | inj₁ (m , i<m|∃ϕ₁ , m|¬∃ϕ₁) with <-cmp m n
    ... | tri> _ _ n<m  = inj₁ (n , (λ i i<n → i<m|∃ϕ₁ i (<-trans i<n n<m)) , i<n|∀ϕ₂)
    ... | tri≈ _ refl _ = inj₁ (m , i<m|∃ϕ₁ , i<n|∀ϕ₂)
    ... | tri< m<n _ _ with ↑ (C≤ m σ) μ | inspect (↑ (C≤ m σ)) μ
    ... | just x | ≣: eq = ⊥-elim (m|¬∃ϕ₁ (yes (i<n|∀ϕ₁ m m<n)))
      where yes : ∀C∈ ↑ (C≤ m σ) μ ⇒ (s m σ ,_⊨ ϕ₁) → s m σ , x ⊨ ϕ₁
            yes x rewrite eq = x
    ... | nothing | ≣: eq = inj₁ (m , i<m|∃ϕ₁ , no-cp)
      where no-cp : ∀C∈ ↑ (C≤ m σ) μ ⇒ (s m σ ,_⊨ ϕ₂)
            no-cp rewrite eq = tt
    ⇒ (inj₂ y) with strong-prefix-lem {A = at∃ σ μ ϕ₁}
    ... | inj₂ always = inj₂ always
    ... | inj₁ (n , i<n|∃ϕ₁ , i<n|¬∃ϕ₁) with ↑ (C≤ n σ) μ | inspect (↑ (C≤ n σ)) μ | y n
    ... | just x | k | r = ⊥-elim (i<n|¬∃ϕ₁ r)
    ... | nothing | ≣: eq | r = inj₁ (n , i<n|∃ϕ₁ , no-cp)
      where no-cp : ∀C∈ ↑ (C≤ n σ) μ ⇒ (s n σ ,_⊨ ϕ₂)
            no-cp rewrite eq = tt

    ⇐ : σ , μ ⊨ ϕ₁ T′ ϕ₂ → σ , μ ⊨ ϕ₁ T ϕ₂
    ⇐ (inj₁ (n , i<n|∃ϕ₁ , i<n|∀ϕ₂)) = inj₁ (n , (λ i i<n → degrade {x = ↑ (C≤ i σ) μ} (i<n|∃ϕ₁ i i<n)) , i<n|∀ϕ₂)
    ⇐ (inj₂ i|∃ϕ₁) = inj₂ λ i → degrade {x = ↑ (C≤ i σ) μ} (i|∃ϕ₁ i)

F-equiv : ∀ {n} {ϕ₁ ϕ₂ : QLTL-alt n} → ϕ₁ F ϕ₂ ≣ ϕ₁ F′ ϕ₂
F-equiv {n} {ϕ₁} {ϕ₂} {A} {σ} {μ} = ⇒ , ⇐
  where
    ⇒ : σ , μ ⊨ ϕ₁ F ϕ₂ → σ , μ ⊨ ϕ₁ F′ ϕ₂
    ⇒ (n , i<n|∀ϕ₁ , i<n|∀ϕ₂) with strong-prefix-lem {A = at∃ σ μ ϕ₁}
    ... | inj₂ always = n , (λ i _ → always i) , i<n|∀ϕ₂
    ... | inj₁ (m , i<m|∃ϕ₁ , m|¬∃ϕ₁) with <-cmp m n
    ... | tri≈ _ refl _ = m , i<m|∃ϕ₁ , i<n|∀ϕ₂
    ... | tri> _ _ n<m  = n , (λ i i<n → i<m|∃ϕ₁ i (<-trans i<n n<m)) , i<n|∀ϕ₂
    ... | tri< m<n _ _ with ↑ (C≤ m σ) μ | inspect (↑ (C≤ m σ)) μ
    ... | nothing | ≣: eq = m , i<m|∃ϕ₁ , no-cp
      where no-cp : ∀C∈ ↑ (C≤ m σ) μ ⇒ (s m σ ,_⊨ ϕ₂)
            no-cp rewrite eq = tt
    ... | just x | ≣: eq with i<n|∀ϕ₁ m m<n
    ... | r rewrite eq = ⊥-elim (m|¬∃ϕ₁ r)

    ⇐ : σ , μ ⊨ ϕ₁ F′ ϕ₂ → σ , μ ⊨ ϕ₁ F ϕ₂
    ⇐ (n , i<n|∃ϕ₁ , i<n|∀ϕ₂) = n , (λ i i<n → degrade {x = ↑ (C≤ i σ) μ} (i<n|∃ϕ₁ i i<n)) , i<n|∀ϕ₂
