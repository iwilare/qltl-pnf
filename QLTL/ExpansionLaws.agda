{-# OPTIONS --guardedness #-}

module QLTL.ExpansionLaws where

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
open import Full

U∃-expansion-law : ∀ {n} {ϕ₁ ϕ₂ : Full n} → (ϕ₁ U∃ ϕ₂) ≡ (ϕ₂ ∨ (ϕ₁ ∧ (◯∃ (ϕ₁ U∃ ϕ₂))))
U∃-expansion-law {_} {ϕ₁} {ϕ₂} {_} {σ} {μ} = ⇒ , ⇐
  where

    ⇒ : μ , σ ⊨ (ϕ₁ U∃ ϕ₂) → μ , σ ⊨ (ϕ₂ ∨ (ϕ₁ ∧ (◯∃ (ϕ₁ U∃ ϕ₂))))
    ⇒ (zero , ϕ₁<i , ϕ₂n) rewrite lift-unit {μ = μ} = inj₁ ϕ₂n
    ⇒ (suc n , (ϕ₁<i , ϕ₂n)) with ϕ₁<i 0 (_≤_.s≤s _≤_.z≤n)
    ... | base rewrite lift-unit {μ = μ} with ↑ (C≤ 1 σ) μ | inspect (↑ (C≤ 1 σ)) μ
    ... | nothing | ≣: eq rewrite ↑-ext-cong {μ = μ} (monad-law1 {f = rel σ})
                                | CRUCIAL-LEMMA {f = rel σ} {g = C≤ n (tail σ)} μ
                                | eq = ⊥-elim ϕ₂n
    ... | just μ′ | ≣: eq = inj₂ (base , n ,
                                         (λ i x → subst (λ p → ∃C∈ p ⇒ _) (sym (thm {σ = σ} {n = i} {μ = μ} eq)) (ϕ₁<i (suc i) (_≤_.s≤s x)))
                                         , subst (λ p → ∃C∈ p ⇒ _) (sym (thm {σ = σ} {n = n} {μ = μ} eq)) ϕ₂n)

    ⇐ : μ , σ ⊨ (ϕ₂ ∨ (ϕ₁ ∧ (◯∃ (ϕ₁ U∃ ϕ₂)))) → μ , σ ⊨ (ϕ₁ U∃ ϕ₂)
    ⇐ (inj₁ x) = 0 , (λ i ()) , a
      where a : ∃C∈ ↑ just μ ⇒ (_, σ ⊨ ϕ₂)
            a rewrite lift-unit {μ = μ} = x
    ⇐ (inj₂ (μ|ϕ₁ , ◯U)) with ↑ (C≤ 1 σ) μ | inspect (↑ (C≤ 1 σ)) μ
    ⇐ (inj₂ (μ|ϕ₁ , n , 1<ϕ₁<i , n|ϕ₂)) | just x | ≣: eq =
      suc n , (λ { zero x → lift-exists {μ = μ} μ|ϕ₁
                 ; (suc i) (_≤_.s≤s x) → subst (λ p → ∃C∈ p ⇒ _) (thm {σ = σ} {n = i} {μ = μ} eq) (1<ϕ₁<i i x) })
            , subst (λ p → ∃C∈ p ⇒ _) (thm {σ = σ} {n = n} {μ = μ} eq) n|ϕ₂

W∃-expansion-law : ∀ {n} {ϕ₁ ϕ₂ : Full n} → (ϕ₁ W∃ ϕ₂) ≡ (ϕ₂ ∨ (ϕ₁ ∧ (◯∃ (ϕ₁ W∃ ϕ₂))))
W∃-expansion-law {_} {ϕ₁} {ϕ₂} {_} {σ} {μ} = ⇒ , ⇐
  where
    ⇒ : μ , σ ⊨ (ϕ₁ W∃ ϕ₂) → μ , σ ⊨ (ϕ₂ ∨ (ϕ₁ ∧ (◯∃ (ϕ₁ W∃ ϕ₂))))
    ⇒ (inj₁ x) with U∃-expansion-law {_} {ϕ₁} {ϕ₂} {_} {σ} {μ}
    ... | ⇒ , ⇐ with ⇒ x
    ... | inj₁ x₁ = inj₁ x₁
    ... | inj₂ (ϕ₁ , u) with ↑ (C≤ 1 σ) μ
    ... | just x₁ = inj₂ (ϕ₁ , inj₁ u)
    ⇒ (inj₂ y) with ↑ (C≤ 1 σ) μ | inspect (↑ (C≤ 1 σ)) μ
    ... | just x | ≣: eq = inj₂ (subst (λ p → ∃C∈ p ⇒ _) (lift-unit {μ = μ}) (y 0) , inj₂ λ i → subst (λ p → ∃C∈ p ⇒ _) (sym (thm {σ = σ} {n = i} {μ = μ} eq)) (y (suc i)))
    ... | nothing | ≣: eq with ↑ (C≤ 1 σ) μ | y 1
    ... | nothing | ()
    ⇒ (inj₂ y) | nothing | ≣: () | just x | r

    ⇐ : μ , σ ⊨ (ϕ₂ ∨ (ϕ₁ ∧ (◯∃ (ϕ₁ W∃ ϕ₂)))) → μ , σ ⊨ (ϕ₁ W∃ ϕ₂)
    ⇐ (inj₁ x) = inj₁ (0 , (λ i ()) , lift-exists {μ = μ} x)
    ⇐ (inj₂ (ϕ₁μ , u)) with U∃-expansion-law {_} {ϕ₁} {ϕ₂} {_} {σ} {μ}
    ... | ⇒ , u⇐ with ↑ (C≤ 1 σ) μ | inspect (↑ (C≤ 1 σ)) μ
    ⇐ (inj₂ (ϕ₁μ , inj₁ u)) | ⇒ , u⇐ | just x | ≣: eq = inj₁ (u⇐ (inj₂ (ϕ₁μ , u)))
    ⇐ (inj₂ (ϕ₁μ , inj₂ y)) | ⇒ , u⇐ | just x | ≣: eq = inj₂ a
        where a : ∀ i → ∃C∈ ↑ (C≤ i σ) μ ⇒ _
              a zero = lift-exists {μ = μ} ϕ₁μ
              a (suc i) with y i
              ... | p rewrite thm {σ = σ} {n = i} {μ = μ} eq = p

♢∃-expansion-law : ∀ {n} {ϕ : Full n} → ♢∃ ϕ ≡ (ϕ ∨ (◯∃ (♢∃ ϕ)))
♢∃-expansion-law {_} {ϕ} {_} {σ} {μ} with U∃-expansion-law {_} {true} {ϕ} {_} {σ} {μ}
... | U∃⇒ , U∃⇐ = ⇒ , ⇐
  where
    ⇒ : μ , σ ⊨ ♢∃ ϕ → μ , σ ⊨ (ϕ ∨ (◯∃ (♢∃ ϕ)))
    ⇒ x with U∃⇒ x
    ... | inj₁ x₁ = inj₁ x₁
    ... | inj₂ (tt , a) = inj₂ a

    ⇐ : μ , σ ⊨ (ϕ ∨ (◯∃ (♢∃ ϕ))) → μ , σ ⊨ ♢∃ ϕ
    ⇐ (inj₁ x) = 0 , (λ i ()) , lift-exists {μ = μ} x
    ⇐ (inj₂ y) = U∃⇐ (inj₂ (tt , y))

□∃-expansion-law : ∀ {n} {ϕ : Full n} → □∃ ϕ ≡ (ϕ ∧ (◯∃ (□∃ ϕ)))
□∃-expansion-law {_} {ϕ} {_} {σ} {μ} with W∃-expansion-law {_} {ϕ} {false} {_} {σ} {μ}
... | W∃⇒ , W∃⇐ = ⇒ , ⇐
  where
    ⇒ : μ , σ ⊨ □∃ ϕ → μ , σ ⊨ (ϕ ∧ (◯∃ (□∃ ϕ)))
    ⇒ x with W∃⇒ x
    ... | inj₁ ()
    ... | inj₂ r = r

    ⇐ : μ , σ ⊨ (ϕ ∧ (◯∃ (□∃ ϕ))) → μ , σ ⊨ □∃ ϕ
    ⇐ e = W∃⇐ (inj₂ e)
