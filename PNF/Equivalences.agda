{-# OPTIONS --guardedness #-}

{-
  Equivalences for the temporal operators in extended PNF.
-}
module PNF.Equivalences where

open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (subst; inspect; refl; sym) renaming ([_] to ≣:)

open import Predicates
open import Counterpart
open import PNF

T-equivalence : ∀ {n} {ϕ₁ ϕ₂ : PNF n} → ϕ₁ T ϕ₂ ≣ ϕ₁ F ϕ₂ ∨ □* ϕ₁
T-equivalence {_} {ϕ₁} {ϕ₂} {_} {σ} {μ} = ⇒ , ⇐
  where
    ⇒ : σ , μ ⊨ ϕ₁ T ϕ₂ → σ , μ ⊨ ϕ₁ F ϕ₂ ∨ □* ϕ₁
    ⇒ (inj₁ x) = inj₁ x
    ⇒ (inj₂ y) = inj₂ (inj₂ y)

    ⇐ : σ , μ ⊨ ϕ₁ F ϕ₂ ∨ □* ϕ₁ → σ , μ ⊨ ϕ₁ T ϕ₂
    ⇐ (inj₁ x) = inj₁ x
    ⇐ (inj₂ (inj₁ (n , ϕ₁<i , ϕ₂n))) with ↑ (C≤ n σ) μ | inspect (↑ (C≤ n σ)) μ
    ... | nothing | ≣: eq = inj₁ (n , ϕ₁<i , ∀ϕ₂)
       where ∀ϕ₂ : ∀C∈ ↑ (C≤ n σ) μ ⇒ (s n σ ,_⊨ ϕ₂)
             ∀ϕ₂ rewrite eq = tt
    ⇐ (inj₂ (inj₂ y)) = inj₂ y

F-equivalence : ∀ {n} {ϕ₁ ϕ₂ : PNF n} → ϕ₁ F ϕ₂ ≣ ϕ₁ T ϕ₂ ∧ ♢* ϕ₂
F-equivalence {_} {ϕ₁} {ϕ₂} {_} {σ} {μ} = ⇒ , ⇐
  where

    ⇒ : σ , μ ⊨ ϕ₁ F ϕ₂ → σ , μ ⊨ ϕ₁ T ϕ₂ ∧ ♢* ϕ₂
    ⇒ (n , ϕ₁<i , ϕ₂n) = inj₁ (n , ϕ₁<i , ϕ₂n) , n , true-before-n , ϕ₂n
      where
        true-before-n : at∀ σ μ true before n
        true-before-n i x with ↑ (C≤ i σ) μ
        ... | nothing = tt
        ... | just μ = tt

    ⇐ : σ , μ ⊨ ϕ₁ T ϕ₂ ∧ ♢* ϕ₂ → σ , μ ⊨ ϕ₁ F ϕ₂
    ⇐ (inj₁ u , _) = u
    ⇐ (inj₂ a , n , _ , ϕ₂n) = n , (λ i _ → a i) , ϕ₂n
