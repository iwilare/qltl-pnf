{-# OPTIONS --guardedness #-}

{-
  Equivalences for the temporal operators in non-extended QLTL.
-}
module QLTL.Equivalences where

open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.Unit

open import Predicates
open import Counterpart
open import Full

U-equivalence : ∀ {n} {ϕ₁ ϕ₂ : Full n} → ϕ₁ U ϕ₂ ≣ ϕ₁ W ϕ₂ ∧ ♢ ϕ₂
U-equivalence {_} {ϕ₁} {ϕ₂} {_} {σ} {μ} = ⇒ , ⇐
  where

    ⇒ : σ , μ ⊨ ϕ₁ U ϕ₂ → σ , μ ⊨ ϕ₁ W ϕ₂ ∧ ♢ ϕ₂
    ⇒ (n , ϕ₁<i , ϕ₂n) = inj₁ (n , ϕ₁<i , ϕ₂n) , n , true-before-n , ϕ₂n
      where
        true-before-n : at∃ σ μ true before n
        true-before-n i x with ↑ (C≤ i σ) μ | ϕ₁<i i x
        ... | just μ | _ = tt

    ⇐ : σ , μ ⊨ ϕ₁ W ϕ₂ ∧ ♢ ϕ₂ → σ , μ ⊨ ϕ₁ U ϕ₂
    ⇐ (inj₁ u , _) = u
    ⇐ (inj₂ a , n , _ , ϕ₂n) = n , (λ i _ → a i) , ϕ₂n

W-equivalence : ∀ {n} {ϕ₁ ϕ₂ : Full n} → ϕ₁ W ϕ₂ ≣ ϕ₁ U ϕ₂ ∨ □ ϕ₁
W-equivalence {_} {ϕ₁} {ϕ₂} {_} {σ} {μ} = ⇒ , ⇐
  where
    ⇒ : σ , μ ⊨ ϕ₁ W ϕ₂ → σ , μ ⊨ ϕ₁ U ϕ₂ ∨ □ ϕ₁
    ⇒ (inj₁ x) = inj₁ x
    ⇒ (inj₂ y) = inj₂ (inj₂ y)

    ⇐ : σ , μ ⊨ ϕ₁ U ϕ₂ ∨ □ ϕ₁ → σ , μ ⊨ ϕ₁ W ϕ₂
    ⇐ (inj₁ x) = inj₁ x
    ⇐ (inj₂ (inj₁ (n , ϕ₁<i , ϕ₂n))) with ↑ (C≤ n σ) μ
    ⇐ (inj₂ (inj₁ (n , ϕ₁<i , ()))) | just x
    ⇐ (inj₂ (inj₁ (n , ϕ₁<i , ()))) | nothing
    ⇐ (inj₂ (inj₂ y)) = inj₂ y
