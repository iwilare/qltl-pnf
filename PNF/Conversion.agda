{-# OPTIONS --guardedness #-}

module PNF.Conversion where

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
open import Counterpart
open import Negation
open import QLTL renaming (_,_⊨_ to _,_⊨QLTL_) renaming (_≡_ to _≡QLTL_) hiding (false; _∧_)
open import PNF renaming (_,_⊨_ to _,_⊨PNF_) renaming (_≡_ to _≡PNF_)

private
  variable
    ℓ : Level

_≡_ : ∀ {n} → QLTL n → PNF n → Set₁
ϕ₁ ≡ ϕ₂ = ∀ {A} {σ : CounterpartTrace A} {μ} → (μ , σ ⊨QLTL ϕ₁ → μ , σ ⊨PNF ϕ₂) × (μ , σ ⊨PNF ϕ₂ → μ , σ ⊨QLTL ϕ₁)

interleaved mutual

  ^¬ : ∀ {n} → QLTL n → PNF n
  ^  : ∀ {n} → QLTL n → PNF n

  ^ true        = true
  ^ (! ϕ)       = ^¬ ϕ
  ^ (∃<> ϕ)     = ∃<> ^ ϕ
  ^ (◯∃ ϕ)      = ◯∃ ^ ϕ
  ^ (ϕ₁ ∨ ϕ₂)   = ^ ϕ₁ ∨ ^ ϕ₂
  ^ (ϕ₁ U∃ ϕ₂)  = ^ ϕ₁ U∃ ^ ϕ₂
  ^ (ϕ₁ W∃ ϕ₂)  = ^ ϕ₁ W∃ ^ ϕ₂

  ^¬ true       = false
  ^¬ (! ϕ)      = ^ ϕ
  ^¬ (∃<> ϕ)    = ∀<> (^¬ ϕ)
  ^¬ (◯∃ ϕ)     = ◯∀ (^¬ ϕ)
  ^¬ (ϕ₁ ∨ ϕ₂)  = ^¬ ϕ₁ ∧ ^¬ ϕ₂
  ^¬ (ϕ₁ U∃ ϕ₂) = (^¬ ϕ₂) W∀ (^¬ ϕ₁ ∧ ^¬ ϕ₂)
  ^¬ (ϕ₁ W∃ ϕ₂) = (^¬ ϕ₂) U∀ (^¬ ϕ₁ ∧ ^¬ ϕ₂)

interleaved mutual

  ^-equivalence : ∀ {n} (ϕ : QLTL n) →     ϕ ≡ ^ ϕ
  ^¬-negation   : ∀ {n} (ϕ : QLTL n) → (! ϕ) ≡ ^¬ ϕ

  ^-equivalence (! ϕ) = ^¬-negation ϕ
  ^-equivalence true = (λ x → tt) , (λ x → tt)
  ^-equivalence (ϕ₁ ∨ ϕ₂) = [ inj₁ ∘ proj₁ (^-equivalence ϕ₁) , inj₂ ∘ proj₁ (^-equivalence ϕ₂) ]
                          , [ inj₁ ∘ proj₂ (^-equivalence ϕ₁) , inj₂ ∘ proj₂ (^-equivalence ϕ₂) ]
  ^-equivalence (∃<> ϕ) = (λ (s , p) → s , proj₁ (^-equivalence ϕ) p)
                        , (λ (s , p) → s , proj₂ (^-equivalence ϕ) p)
  ^-equivalence (◯∃ ϕ) {σ = σ} {μ = μ} = (λ x → imply∃ {x = ↑ (C≤ 1 σ) μ} (proj₁ (^-equivalence ϕ)) x)
                                        , (λ x → imply∃ {x = ↑ (C≤ 1 σ) μ} (proj₂ (^-equivalence ϕ)) x)
  ^-equivalence (ϕ₁ U∃ ϕ₂) {σ = σ} {μ = μ} = congUntil (λ {i} → imply∃ {x = ↑ (C≤ i σ) μ} (proj₁ (^-equivalence ϕ₁)))
                                                        (λ {i} → imply∃ {x = ↑ (C≤ i σ) μ} (proj₁ (^-equivalence ϕ₂)))
                                            , congUntil (λ {i} → imply∃ {x = ↑ (C≤ i σ) μ} (proj₂ (^-equivalence ϕ₁)))
                                                        (λ {i} → imply∃ {x = ↑ (C≤ i σ) μ} (proj₂ (^-equivalence ϕ₂)))
  ^-equivalence (ϕ₁ W∃ ϕ₂)  {σ = σ} {μ = μ} = congWeakUntil (λ {i} → imply∃ {x = ↑ (C≤ i σ) μ} (proj₁ (^-equivalence ϕ₁)))
                                                            (λ {i} → imply∃ {x = ↑ (C≤ i σ) μ} (proj₁ (^-equivalence ϕ₂)))
                                            , congWeakUntil (λ {i} → imply∃ {x = ↑ (C≤ i σ) μ} (proj₂ (^-equivalence ϕ₁)))
                                                            (λ {i} → imply∃ {x = ↑ (C≤ i σ) μ} (proj₂ (^-equivalence ϕ₂)))

  ^¬-negation true = (λ x → x tt) , (λ x x₁ → x)
  ^¬-negation (! ϕ) {σ = σ} {μ = μ} with ^-equivalence ϕ {σ = σ} {μ = μ}
  ... | ⇒ , ⇐ = (λ x → ⇒ (DNE x)) , (λ x → λ z → z (⇐ x))
  ^¬-negation (ϕ₁ U∃ ϕ₂) {σ = σ} {μ = μ} =
        (λ x → congWeakUntil (λ {i} → imply∀ {x = ↑ (C≤ i σ) μ} (proj₁ (^¬-negation ϕ₂)) ∘ (¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ}))
                            (λ {i} (p1 , p2) → conjunct∀ {x = ↑ (C≤ i σ) μ} (imply∀ {x = ↑ (C≤ i σ) μ} (proj₁ (^¬-negation ϕ₁)) (¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ} p1))
                                                                            (imply∀ {x = ↑ (C≤ i σ) μ} (proj₁ (^¬-negation ϕ₂)) (¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ} p2)))
                            (¬until→weakUntil x))
    ,  (λ x → ¬until←weakUntil (congWeakUntil (λ {i} → ¬∃C←∀C¬ {x = ↑ (C≤ i σ) μ} ∘ imply∀ {x = ↑ (C≤ i σ) μ} (proj₂ (^¬-negation ϕ₂)))
                                                (λ {i} x → let a , b = (disjunct∀ {x = ↑ (C≤ i σ) μ} x) in
                                                    (¬∃C←∀C¬ {x = ↑ (C≤ i σ) μ} (imply∀ {x = ↑ (C≤ i σ) μ} (proj₂ (^¬-negation ϕ₁)) a))
                                                  , (¬∃C←∀C¬ {x = ↑ (C≤ i σ) μ} (imply∀ {x = ↑ (C≤ i σ) μ} (proj₂ (^¬-negation ϕ₂)) b)))
                                                x))
  ^¬-negation (ϕ₁ W∃ ϕ₂) {σ = σ} {μ = μ} =
        (λ x → congUntil (λ {i} → imply∀ {x = ↑ (C≤ i σ) μ} (proj₁ (^¬-negation ϕ₂)) ∘ (¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ}))
                            (λ {i} (p1 , p2) → conjunct∀ {x = ↑ (C≤ i σ) μ} (imply∀ {x = ↑ (C≤ i σ) μ} (proj₁ (^¬-negation ϕ₁)) (¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ} p1))
                                                                            (imply∀ {x = ↑ (C≤ i σ) μ} (proj₁ (^¬-negation ϕ₂)) (¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ} p2)))
                            (¬weakUntil→until x))
      , (λ x → ¬weakUntil←until (congUntil (λ {i} → ¬∃C←∀C¬ {x = ↑ (C≤ i σ) μ} ∘ imply∀ {x = ↑ (C≤ i σ) μ} (proj₂ (^¬-negation ϕ₂)))
                                                (λ {i} x → let a , b = (disjunct∀ {x = ↑ (C≤ i σ) μ} x) in
                                                    (¬∃C←∀C¬ {x = ↑ (C≤ i σ) μ} (imply∀ {x = ↑ (C≤ i σ) μ} (proj₂ (^¬-negation ϕ₁)) a))
                                                  , (¬∃C←∀C¬ {x = ↑ (C≤ i σ) μ} (imply∀ {x = ↑ (C≤ i σ) μ} (proj₂ (^¬-negation ϕ₂)) b)))
                                                x))
  ^¬-negation (ϕ₁ ∨ ϕ₂) = (λ x → let a , b = ¬⊎→¬×¬ x in proj₁ (^¬-negation ϕ₁) a , proj₁ (^¬-negation ϕ₂) b)
                        , λ { (a , b) (inj₁ x) → proj₂ (^¬-negation ϕ₁) a x
                            ; (a , b) (inj₂ y) → proj₂ (^¬-negation ϕ₂) b y
                            }
  ^¬-negation (∃<> ϕ) = (λ x → λ i → proj₁ (^¬-negation ϕ) ((¬∃⟶∀¬ x) i))
                      , (λ x → λ (a , b) → (proj₂ (^¬-negation ϕ)) (x a) b)
  ^¬-negation (◯∃ ϕ){σ = σ} {μ = μ} = (imply∀ {x = ↑ (C≤ 1 σ) μ} (proj₁ (^¬-negation ϕ)) ∘ (¬∃C→∀C¬ {x = ↑ (C≤ 1 σ) μ}))
                                    , ((¬∃C←∀C¬ {x = ↑ (C≤ 1 σ) μ}) ∘ (imply∀ {x = ↑ (C≤ 1 σ) μ} (proj₂ (^¬-negation ϕ))))
