{-# OPTIONS --guardedness #-}

{-
  Negation for the temporal operators in full QLTL.
-}
module Relation.QLTL.Full.ExpansionLaws where

open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Nat
open import Data.Unit
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality using (refl; subst)
open import Data.Nat.Properties using (≤⇒≤′; ≤⇒≤‴; <-transˡ; <-trans; <⇒≤; <-cmp; ≤-<-connex)
open import Data.Vec using (replicate)
open import Relation.Nullary 

open import Relation.Counterpart
open import Relation.QLTL.Full.Semantics
open import Predicates
open import Negation
open import VecT

_≣_ : ∀ {n} → QLTL-Full n → QLTL-Full n → Set₁
ϕ₁ ≣ ϕ₂ = ∀ {A} {σ : CounterpartTrace A} {μ} → (σ , μ ⊨ ϕ₁ → σ , μ ⊨ ϕ₂) × (σ , μ ⊨ ϕ₂ → σ , μ ⊨ ϕ₁)

U-expansion-law : ∀ {n} {ϕ₁ ϕ₂ : QLTL-Full n} → ϕ₁ U ϕ₂ ≣ ϕ₂ ∨ (ϕ₁ ∧ ◯ (ϕ₁ U ϕ₂))
U-expansion-law {_} {ϕ₁} {ϕ₂} {_} {σ} {μ} = ⇒ , ⇐
  where
  {-
    lemma : (r : σ , μ ⊨ ϕ₁ U ϕ₂)
          → ∀ i → i < (proj₁ r) 
                → ∃[ μ ] VecT.zip (C≤ i σ) μ 
    lemma = ?-}

    ⇒ : σ , μ ⊨ ϕ₁ U ϕ₂ → σ , μ ⊨ ϕ₂ ∨ (ϕ₁ ∧ ◯ (ϕ₁ U ϕ₂))
    ⇒ (zero , ϕ₁<i , μn , cn , ϕ₂n) rewrite zip-ext cn = inj₁ ϕ₂n
    ⇒ (suc n , (ϕ₁<i , μn , μc , ϕ₂n)) with ϕ₁<i 0 (_≤_.s≤s _≤_.z≤n)
    ... | μ′ , μ≡μ′ , μ′ϕ₁ rewrite zip-ext μ≡μ′ =
          inj₂ (μ′ϕ₁ , let μ₁ , μμ₁ , μ₁μc = zip-rel-decomp μc in
                       μ₁ , zip-id-right {σ = σ} μμ₁ , n , 
                          ({!   !}) , μn , μ₁μc , ϕ₂n)

    ⇐ : σ , μ ⊨ ϕ₂ ∨ (ϕ₁ ∧ ◯ (ϕ₁ U ϕ₂)) → σ , μ ⊨ ϕ₁ U ϕ₂
    ⇐ (inj₁ x) = zero , (λ i ()) , μ , zip-id , x
    ⇐ (inj₂ (ϕ₁<i , μn , μc , r , b , c , k , l)) = suc r 
              , (λ { zero (s≤s z≤n) → μ , zip-id , ϕ₁<i
                   ; (suc i) (s≤s x) →  let m1 , m2 , m3 = b i x 
                                         in m1 , zip-rel-comp (zip-id-right-inv {σ = σ} μc) m2 , m3 }) 
              , c , zip-rel-comp (zip-id-right-inv {σ = σ} μc) k , l


F-expansion-law : ∀ {n} {ϕ₁ ϕ₂ : QLTL-Full n} → ϕ₁ F ϕ₂ ≣ ϕ₂ ∨ (ϕ₁ ∧ A (ϕ₁ F ϕ₂))
F-expansion-law {_} {ϕ₁} {ϕ₂} {_} {σ} {μ} = ⇒ , ⇐
  where
    ⇒ : σ , μ ⊨ ϕ₁ F ϕ₂ → σ , μ ⊨ ϕ₂ ∨ (ϕ₁ ∧ A (ϕ₁ F ϕ₂))
    ⇒ (zero , ϕ₁<i , f) = inj₁ (f μ zip-id)
    ⇒ (suc n , (ϕ₁<i , f)) = inj₂ (ϕ₁<i zero (s≤s z≤n) μ zip-id , 
          λ c x → n , (λ i x₁ c₁ x₂ → ϕ₁<i (suc i) (s≤s x₁) c₁ (zip-rel-comp (zip-id-right-inv {σ = σ} x) x₂)) 
                    , λ c₁ x₁ → f c₁ (zip-rel-comp (zip-id-right-inv {σ = σ} x) x₁))

    ⇐ : σ , μ ⊨ ϕ₂ ∨ (ϕ₁ ∧ A (ϕ₁ F ϕ₂)) → σ , μ ⊨ ϕ₁ F ϕ₂
    ⇐ (inj₁ x) = zero , ((λ i ()) , (λ c x₁ → subst (λ p → σ , p ⊨ ϕ₂) (zip-ext x₁) x))
    ⇐ (inj₂ (μϕ₂ , f)) with LEM {_} {Σ (mapT (λ _ → wi 1 σ) (replicate tt)) (λ k → VecT.zip (C≤ 1 σ) μ k)}
    ... | no n = suc zero , (λ { zero (s≤s z≤n) c x₁ → subst (λ p → σ , p ⊨ ϕ₁) (zip-ext x₁) μϕ₂ }) 
                          , λ c x → ⊥-elim (n (c , {!   !}))
    ... | yes (m , c) with f m c
    ... | n , nf , mf = suc n , (λ { zero (s≤s z≤n) c₁ x₁ → subst (λ p → σ , p ⊨ ϕ₁) (zip-ext x₁) μϕ₂
                                   ; (suc i) (s≤s x) c₁ x₁ → let z , z2 , z3 = zip-rel-decomp x₁ in nf i x c₁ {!   !} }) 
                               , λ c₁ x → let w , r , z = zip-rel-decomp x in mf c₁ {!   !}
    --f m c in
    --                   n , (λ { i x c₁ x₁ → {! nf ? ? ? ?  !} }) 
    --                     , λ c₁ x → {! n !}
    {-
      ⇒ : σ , μ ⊨ ϕ₁ U ϕ₂ → σ , μ ⊨ ϕ₂ ∨ (ϕ₁ ∧ ◯ (ϕ₁ U ϕ₂))
      ⇒ (zero , ϕ₁<i , ϕ₂n) rewrite lift-unit {μ = μ} = inj₁ ϕ₂n
      ⇒ (suc n , (ϕ₁<i , ϕ₂n)) with ϕ₁<i 0 (_≤_.s≤s _≤_.z≤n)
      ... | base rewrite lift-unit {μ = μ} with ↑ (C≤ 1 σ) μ | inspect (↑ (C≤ 1 σ)) μ
      ... | nothing | ≣: eq rewrite ↑-ext-cong {μ = μ} (monad-law1 {f = rel σ})
                                  | ↑-homomorphism {f = rel σ} {g = C≤ n (tail σ)} μ
                                  | eq = ⊥-elim ϕ₂n
      ... | just μ′ | ≣: eq = inj₂ (base , n ,
                                          (λ i x → subst (λ p → ∃C∈ p ⇒ _) (sym (switch-tail-suc {σ = σ} {n = i} {μ = μ} eq)) (ϕ₁<i (suc i) (_≤_.s≤s x)))
                                          , subst (λ p → ∃C∈ p ⇒ _) (sym (switch-tail-suc {σ = σ} {n = n} {μ = μ} eq)) ϕ₂n)

      ⇐ : σ , μ ⊨ ϕ₂ ∨ (ϕ₁ ∧ ◯ (ϕ₁ U ϕ₂)) → σ , μ ⊨ ϕ₁ U ϕ₂
      ⇐ (inj₁ x) = 0 , (λ i ()) , a
        where a : ∃C∈ ↑ just μ ⇒ (σ ,_⊨ ϕ₂)
              a rewrite lift-unit {μ = μ} = x
      ⇐ (inj₂ (μ|ϕ₁ , ◯U)) with ↑ (C≤ 1 σ) μ | inspect (↑ (C≤ 1 σ)) μ
      ⇐ (inj₂ (μ|ϕ₁ , n , 1<ϕ₁<i , n|ϕ₂)) | just x | ≣: eq =
        suc n , (λ { zero x → lift-exists {μ = μ} μ|ϕ₁
                  ; (suc i) (_≤_.s≤s x) → subst (λ p → ∃C∈ p ⇒ _) (switch-tail-suc {σ = σ} {n = i} {μ = μ} eq) (1<ϕ₁<i i x) })
              , subst (λ p → ∃C∈ p ⇒ _) (switch-tail-suc {σ = σ} {n = n} {μ = μ} eq) n|ϕ₂
  -}  