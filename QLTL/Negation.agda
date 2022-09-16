{-# OPTIONS --guardedness #-}

{-
  Negation for the temporal operators in non-extended QLTL.
-}
module QLTL.Negation where

open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Nat
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Nat.Properties using (≤⇒≤′; ≤⇒≤‴; <-transˡ; <-trans; <⇒≤; <-cmp; ≤-<-connex)

open import Counterpart
open import Predicates
open import Negation
open import QLTL

◯-negation : ∀ {n} {ϕ : QLTL n} → ! (◯ ϕ) ≣ A (! ϕ)
◯-negation = ¬∃C⟶∀C¬ , ¬∃C←∀C¬

U-negation : ∀ {n} {ϕ₁ ϕ₂ : QLTL n} → ! (ϕ₁ U ϕ₂) ≣ ! ϕ₂ T (! ϕ₁ ∧ ! ϕ₂)
U-negation =
  (λ x → congWeakUntil ¬∃C⟶∀C¬
                       ((λ { (a , b) → ∀→∩ (¬∃C⟶∀C¬ a) (¬∃C⟶∀C¬ b) }))
                       (¬until→weakUntil x)) ,
  (λ x → ¬until←weakUntil (congWeakUntil ¬∃C←∀C¬
                                         (λ x → let a , b = ∀←∩ x in ¬∃C←∀C¬ a , ¬∃C←∀C¬ b)
                                         x))

T-negation : ∀ {n} {ϕ₁ ϕ₂ : QLTL n} → ! (ϕ₁ T ϕ₂) ≣ ! ϕ₂ UD (! ϕ₁)
T-negation {n} {ϕ₁} {ϕ₂} {σ = σ} {μ = μ} =
    (λ x → congUntil ¬∀C⟶∃C¬
                     (λ (a , b) → ¬∀C⟶∃C¬ b , ¬∀C⟶∃C¬ a) 
                     (¬weakUntil→until x))
    , λ x → ¬weakUntil←until (congUntil ¬∀C←∃C¬
                                        (λ (a , b) → ¬∀C←∃C¬ b , ¬∀C←∃C¬ a)
                                        x)

UD-negation : ∀ {n} {ϕ₁ ϕ₂ : QLTL n} → ! (ϕ₁ UD ϕ₂) ≣ (! ϕ₁ ∨ ! ϕ₂) TD (! ϕ₁)
UD-negation {n} {ϕ₁} {ϕ₂} {σ = σ} {μ = μ} =
    (λ x → congWeakUntil (λ x₁ → [ (λ x₃ → λ c x₄ → inj₁ (¬∃C⟶∀C¬ x₃ c x₄)) 
                                 , (λ x₃ → λ c x₄ → inj₂ (¬∃C⟶∀C¬ x₃ c x₄)) 
                                 ] (¬×→¬⊎¬ x₁)) 
                         (λ (a , b) → 
                                 [ (λ x₁ → inj₂ (¬∃C⟶∀C¬ x₁)) 
                                 , (λ x₁ → inj₁ λ c x₃ → inj₁ (¬∃C⟶∀C¬ a c x₃))
                                 ] (¬×→¬⊎¬ b)) (¬until→weakUntil x))
    , λ x → ¬until←weakUntil (congWeakUntil (λ x₁ → ¬×←¬⊎¬ {!   !}) {!   !} x)


TD-negation : ∀ {n} {ϕ₁ ϕ₂ : QLTL n} → ! (ϕ₁ TD ϕ₂) ≣ ! ϕ₂ U (! ϕ₁ ∧ ! ϕ₂)
TD-negation {n} {ϕ₁} {ϕ₂} {σ = σ} {μ = μ} =
    (λ x → congUntil {!   !} {!   !}
                     (¬weakUntil→until x))
    , λ x → ¬weakUntil←until (congUntil {!   !} {!   !}
                                        x)
{-

                                        ¬×→¬⊎¬
                                        ¬×←¬⊎¬
                                        ¬∃C⟶∀C¬
-}


T-negation′ : ∀ {n} {ϕ₁ ϕ₂ : QLTL n} → ! (ϕ₁ T ϕ₂) ≣ ! ϕ₂ U (! ϕ₁ ∧ ! ϕ₂)
T-negation′ {n} {ϕ₁} {ϕ₂} {σ = σ} {μ = μ} =
    (λ x → congUntil ¬∀C⟶∃C¬ --¬∀C⟶∃C¬
                     (λ (a , b) → {!   !}) --(λ (a , b) → {!   !})
                     (¬weakUntil→until x))
    , λ x → ¬weakUntil←until (congUntil ¬∀C←∃C¬ --¬∀C←∃C¬
                                        (λ (μ , c , μ2 , μ1) → ¬∀C←∃C¬ (μ , c , μ2) , ¬∀C←∃C¬ (μ , c , μ1))
                                        x)
{-
T-negation2 : ∀ {n} {ϕ₁ ϕ₂ : QLTL n} → ! (ϕ₁ T ϕ₂) ≣ ! ϕ₂ UR (! ϕ₁)
T-negation2 {n} {ϕ₁} {ϕ₂} {σ = σ} {μ = μ} =
    (λ x → congUntil ¬∀C⟶∃C¬ --¬∀C⟶∃C¬
                     (λ (a , b) → {!   !}) --(λ (a , b) → {!   !})
                     (¬weakUntil→until x))
    , λ x → ¬weakUntil←until (congUntil ¬∀C←∃C¬ --¬∀C←∃C¬
                                        (λ (μ , c , μ2 , μ1) → ¬∀C←∃C¬ (μ , c , μ1) , ¬∀C←∃C¬ (μ , c , μ2))
                                        x)

U-negation′ : ∀ {n} {ϕ₁ ϕ₂ : QLTL n} → ! (ϕ₁ U ϕ₂) ≣ ! ϕ₂ M ! ϕ₁
U-negation′ =
  (λ x → congWeakUntil ¬∃C⟶∀C¬
                       (λ { (a , b) → ∀→∩ (¬∃C⟶∀C¬ b) (¬∃C⟶∀C¬ a) })
                       (¬until→weakUntil x)) ,
  (λ x → ¬until←weakUntil (congWeakUntil ¬∃C←∀C¬ 
                                         (λ x → let a , b = ∀←∩ x in ¬∃C←∀C¬ b , ¬∃C←∀C¬ a)
                                         x))
-}
{-  where

    ⇒ : σ , μ ⊨ ! (ϕ₁ T ϕ₂) → σ , μ ⊨ ! ϕ₂ UR (! ϕ₁)
    ⇒ nu with wu¬wul nu
    ... | then , (n , n¬∀1) with strong-prefix-lem {λ i → ∀C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₁)}
    ... | inj₂ i∀1 = ⊥-elim (n¬∀1 (i∀1 n))
    ... | inj₁ (m , <m∀1 , m¬∀1) = m , (λ i x → {!   !}) , {!   !} --¬∀C⟶∃C¬ m¬∀1
    
    -- ... | n , <n¬∀ϕ₂ , n¬∀ϕ₁ , n¬∀ϕ₂ = n , (λ i x₁ → ¬∀C⟶∃C¬ (<n¬∀ϕ₂ i x₁)) , {!   !}

    ⇐ : σ , μ ⊨ ! ϕ₂ UR (! ϕ₁) → σ , μ ⊨ ! (ϕ₁ T ϕ₂)
    ⇐ x = {!   !}
-}
{-
U-negation′ : ∀ {n} {ϕ₁ ϕ₂ : QLTL n} → ! (ϕ₁ U ϕ₂) ≣ ! ϕ₂ M ! ϕ₁
U-negation′ =
  (λ x → congWeakUntil ¬∃C⟶∀C¬
                       (λ { (a , b) → ∀→∩ (¬∃C⟶∀C¬ b) (¬∃C⟶∀C¬ a) })
                       (¬until→weakUntil x)) ,
  (λ x → ¬until←weakUntil (congWeakUntil ¬∃C←∀C¬ 
                                         (λ x → let a , b = ∀←∩ x in ¬∃C←∀C¬ b , ¬∃C←∀C¬ a)
                                         x))

T-negation : ∀ {n} {ϕ₁ ϕ₂ : QLTL n} → ! (ϕ₁ M ϕ₂) ≣ ! ϕ₂ UR (! ϕ₁)
T-negation {n} {ϕ₁} {ϕ₂} {σ = σ} {μ = μ} = ⇒ , ⇐
  where

    ⇒ : σ , μ ⊨ ! (ϕ₁ M ϕ₂) → σ , μ ⊨ ! ϕ₂ UR (! ϕ₁)
    ⇒ notM with wu¬wul notM
    ... | ¬AULB , n , n¬∀ϕ₁ with strong-prefix-lem {(λ i → ∀C∈ ↑ (C≤ i σ) μ ⇒ (s i σ ,_⊨ ϕ₁))}
    ... | inj₂ y = ⊥-elim (n¬∀ϕ₁ (y n))
    ... | inj₁ (m , <m∀ϕ₁ , m¬∀ϕ₁) with ¬∀C⟶∃C¬ m¬∀ϕ₁ | ¬∀C⟶∃C¬ n¬∀ϕ₁
    ... | μm , cm , ¬ϕ₁m | μn , cn , ¬ϕ₁n =
         m , (λ i x → {! ¬AULB  !}) 
          --let wwe , r = ¬∀⟶∃¬ (¬AULB i λ i₁ x₁ c₁ x₂ → ∀ϕ₁<m i₁ (<-trans x₁ x) c₁ x₂) in
             --                      wwe , proj₁ (¬∀⟶∃¬ r) , λ x₁ → ¬An (∀ϕ₁<m n {!   !}))
           , μm , cm , (λ x → ¬AULB {!   !}  {!   !} {!   !}) , ¬ϕ₁m
                    

    ⇐ : σ , μ ⊨ ! ϕ₂ UR (! ϕ₁) → σ , μ ⊨ ! (ϕ₁ M ϕ₂)
    ⇐ (n , <n∃¬ϕ₂ , μn , cn , n¬ϕ₁) (inj₂ y) = {!   !} --n¬ϕ₁ (y n μn cn)
    ⇐ (n , <n∃¬ϕ₂ , μn , cn , n¬ϕ₁) (inj₁ (m , <m∀ϕ₁ , m∀ϕ₁ϕ₂)) with <-cmp m n
    ... | tri< m<n _ _ = proj₂ (proj₂ (<n∃¬ϕ₂ {!   !} (<-trans {!   !} m<n))) {!   !}
    ... | tri≈ _ refl _ = {!   !} --n¬ϕ₁ (proj₁ (m∀ϕ₁ϕ₂ μn cn))
    ... | tri> _ _ n<m = {!   !}
-}
{-

  (λ x → congUntil (λ x₁ → let a , b , c = ¬∀C⟶∃C¬ x₁ in a , (b , (λ x₃ → c ({!   !} , x₃))))
                   (λ { (a , b) → {!   !} })
                   (¬weakUntil→until x)) ,
  (λ x → ¬weakUntil←until (congUntil (λ x₁ → λ x₃ → ¬∀C←∃C¬ x₁ {!   !}) --¬∃C←∀C¬ 
                                     {!   !} --(λ x → let a , b = ∀←∩ x in ¬∃C←∀C¬ b , ¬∃C←∀C¬ a) 
                                     x))
-}
{-
T-negation : ∀ {n} {ϕ₁ ϕ₂ : QLTL n} → ! (ϕ₁ T ϕ₂) ≣ ! ϕ₂ U (! ϕ₂)
T-negation =
  (λ x → congUntil {!   !} --(λ x → let a , b , c = ¬∀C⟶∃C¬ x in a , b , λ r → c (inj₂ r)) --¬∃C⟶∀C¬
                   {!   !} --(λ { (a , b) → ∀→∩ (¬∃C⟶∀C¬ b) (¬∃C⟶∀C¬ a) })
                   (¬weakUntil→until x)) ,
  (λ x → ¬weakUntil←until (congUntil (λ x₁ → λ x₃ → ¬∀C←∃C¬ x₁ {!   !}) --¬∃C←∀C¬ 
                                     {!   !} --(λ x → let a , b = ∀←∩ x in ¬∃C←∀C¬ b , ¬∃C←∀C¬ a) 
                                     x))
-}
{-
F-negation : ∀ {n} {ϕ₁ ϕ₂ : QLTL n} → ! (ϕ₁ F ϕ₂) ≣ ! ϕ₂ R (! ϕ₁)
F-negation =
  (λ x → congWeakUntil {!   !} --(λ x₁ → let a , b , c = ¬∀C⟶∃C¬ x₁ in a , b , {!   !}) 
                       {!   !} --(λ (a , b) → ¬∀C⟶∃C¬ a)
                       (¬until→weakUntil x)) ,
  (λ x → ¬until←weakUntil (congWeakUntil {!   !} --(λ k x₃ → ¬∀C←∃C¬ k λ c z → proj₂ (x₃ c z))
                                         {!   !} --(λ x₁ → ¬∀C←∃C¬ x₁ , λ x₃ → ¬∀C←∃C¬ x₁ λ c z → proj₁ (x₃ c z)) 
                                         x))

W-negation : ∀ {n} {ϕ₁ ϕ₂ : QLTL n} → ! (ϕ₁ R ϕ₂) ≣ ! ϕ₂ F (! ϕ₁)
W-negation =
  (λ x → congUntil {! ¬∃C⟶∀C¬  !} --¬∃C⟶∀C¬
                   {!   !} --(λ { (a , b) → ∀→∩ (¬∃C⟶∀C¬ b) (¬∃C⟶∀C¬ a) })
                   (¬weakUntil→until x)) ,
  (λ x → ¬weakUntil←until (congUntil {!   !} --¬∃C←∀C¬ 
                                     {!   !} --(λ x → let a , b = ∀←∩ x in ¬∃C←∀C¬ b , ¬∃C←∀C¬ a) 
                                     x))
                                     -}   