module VecT where

open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; _≤_; _<_)
open import Data.Fin using (Fin; zero; suc)
open import Function using ()
open import Data.Sum using (_⊎_)
open import Level using (Level; lift) renaming (suc to sucℓ)
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_; proj₁; proj₂; -,_; <_,_>)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; isEquivalence; sym; trans; cong; cong-app; cong₂)
open import Level using (lift; _⊔_; lower)

open import Data.Vec as Vec using (Vec; _∷_; [])
open import Data.Vec.Membership.Propositional using (_∈_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.List.Relation.Unary.Any using (here; there)

import Data.Unit
open import Data.Unit.Polymorphic using (⊤)
open import Data.Empty using (⊥-elim)
open import Data.Empty.Polymorphic using (⊥)

open import Relation.Binary.Construct.Composition using (_;_)
open import Relation.Binary using (REL; Rel)

pattern * = lift Data.Unit.tt
open Function using (id; _∘_; flip)

private
  variable
    n : ℕ
    ℓ ℓ′ : Level
    A B : Set ℓ
    f g : A → Set ℓ
    o : Vec A n

mapT : (A → Set ℓ) → Vec A n → Set ℓ
mapT f [] = ⊤
mapT f (x ∷ v) = f x × mapT f v

zipT : (A → B → Set ℓ) → Vec A n → Vec B n → Set ℓ
zipT f [] [] =  ⊤
zipT f (x ∷ v) (x′ ∷ v′) = f x x′ × zipT f v v′

map : (∀ {x} → f x → g x)
    → mapT f o → mapT g o
map {o = []} a * = *
map {o = _ ∷ _} a (x , v) = a x , map a v

zip : (∀ {x} → f x → g x → Set ℓ′)
    → mapT f o → mapT g o → Set ℓ′
zip {o = []} a * * =  ⊤
zip {o = _ ∷ _} a (x , v) (x′ , v′) = a x x′ × zip a v v′

lookup : (i : Fin n)
        → mapT f o
        → f (Vec.lookup o i)
lookup {o = _ ∷ _} zero (x , v) = x
lookup {o = _ ∷ _} (suc i) (x , v) = lookup i v

_[_] : mapT f o
     → (i : Fin n)
     → f (Vec.lookup o i)
v [ i ] = lookup i v

lookup-zip : ∀ {f g : A → Set ℓ} {o : Vec A n} {v : mapT f o} {v′ : mapT g o} {ρ : ∀ {x} → f x → g x → Set ℓ}
          → (i : Fin n)
          → zip ρ v v′
          → ρ (lookup i v) (lookup i v′)
lookup-zip {o = _ ∷ _} zero (x , v) = x
lookup-zip {o = _ ∷ _} (suc i) (x , v) = lookup-zip i v

zip-imply : ∀ {n} {o : Vec A n} {f g : (A → Set ℓ′)} {v : mapT f o} {v′ : mapT g o} {s t : (∀ {x} → f x → g x → Set ℓ′)}
      → (∀ {m} {x y} → s {m} x y → t {m} x y)
      → zip s v v′
      → zip t v v′
zip-imply {o = []} e * = *
zip-imply {o = _ ∷ _} e (x , v) = e x , zip-imply e v

zip-ext : ∀ {o : Vec A n} {f : (A → Set ℓ)} {v v′ : mapT f o}
        → zip _≡_ v v′
        → v ≡ v′
zip-ext {o = []} {v = *} {v′ = *} * = refl
zip-ext {o = _ ∷ _} {v = _ , _} {v′ = _ , _} (refl , v) rewrite zip-ext v = refl

zip-id : ∀ {o : Vec A n} {f : (A → Set ℓ)} {v : mapT f o}
        → zip _≡_ v v
zip-id {o = []} {v = *} = *
zip-id {o = _ ∷ _} {v = _ , v} = refl , zip-id {v = v}

map-cong : ∀ {o : Vec A n} {f g : A → Set ℓ} {v : mapT f o} {f g : (∀ {x} → f x → g x)}
          → (e : ∀ {x} σ → f {x} σ ≡ g {x} σ)
          → map f v ≡ map g v
map-cong {o = []} e = refl
map-cong {o = _ ∷ _} {v = x , v} e rewrite e x | map-cong {v = v} e = refl

map-comp : ∀ {o : Vec A n} {i j k : A → Set ℓ} {v : mapT i o} {f : (∀ {x} → j x → k x)} {g : (∀ {x} → i x → j x)}
          → map (f ∘ g) v ≡ map f (map g v)
map-comp {o = []} = refl
map-comp {o = x ∷ o} {v = _ , v} {f = f} {g = g} rewrite map-comp {v = v} {f = f} {g = g} = refl

map-id : ∀ {o : Vec A n} {f : A → Set ℓ} {v : mapT f o}
        → map id v ≡ v
map-id {o = []} = refl
map-id {o = _ ∷ _} {v = _ , v} rewrite map-id {v = v}= refl

zip-rel-decomp : ∀ {o : Vec A n} {f g h : (A → Set ℓ)} {x : mapT g o} {y : mapT h o}
        → {s : (∀ {x} → g x → f x → Set ℓ)}
        → {t : (∀ {x} → f x → h x → Set ℓ)}
        → zip (λ x y → ∃[ a ] (s x a × t a y)) x y
        → Σ[ a ∈ mapT f o ] (zip s x a × zip t a y)
zip-rel-decomp {o = []} * = * , * , *
zip-rel-decomp {o = _ ∷ _} (x , v) with zip-rel-decomp v | x
... | f , g , h | a , x , y = (a , f)
              , (x , g) , (y , h)

zip-rel-comp : ∀ {o : Vec A n} {f g h : (A → Set ℓ)} {a : mapT f o} {x : mapT g o} {y : mapT h o}
        → {s : (∀ {x} → g x → f x → Set ℓ)}
        → {t : (∀ {x} → f x → h x → Set ℓ)}
        → zip s x a → zip t a y
        → zip (λ x y → ∃[ a ] (s x a × t a y)) x y
zip-rel-comp {o = []} * * = *
zip-rel-comp {o = _ ∷ _} (x , v) (x′ , v′) = (_ , x , x′) , zip-rel-comp v v′

op : ∀ {o : Vec A n} {f g : (A → Set ℓ)} {x : mapT f o} {y : mapT g o}
    → {f : (∀ {x} → f x → g x → Set ℓ′)}
    → zip f        x y
    → zip (flip f) y x
op {o = []} * = *
op {o = _ ∷ _} (x , v) = x , (op v)