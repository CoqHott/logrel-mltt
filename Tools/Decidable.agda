{-# OPTIONS --without-K  #-}

module Tools.Decidable where

open import Tools.Sum
open import Tools.PropositionalEquality as PE
open import Tools.Empty

dec : (A : Set) → Set
dec A = A ⊎ (A → ⊥)

decEq : (A : Set) → Set
decEq A = (x y : A) → dec (x PE.≡ y)

module _ {A : Set} (d : decEq A) where

  postulate hedberg : {x y : A} (e e' : x PE.≡ y) → e PE.≡ e'

  dec-eq : {x y : A} (e : x PE.≡ y) → d x y PE.≡ inj₁ e
  dec-eq {x} {y} e with d x y
  ... | inj₁ e' = PE.cong inj₁ (hedberg e' e)
  ... | inj₂ f = ⊥-elim (f e)

  dec-refl : (x : A) → d x x PE.≡ inj₁ PE.refl
  dec-refl x = dec-eq PE.refl
