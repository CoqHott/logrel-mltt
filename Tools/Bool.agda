-- The boolean numbers.

{-# OPTIONS --without-K --safe #-}

module Tools.Bool where

open import Tools.PropositionalEquality
open import Tools.Nullary

-- We reexport Agda's built-in type of booleans.

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Bool using (Bool) public

infix 4 _≟_

-- Predecessor, cutting off at 0.

neg : Bool → Bool
neg false = true
neg true = false

-- Decision of number equality.

_≟_ : (m n : Bool) → Dec (m ≡ n)
true  ≟ true   = yes refl
false ≟ false  = yes refl
true  ≟ false  = no λ()
false ≟ true   = no λ()

true_not_false : true ≢ false
true_not_false = λ ()

false_not_true : false ≢ true
false_not_true = λ ()
