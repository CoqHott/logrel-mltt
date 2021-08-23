{-# OPTIONS --safe #-}

module Definition.Conversion.Universe where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.Conversion
open import Definition.Conversion.Reduction
open import Definition.Conversion.Lift

import Tools.PropositionalEquality as PE


-- Algorithmic equality of terms in WHNF of type U are equal as types.
univConv↓ : ∀ {A B r Γ l}
          → Γ ⊢ A [conv↓] B ∷ Univ r l ^ next l
          → Γ ⊢ A [conv↓] B ^ [ r , ι l ]
univConv↓ X = univ X

-- Algorithmic equality of terms of type U are equal as types.
univConv↑ : ∀ {A B r Γ l}
      → Γ ⊢ A [conv↑] B ∷ Univ r l ^ next l
      → Γ ⊢ A [conv↑] B ^ [ r , ι l ]
univConv↑ ([↑]ₜ B₁ t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
      rewrite PE.sym (whnfRed* D Uₙ) =
  reductionConv↑ (univ* d) (univ* d′) whnft′ whnfu′ (liftConv (univConv↓ t<>u))

