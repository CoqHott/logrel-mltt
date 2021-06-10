{-# OPTIONS --without-K  #-}

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
univConv↓ : ∀ {A B s Γ}
          → Γ ⊢ A [conv↓] B ∷ Univ s ⦂ 𝕥y
          → Γ ⊢ A [conv↓] B ⦂ s
univConv↓ (ne-ins t u () x)
univConv↓ (univ x x₁ x₂) = x₂

-- Algorithmic equality of terms of type U are equal as types.
univConv↑ : ∀ {A B s Γ}
      → Γ ⊢ A [conv↑] B ∷ Univ s ⦂ 𝕥y
      → Γ ⊢ A [conv↑] B ⦂ s
univConv↑ ([↑]ₜ B₁ t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
      rewrite PE.sym (whnfRed* D Uₙ) =
  reductionConv↑ (univ* d) (univ* d′) whnft′ whnfu′ (liftConv (univConv↓ t<>u))
