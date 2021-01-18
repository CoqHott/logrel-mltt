{-# OPTIONS --without-K --safe #-}

module Definition.Conversion.Reduction where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Conversion


-- Weak head expansion of algorithmic equality of types.
reductionConv↑ : ∀ {A A′ B B′ r Γ}
               → Γ ⊢ A ⇒* A′ ^ r
               → Γ ⊢ B ⇒* B′ ^ r
               → Whnf A′
               → Whnf B′
               → Γ ⊢ A′ [conv↑] B′ ^ r
               → Γ ⊢ A  [conv↑] B ^ r
reductionConv↑ x x₁ x₂ x₃ ([↑] A″ B″ D D′ whnfA′ whnfB′ A′<>B′)
              rewrite whnfRed* D x₂ | whnfRed* D′ x₃ =
  [↑] A″ B″ x x₁ whnfA′ whnfB′ A′<>B′

-- Weak head expansion of algorithmic equality of terms.
reductionConv↑Term : ∀ {t t′ u u′ A B Γ}
                   → Γ ⊢ A ⇒* B ^ !
                   → Γ ⊢ t ⇒* t′ ∷ B 
                   → Γ ⊢ u ⇒* u′ ∷ B 
                   → Whnf B
                   → Whnf t′
                   → Whnf u′
                   → Γ ⊢ t′ [conv↑] u′ ∷ B
                   → Γ ⊢ t  [conv↑] u  ∷ A
reductionConv↑Term x x₁ x₂ x₃ x₄ x₅
                   ([↑]ₜ B₁ t″ u″ D d d′ whnfB whnft′ whnfu′ t<>u)
                   rewrite whnfRed* D x₃ | whnfRed*Term d x₄ | whnfRed*Term d′ x₅ =
  [↑]ₜ B₁ t″ u″ x x₁ x₂ whnfB whnft′ whnfu′ t<>u
