{-# OPTIONS --without-K  #-}

module Definition.Conversion.Reduction where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Conversion


-- Weak head expansion of algorithmic equality of types.
reductionConv↑ : ∀ {A A′ B B′ s Γ}
               → Γ ⊢ A ⇒* A′ ⦂ s
               → Γ ⊢ B ⇒* B′ ⦂ s
               → Whnf A′
               → Whnf B′
               → Γ ⊢ A′ [conv↑] B′ ⦂ s
               → Γ ⊢ A  [conv↑] B ⦂ s
reductionConv↑ x x₁ x₂ x₃ ([↑] A″ B″ D D′ whnfA′ whnfB′ A′<>B′)
              rewrite whnfRed* D x₂ | whnfRed* D′ x₃ =
  [↑] A″ B″ x x₁ whnfA′ whnfB′ A′<>B′

-- Weak head expansion of algorithmic equality of terms.
reductionConv↑Term : ∀ {t t′ u u′ A B s Γ}
                   → Γ ⊢ A ⇒* B ⦂ s
                   → Γ ⊢ t ⇒* t′ ∷ B ⦂ s
                   → Γ ⊢ u ⇒* u′ ∷ B ⦂ s
                   → Whnf B
                   → Whnf t′
                   → Whnf u′
                   → Γ ⊢ t′ [conv↑] u′ ∷ B ⦂ s
                   → Γ ⊢ t  [conv↑] u  ∷ A ⦂ s
reductionConv↑Term x x₁ x₂ x₃ x₄ x₅
                   ([↑]ₜ B₁ t″ u″ D d d′ whnfB whnft′ whnfu′ t<>u)
                   rewrite whnfRed* D x₃ | whnfRed*Term d x₄ | whnfRed*Term d′ x₅ =
  [↑]ₜ B₁ t″ u″ x x₁ x₂ whnfB whnft′ whnfu′ t<>u
