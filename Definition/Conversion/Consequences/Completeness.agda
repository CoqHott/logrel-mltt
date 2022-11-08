-- {-# OPTIONS --safe #-}
{-# OPTIONS --allow-unsolved-metas #-}

module Definition.Conversion.Consequences.Completeness where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Conversion
open import Definition.Typed.Properties

open import Definition.Conversion.EqRelInstance
open import Definition.Conversion.Inversion

open import Definition.LogicalRelation
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Escape
open import Definition.LogicalRelation.Fundamental

open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Empty

-- Algorithmic equality is derivable from judgemental equality of types.
completeEq : ∀ {A B r Γ} → Γ ⊢ A ≡ B ^ r → Γ ⊢ A [conv↑] B ^ r
completeEq A≡B =
  let [Γ] , [A] , [B] , [A≡B] = fundamentalEq A≡B
  in  escapeEqᵛ [Γ] [A] [A≡B]

-- Algorithmic equality is derivable from judgemental equality of terms.
completeEqTerm : ∀ {t u A r Γ} → Γ ⊢ t ≡ u ∷ A ^ r → Γ ⊢ t [genconv↑] u ∷ A ^ r
completeEqTerm t≡u =
  let [Γ] , modelsTermEq [A] [t] [u] [t≡u] = fundamentalTermEq t≡u
  in  escapeEqTermᵛ [Γ] [A] [t≡u]

completeEqTerm↓ : ∀ {t u A l Γ} → Whnf A → Whnf t → Whnf u → Γ ⊢ t ≡ u ∷ A ^ [ ! , l ] → Γ ⊢ t [conv↓] u ∷ A ^ l
completeEqTerm↓ whnfA whnft whnfu t≡u = whnfconv↑conv↓ whnfA whnft whnfu (completeEqTerm t≡u)

completeEqNeutral : ∀ {t u l' l Γ} → Neutral t → Neutral u →  Γ ⊢ t ≡ u ∷ U l' ^  [ ! , l ] → Γ ⊢ t ~ u ↓! U l' ^ l
completeEqNeutral net neu t≡u = neutralconv↓ net neu (completeEqTerm↓ Uₙ (ne net) (ne neu) t≡u)
