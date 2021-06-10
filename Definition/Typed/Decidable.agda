{-# OPTIONS --without-K  #-}

module Definition.Typed.Decidable where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Conversion
open import Definition.Conversion.Decidable
open import Definition.Conversion.Soundness
open import Definition.Conversion.Stability
open import Definition.Conversion.Consequences.Completeness

open import Tools.Nullary


-- Decidability of conversion of well-formed types
dec : ∀ {A B s Γ} → Γ ⊢ A ⦂ s → Γ ⊢ B ⦂ s → Dec (Γ ⊢ A ≡ B ⦂ s)
dec ⊢A ⊢B =
  let ⊢Γ≡Γ = reflConEq (wf ⊢A)
  in  map soundnessConv↑ completeEq
          (decConv↑ ⊢Γ≡Γ (completeEq (refl ⊢A)) (completeEq (refl ⊢B)))

-- Decidability of conversion of well-formed terms
decTerm : ∀ {t u A s Γ} → Γ ⊢ t ∷ A ⦂ s → Γ ⊢ u ∷ A ⦂ s → Dec (Γ ⊢ t ≡ u ∷ A ⦂ s)
decTerm ⊢t ⊢u =
  let ⊢Γ≡Γ = reflConEq (wfTerm ⊢t)
  in  map soundnessConv↑Term completeEqTerm
          (decConv↑Term ⊢Γ≡Γ (completeEqTerm (refl ⊢t)) (completeEqTerm (refl ⊢u)))
