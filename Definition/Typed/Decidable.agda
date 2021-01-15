{-# OPTIONS --safe #-}

module Definition.Typed.Decidable where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Consequences.Syntactic
open import Definition.Conversion
open import Definition.Conversion.Decidable
open import Definition.Conversion.Soundness
open import Definition.Conversion.Stability
open import Definition.Conversion.Consequences.Completeness

open import Tools.Nullary


-- Decidability of conversion of well-formed types
dec : ∀ {A B r Γ} → Γ ⊢ A ^ r → Γ ⊢ B ^ r → Dec (Γ ⊢ A ≡ B ^ r)
dec ⊢A ⊢B =
  let ⊢Γ≡Γ = reflConEq (wf ⊢A)
  in  map soundnessConv↑ completeEq
          (decConv↑ ⊢Γ≡Γ (completeEq (refl ⊢A)) (completeEq (refl ⊢B)))

-- Decidability of conversion of well-formed terms
decTerm : ∀ {t u A r Γ} → Γ ⊢ t ∷ A ^ r → Γ ⊢ u ∷ A ^ r → Dec (Γ ⊢ t ≡ u ∷ A ^ r)
decTerm {r = !} ⊢t ⊢u =
  let ⊢Γ≡Γ = reflConEq (wfTerm ⊢t)
  in  map soundnessConv↑Term completeEqTerm
          (decConv↑TermConv ⊢Γ≡Γ (refl (syntacticTerm ⊢t)) (completeEqTerm (genRefl ⊢t)) (completeEqTerm (genRefl ⊢u)))
decTerm {r = %} ⊢t ⊢u =
  let ⊢Γ≡Γ = reflConEq (wfTerm ⊢t)
  in  map soundness~↑% completeEqTerm
          (decConv↑TermConv ⊢Γ≡Γ (refl (syntacticTerm ⊢t)) (completeEqTerm (genRefl ⊢t)) (completeEqTerm (genRefl ⊢u)))
