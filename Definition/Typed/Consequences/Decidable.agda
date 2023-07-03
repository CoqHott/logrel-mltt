{-# OPTIONS --safe #-}

module Definition.Typed.Consequences.Decidable where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.EqRelInstance
open import Definition.Conversion
open import Definition.Conversion.Stability
open import Definition.Conversion.Soundness
open import Definition.Conversion.Decidable
open import Definition.Conversion.Consequences.Completeness

open import Tools.Nat
open import Tools.Product
open import Tools.Empty
open import Tools.Nullary
import Tools.PropositionalEquality as PE

-- Decidability of algorithmic equality of neutrals.
dec-aux : ∀ {Γ t u T l}
        → Dec (Γ ⊢ t [conv↑] u ∷ T ^ l)
        → Dec (Γ ⊢ t ≡ u ∷ T ^ [ ! , l ])
dec-aux (yes p) = yes (soundnessConv↑Term p)
dec-aux (no ¬p) = no λ x → ¬p (completeEqTerm x)


dec : ∀ {Γ t u T l}
        → (⊢t : Γ ⊢ t ∷ T ^ [ ! , l ])
        → (⊢u : Γ ⊢ u ∷ T ^ [ ! , l ])
        → Dec (Γ ⊢ t ≡ u ∷ T ^ [ ! , l ])
dec ⊢t ⊢u = dec-aux (decConv↑Term (reflConEq (wfTerm ⊢t)) (completeEqTerm (refl ⊢t)) (completeEqTerm (refl ⊢u)) (le-refl _))
