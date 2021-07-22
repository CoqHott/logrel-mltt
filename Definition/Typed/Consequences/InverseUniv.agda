{-# OPTIONS --safe #-}

module Definition.Typed.Consequences.InverseUniv where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Consequences.Syntactic

import Tools.Sum as Sum
open import Tools.Sum using (_⊎_; inj₁; inj₂)
open import Tools.Product
open import Tools.Empty
open import Tools.Nullary


-- If type A does not contain U, then A can be a term of type U.
inverseUniv : ∀ {A rA lA Γ} → Γ ⊢ A ^ [ rA , ι lA ] → Γ ⊢ A ∷ Univ rA lA ^ [ ! , next lA ]
inverseUniv X = un-univ X

-- Helper function where if at least one type does not contain U, then the
-- equality of types can be an equality of term of type U.
inverseUnivEq : ∀ {A B r Γ l} → Γ ⊢ A ≡ B ^ [ r , ι l ] → Γ ⊢ A ≡ B ∷ Univ r l ^ [ ! , next l ]
inverseUnivEq X = un-univ≡ X
