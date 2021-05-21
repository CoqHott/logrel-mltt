{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.MaybeEmb {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.LogicalRelation
import Tools.PropositionalEquality as PE

import Data.Nat as Nat


-- Any level can be embedded into the highest level.
maybeEmb : ∀ {l A r Γ}
         → Γ ⊩⟨ l ⟩ A ^ r
         → Γ ⊩⟨ ∞ ⟩ A ^ r
maybeEmb {ι ⁰} [A] = emb ∞< (emb emb< [A])
maybeEmb {ι ¹} [A] = emb ∞< [A]
maybeEmb {∞} [A] = [A]

-- The lowest level can be embedded in any level.
maybeEmb′ : ∀ {l l' A r Γ}
          → l ≤ l'
          → Γ ⊩⟨ ι l ⟩ A ^ r
          → Γ ⊩⟨ ι l' ⟩ A ^ r
maybeEmb′ (<is≤ 0<1) [A] = emb emb< [A]
maybeEmb′ (≡is≤ PE.refl) [A] = [A]
