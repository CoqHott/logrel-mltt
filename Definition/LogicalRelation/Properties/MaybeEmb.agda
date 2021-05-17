{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.MaybeEmb {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.LogicalRelation

import Data.Nat as Nat


{- not true anymore with the new presentation -}

{- 
-- Any level can be embedded into the highest level.
maybeEmb : ∀ {l A r Γ}
         → Γ ⊩⟨ l ⟩ A ^ r
         → Γ ⊩⟨ ∞ ⟩ A ^ r
maybeEmb {ι ⁰} [A] = emb emb< [A]
maybeEmb {ι ¹} [A] = emb ∞< [A]
maybeEmb {∞} [A] = [A]

-- The lowest level can be embedded in any level.
maybeEmb′ : ∀ {l A r Γ}
          → Γ ⊩⟨ ι ⁰ ⟩ A ^ r
          → Γ ⊩⟨ l ⟩ A ^ r
maybeEmb′ {ι ⁰} [A] = [A]
maybeEmb′ {ι ¹} [A] = emb {l′ = ι ⁰} (Nat.s≤s Nat.z≤n) [A]
maybeEmb′ {∞} [A] = emb {l′ = ι ⁰} (Nat.s≤s Nat.z≤n) [A]
-}
