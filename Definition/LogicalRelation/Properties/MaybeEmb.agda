{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.MaybeEmb {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.LogicalRelation


-- Any level can be embedded into the highest level.
maybeEmb : ∀ {l A r Γ}
         → Γ ⊩⟨ l ⟩ A ^ r
         → Γ ⊩⟨ ¹ ⟩ A ^ r
maybeEmb {⁰} [A] = emb 0<1 [A]
maybeEmb {¹} [A] = [A]

-- The lowest level can be embedded in any level.
maybeEmb′ : ∀ {l A r Γ}
          → Γ ⊩⟨ ⁰ ⟩ A ^ r
          → Γ ⊩⟨ l ⟩ A ^ r
maybeEmb′ {⁰} [A] = [A]
maybeEmb′ {¹} [A] = emb 0<1 [A]
