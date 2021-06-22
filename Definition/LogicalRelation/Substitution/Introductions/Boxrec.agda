{-# OPTIONS --without-K  --allow-unsolved-meta #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Boxrec {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Introductions.Universe
open import Definition.LogicalRelation.Substitution.Introductions.Box
open import Definition.LogicalRelation.Substitution.Introductions.Pi

open import Tools.Product


Boxrecᵛ : ∀ {Γ sA sC A C t u l}
            ([Γ] : ⊩ᵛ Γ)
            ([A] : Γ ⊩ᵛ⟨ l ⟩ A ⦂ sA / [Γ])
            ([C] : Γ ∙ Box sA A ⦂ 𝕥y ⊩ᵛ⟨ l ⟩ C ⦂ sC / [Γ] ∙ Boxᵛ [Γ] [A])
            ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ )
            ()Γ ⊢ u ∷ Π A ⦂ ‼ sA ▹ (C [ box sA (var 0) ]↑) ⦂ sC
            → Γ ⊢ t ∷ Box sA A ⦂ 𝕥y
            → Γ ⊢ Boxrec sC A C u t ∷ C [ t ] ⦂ sC

