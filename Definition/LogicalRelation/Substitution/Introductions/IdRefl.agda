{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.IdRefl {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed 
open import Definition.LogicalRelation.Properties.Escape
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Introductions.Id
open import Definition.LogicalRelation.Substitution.ProofIrrelevance

open import Tools.Product

Idreflᵛ : ∀{Γ A l t}
  → ([Γ] : ⊩ᵛ Γ)
  → ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ ! , ι l ] / [Γ])
  → ([t] : Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ [ ! , ι l ] / [Γ] / [A])
  → let [Id] = Idᵛ {A = A} {t = t} {u = t } [Γ] [A] [t] [t]
    in Γ ⊩ᵛ⟨ ∞ ⟩ Idrefl A t ∷ Id A t t ^ [ % , ι ⁰ ] / [Γ] / [Id]

Idreflᵛ {Γ} {A} {l} {t} [Γ] [A] [t]  =
  let [Id] = Idᵛ {A = A} {t = t} {u = t } [Γ] [A] [t] [t]
  in validityIrr {A = Id A t t} {t = Idrefl A t} [Γ] [Id] λ ⊢Δ [σ] → Idreflⱼ (escapeTerm (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ])))

