{-# OPTIONS --without-K  #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Reflexivity {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution

open import Tools.Product


-- Reflexivity of valid types.
reflᵛ : ∀ {A Γ sA l}
        ([Γ] : ⊩ᵛ Γ)
        ([A] : Γ ⊩ᵛ⟨ l ⟩ A ⦂ sA / [Γ])
      → Γ ⊩ᵛ⟨ l ⟩ A ≡ A ⦂ sA / [Γ] / [A]
reflᵛ [Γ] [A] ⊢Δ [σ] =
  reflEq (proj₁ ([A] ⊢Δ [σ]))

-- Reflexivity of valid terms.
reflᵗᵛ : ∀ {A t Γ sA l}
         ([Γ] : ⊩ᵛ Γ)
         ([A] : Γ ⊩ᵛ⟨ l ⟩ A ⦂ sA / [Γ])
         ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ A ⦂ sA / [Γ] / [A])
       → Γ ⊩ᵛ⟨ l ⟩ t ≡ t ∷ A ⦂ sA / [Γ] / [A]
reflᵗᵛ [Γ] [A] [t] ⊢Δ [σ] =
  reflEqTerm (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ]))
