{-# OPTIONS --without-K  #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Universe {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Validity of the universe type.
Uᵛ : ∀ {Γ sU} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ ¹ ⟩ Univ sU ⦂ 𝕥y / [Γ]
Uᵛ [Γ] ⊢Δ [σ] = Uᵣ′ _ ⁰ 0<1 ⊢Δ , λ _ x₂ → PE.refl

-- Valid terms of type U are valid types.
univᵛ : ∀ {A Γ sU l l′} ([Γ] : ⊩ᵛ Γ)
        ([U] : Γ ⊩ᵛ⟨ l ⟩ Univ sU ⦂ 𝕥y / [Γ])
      → Γ ⊩ᵛ⟨ l ⟩ A ∷ Univ sU ⦂ 𝕥y / [Γ] / [U]
      → Γ ⊩ᵛ⟨ l′ ⟩ A ⦂ sU / [Γ]
univᵛ {l′ = l′} [Γ] [U] [A] ⊢Δ [σ] =
  let [A]₁ = maybeEmb′ {l′} (univEq (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])))
  in  [A]₁ , (λ [σ′] [σ≡σ′] → univEqEq (proj₁ ([U] ⊢Δ [σ])) [A]₁
                                       ((proj₂ ([A] ⊢Δ [σ])) [σ′] [σ≡σ′]))

-- Valid term equality of type U is valid type equality.
univEqᵛ : ∀ {A B Γ sU l l′} ([Γ] : ⊩ᵛ Γ)
          ([U] : Γ ⊩ᵛ⟨ l′ ⟩ Univ sU ⦂ 𝕥y / [Γ])
          ([A] : Γ ⊩ᵛ⟨ l ⟩ A ⦂ sU / [Γ])
        → Γ ⊩ᵛ⟨ l′ ⟩ A ≡ B ∷ Univ sU ⦂ 𝕥y / [Γ] / [U]
        → Γ ⊩ᵛ⟨ l ⟩ A ≡ B  ⦂ sU / [Γ] / [A]
univEqᵛ {A} [Γ] [U] [A] [t≡u] ⊢Δ [σ] =
  univEqEq (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])) ([t≡u] ⊢Δ [σ])
