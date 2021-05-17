{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Empty {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Introductions.Universe

open import Tools.Unit
open import Tools.Product


-- Validity of the Empty type.
Emptyᵛ : ∀ {Γ ll l} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ l ⟩ Empty ^ [ % , ι ll ] / [Γ]
Emptyᵛ [Γ] ⊢Δ [σ] = Emptyᵣ (idRed:*: (univ (Emptyⱼ ⊢Δ))) , λ _ x₂ → id (univ (Emptyⱼ ⊢Δ))

-- Validity of the Empty type as a term.
Emptyᵗᵛ : ∀ {Γ l ll} ([Γ] : ⊩ᵛ Γ) → (l< : ι ll <∞ l)
    → Γ ⊩ᵛ⟨ l ⟩ Empty ∷ Univ % ll ^ [ ! , next ll ]  / [Γ] / Uᵛ l< [Γ]
Emptyᵗᵛ [Γ] emb< ⊢Δ [σ] = let ⊢Empty  = Emptyⱼ ⊢Δ
                       in  Uₜ Empty (idRedTerm:*: ⊢Empty) Emptyₙ (≅ₜ-Emptyrefl ⊢Δ) (λ x ⊢Δ' → Emptyᵣ (idRed:*: (univ (Emptyⱼ ⊢Δ'))))
                           , λ x x₁ → Uₜ₌ -- Empty Empty (idRedTerm:*: ⊢Empty) (idRedTerm:*: ⊢Empty) Emptyₙ Emptyₙ
                                   (Uₜ Empty (idRedTerm:*: ⊢Empty) Emptyₙ (≅ₜ-Emptyrefl ⊢Δ) (λ x₂ ⊢Δ' → Emptyᵣ (idRed:*: (univ (Emptyⱼ ⊢Δ')))))
                                   (Uₜ Empty (idRedTerm:*: ⊢Empty) Emptyₙ (≅ₜ-Emptyrefl ⊢Δ) (λ x₂ ⊢Δ' → Emptyᵣ (idRed:*: (univ (Emptyⱼ ⊢Δ')))))
                                   (≅ₜ-Emptyrefl ⊢Δ) λ [ρ] ⊢Δ' → id (univ (Emptyⱼ ⊢Δ'))
Emptyᵗᵛ [Γ] ∞< ⊢Δ [σ] = let ⊢Empty  = Emptyⱼ ⊢Δ
                       in  Uₜ Empty (idRedTerm:*: ⊢Empty) Emptyₙ (≅ₜ-Emptyrefl ⊢Δ) (λ x ⊢Δ' → Emptyᵣ (idRed:*: (univ (Emptyⱼ ⊢Δ'))))
                           , λ x x₁ → Uₜ₌ -- Empty Empty (idRedTerm:*: ⊢Empty) (idRedTerm:*: ⊢Empty) Emptyₙ Emptyₙ
                                   (Uₜ Empty (idRedTerm:*: ⊢Empty) Emptyₙ (≅ₜ-Emptyrefl ⊢Δ) (λ x₂ ⊢Δ' → Emptyᵣ (idRed:*: (univ (Emptyⱼ ⊢Δ')))))
                                   (Uₜ Empty (idRedTerm:*: ⊢Empty) Emptyₙ (≅ₜ-Emptyrefl ⊢Δ) (λ x₂ ⊢Δ' → Emptyᵣ (idRed:*: (univ (Emptyⱼ ⊢Δ')))))
                                   (≅ₜ-Emptyrefl ⊢Δ) λ [ρ] ⊢Δ' → id (univ (Emptyⱼ ⊢Δ'))
