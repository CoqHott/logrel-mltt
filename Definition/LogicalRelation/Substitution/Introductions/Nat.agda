{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Nat {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Introductions.Universe

open import Tools.Product


-- Validity of the natural number type.
ℕᵛ : ∀ {Γ l} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ l ⟩ ℕ ^ [ ! , ι ⁰ ] / [Γ]
ℕᵛ [Γ] ⊢Δ [σ] = ℕᵣ (idRed:*: (univ (ℕⱼ ⊢Δ))) , λ _ x₂ → id (univ (ℕⱼ ⊢Δ)) 

-- Validity of the natural number type as a term.
ℕᵗᵛ : ∀ {Γ} ([Γ] : ⊩ᵛ Γ)
    → Γ ⊩ᵛ⟨ ι ¹ ⟩ ℕ ∷ Univ ! ⁰  ^ [ ! , ι ¹ ] / [Γ] / Uᵛ emb< [Γ]
ℕᵗᵛ [Γ] ⊢Δ [σ] = let Uℕₜ = Uₜ ℕ (idRedTerm:*: (ℕⱼ ⊢Δ)) ℕₙ (≅ₜ-ℕrefl ⊢Δ) (λ x ⊢Δ₁ → ℕᵣ (idRed:*: (univ (ℕⱼ ⊢Δ₁))))
                in  Uℕₜ , λ x ⊢Δ₁ → Uₜ₌ Uℕₜ Uℕₜ (≅ₜ-ℕrefl ⊢Δ) λ [ρ] ⊢Δ₂ → (id (univ (ℕⱼ ⊢Δ₂)))


-- Validity of zero.
zeroᵛ : ∀ {Γ l} ([Γ] : ⊩ᵛ Γ)
      → Γ ⊩ᵛ⟨ l ⟩ zero ∷ ℕ ^ [ ! , ι ⁰ ] / [Γ] / ℕᵛ [Γ]
zeroᵛ [Γ] ⊢Δ [σ] =
  ℕₜ zero (idRedTerm:*: (zeroⱼ ⊢Δ)) (≅ₜ-zerorefl ⊢Δ) zeroᵣ
    , (λ _ x₁ → ℕₜ₌ zero zero (idRedTerm:*: (zeroⱼ ⊢Δ)) (idRedTerm:*: (zeroⱼ ⊢Δ))
                    (≅ₜ-zerorefl ⊢Δ) zeroᵣ)

-- Validity of successor of valid natural numbers.
sucᵛ : ∀ {Γ n l} ([Γ] : ⊩ᵛ Γ)
         ([ℕ] : Γ ⊩ᵛ⟨ l ⟩ ℕ ^ [ ! , ι ⁰ ] / [Γ])
     → Γ ⊩ᵛ⟨ l ⟩ n ∷ ℕ ^ [ ! , ι ⁰ ] / [Γ] / [ℕ]
     → Γ ⊩ᵛ⟨ l ⟩ suc n ∷ ℕ ^ [ ! , ι ⁰ ] / [Γ] / [ℕ]
sucᵛ ⊢Γ [ℕ] [n] ⊢Δ [σ] =
  sucTerm (proj₁ ([ℕ] ⊢Δ [σ])) (proj₁ ([n] ⊢Δ [σ]))
  , (λ x x₁ → sucEqTerm (proj₁ ([ℕ] ⊢Δ [σ])) (proj₂ ([n] ⊢Δ [σ]) x x₁))
