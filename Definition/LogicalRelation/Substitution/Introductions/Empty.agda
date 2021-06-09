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
open import Definition.LogicalRelation.Substitution.Introductions.Pi
open import Definition.LogicalRelation.Substitution.MaybeEmbed

open import Tools.Unit as TU
open import Tools.Product
import Tools.PropositionalEquality as PE


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

Unitᵗᵛ : ∀ {Γ} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ ∞ ⟩ Unit ∷ (SProp ⁰) ^ [ ! , next ⁰ ] / [Γ] / maybeEmbᵛ {A = SProp _} [Γ] (Uᵛ emb< [Γ])
Unitᵗᵛ {Γ} [Γ] = let [SProp] = Uᵛ {rU = %} emb< [Γ]
                     [Empty] = Emptyᵛ {ll = ⁰} {l = ∞} [Γ]
                     [Γ∙Empty] = (_∙_ {Γ} {Empty} [Γ] [Empty])
                     [SProp]₁ : Γ ∙ Empty ^ [ % , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ (SProp ⁰) ^ [ ! , next ⁰ ] / [Γ∙Empty]
                     [SProp]₁ {Δ} {σ} = maybeEmbᵛ {A = SProp ⁰} [Γ∙Empty] (λ {Δ} {σ} → Uᵛ emb< [Γ∙Empty] {Δ} {σ}) {Δ} {σ}
                     [Empty]₁ = Emptyᵗᵛ [Γ] emb<
                     [Empty]₂ = Emptyᵗᵛ [Γ∙Empty] emb<
                in maybeEmbTermᵛ {A = SProp _} {t = Unit} [Γ] (Uᵛ emb< [Γ])
                               (Πᵗᵛ {Empty} {Empty} (≡is≤ PE.refl) (≡is≤ PE.refl) [Γ] ( Emptyᵛ {ll = ⁰} [Γ]) (λ {Δ} {σ} → [SProp]₁ {Δ} {σ}) [Empty]₁ (λ {Δ} {σ} → [Empty]₂ {Δ} {σ}))


Unit≡Unit : ∀ {Γ} (⊢Γ : ⊢ Γ)
          → Γ ⊢ Unit ≅ Unit ∷ SProp ⁰ ^ [ ! , ι ¹ ]
Unit≡Unit ⊢Γ = ≅ₜ-Π-cong (univ (Emptyⱼ ⊢Γ)) (≅ₜ-Emptyrefl ⊢Γ) (≅ₜ-Emptyrefl (⊢Γ ∙ univ (Emptyⱼ ⊢Γ)))

Unitᵛ : ∀ {Γ} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ ι ⁰ ⟩ Unit ^ [ % , ι ⁰ ] / [Γ]
Unitᵛ {Γ} [Γ] = univᵛ {A = Unit} [Γ] (≡is≤ PE.refl) (Uᵛ emb< [Γ]) (Unitᵗᵛ [Γ])

UnitType : ∀ {Γ} (⊢Γ : ⊢ Γ) → Γ ⊩⟨ ι ⁰ ⟩ Unit ^ [ % , ι ⁰ ]
UnitType {Γ} ⊢Γ = proj₁ (Unitᵛ ε {Γ} {idSubst} ⊢Γ TU.tt)
