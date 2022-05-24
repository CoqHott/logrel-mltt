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
open import Tools.Empty using (⊥; ⊥-elim)



-- Validity of the Empty type.
Emptyᵛ : ∀ {Γ l} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ l ⟩ sEmpty ^ [ % , ι ⁰ ] / [Γ]
Emptyᵛ [Γ] ⊢Δ [σ] = Emptyᵣ (idRed:*: (univ (Emptyⱼ ⊢Δ))) , λ _ x₂ → id (univ (Emptyⱼ ⊢Δ))

-- Validity of the Empty type as a term.
Emptyᵗᵛ : ∀ {Γ l } ([Γ] : ⊩ᵛ Γ) → (l< : ι ⁰ <∞ l)
    → Γ ⊩ᵛ⟨ l ⟩ sEmpty ∷ SProp ^ [ ! , next ⁰ ]  / [Γ] / Uᵛ l< [Γ]
Emptyᵗᵛ [Γ] emb< ⊢Δ [σ] = let ⊢Empty  = Emptyⱼ ⊢Δ
                         in  Uₜ sEmpty (idRedTerm:*: ⊢Empty) Emptyₙ (≅ₜ-Emptyrefl ⊢Δ) (λ x ⊢Δ' → Emptyᵣ (idRed:*: (univ (Emptyⱼ ⊢Δ'))))
                            , λ x x₁ → Uₜ₌ -- Empty Empty (idRedTerm:*: ⊢Empty) (idRedTerm:*: ⊢Empty) Emptyₙ Emptyₙ
                                   (Uₜ sEmpty (idRedTerm:*: ⊢Empty) Emptyₙ (≅ₜ-Emptyrefl ⊢Δ) (λ x₂ ⊢Δ' → Emptyᵣ (idRed:*: (univ (Emptyⱼ ⊢Δ')))))
                                   (Uₜ sEmpty (idRedTerm:*: ⊢Empty) Emptyₙ (≅ₜ-Emptyrefl ⊢Δ) (λ x₂ ⊢Δ' → Emptyᵣ (idRed:*: (univ (Emptyⱼ ⊢Δ')))))
                                   (≅ₜ-Emptyrefl ⊢Δ) λ [ρ] ⊢Δ' → id (univ (Emptyⱼ ⊢Δ'))

Unitᵗᵛ : ∀ {Γ} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ ∞ ⟩ sUnit ∷ SProp ^ [ ! , next ⁰ ] / [Γ] / maybeEmbᵛ {A = SProp} [Γ] (Uᵛ emb< [Γ])
Unitᵗᵛ {Γ} [Γ] =
  let [SProp] = maybeEmbᵛ {A = SProp} [Γ] (Uᵛ {rU = %} (proj₂ (levelBounded _)) [Γ])
      [Empty] = Emptyᵛ {l = ∞} [Γ]
      [Γ∙Empty] = (_∙_ {Γ} {sEmpty} [Γ] [Empty])
      [SProp]₁ : Γ ∙ sEmpty ^ [ % , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ SProp ^ [ ! , next ⁰ ] / [Γ∙Empty]
      [SProp]₁ {Δ} {σ} = maybeEmbᵛ {A = SProp} [Γ∙Empty] (λ {Δ} {σ} → Uᵛ emb< [Γ∙Empty] {Δ} {σ}) {Δ} {σ}
      [Empty]₁ = maybeEmbTermᵛ {A = SProp} {t = sEmpty} [Γ] (Uᵛ {rU = %} emb< [Γ]) (Emptyᵗᵛ [Γ] (proj₂ (levelBounded _)))
      [Empty]₂ = maybeEmbTermᵛ {A = SProp} {t = sEmpty} [Γ∙Empty] (λ {Δ} {σ} → Uᵛ emb< [Γ∙Empty] {Δ} {σ}) λ {Δ} {σ} → Emptyᵗᵛ [Γ∙Empty] emb< {Δ} {σ}
  in maybeEmbTermᵛ {A = SProp} {t = sUnit} [Γ] [SProp] 
                   (Πirrᵗᵛ {F = sEmpty} {G = sEmpty} [Γ] (Emptyᵛ [Γ]) (λ {Δ} {σ} → [SProp]₁ {Δ} {σ}) [Empty]₁ (λ {Δ} {σ} → [Empty]₂ {Δ} {σ}))


Unit≡Unit : ∀ {Γ} (⊢Γ : ⊢ Γ)
          → Γ ⊢ sUnit ≅ sUnit ∷ SProp ^ [ ! , next ⁰ ]
Unit≡Unit ⊢Γ = ≅ₜ-Π-cong (λ abs → ⊥-elim (!≢% (PE.sym abs))) (λ _ → PE.refl , PE.refl) (univ (Emptyⱼ ⊢Γ)) (≅ₜ-Emptyrefl ⊢Γ) (≅ₜ-Emptyrefl (⊢Γ ∙ univ (Emptyⱼ ⊢Γ)))

Unitᵛ : ∀ {Γ} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ ι ⁰ ⟩ sUnit ^ [ % , ι ⁰ ] / [Γ]
Unitᵛ {Γ} [Γ] = univᵛ {A = sUnit} [Γ] (≡is≤ PE.refl) (maybeEmbᵛ {A = SProp} [Γ] (Uᵛ {rU = %} (proj₂ (levelBounded _)) [Γ])) (Unitᵗᵛ [Γ])


UnitType : ∀ {Γ} (⊢Γ : ⊢ Γ) → Γ ⊩⟨ ι ⁰ ⟩ sUnit ^ [ % , ι ⁰ ]
UnitType {Γ} ⊢Γ = proj₁ (Unitᵛ ε {Γ} {idSubst} ⊢Γ TU.tt)

EmptyType : ∀ {Γ} (⊢Γ : ⊢ Γ) → Γ ⊩⟨ ι ⁰ ⟩ sEmpty ^ [ % , ι ⁰ ]
EmptyType {Γ} ⊢Γ = proj₁ (Emptyᵛ ε {Γ} {idSubst} ⊢Γ TU.tt)
