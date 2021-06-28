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

Unitᵗᵛ : ∀ {Γ l} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ ∞ ⟩ Unit ∷ (SProp l) ^ [ ! , next l ] / [Γ] / maybeEmbᵛ {A = SProp l} [Γ] (Uᵛ (proj₂ (levelBounded _)) [Γ])
Unitᵗᵛ {Γ} {l} [Γ] = let [SProp] = maybeEmbᵛ {A = SProp l} [Γ] (Uᵛ {rU = %} (proj₂ (levelBounded _)) [Γ])
                         [Empty] = Emptyᵛ {ll = l} {l = ∞} [Γ]
                         [Γ∙Empty] = (_∙_ {Γ} {Empty} [Γ] [Empty])
                         [SProp]₁ : Γ ∙ Empty ^ [ % , ι l ] ⊩ᵛ⟨ ∞ ⟩ (SProp l) ^ [ ! , next l ] / [Γ∙Empty]
                         [SProp]₁ {Δ} {σ} = maybeEmbᵛ {A = SProp l} [Γ∙Empty] (λ {Δ} {σ} → Uᵛ (proj₂ (levelBounded _)) [Γ∙Empty] {Δ} {σ}) {Δ} {σ}
                         [Empty]₁ = maybeEmbTermᵛ {A = SProp l} {t = Empty} [Γ] (Uᵛ {rU = %} (proj₂ (levelBounded _)) [Γ]) (Emptyᵗᵛ {ll = l} [Γ] (proj₂ (levelBounded _)))
                         [Empty]₂ = maybeEmbTermᵛ {A = SProp l} {t = Empty} [Γ∙Empty] (λ {Δ} {σ} → Uᵛ (proj₂ (levelBounded _)) [Γ∙Empty] {Δ} {σ}) (Emptyᵗᵛ {ll = l} [Γ∙Empty] (proj₂ (levelBounded _)))
                in maybeEmbTermᵛ {A = SProp l} {t = Unit} [Γ] [SProp] 
                                 (Πᵗᵛ {Empty} {Empty} (≡is≤ PE.refl) (≡is≤ PE.refl) [Γ] ( Emptyᵛ {ll = l} [Γ]) (λ {Δ} {σ} → [SProp]₁ {Δ} {σ}) [Empty]₁ (λ {Δ} {σ} → [Empty]₂ {Δ} {σ}))


Unit≡Unit : ∀ {Γ l} (⊢Γ : ⊢ Γ)
          → Γ ⊢ Unit {l} ≅ Unit {l} ∷ SProp l ^ [ ! , next l ]
Unit≡Unit ⊢Γ = ≅ₜ-Π-cong (univ (Emptyⱼ ⊢Γ)) (≅ₜ-Emptyrefl ⊢Γ) (≅ₜ-Emptyrefl (⊢Γ ∙ univ (Emptyⱼ ⊢Γ)))

Unitᵛ : ∀ {Γ l} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ ι l ⟩ Unit ^ [ % , ι l ] / [Γ]
Unitᵛ {Γ} {l} [Γ] = univᵛ {A = Unit} [Γ] (≡is≤ PE.refl) (maybeEmbᵛ {A = SProp l} [Γ] (Uᵛ {rU = %} (proj₂ (levelBounded _)) [Γ])) (Unitᵗᵛ {l = l} [Γ])


UnitType : ∀ {Γ l} (⊢Γ : ⊢ Γ) → Γ ⊩⟨ ι l ⟩ Unit ^ [ % , ι l ]
UnitType {Γ} ⊢Γ = proj₁ (Unitᵛ ε {Γ} {idSubst} ⊢Γ TU.tt)

EmptyType : ∀ {Γ l} (⊢Γ : ⊢ Γ) → Γ ⊩⟨ ι l ⟩ Empty ^ [ % , ι l ]
EmptyType {Γ} ⊢Γ = proj₁ (Emptyᵛ ε {Γ} {idSubst} ⊢Γ TU.tt)
