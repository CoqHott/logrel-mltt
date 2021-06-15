{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Weakening {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.MaybeEmbed
open import Definition.LogicalRelation.Substitution.Introductions.Universe

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Weakening of valid types by one.
wk1ᵛ : ∀ {A F rA rF Γ l l'}
      ([Γ] : ⊩ᵛ Γ)
      ([F] : Γ ⊩ᵛ⟨ l' ⟩ F ^ rF / [Γ])
    → Γ ⊩ᵛ⟨ l ⟩ A ^ rA / [Γ]
    → Γ ∙ F ^ rF ⊩ᵛ⟨ l ⟩ wk1 A ^ rA / ([Γ] ∙ [F])
wk1ᵛ {A} [Γ] [F] [A] ⊢Δ [σ] =
  let [σA] = proj₁ ([A] ⊢Δ (proj₁ [σ]))
      [σA]′ = irrelevance′ (PE.sym (subst-wk A)) [σA]
  in  [σA]′
  ,   (λ [σ′] [σ≡σ′] →
         irrelevanceEq″ (PE.sym (subst-wk A))
                        (PE.sym (subst-wk A)) PE.refl PE.refl
                        [σA] [σA]′
                        (proj₂ ([A] ⊢Δ (proj₁ [σ])) (proj₁ [σ′]) (proj₁ [σ≡σ′])))

-- Weakening of valid type equality by one.
wk1Eqᵛ : ∀ {A B F rA rF Γ l l'}
         ([Γ] : ⊩ᵛ Γ)
         ([F] : Γ ⊩ᵛ⟨ l' ⟩ F ^ rF / [Γ])
         ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ rA / [Γ])
         ([A≡B] : Γ ⊩ᵛ⟨ l ⟩ A ≡ B ^ rA / [Γ] / [A])
       → Γ ∙ F ^ rF ⊩ᵛ⟨ l ⟩ wk1 A ≡ wk1 B ^ rA / [Γ] ∙ [F] / wk1ᵛ {A} {F} [Γ] [F] [A]
wk1Eqᵛ {A} {B} [Γ] [F] [A] [A≡B] ⊢Δ [σ] =
  let [σA] = proj₁ ([A] ⊢Δ (proj₁ [σ]))
      [σA]′ = irrelevance′ (PE.sym (subst-wk A)) [σA]
  in  irrelevanceEq″ (PE.sym (subst-wk A))
                     (PE.sym (subst-wk B)) PE.refl PE.refl
                     [σA] [σA]′
                     ([A≡B] ⊢Δ (proj₁ [σ]))

-- Weakening of valid term as a type by one.
wk1ᵗᵛ : ∀ {F G rF rG lG Γ l'}
         ([Γ] : ⊩ᵛ Γ)
         ([F] : Γ ⊩ᵛ⟨ l' ⟩ F ^ rF / [Γ]) →
       let l    = ∞
           [UG] = maybeEmbᵛ {A = Univ rG _} [Γ] (Uᵛ (proj₂ (levelBounded lG)) [Γ])
           [wUG] = maybeEmbᵛ {A = Univ rG _} (_∙_ {A = F} [Γ] [F]) (λ {Δ} {σ} → Uᵛ (proj₂ (levelBounded lG)) (_∙_ {A = F} [Γ] [F])  {Δ} {σ})
       in Γ ⊩ᵛ⟨ l ⟩ G ∷ Univ rG lG ^ [ ! , next lG ] / [Γ] / [UG] →
          Γ ∙ F ^ rF ⊩ᵛ⟨ l ⟩ wk1 G ∷ Univ rG lG ^ [ ! , next lG ] / ([Γ] ∙ [F]) / (λ {Δ} {σ} → [wUG] {Δ} {σ})
wk1ᵗᵛ {F} {G} {rF} {rG} {lG} [Γ] [F] [G]ₜ {Δ} {σ} ⊢Δ [σ] =
  let l    = ∞
      [UG] = maybeEmbᵛ {A = Univ rG _} [Γ] (Uᵛ (proj₂ (levelBounded lG)) [Γ])
      [wUG] = maybeEmbᵛ {A = Univ rG _} (_∙_ {A = F} [Γ] [F]) (λ {Δ} {σ} → Uᵛ (proj₂ (levelBounded lG)) (_∙_ {A = F} [Γ] [F])  {Δ} {σ})
      [σG] = proj₁ ([G]ₜ ⊢Δ (proj₁ [σ]))
      [Geq] = PE.sym (subst-wk G)
      [σG]′ = irrelevanceTerm″ PE.refl PE.refl PE.refl [Geq] (proj₁ ([UG] ⊢Δ (proj₁ [σ]))) (proj₁ ([wUG] {Δ} {σ} ⊢Δ [σ])) [σG]
  in  [σG]′
  ,   (λ [σ′] [σ≡σ′] →
         irrelevanceEqTerm″ PE.refl PE.refl
                            (PE.sym (subst-wk G))
                            (PE.sym (subst-wk G)) PE.refl 
                            (proj₁ ([UG] ⊢Δ (proj₁ [σ]))) (proj₁ ([wUG] {Δ} {σ} ⊢Δ [σ]))
                            (proj₂ ([G]ₜ ⊢Δ (proj₁ [σ])) (proj₁ [σ′]) (proj₁ [σ≡σ′])))
