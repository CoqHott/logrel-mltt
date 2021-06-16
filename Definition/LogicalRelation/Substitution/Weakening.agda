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


wk1Termᵛ : ∀ {F G rF rG t Γ l l'}
         ([Γ] : ⊩ᵛ Γ)
         ([F] : Γ ⊩ᵛ⟨ l' ⟩ F ^ rF / [Γ]) →
         ([G] : Γ ⊩ᵛ⟨ l ⟩ G ^ rG / [Γ]) →
          Γ ⊩ᵛ⟨ l ⟩ t ∷ G ^ rG / [Γ] / [G] →
          Γ ∙ F ^ rF ⊩ᵛ⟨ l ⟩ wk1 t ∷ wk1 G ^ rG / ([Γ] ∙ [F]) / wk1ᵛ {A = G} {F = F} [Γ] [F] [G]
wk1Termᵛ {F} {G} {rF} {rG} {t} [Γ] [F] [G] [t]ₜ {Δ} {σ} ⊢Δ [σ] =
         let [σt] = proj₁ ([t]ₜ ⊢Δ (proj₁ [σ]))
             [σG] = proj₁ ([G] ⊢Δ (proj₁ [σ]))
             [teq] = PE.sym (subst-wk {step id} {σ} t)
             [Geq] = PE.sym (subst-wk {step id} {σ} G)
             [σG]' = irrelevance′ [Geq] [σG]
         in irrelevanceTerm″ [Geq] PE.refl PE.refl [teq] [σG] [σG]' [σt] ,
            λ [σ′] [σ≡σ′] → irrelevanceEqTerm″ PE.refl PE.refl
                            (PE.sym (subst-wk t)) (PE.sym (subst-wk t)) (PE.sym (subst-wk G))
                            [σG] [σG]' (proj₂ ([t]ₜ ⊢Δ (proj₁ [σ])) (proj₁ [σ′]) (proj₁ [σ≡σ′]))

wk1dᵛ : ∀ {F F' G rF rF' lG Γ l'}
         ([Γ] : ⊩ᵛ Γ)
         ([F] : Γ ⊩ᵛ⟨ l' ⟩ F ^ rF / [Γ]) →
         ([F'] : Γ ⊩ᵛ⟨ l' ⟩ F' ^ rF' / [Γ]) →
       let l    = ∞
           [ΓF] = _∙_ {A = F} [Γ] [F]
           [ΓF'] = _∙_ {A = F'} [Γ] [F']
           [ΓF'F] = _∙_ {A = wk1 F} [ΓF'] (wk1ᵛ {A = F} {F = F'} [Γ] [F'] [F])
       in Γ ∙ F ^ rF ⊩ᵛ⟨ l ⟩ G ^ [ ! , lG ] / [ΓF] →
          Γ ∙ F' ^ rF' ∙ wk1 F ^ rF ⊩ᵛ⟨ l ⟩ wk1d G ^ [ ! , lG ] / [ΓF'F] 
wk1dᵛ {F} {F'} {G} [Γ] [F] [F'] [G] {Δ} {σ} ⊢Δ [σ] =
     let l    = ∞
         [ΓF'] = _∙_ {A = F'} [Γ] [F']
         [ΓF'F] = _∙_ {A = wk1 F} [ΓF'] (wk1ᵛ {A = F} {F = F'} [Γ] [F'] [F])
         [wσ] = proj₁ (proj₁ [σ]) , irrelevanceTerm″ (subst-wk F) PE.refl PE.refl PE.refl
                                                     (proj₁ (wk1ᵛ {A = F} {F = F'} [Γ] [F'] [F] ⊢Δ (proj₁ [σ])))
                                                     (proj₁ ([F] ⊢Δ (proj₁ (proj₁ [σ]))))
                                                     (proj₂ [σ]) 
         [σG] = proj₁ ([G] ⊢Δ [wσ])
         [Geq] = PE.sym (subst-wk G)
         [σG]′ = irrelevance′ [Geq] [σG]
     in  [σG]′
         ,   (λ {σ′} [σ′] [σ≡σ′] → let [wσ′] = proj₁ (proj₁ [σ′]) ,
                                               irrelevanceTerm″ (subst-wk F) PE.refl PE.refl PE.refl
                                                     (proj₁ (wk1ᵛ {A = F} {F = F'} [Γ] [F'] [F] ⊢Δ (proj₁ [σ′])))
                                                     (proj₁ ([F] ⊢Δ (proj₁ (proj₁ [σ′]))))
                                                     (proj₂ [σ′]) 
                                       [wσ≡σ′] = (proj₁ (proj₁ [σ≡σ′])),
                                                 irrelevanceEqTerm″ PE.refl PE.refl PE.refl PE.refl (subst-wk F)
                                                     (proj₁ (wk1ᵛ {A = F} {F = F'} [Γ] [F'] [F] ⊢Δ (proj₁ [σ])))
                                                     (proj₁ ([F] ⊢Δ (proj₁ (proj₁ [σ]))))
                                                     (proj₂  [σ≡σ′])
                              in irrelevanceEq″ (PE.sym (subst-wk G)) (PE.sym (subst-wk G)) PE.refl PE.refl
                                                (proj₁ ([G] ⊢Δ [wσ])) [σG]′
                                                (proj₂ ([G] ⊢Δ [wσ]) [wσ′] [wσ≡σ′]))


wk1dᵗᵛ : ∀ {F F' G rF rF' rG lG Γ l'}
         ([Γ] : ⊩ᵛ Γ)
         ([F] : Γ ⊩ᵛ⟨ l' ⟩ F ^ rF / [Γ]) →
         ([F'] : Γ ⊩ᵛ⟨ l' ⟩ F' ^ rF' / [Γ]) →
       let l    = ∞
           [ΓF] = _∙_ {A = F} [Γ] [F]
           [ΓF'] = _∙_ {A = F'} [Γ] [F']
           [ΓF'F] = _∙_ {A = wk1 F} [ΓF'] (wk1ᵛ {A = F} {F = F'} [Γ] [F'] [F])
       in ([UG] : (Γ ∙ F ^ rF) ⊩ᵛ⟨ ∞ ⟩ Univ rG lG ^ [ ! , next lG ] / [ΓF]) →
          ([wUG] : (Γ ∙ F' ^ rF' ∙ wk1 F ^ rF) ⊩ᵛ⟨ ∞ ⟩ Univ rG lG ^ [ ! , next lG ] / [ΓF'F]) →
          Γ ∙ F ^ rF ⊩ᵛ⟨ l ⟩ G ∷ Univ rG lG ^ [ ! , next lG ] / [ΓF] / (λ {Δ} {σ} → [UG] {Δ} {σ}) →
          Γ ∙ F' ^ rF' ∙ wk1 F ^ rF ⊩ᵛ⟨ l ⟩ wk1d G ∷ Univ rG lG ^ [ ! , next lG ] / [ΓF'F] / (λ {Δ} {σ} → [wUG] {Δ} {σ})
wk1dᵗᵛ {F} {F'} {G} {rF} {rF'} {rG} {lG} [Γ] [F] [F'] [UG] [wUG] [G]ₜ {Δ} {σ} ⊢Δ [σ] =
     let l    = ∞
         [ΓF'] = _∙_ {A = F'} [Γ] [F']
         [ΓF'F] = _∙_ {A = wk1 F} [ΓF'] (wk1ᵛ {A = F} {F = F'} [Γ] [F'] [F])
         [wσ] = proj₁ (proj₁ [σ]) , irrelevanceTerm″ (subst-wk F) PE.refl PE.refl PE.refl
                                                     (proj₁ (wk1ᵛ {A = F} {F = F'} [Γ] [F'] [F] ⊢Δ (proj₁ [σ])))
                                                     (proj₁ ([F] ⊢Δ (proj₁ (proj₁ [σ]))))
                                                     (proj₂ [σ]) 
         [σG] = proj₁ ([G]ₜ ⊢Δ [wσ])
         [Geq] = PE.sym (subst-wk G)
         [σG]′ = irrelevanceTerm″ PE.refl PE.refl PE.refl [Geq] (proj₁ ([UG] ⊢Δ [wσ])) (proj₁ ([wUG] {Δ} {σ} ⊢Δ [σ])) [σG]
     in  [σG]′
         ,   (λ {σ′} [σ′] [σ≡σ′] → let [wσ′] = proj₁ (proj₁ [σ′]) ,
                                               irrelevanceTerm″ (subst-wk F) PE.refl PE.refl PE.refl
                                                     (proj₁ (wk1ᵛ {A = F} {F = F'} [Γ] [F'] [F] ⊢Δ (proj₁ [σ′])))
                                                     (proj₁ ([F] ⊢Δ (proj₁ (proj₁ [σ′]))))
                                                     (proj₂ [σ′]) 
                                       [wσ≡σ′] = (proj₁ (proj₁ [σ≡σ′])),
                                                 irrelevanceEqTerm″ PE.refl PE.refl PE.refl PE.refl (subst-wk F)
                                                     (proj₁ (wk1ᵛ {A = F} {F = F'} [Γ] [F'] [F] ⊢Δ (proj₁ [σ])))
                                                     (proj₁ ([F] ⊢Δ (proj₁ (proj₁ [σ]))))
                                                     (proj₂  [σ≡σ′])
                              in irrelevanceEqTerm″ PE.refl PE.refl
                                                    (PE.sym (subst-wk G))
                                                    (PE.sym (subst-wk G)) PE.refl 
                                                    (proj₁ ([UG] ⊢Δ [wσ])) (proj₁ ([wUG] {Δ} {σ} ⊢Δ [σ]))
                                                    (proj₂ ([G]ₜ ⊢Δ [wσ]) [wσ′] [wσ≡σ′]))
