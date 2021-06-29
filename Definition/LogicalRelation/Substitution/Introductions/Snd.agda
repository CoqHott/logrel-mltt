{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Snd {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening as T hiding (wk; wkTerm; wkEqTerm)
open import Definition.Typed.RedSteps
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Weakening
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Application
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Substitution.Reflexivity
open import Definition.LogicalRelation.Substitution.Introductions.Sigma
open import Definition.LogicalRelation.Substitution.Introductions.Fst
open import Definition.LogicalRelation.Substitution.Introductions.Pi
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Definition.LogicalRelation.Substitution.MaybeEmbed
open import Definition.LogicalRelation.Substitution.Introductions.Universe

open import Tools.Product
import Tools.PropositionalEquality as PE

-- Valid lambda term construction.
sndᵛ : ∀ {F G l∃ tu Γ}
       ([Γ] : ⊩ᵛ Γ) →
       let l    = ∞
           [UF] = maybeEmbᵛ {A = Univ % _} [Γ] (Uᵛ (proj₂ (levelBounded l∃)) [Γ])
           [U∃] = maybeEmbᵛ {A = Univ % _} [Γ] (Uᵛ (proj₂ (levelBounded l∃)) [Γ])
       in      
        ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ % , ι l∃ ] / [Γ])
        ([G] : Γ ∙ F ^ [ % , ι l∃ ] ⊩ᵛ⟨ l ⟩ G ^ [ % , ι l∃ ] / [Γ] ∙ [F])
        ([UG] : Γ ∙ F ^ [ % , ι l∃ ] ⊩ᵛ⟨ l ⟩ Univ % l∃ ^ [ ! , next l∃ ] / [Γ] ∙ [F])
        ([Fₜ] : Γ ⊩ᵛ⟨ l ⟩ F ∷ Univ % l∃ ^ [ ! , next l∃ ] / [Γ] / [UF])
        ([Gₜ] : Γ ∙ F ^ [ % , ι l∃ ] ⊩ᵛ⟨ l ⟩ G ∷ Univ % l∃ ^ [ ! , next l∃ ] / [Γ] ∙ [F] / (λ {Δ} {σ} → [UG] {Δ} {σ}))
        ([tu] : Γ ⊩ᵛ⟨ l ⟩ tu ∷ ∃ F ▹ G ^ [ % , ι l∃ ] / [Γ] / ∃ᵛ {F} {G} [Γ] [F] [G])
        → Γ ⊩ᵛ⟨ l ⟩ snd tu ∷ G [ fst tu ] ^ [ % , ι l∃ ] / [Γ] / substS {F} {G} {fst tu} [Γ] [F] [G] (fstᵛ {F} {G} {l∃} {tu} {Γ} [Γ] [F] [G] (λ {Δ} {σ} → [UG] {Δ} {σ}) [Fₜ] [Gₜ] [tu])
sndᵛ {F} {G} {l∃} {tu} {Γ} [Γ] [F] [G] [UG] [Fₜ] [Gₜ] [tu] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [fst] = fstᵛ {F} {G} {l∃} {tu} {Γ} [Γ] [F] [G] (λ {Δ} {σ} → [UG] {Δ} {σ}) [Fₜ] [Gₜ] [tu]
      [G[fsttu]] = substS {F} {G} {fst tu} [Γ] [F] [G] [fst]
      [UF] = maybeEmbᵛ {A = Univ % _} [Γ] (Uᵛ (proj₂ (levelBounded l∃)) [Γ])
      [σUF] = proj₁ ([UF] ⊢Δ [σ])
      [σF] = proj₁ ([F] ⊢Δ [σ])
      ⊢F = escape [σF]
      [σF]ₜ = proj₁ ([Fₜ] ⊢Δ [σ])
      ⊢Fₜ = escapeTerm [σUF] [σF]ₜ
      [σUG] = proj₁ ([UG] {σ = liftSubst σ} (⊢Δ ∙ ⊢F)
                          (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
      [σG]ₜ = proj₁ ([Gₜ] (⊢Δ ∙ ⊢F)
                        (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
      ⊢Gₜ = escapeTerm [σUG] [σG]ₜ
      [σtu] = proj₁ ([tu] (⊢Δ) [σ])
      [∃FG] = ∃ᵛ {F} {G} {Γ} [Γ] [F] [G]
      [σ∃FG] = proj₁ ([∃FG] ⊢Δ [σ])
      ⊢tu = escapeTerm [σ∃FG] [σtu]
      ⊢snd = sndⱼ {F = subst σ F} {G = subst (liftSubst σ) G} {t = subst σ tu}
                   ⊢Fₜ ⊢Gₜ ⊢tu
      [σG[fsttu]] = proj₁ ([G[fsttu]] ⊢Δ [σ])
      ⊢sndSubst = PE.subst (λ x → _ ⊢ _ ∷ x  ^ _) (PE.sym (singleSubstLift G (fst tu))) ⊢snd
   in logRelIrr [σG[fsttu]] ⊢sndSubst , 
      (λ {σ′} [σ]′ [σ≡σ′] → logRelIrrEq [σG[fsttu]] ⊢sndSubst
     let [UF]′ = maybeEmbᵛ {A = Univ % _} [Γ] (Uᵛ (proj₂ (levelBounded l∃)) [Γ])
         [σUF]′ = proj₁ ([UF] ⊢Δ [σ]′)
         [σF]′ = proj₁ ([F] ⊢Δ [σ]′)
         ⊢F′ = escape [σF]′
         [σF]ₜ′ = proj₁ ([Fₜ] ⊢Δ [σ]′)
         ⊢Fₜ′ = escapeTerm [σUF]′ [σF]ₜ′
         [σUG]′ = proj₁ ([UG] {σ = liftSubst σ′} (⊢Δ ∙ ⊢F′)
                             (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]′))
         [σG]ₜ′ = proj₁ ([Gₜ] (⊢Δ ∙ ⊢F′)
                             (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]′))
         ⊢Gₜ′ = escapeTerm [σUG]′ [σG]ₜ′
         [σtu]′ = proj₁ ([tu] (⊢Δ) [σ]′)
         [σ∃FG]′ = proj₁ ([∃FG] ⊢Δ [σ]′)
         ⊢tu′ = escapeTerm [σ∃FG]′ [σtu]′
         ⊢snd′ = sndⱼ {F = subst σ′ F} {G = subst (liftSubst σ′) G} {t = subst σ′ tu}
                   ⊢Fₜ′ ⊢Gₜ′ ⊢tu′
         [σG[fsttu]′] = proj₁ ([G[fsttu]] ⊢Δ [σ]′)
         ⊢sndSubst′ = PE.subst (λ x → _ ⊢ _ ∷ x  ^ _) (PE.sym (singleSubstLift G (fst tu))) ⊢snd′
         [σG[fsttu]≡σG[fsttu]′] = proj₂ ([G[fsttu]] ⊢Δ [σ]) [σ]′ [σ≡σ′]
         ⊢σG[fsttu]≡σG[fsttu]′ = escapeEq [σG[fsttu]] [σG[fsttu]≡σG[fsttu]′]
      in conv ⊢sndSubst′ (≅-eq (≅-sym ⊢σG[fsttu]≡σG[fsttu]′)) ) 
