{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Pair {{eqrel : EqRelSet}} where
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
open import Definition.LogicalRelation.Substitution.Introductions.Pi
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Valid lambda term construction.
⦅⦆ᵛ : ∀ {F G l∃ t u Γ l}
       ([Γ] : ⊩ᵛ Γ)
       ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ % , ι l∃ ] / [Γ])
       ([G] : Γ ∙ F ^ [ % , ι l∃ ] ⊩ᵛ⟨ l ⟩ G ^ [ % , ι l∃ ] / [Γ] ∙ [F]) 
       ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ F ^ [ % , ι l∃ ] / [Γ] / [F])
       ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ G [ t ] ^ [ % , ι l∃ ] / [Γ] / substS {F} {G} {t} [Γ] [F] [G] [t])
          → Γ ⊩ᵛ⟨ l ⟩ ⦅ t , u ⦆ ∷ ∃ F ▹ G ^ [ % , ι l∃ ] / [Γ] / ∃ᵛ {F} {G} [Γ] [F] [G]
⦅⦆ᵛ {F} {G} {l∃} {t} {u} {Γ} {l} [Γ] [F] [G] [t] [u] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [G[t]] = substS {F} {G} {t} [Γ] [F] [G] [t]
      [ΠFG] = Πᵛ {F = F} {G = G} (≡is≤ PE.refl) (≡is≤ PE.refl) [Γ] [F] [G]
      [σF] = proj₁ ([F] ⊢Δ [σ])
      ⊢F = escape [σF]
      [σG] = proj₁ ([G] (⊢Δ ∙ ⊢F) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
      ⊢G = escape [σG]
      [σt] = proj₁ ([t] (⊢Δ) [σ])
      ⊢t = escapeTerm [σF] [σt]
      [σu] = proj₁ ([u] (⊢Δ) [σ])
      [σG[t]] = proj₁ ([G[t]] ⊢Δ [σ])
      [σΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
      [σG[t]]′ = irrelevance′ (singleSubstLift G t) [σG[t]]
      [σu]′ = irrelevanceTerm′ (singleSubstLift G t) PE.refl PE.refl [σG[t]] [σG[t]]′ [σu]
      ⊢u = escapeTerm [σG[t]]′ [σu]′
      ⦅t,u⦆ⱼ = ⦅_,_,_,_⦆ⱼ {F = subst σ F} {G = subst (liftSubst σ) G} {t = subst σ t} {u = subst σ u}
                      ⊢F ⊢G ⊢t ⊢u
  in ⦅t,u⦆ⱼ , λ {σ′} [σ′] [σ≡σ′] →
            ⦅t,u⦆ⱼ ,
            let ⊢Γ = wfTerm ⊢t
                [σt′] = convTerm₂ [σF] (proj₁ ([F] ⊢Δ [σ′]))
                               (proj₂ ([F] ⊢Δ [σ]) [σ′] [σ≡σ′])
                               (proj₁ ([t] ⊢Δ [σ′]))
                [σt≡σt′] = proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]
                ⊢t′ = escapeTerm [σF] [σt′]
                _ , Πᵣ _ _ _  _ _ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]₁ [G]₁ G-ext =
                  extractMaybeEmb (Π-elim (proj₁ ([ΠFG] ⊢Δ [σ])))
                [σ′u] = proj₁ ([u] ⊢Δ [σ′])
                [σ′G[t]] = proj₁ ([G[t]] ⊢Δ [σ′])
                [σ′G[t]]′ = irrelevance′ (singleSubstLift G t) [σ′G[t]]
                [σG[t]]₂ = proj₂ ([G[t]] ⊢Δ [σ]) [σ′] [σ≡σ′]
                [σt]id = irrelevanceTerm′ (PE.sym (wk-id (subst σ F))) PE.refl PE.refl
                                          [σF] ([F]₁ id ⊢Γ)
                                          [σt]
                [σt′]id = irrelevanceTerm′ (PE.sym (wk-id (subst σ F))) PE.refl PE.refl 
                                          [σF] ([F]₁ id ⊢Γ)
                                          [σt′]
                [σt≡σt′]id = irrelevanceEqTerm′ (PE.sym (wk-id (subst σ F))) PE.refl PE.refl 
                                          [σF] ([F]₁ id ⊢Γ)
                                          [σt≡σt′]
                [G] = G-ext id ⊢Γ [σt]id [σt′]id [σt≡σt′]id
                [σG[t]]_id = irrelevance′ (PE.cong (λ x → x [ _ ]) (PE.sym (wk-lift-id (subst (liftSubst σ) G)))) [σG[t]]′
                [σ′G[t]]_id = irrelevance′ (PE.cong (λ x → x [ _ ]) (PE.sym (wk-lift-id (subst (liftSubst σ′) G)))) [σ′G[t]]′
                [Gσt≡σt′] = irrelevanceEq″ (PE.cong (λ x → x [ subst σ t ]) (wk-lift-id (subst (liftSubst σ) G)))
                                           (PE.cong (λ x → x [ subst σ′ t ]) (wk-lift-id (subst (liftSubst σ) G))) PE.refl PE.refl
                                           [σG[t]]_id [σG[t]]′ 
                                           (irrelevanceEq ([G]₁ id ⊢Γ [σt]id) [σG[t]]_id [G])
                [σG₁[t]] = irrelevance′ (PE.cong (λ x → x [ _ ]) (wk-lift-id (subst (liftSubst σ) G))) ([G]₁ id ⊢Γ [σt′]id)
                [σG₁[t]] = irrelevance′ (PE.cong (λ x → x [ _ ]) (wk-lift-id (subst (liftSubst σ) G))) ([G]₁ id ⊢Γ [σt′]id)
                [σG≡σG′] = proj₂ ([G[t]] ⊢Δ [σ]) [σ′] [σ≡σ′]
                [σ′u]′ = convTerm₂ [σG[t]] [σ′G[t]] [σG≡σG′] [σ′u]
                [σ′u]′′ = irrelevanceTerm′ (singleSubstLift G t) PE.refl PE.refl [σG[t]] [σG[t]]′ [σ′u]′
                [G] = G-ext id ⊢Γ [σt]id [σt′]id [σt≡σt′]id
                [σ′u]′ = convTerm₁ [σG[t]]′ [σG₁[t]]
                                   [Gσt≡σt′] [σ′u]′′ 
                ⊢u′ = escapeTerm [σG₁[t]] [σ′u]′
             in ⦅_,_,_,_⦆ⱼ {F = subst σ F} {G = subst (liftSubst σ) G} {t = subst σ′ t}
                       {u = subst σ′ u} ⊢F ⊢G ⊢t′ ⊢u′
