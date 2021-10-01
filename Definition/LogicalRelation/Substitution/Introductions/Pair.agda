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

-- Valid pair construction.
⦅⦆ᵛ : ∀ {F G l∃ t u Γ l}
       ([Γ] : ⊩ᵛ Γ)
       ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ % , ι l∃ ] / [Γ])
       ([G] : Γ ∙ F ^ [ % , ι l∃ ] ⊩ᵛ⟨ l ⟩ G ^ [ % , ι l∃ ] / [Γ] ∙ [F]) 
       ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ F ^ [ % , ι l∃ ] / [Γ] / [F])
       ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ G [ t ] ^ [ % , ι l∃ ] / [Γ] / substS {F} {G} {t} [Γ] [F] [G] [t])
          → Γ ⊩ᵛ⟨ l ⟩ ⦅ G , t , u ⦆ ∷ ∃ F ▹ G ^ [ % , ι l∃ ] / [Γ] / ∃ᵛ {F} {G} [Γ] [F] [G]
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
                [σt′] = proj₁ ([t] ⊢Δ [σ′])
                [σt≡σt′] = proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]
                [σF′] = proj₁ ([F] ⊢Δ [σ′])
                ⊢F′ = escape [σF′]
                ⊢t′ = escapeTerm [σF′] [σt′]
                [σG′] = proj₁ ([G] {σ = liftSubst σ′} (⊢Δ ∙ ⊢F′) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ′]))
                ⊢G′ = escape [σG′]
                _ , Πᵣ _ _ _  _ _ F′ G′ D′ _ _  A≡A′ [F]₁ [G]₁ G-ext =
                  extractMaybeEmb (Π-elim (proj₁ ([ΠFG] ⊢Δ [σ′])))
                [σ′u] = proj₁ ([u] ⊢Δ [σ′])               
                [σ′G[t]] = proj₁ ([G[t]] ⊢Δ [σ′])
                [σ′G[t]]′ = irrelevance′ (singleSubstLift G t) [σ′G[t]]
                [σ′u]′ = irrelevanceTerm′ (singleSubstLift G t) PE.refl PE.refl [σ′G[t]] [σ′G[t]]′ [σ′u]
                ⊢u′ = escapeTerm [σ′G[t]]′ [σ′u]′ 
                pair' =  ⦅_,_,_,_⦆ⱼ {F = subst σ′ F} {G = subst (liftSubst σ′) G} {t = subst σ′ t}
                                  {u = subst σ′ u} ⊢F′ ⊢G′ ⊢t′ ⊢u′
                [σ′≡σ]  = symS [Γ] ⊢Δ [σ] [σ′] [σ≡σ′]
                [σF′≡σF] = proj₂ ([F] ⊢Δ [σ′]) [σ] [σ′≡σ]
                σF′≡σF = escapeEq [σF′] [σF′≡σF]
                [liftσ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
                [wk1σ′] = wk1SubstS [Γ] ⊢Δ ⊢F′ [σ′]
                [wk1σ] = wk1SubstS [Γ] ⊢Δ ⊢F′ [σ]
                foo = proj₁ ([F] (⊢Δ ∙ ⊢F′) [wk1σ′])
                [liftσ′] : (Δ ∙ subst σ′ F ^ [ % , ι l∃ ]) ⊩ˢ liftSubst σ ∷
                           Γ ∙ F ^ [ % , ι l∃ ] / [Γ] ∙ [F] / (⊢Δ ∙ escape (proj₁ ([F] ⊢Δ [σ′])))
                [liftσ′] =   let ⊢F = escape (proj₁ ([F] ⊢Δ [σ]))
                                 [tailσ] = wk1SubstS {F = subst σ′ F} [Γ] ⊢Δ (escape (proj₁ ([F] ⊢Δ [σ′]))) [σ]
                                 var0′ : (Δ ∙ subst σ′ F ^ [ % , ι l∃ ]) ⊢ var 0 ∷ subst (wk1Subst σ′) F ^ [ % , ι l∃ ]
                                 var0′ = var (⊢Δ ∙ ⊢F′) (PE.subst (λ x → 0 ∷ x ^ _ ∈ (Δ ∙ subst σ′ F ^ _))
                                             (wk-subst F) here)
                                 var0 = conv var0′ (≅-eq (escapeEq (proj₁ ([F] (⊢Δ ∙ ⊢F′) [wk1σ′])) (proj₂ ([F] (⊢Δ ∙ ⊢F′) [wk1σ′]) [wk1σ]
                                                            (wk1SubstSEq [Γ] ⊢Δ ⊢F′ [σ′] [σ′≡σ]))))
                             in  [tailσ] , neuTerm (proj₁ ([F] (⊢Δ ∙ ⊢F′) [tailσ])) (var 0)
                                 var0 (~-var var0)
                [σG′≡σG] = proj₂ ([G] (⊢Δ ∙ ⊢F′) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ′] )) [liftσ′]
                                 (liftSubstSEq {F = F} [Γ] ⊢Δ [F] [σ′] (symS [Γ] ⊢Δ [σ] [σ′] [σ≡σ′]))
                σG′≡σG = escapeEq [σG′] [σG′≡σG]
             in conv pair' (univ (∃-cong ⊢F′ (un-univ≡ (≅-eq σF′≡σF)) (un-univ≡ (≅-eq σG′≡σG))) )
