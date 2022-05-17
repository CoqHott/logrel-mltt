{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Sigma {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Weakening using (_∷_⊆_ ; _•ₜ_)
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Weakening
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Weakening
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Substitution.MaybeEmbed
import Definition.LogicalRelation.Substitution.Irrelevance as S
open import Definition.LogicalRelation.Substitution.Introductions.Universe
open import Definition.LogicalRelation.Substitution.Introductions.Pi

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Empty using (⊥; ⊥-elim)


-- Validity of ∃.
∃ᵛ : ∀ {F G Γ l}
     ([Γ] : ⊩ᵛ Γ)
     ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ % , ι ⁰ ] / [Γ])
   → Γ ∙ F ^ [ % , ι ⁰ ] ⊩ᵛ⟨ l ⟩ G ^ [ % , ι ⁰ ] / [Γ] ∙ [F]
   → Γ ⊩ᵛ⟨ l ⟩ ∃ F ▹ G ^ [ % , ι ⁰ ] / [Γ]
∃ᵛ {F} {G} {Γ} {l} [Γ] [F] [G] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [F]σ {σ′} [σ′] = [F] {σ = σ′} ⊢Δ [σ′]
      [σF] = proj₁ ([F]σ [σ])
      ⊢F {σ′} [σ′] = escape (proj₁ ([F]σ {σ′} [σ′]))
      ⊢F≡F = escapeEq [σF] (reflEq [σF])
      [G]σ {σ′} [σ′] = [G] {σ = liftSubst σ′} (⊢Δ ∙ ⊢F [σ′])
                           (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ′])
      ⊢G {σ′} [σ′] = escape (proj₁ ([G]σ {σ′} [σ′]))
      ⊢G≡G = escapeEq (proj₁ ([G]σ [σ])) (reflEq (proj₁ ([G]σ [σ])))
      ⊢∃F▹G = ∃ⱼ un-univ (⊢F [σ]) ▹ un-univ (⊢G [σ])
  in ∃ᵣ′ (subst σ F) (subst (liftSubst σ) G) (idRed:*: (univ ⊢∃F▹G)) (⊢F [σ]) (⊢G [σ]) (≅-univ (≅ₜ-∃-cong (⊢F [σ]) (≅-un-univ ⊢F≡F) (≅-un-univ ⊢G≡G)))
        
     ,  λ {σ′} [σ′] [σ≡σ′] → 
        let var0 = var (⊢Δ ∙ ⊢F [σ])
                       (PE.subst (λ x → 0 ∷ x ^ [ % , ι ⁰ ] ∈ (Δ ∙ subst σ F ^ [ % , ι ⁰ ]))
                                 (wk-subst F) here)
            [wk1σ] = wk1SubstS [Γ] ⊢Δ (⊢F [σ]) [σ]
            [wk1σ′] = wk1SubstS [Γ] ⊢Δ (⊢F [σ]) [σ′]
            [wk1σ≡wk1σ′] = wk1SubstSEq [Γ] ⊢Δ (⊢F [σ]) [σ] [σ≡σ′]
            [F][wk1σ] = proj₁ ([F] (⊢Δ ∙ ⊢F [σ]) [wk1σ])
            [F][wk1σ′] = proj₁ ([F] (⊢Δ ∙ ⊢F [σ]) [wk1σ′])
            var0′ = conv var0
                         (≅-eq (escapeEq [F][wk1σ]
                                             (proj₂ ([F] (⊢Δ ∙ ⊢F [σ]) [wk1σ])
                                                    [wk1σ′] [wk1σ≡wk1σ′])))
        in  ∃₌ _ _ (id (univ (∃ⱼ un-univ (⊢F [σ′]) ▹ un-univ (⊢G [σ′]))))
               (≅-univ (≅ₜ-∃-cong (⊢F [σ])
                                  (≅-un-univ (escapeEq (proj₁ ([F] ⊢Δ [σ]))
                                    (proj₂ ([F] ⊢Δ [σ]) [σ′] [σ≡σ′])))
                                  (≅-un-univ (escapeEq (proj₁ ([G]σ [σ])) (proj₂ ([G]σ [σ])
                                  ([wk1σ′] , neuTerm [F][wk1σ′] (var 0) var0′ (~-var var0′))
                                  ([wk1σ≡wk1σ′] , neuEqTerm [F][wk1σ]
                                  (var 0) (var 0) var0 var0 (~-var var0)))))))
             
-- Validity of ∃-congurence.
∃-congᵛ : ∀ {F G H E Γ l}
          ([Γ] : ⊩ᵛ Γ)
          ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ % , ι ⁰ ] / [Γ])
          ([G] : Γ ∙ F ^ [ % , ι ⁰ ] ⊩ᵛ⟨ l ⟩ G ^ [ % , ι ⁰ ] / [Γ] ∙ [F])
          ([H] : Γ ⊩ᵛ⟨ l ⟩ H ^ [ % , ι ⁰ ] / [Γ])
          ([E] : Γ ∙ H ^ [ % , ι ⁰ ] ⊩ᵛ⟨ l ⟩ E ^ [ % , ι ⁰ ] / [Γ] ∙ [H])
          ([F≡H] : Γ ⊩ᵛ⟨ l ⟩ F ≡ H ^ [ % , ι ⁰ ] / [Γ] / [F])
          ([G≡E] : Γ ∙ F ^ [ % , ι ⁰ ] ⊩ᵛ⟨ l ⟩ G ≡ E ^ [ % , ι ⁰ ] / [Γ] ∙ [F] / [G])
        → Γ ⊩ᵛ⟨ l ⟩ ∃ F ▹ G ≡ ∃ H ▹ E ^ [ % , ι ⁰ ] / [Γ] / ∃ᵛ {F} {G} [Γ] [F] [G]
∃-congᵛ {F} {G} {H} {E} [Γ] [F] [G] [H] [E] [F≡H] [G≡E] {σ = σ} ⊢Δ [σ] =
  let [∃FG] = ∃ᵛ {F} {G} [Γ] [F] [G]
      [σ∃FG] = proj₁ ([∃FG] ⊢Δ [σ])
      _ , ∃ᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ = extractMaybeEmb (∃-elim [σ∃FG])
      [σF] = proj₁ ([F] ⊢Δ [σ])
      ⊢σF = escape [σF]
      [σG] = proj₁ ([G] (⊢Δ ∙ ⊢σF) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
      ⊢σH = escape (proj₁ ([H] ⊢Δ [σ]))
      ⊢σE = escape (proj₁ ([E] (⊢Δ ∙ ⊢σH) (liftSubstS {F = H} [Γ] ⊢Δ [H] [σ])))
      ⊢σF≡σH = escapeEq [σF] ([F≡H] ⊢Δ [σ])
      ⊢σG≡σE = escapeEq [σG] ([G≡E] (⊢Δ ∙ ⊢σF) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))                                   
  in  ∃₌ (subst σ H)
         (subst (liftSubst σ) E)
         (id (univ (∃ⱼ (un-univ ⊢σH) ▹ (un-univ ⊢σE))))
         (≅-univ (≅ₜ-∃-cong ⊢σF (≅-un-univ ⊢σF≡σH) (≅-un-univ ⊢σG≡σE)))
                                
-- Validity of ∃ as a term.

∃ᵗᵛ₁ : ∀ {F G Γ} ([Γ] : ⊩ᵛ Γ)→
      let l    = ∞
          [UF] = maybeEmbᵛ {A = Univ % _} [Γ] (Uᵛ (proj₂ (levelBounded ⁰)) [Γ])
          [U∃] = maybeEmbᵛ {A = Univ % _} [Γ] (Uᵛ (proj₂ (levelBounded ⁰)) [Γ])
      in      
        ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ % , ι ⁰ ] / [Γ])
        ([UG] : Γ ∙ F ^ [ % , ι ⁰ ] ⊩ᵛ⟨ l ⟩ Univ % ⁰ ^ [ ! , next ⁰ ] / [Γ] ∙ [F])
      → Γ ⊩ᵛ⟨ l ⟩ F ∷ Univ % ⁰ ^ [ ! , next ⁰ ] / [Γ] / [UF]
      → Γ ∙ F ^ [ % , ι ⁰ ] ⊩ᵛ⟨ l ⟩ G ∷ Univ % ⁰ ^ [ ! , next ⁰ ] / [Γ] ∙ [F] / (λ {Δ} {σ} → [UG] {Δ} {σ})
      → ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
      → Δ ⊩⟨ l ⟩ subst σ (∃ F ▹ G) ∷ subst σ (Univ % ⁰) ^ [ ! , next ⁰ ] / proj₁ ([U∃] ⊢Δ [σ])
∃ᵗᵛ₁ {F} {G} {Γ} [Γ] [F] [UG] [Fₜ] [Gₜ] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let
      l = ∞
      ⁰≤ = ≡is≤ PE.refl
      [UF] = maybeEmbᵛ {A = Univ % _} [Γ] (Uᵛ (proj₂ (levelBounded ⁰)) [Γ])
      [U∃] = maybeEmbᵛ {A = Univ % _} [Γ] (Uᵛ (proj₂ (levelBounded ⁰)) [Γ])
      ⊢F = escape (proj₁ ([F] ⊢Δ [σ]))
      [liftσ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
      univΔ = proj₁ ([UF] ⊢Δ [σ]) 
      [Fₜ]σ {σ′} [σ′] = [Fₜ] {σ = σ′} ⊢Δ [σ′]
      [σF] = proj₁ ([Fₜ]σ [σ])
      ⊢Fₜ = escapeTerm univΔ (proj₁ ([Fₜ] ⊢Δ [σ]))
      ⊢F≡Fₜ = escapeTermEq univΔ (reflEqTerm univΔ (proj₁ ([Fₜ] ⊢Δ [σ])))
      [UG]σ = proj₁ ([UG] {σ = liftSubst σ} (⊢Δ ∙ ⊢F) [liftσ])
      [Gₜ]σ = proj₁ ([Gₜ] (⊢Δ ∙ ⊢F) [liftσ])
      ⊢Gₜ = escapeTerm [UG]σ [Gₜ]σ                       
      ⊢G≡Gₜ = escapeTermEq [UG]σ (reflEqTerm [UG]σ [Gₜ]σ)
      [F]₀ = univᵛ {F} [Γ] ⁰≤ [UF] [Fₜ]
      [UG]′ = S.irrelevance {A = Univ % ⁰} {r = [ ! , next ⁰ ]} (_∙_ {A = F} [Γ] [F]) (_∙_ {A = F} [Γ] [F]₀) (λ {Δ} {σ} → [UG] {Δ} {σ})
      [Gₜ]′ = S.irrelevanceTerm {l′ = ∞} {A = Univ % ⁰} {t = G} 
                                (_∙_ {A = F} [Γ] [F]) (_∙_ {A = F} [Γ] [F]₀)
                                (λ {Δ} {σ} → [UG] {Δ} {σ})
                                (λ {Δ} {σ} → [UG]′ {Δ} {σ})
                                [Gₜ]
      [G]₀ = univᵛ {G} (_∙_ {A = F} [Γ] [F]₀) ⁰≤
                   (λ {Δ} {σ} → [UG]′ {Δ} {σ}) (λ {Δ} {σ} → [Gₜ]′ {Δ} {σ})
      [Guniv] = univᵛ {A = G} (_∙_ {A = F} [Γ] [F]₀) ⁰≤ (λ {Δ} {σ} → [UG]′ {Δ} {σ}) [Gₜ]′
  in  Uₜ (∃ subst σ F ▹ subst (liftSubst σ) G) (idRedTerm:*: (∃ⱼ ⊢Fₜ ▹ ⊢Gₜ))  ∃ₙ (≅ₜ-∃-cong ⊢F ⊢F≡Fₜ ⊢G≡Gₜ) 
         (λ {ρ} {Δ₁} [ρ] ⊢Δ₁ → let
                            ⊢Fₜ' = Definition.Typed.Weakening.wkTerm [ρ] ⊢Δ₁ ⊢Fₜ
                            ⊢Gₜ' = Definition.Typed.Weakening.wkTerm
                                      (Definition.Typed.Weakening.lift [ρ]) (⊢Δ₁ ∙ univ ⊢Fₜ') ⊢Gₜ
                            [wkFₜ] = wkTerm [ρ] ⊢Δ₁ univΔ (proj₁ ([Fₜ] ⊢Δ [σ]))
                            [wkGₜ] = wkTerm (Definition.Typed.Weakening.lift [ρ]) (⊢Δ₁ ∙ univ ⊢Fₜ') (proj₁ ([UG] {σ = liftSubst σ} (⊢Δ ∙ ⊢F) [liftσ])) (proj₁ ([Gₜ] (⊢Δ ∙ ⊢F) [liftσ]))
                            [⊢weakF≡Fₜ] = escapeTermEq (wk [ρ] ⊢Δ₁ univΔ)
                                                       (reflEqTerm (wk [ρ] ⊢Δ₁ univΔ) [wkFₜ])
                            [⊢weakG≡Gₜ] = escapeTermEq (wk (Definition.Typed.Weakening.lift [ρ]) (⊢Δ₁ ∙ univ ⊢Fₜ') (proj₁ ([UG] (⊢Δ ∙ ⊢F) [liftσ])))
                                                       (reflEqTerm (wk (Definition.Typed.Weakening.lift [ρ]) (⊢Δ₁ ∙ univ ⊢Fₜ') (proj₁ ([UG] (⊢Δ ∙ ⊢F) [liftσ])))
                                                       (wkTerm (Definition.Typed.Weakening.lift [ρ]) (⊢Δ₁ ∙ univ ⊢Fₜ') (proj₁ ([UG] (⊢Δ ∙ ⊢F) [liftσ])) (proj₁ ([Gₜ] (⊢Δ ∙ ⊢F) [liftσ]))))
                            [wkFₜ]Type : ∀ {ρ₁ Δ₂} [ρ₁] ⊢Δ₂ → Δ₂ ⊩⟨ ι ⁰ ⟩ U.wk ρ₁ (U.wk ρ (subst σ F)) ^ [ % , ι ⁰ ]
                            [wkFₜ]Type = λ {ρ₁} {Δ₂} [ρ₁] ⊢Δ₂ → let [wkFₜ]Type = univEq (wk [ρ₁] ⊢Δ₂ (wk [ρ] ⊢Δ₁ univΔ))
                                                                      (wkTerm [ρ₁] ⊢Δ₂ (wk [ρ] ⊢Δ₁ univΔ) [wkFₜ])
                                                   in maybeEmb′ ⁰≤ [wkFₜ]Type
                            in ∃ᵣ′ (U.wk ρ (subst σ F)) (U.wk (lift ρ) (subst (liftSubst σ) G))
                                  (idRed:*: (univ (∃ⱼ ⊢Fₜ' ▹ ⊢Gₜ')))
                                  (univ ⊢Fₜ') (univ ⊢Gₜ') (≅-univ (≅ₜ-∃-cong (univ ⊢Fₜ') [⊢weakF≡Fₜ] [⊢weakG≡Gₜ])))



 
∃ᵗᵛ : ∀ {F G Γ} ([Γ] : ⊩ᵛ Γ)→
      let l    = ∞
          [UF] = maybeEmbᵛ {A = Univ % _} [Γ] (Uᵛ (proj₂ (levelBounded ⁰)) [Γ])
          [U∃] = maybeEmbᵛ {A = Univ % _} [Γ] (Uᵛ (proj₂ (levelBounded ⁰)) [Γ])
      in      
        ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ % , ι ⁰ ] / [Γ])
        ([UG] : Γ ∙ F ^ [ % , ι ⁰ ] ⊩ᵛ⟨ l ⟩ Univ % ⁰ ^ [ ! , next ⁰ ] / [Γ] ∙ [F])
      → Γ ⊩ᵛ⟨ l ⟩ F ∷ Univ % ⁰ ^ [ ! , next ⁰ ] / [Γ] / [UF]
      → Γ ∙ F ^ [ % , ι ⁰ ] ⊩ᵛ⟨ l ⟩ G ∷ Univ % ⁰ ^ [ ! , next ⁰ ] / [Γ] ∙ [F] / (λ {Δ} {σ} → [UG] {Δ} {σ})
      → Γ ⊩ᵛ⟨ l ⟩ ∃ F ▹ G ∷ Univ % ⁰ ^ [ ! , next ⁰ ] / [Γ] / [U∃]
∃ᵗᵛ {F} {G} {Γ} [Γ] [F] [UG] [Fₜ] [Gₜ] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let l = ∞
      ⁰≤ = ≡is≤ PE.refl
      [UF] = maybeEmbᵛ {A = Univ % _} [Γ] (Uᵛ (proj₂ (levelBounded ⁰)) [Γ])
  in ∃ᵗᵛ₁ {F} {G} {Γ} [Γ] [F] (λ {Δ} {σ} → [UG] {Δ} {σ}) [Fₜ] [Gₜ] {Δ = Δ} {σ = σ} ⊢Δ [σ]
    , (λ {σ′} [σ′] [σ≡σ′] → 
         let ⊢F = escape (proj₁ ([F] ⊢Δ [σ]))
             [liftσ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
             univΔ = proj₁ ([UF] ⊢Δ [σ]) 
             [Fₜ]σ {σ′} [σ′] = [Fₜ] {σ = σ′} ⊢Δ [σ′]
             [σF] = proj₁ ([Fₜ]σ [σ])
             ⊢Fₜ = escapeTerm univΔ (proj₁ ([Fₜ] ⊢Δ [σ]))
             ⊢F≡Fₜ = escapeTermEq univΔ (reflEqTerm univΔ (proj₁ ([Fₜ] ⊢Δ [σ])))
             [liftσ′] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ′]
             [wk1σ] = wk1SubstS [Γ] ⊢Δ ⊢F [σ]
             [wk1σ′] = wk1SubstS [Γ] ⊢Δ ⊢F [σ′]
             var0 = conv (var (⊢Δ ∙ ⊢F)
                         (PE.subst (λ x → 0 ∷ x ^ [ % , ι ⁰ ] ∈ (Δ ∙ subst σ F ^ [ % , ι ⁰ ]))
                                   (wk-subst F) here))
                    (≅-eq (escapeEq (proj₁ ([F] (⊢Δ ∙ ⊢F) [wk1σ]))
                                        (proj₂ ([F] (⊢Δ ∙ ⊢F) [wk1σ]) [wk1σ′]
                                               (wk1SubstSEq [Γ] ⊢Δ ⊢F [σ] [σ≡σ′]))))
             [liftσ′]′ = [wk1σ′]
                       , neuTerm (proj₁ ([F] (⊢Δ ∙ ⊢F) [wk1σ′])) (var 0)
                                 var0 (~-var var0)
             ⊢F′ = escape (proj₁ ([F] ⊢Δ [σ′]))
             univΔ = proj₁ ([UF] ⊢Δ [σ]) 
             univΔ′ = proj₁ ([UF] ⊢Δ [σ′]) 
             [Fₜ]σ {σ′} [σ′] = [Fₜ] {σ = σ′} ⊢Δ [σ′]
             [σF] = proj₁ ([Fₜ]σ [σ])
             ⊢Fₜ′ = escapeTerm univΔ′ (proj₁ ([Fₜ] ⊢Δ [σ′]))
             ⊢Gₜ′ = escapeTerm (proj₁ ([UG] {σ = liftSubst σ′} (⊢Δ ∙ ⊢F′) [liftσ′]))
                                  (proj₁ ([Gₜ] (⊢Δ ∙ ⊢F′) [liftσ′]))
             ⊢F≡F′ = escapeTermEq univΔ (proj₂ ([Fₜ] ⊢Δ [σ]) [σ′] [σ≡σ′])
             ⊢G≡G′ = escapeTermEq (proj₁ ([UG] (⊢Δ ∙ ⊢F) [liftσ]))
                                     (proj₂ ([Gₜ] (⊢Δ ∙ ⊢F) [liftσ]) [liftσ′]′
                                            (liftSubstSEq {F = F} [Γ] ⊢Δ [F] [σ] [σ≡σ′]))
             [F]₀ = univᵛ {F} [Γ] (≡is≤ PE.refl) [UF] [Fₜ]
             [UG]′ = S.irrelevance {A = Univ % ⁰} {r = [ ! , next ⁰ ]} (_∙_ {A = F} [Γ] [F]) (_∙_ {A = F} [Γ] [F]₀) (λ {Δ} {σ} → [UG] {Δ} {σ})
             [Gₜ]′ = S.irrelevanceTerm {l′ = ∞} {A = Univ % ⁰} {t = G} 
                                (_∙_ {A = F} [Γ] [F]) (_∙_ {A = F} [Γ] [F]₀)
                                (λ {Δ} {σ} → [UG] {Δ} {σ})
                                (λ {Δ} {σ} → [UG]′ {Δ} {σ})
                                [Gₜ]
             [G]₀ = univᵛ {G} (_∙_ {A = F} [Γ] [F]₀) ⁰≤
                   (λ {Δ} {σ} → [UG]′ {Δ} {σ}) (λ {Δ} {σ} → [Gₜ]′ {Δ} {σ})
             [∃FG-cong] = ∃-congᵛ {F} {G} {F} {G} [Γ] [F]₀ [G]₀ [F]₀ [G]₀
                                  (λ ⊢Δ₁ [σ]₁ → proj₂ ([F]₀ ⊢Δ₁ [σ]₁) [σ]₁ (reflSubst [Γ] ⊢Δ₁ [σ]₁))
                                  (λ {Δ₁} {σ₁} ⊢Δ₁ [σ]₁ → proj₂ ([G]₀ ⊢Δ₁ [σ]₁) [σ]₁ (reflSubst {σ₁} ((_∙_ {A = F} [Γ] [F]₀)) ⊢Δ₁ [σ]₁))
             [∃FG]ᵗ  = ∃ᵗᵛ₁ {F} {G} {Γ} [Γ] [F] (λ {Δ} {σ} → [UG] {Δ} {σ}) [Fₜ] [Gₜ] {Δ = Δ} {σ = σ} ⊢Δ [σ]
             [∃FG]ᵗ′ = ∃ᵗᵛ₁ {F} {G} {Γ} [Γ] [F] (λ {Δ} {σ} → [UG] {Δ} {σ}) [Fₜ] [Gₜ] {Δ = Δ} {σ = σ′} ⊢Δ [σ′]             
             [∃FG]  = ∃ᵛ {F} {G} {Γ} [Γ] [F]₀ [G]₀
          in Uₜ₌ [∃FG]ᵗ
                 [∃FG]ᵗ′
                 (≅ₜ-∃-cong ⊢F ⊢F≡F′ ⊢G≡G′)
                 (λ {ρ} {Δ₁} [ρ] ⊢Δ₁ → let [∃FG-cong]′ = [∃FG-cong] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ])
                                           X = irrelevanceEq″ (PE.sym (wk-subst (∃ F ▹ G)))
                                                              (PE.sym (wk-subst (∃ F ▹ G)))
                                                              PE.refl PE.refl 
                                                              (proj₁ ([∃FG] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]))) 
                                                              (LogRel._⊩¹U_∷_^_/_.[t] [∃FG]ᵗ [ρ] ⊢Δ₁)
                                                              [∃FG-cong]′
                                           [σ∃FG] = proj₁ ([∃FG] ⊢Δ [σ])
                                           _ , ∃ᵣ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ = extractMaybeEmb (∃-elim [σ∃FG])
                                           [ρσ] =  wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]
                                           [σF]₀ = proj₁ ([F]₀ ⊢Δ₁ [ρσ])
                                           ⊢σF₀ = escape [σF]₀
                                           [σG]₀ = proj₁ ([G]₀ (⊢Δ₁ ∙ ⊢σF₀) (liftSubstS {F = F} [Γ] ⊢Δ₁ [F]₀ [ρσ]))
                                           [ρσ′] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ′]
                                           [σF′]₀ = proj₁ ([F]₀ ⊢Δ₁ [ρσ′])
                                           ⊢σH = escape (proj₁ ([F]₀ ⊢Δ₁ [ρσ′]))
                                           ⊢σE = escape (proj₁ ([G]₀ (⊢Δ₁ ∙ ⊢σH) (liftSubstS {F = F} [Γ] ⊢Δ₁ [F]₀ [ρσ′])))
                                           univΔ₁ = proj₁ ([UF] ⊢Δ₁ [ρσ])
                                           [ρσ≡ρσ′] = wkSubstSEq [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ] [σ≡σ′]
                                           [σF≡σH] = univEqEq univΔ₁ [σF]₀ (proj₂ ([Fₜ] ⊢Δ₁ [ρσ]) [ρσ′] [ρσ≡ρσ′])
                                           ⊢σF≡σH = escapeEq [σF]₀ [σF≡σH]
                                           [σF] = proj₁ ([F] ⊢Δ₁ [ρσ])
                                           ⊢σF = escape [σF]
                                           liftσ = liftSubstS {F = F} [Γ] ⊢Δ₁ [F] [ρσ]
                                           [wk1σ] = wk1SubstS [Γ] ⊢Δ₁ ⊢σF [ρσ]
                                           [wk1σ′] = wk1SubstS [Γ] ⊢Δ₁ ⊢σF [ρσ′]
                                           var0 = conv (var (⊢Δ₁ ∙ ⊢σF)
                                                            (PE.subst (λ x → 0 ∷ x ^ [ % , ι ⁰ ] ∈ (Δ₁ ∙ subst (ρ •ₛ σ) F ^ [ % , ι ⁰ ]))
                                                            (wk-subst F) here))
                                                       (≅-eq (escapeEq (proj₁ ([F] (⊢Δ₁ ∙ ⊢σF) [wk1σ]))
                                                            (proj₂ ([F] (⊢Δ₁ ∙ ⊢σF) [wk1σ]) [wk1σ′]
                                                            (wk1SubstSEq [Γ] ⊢Δ₁ ⊢σF [ρσ] [ρσ≡ρσ′]))))
                                           [liftσ′]′  : (Δ₁ ∙ subst (ρ •ₛ σ) F ^ [ % , ι ⁰ ]) ⊩ˢ liftSubst (ρ •ₛ σ′) ∷
                                                            Γ ∙ F ^ [ % , ι ⁰ ] / [Γ] ∙ [F] /
                                                        (⊢Δ₁ ∙ escape (proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]))))
                                           [liftσ′]′ = [wk1σ′]
                                                       , neuTerm (proj₁ ([F] (⊢Δ₁ ∙ ⊢σF) [wk1σ′])) (var 0)
                                                                 var0 (~-var var0)
                                           liftσ′ = liftSubstS {F = F} [Γ] ⊢Δ₁ [F] [ρσ′]
                                           univΔ₁G = proj₁ ([UG] (⊢Δ₁ ∙ ⊢σF) liftσ)
                                           [σG≡σE] = univEqEq univΔ₁G [σG]₀ (proj₂ ([Gₜ] {σ = liftSubst (ρ •ₛ σ)} (⊢Δ₁ ∙ ⊢σF) liftσ) [liftσ′]′
                                                             (liftSubstSEq {F = F} [Γ] ⊢Δ₁ [F] [ρσ] [ρσ≡ρσ′]))
                                           ⊢σG≡σE = escapeEq [σG]₀ [σG≡σE]                                   
                                           X = ∃₌  (subst (ρ •ₛ σ′) F)
                                                   (subst (liftSubst (ρ •ₛ σ′)) G)
                                                   (id (univ (∃ⱼ (un-univ ⊢σH) ▹ (un-univ ⊢σE))))
                                                   ((≅-univ (≅ₜ-∃-cong ⊢σF (≅-un-univ ⊢σF≡σH) (≅-un-univ ⊢σG≡σE))))
                                        in irrelevanceEq″ (PE.sym (wk-subst (∃ F ▹ G)))
                                                          (PE.sym (wk-subst (∃ F ▹ G)))
                                                          PE.refl PE.refl 
                                                          (proj₁ ([∃FG] ⊢Δ₁ [ρσ])) 
                                                          (LogRel._⊩¹U_∷_^_/_.[t] [∃FG]ᵗ [ρ] ⊢Δ₁)
                                                          X))
                                                          

-- Validity of ∃-congurence as a term equality.
∃-congᵗᵛ : ∀ {F G H E Γ} ([Γ] : ⊩ᵛ Γ) →
        let l    = ∞
            [UF] = maybeEmbᵛ {A = Univ % _} [Γ] (Uᵛ (proj₂ (levelBounded ⁰)) [Γ])
            [U∃] = maybeEmbᵛ {A = Univ % _} [Γ] (Uᵛ (proj₂ (levelBounded ⁰)) [Γ])
        in      
           ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ % , ι ⁰ ] / [Γ])
           ([H] : Γ ⊩ᵛ⟨ l ⟩ H ^ [ % , ι ⁰ ] / [Γ])
           ([UG] : Γ ∙ F ^ [ % , ι ⁰ ] ⊩ᵛ⟨ l ⟩ Univ % ⁰ ^ [ ! , next ⁰ ] / [Γ] ∙ [F])
           ([UE] : Γ ∙ H ^ [ % , ι ⁰ ] ⊩ᵛ⟨ l ⟩ Univ % ⁰ ^ [ ! , next ⁰ ] / [Γ] ∙ [H])
           ([F]ₜ : Γ ⊩ᵛ⟨ l ⟩ F ∷ Univ % ⁰ ^ [ ! , next ⁰ ] / [Γ] / [UF])
           ([G]ₜ : Γ ∙ F ^ [ % , ι ⁰ ] ⊩ᵛ⟨ l ⟩ G ∷ Univ % ⁰ ^ [ ! , next ⁰ ] / [Γ] ∙ [F] / (λ {Δ} {σ} → [UG] {Δ} {σ}))
           ([H]ₜ : Γ ⊩ᵛ⟨ l ⟩ H ∷ Univ % ⁰ ^ [ ! , next ⁰ ] / [Γ] / [UF])
           ([E]ₜ :  Γ ∙ H ^ [ % , ι ⁰ ] ⊩ᵛ⟨ l ⟩ E ∷ Univ % ⁰ ^ [ ! , next ⁰ ] / [Γ] ∙ [H] / (λ {Δ} {σ} → [UE] {Δ} {σ}))
           ([F≡H]ₜ : Γ ⊩ᵛ⟨ l ⟩ F ≡ H ∷ Univ % ⁰ ^ [ ! , next ⁰ ] / [Γ] / [UF])
           ([G≡E]ₜ : Γ ∙ F ^ [ % , ι ⁰ ] ⊩ᵛ⟨ l ⟩ G ≡ E ∷ Univ % ⁰ ^ [ ! , next ⁰ ] / [Γ] ∙ [F]
                                  / (λ {Δ} {σ} → [UG] {Δ} {σ}))
         → Γ ⊩ᵛ⟨ l ⟩ ∃ F ▹ G ≡ ∃ H ▹ E ∷ Univ % ⁰ ^ [ ! , next ⁰ ] / [Γ] / [U∃]
∃-congᵗᵛ {F} {G} {H} {E} {Γ}
         [Γ] [F] [H] [UG] [UE] [F]ₜ [G]ₜ [H]ₜ [E]ₜ [F≡H]ₜ [G≡E]ₜ {Δ} {σ} ⊢Δ [σ] =
  let l = ∞
      ⁰ = ⁰
      ⁰≤ = ≡is≤ PE.refl
      [UF] = maybeEmbᵛ {A = Univ % _} [Γ] (Uᵛ (proj₂ (levelBounded ⁰)) [Γ])
      [∃FG]ᵗ = ∃ᵗᵛ₁ {F} {G} {Γ} [Γ] [F] (λ {Δ} {σ} → [UG] {Δ} {σ}) [F]ₜ [G]ₜ {Δ = Δ} {σ = σ} ⊢Δ [σ]
      [∃HE]ᵗ = ∃ᵗᵛ₁ {H} {E} {Γ} [Γ] [H] (λ {Δ} {σ} → [UE] {Δ} {σ}) [H]ₜ [E]ₜ {Δ = Δ} {σ = σ} ⊢Δ [σ]
      ⊢F = escape (proj₁ ([F] ⊢Δ [σ]))
      [liftσ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
      univΔ = proj₁ ([UF] ⊢Δ [σ]) 
      [Fₜ]σ {σ′} [σ′] = [F]ₜ {σ = σ′} ⊢Δ [σ′]
      [σF] = proj₁ ([Fₜ]σ [σ])
      [G] = maybeEmbᵛ {A = G} (_∙_ {A = F} [Γ] [F]) (univᵛ {G} (_∙_ {A = F} [Γ] [F]) ⁰≤ (λ {Δ} {σ} → [UG] {Δ} {σ}) [G]ₜ)
      [E] = maybeEmbᵛ {A = E} (_∙_ {A = H} [Γ] [H]) (univᵛ {E} (_∙_ {A = H} [Γ] [H]) ⁰≤ (λ {Δ} {σ} → [UE] {Δ} {σ}) [E]ₜ)
      [F≡H] = univEqᵛ {F} {H} [Γ] [UF] [F] [F≡H]ₜ
      [G≡E] = univEqᵛ {G} {E} (_∙_ {A = F} [Γ] [F]) (λ {Δ} {σ} → [UG] {Δ} {σ}) [G] [G≡E]ₜ
  in Uₜ₌ [∃FG]ᵗ [∃HE]ᵗ (≅ₜ-∃-cong ⊢F (escapeTermEq univΔ ([F≡H]ₜ ⊢Δ [σ]))
                                    (escapeTermEq (proj₁ ([UG] (⊢Δ ∙ ⊢F) [liftσ]))
                                          ([G≡E]ₜ (⊢Δ ∙ ⊢F) [liftσ])))
         λ {ρ} {Δ₁} [ρ] ⊢Δ₁ → let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]
                                  X = ∃-congᵛ {F} {G} {H} {E} {Γ} [Γ] [F] [G] [H] [E] [F≡H] [G≡E] ⊢Δ₁ [ρσ]
                              in irrelevanceEq″ (PE.sym (wk-subst (∃ F ▹ G)))
                                                (PE.sym (wk-subst (∃ H ▹ E))) PE.refl PE.refl
                                                (proj₁ (∃ᵛ {F} {G} [Γ] [F] [G] ⊢Δ₁ [ρσ])) (LogRel._⊩¹U_∷_^_/_.[t] [∃FG]ᵗ [ρ] ⊢Δ₁) X 

-- Validity of non-dependent sum types.
××ᵛ : ∀ {F G Γ l}
      ([Γ] : ⊩ᵛ Γ)
      ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ % , ι ⁰ ] / [Γ])
    → Γ ⊩ᵛ⟨ l ⟩ G ^ [ % , ι ⁰ ] / [Γ]
    → Γ ⊩ᵛ⟨ l ⟩ F ×× G ^ [ % , ι ⁰ ] / [Γ]
××ᵛ {F} {G} [Γ] [F] [G] =
  ∃ᵛ {F} {wk1 G} [Γ] [F] (wk1ᵛ {G} {F} [Γ] [F] [G])

-- Validity of non-dependent sum type congurence.
××-congᵛ : ∀ {F F′ G G′ Γ l}
           ([Γ] : ⊩ᵛ Γ)
           ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ % , ι ⁰ ] / [Γ])
           ([F′] : Γ ⊩ᵛ⟨ l ⟩ F′ ^ [ % , ι ⁰ ] / [Γ])
           ([F≡F′] : Γ ⊩ᵛ⟨ l ⟩ F ≡ F′ ^ [ % , ι ⁰ ] / [Γ] / [F])
           ([G] : Γ ⊩ᵛ⟨ l ⟩ G ^ [ % , ι ⁰ ] / [Γ])
           ([G′] : Γ ⊩ᵛ⟨ l ⟩ G′ ^ [ % , ι ⁰ ] / [Γ])
           ([G≡G′] : Γ ⊩ᵛ⟨ l ⟩ G ≡ G′ ^ [ % , ι ⁰ ] / [Γ] / [G])
         → Γ ⊩ᵛ⟨ l ⟩ F ×× G ≡ F′ ×× G′ ^ [ % , ι ⁰ ] / [Γ] / ××ᵛ {F} {G} [Γ] [F] [G]
××-congᵛ {F} {F′} {G} {G′} [Γ] [F] [F′] [F≡F′] [G] [G′] [G≡G′] =
  ∃-congᵛ {F} {wk1 G} {F′} {wk1 G′} [Γ]
          [F] (wk1ᵛ {G} {F} [Γ] [F] [G])
          [F′] (wk1ᵛ {G′} {F′} [Γ] [F′] [G′])
          [F≡F′] (wk1Eqᵛ {G} {G′} {F} [Γ] [F] [G] [G≡G′])

××ᵗᵛ : ∀ {F G Γ} ([Γ] : ⊩ᵛ Γ)→
      let l    = ∞
          [U] = maybeEmbᵛ {A = Univ % _} [Γ] (Uᵛ (proj₂ (levelBounded ⁰)) [Γ])
      in      
        ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ % , ι ⁰ ] / [Γ])
      → Γ ⊩ᵛ⟨ l ⟩ F ∷ Univ % ⁰ ^ [ ! , next ⁰ ] / [Γ] / [U]
      → Γ ⊩ᵛ⟨ l ⟩ G ∷ Univ % ⁰ ^ [ ! , next ⁰ ] / [Γ] / (λ {Δ} {σ} → [U] {Δ} {σ})
      → Γ ⊩ᵛ⟨ l ⟩ F ×× G ∷ Univ % ⁰ ^ [ ! , next ⁰ ] / [Γ] / [U]
××ᵗᵛ {F} {G} [Γ] [F] [Fₜ] [Gₜ] =
  let l    = ∞
      [U] = maybeEmbᵛ {A = Univ % _} [Γ] (Uᵛ (proj₂ (levelBounded ⁰)) [Γ])
      [Gₜ]′ = wk1ᵗᵛ {F} {G} {[ % , ι ⁰ ]} {%} {⁰} [Γ] [F] [Gₜ]
      [wU] = maybeEmbᵛ {A = Univ % _} (_∙_ {A = F} [Γ] [F]) (λ {Δ} {σ} → Uᵛ (proj₂ (levelBounded ⁰)) (_∙_ {A = F} [Γ] [F]) {Δ} {σ})
      [wU]′ = wk1ᵛ {Univ _ _ } {F} [Γ] [F] [U]
  in ∃ᵗᵛ {F} {wk1 G} [Γ] [F] (λ {Δ} {σ} → [wU]′ {Δ} {σ}) [Fₜ]
        (S.irrelevanceTerm {A = Univ _ _} {t = wk1 G} (_∙_ {A = F} [Γ] [F]) (_∙_ {A = F} [Γ] [F])
                                                      (λ {Δ} {σ} → [wU] {Δ} {σ}) (λ {Δ} {σ} → [wU]′ {Δ} {σ}) [Gₜ]′) 

