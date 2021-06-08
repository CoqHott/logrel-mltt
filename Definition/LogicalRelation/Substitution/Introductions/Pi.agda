{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Pi {{eqrel : EqRelSet}} where
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

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Empty using (⊥; ⊥-elim)


GappGen : ∀ {F G Γ rF lF lG rΠ l Δ σ ρ Δ₁}
         ([Γ] : ⊩ᵛ Γ)
         ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / [Γ])
         → Γ ∙ F ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ G ^ [ rΠ , ι lG ] / [Γ] ∙ [F]  
         → ∀ ⊢Δ [σ] a ([ρ] : ρ ∷ Δ₁ ⊆ Δ) (⊢Δ₁ : ⊢ Δ₁)
         ([a] : Δ₁ ⊩⟨ l ⟩ a ∷ subst (ρ •ₛ σ) F ^ [ rF , ι lF ]
                / proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ])))
         → Σ (Δ₁ ⊩⟨ l ⟩ subst (consSubst (ρ •ₛ σ) a) G ^ [ rΠ , ι lG ])
               (λ [Aσ] →
               {σ′ : Nat → Term} →
               (Σ (Δ₁ ⊩ˢ tail σ′ ∷ Γ / [Γ] / ⊢Δ₁)
               (λ [tailσ] →
                  Δ₁ ⊩⟨ l ⟩ head σ′ ∷ subst (tail σ′) F ^ [ rF , ι lF ] / proj₁ ([F] ⊢Δ₁ [tailσ]))) →
               Δ₁ ⊩ˢ consSubst (ρ •ₛ σ) a ≡ σ′ ∷ Γ ∙ F ^ [ rF , ι lF ] /
               [Γ] ∙ [F] / ⊢Δ₁ /
               consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]) [F]
               [a] →
               Δ₁ ⊩⟨ l ⟩ subst (consSubst (ρ •ₛ σ) a) G ≡
               subst σ′ G ^ [ rΠ , ι lG ] / [Aσ])
GappGen {F} {G} {Γ} {rF} {lF} {lG} {rΠ} {l} {Δ} {σ} {ρ} {Δ₁} [Γ] [F] [G] ⊢Δ [σ] a [ρ] ⊢Δ₁ [a] =
 [G] {σ = consSubst (ρ •ₛ σ) a} ⊢Δ₁
                              (consSubstS {t = a} {A = F} [Γ] ⊢Δ₁
                                          (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ])
                                          [F] [a])

Gapp : ∀ {F G Γ rF lF lG rΠ l Δ σ ρ Δ₁}
         ([Γ] : ⊩ᵛ Γ)
         ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / [Γ])
         → Γ ∙ F ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ G ^ [ rΠ , ι lG ] / [Γ] ∙ [F]  
         → ∀ ⊢Δ [σ] a ([ρ] : ρ ∷ Δ₁ ⊆ Δ) (⊢Δ₁ : ⊢ Δ₁)
         ([a] : Δ₁ ⊩⟨ l ⟩ a ∷ subst (ρ •ₛ σ) F ^ [ rF , ι lF ]
                / proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ])))
         → Δ₁ ⊩⟨ l ⟩ U.wk (lift ρ) (subst (liftSubst σ) G) [ a ] ^ [ rΠ , ι lG ]
Gapp {F} {G} {Γ} {rF} {lF} {lG} {rΠ} {l} {Δ} {σ} {ρ} {Δ₁} [Γ] [F] [G] ⊢Δ [σ] a [ρ] ⊢Δ₁ [a] =
  irrelevance′ (PE.sym (singleSubstWkComp a σ G)) (proj₁ (GappGen {F} {G} {Γ} {rF} {lF} {lG} {rΠ} {l} {Δ} {σ} {ρ} {Δ₁} [Γ] [F] [G] ⊢Δ [σ] a [ρ] ⊢Δ₁ [a]))

-- Validity of Π.
Πᵛ : ∀ {F G Γ rF lF lG rΠ lΠ l}
     (lF≤ : lF ≤ lΠ)
     (lG≤ : lG ≤ lΠ)
     ([Γ] : ⊩ᵛ Γ)
     ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / [Γ])
   → Γ ∙ F ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ G ^ [ rΠ , ι lG ] / [Γ] ∙ [F]
   → Γ ⊩ᵛ⟨ l ⟩ Π F ^ rF ° lF ▹ G ° lG ^ [ rΠ , ι lΠ ] / [Γ]
Πᵛ {F} {G} {Γ} {rF} {lF} {lG} {rΠ} {lΠ} {l} lF≤ lG≤ [Γ] [F] [G] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [F]σ {σ′} [σ′] = [F] {σ = σ′} ⊢Δ [σ′]
      [σF] = proj₁ ([F]σ [σ])
      ⊢F {σ′} [σ′] = escape (proj₁ ([F]σ {σ′} [σ′]))
      ⊢F≡F = escapeEq [σF] (reflEq [σF])
      [G]σ {σ′} [σ′] = [G] {σ = liftSubst σ′} (⊢Δ ∙ ⊢F [σ′])
                           (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ′])
      ⊢G {σ′} [σ′] = escape (proj₁ ([G]σ {σ′} [σ′]))
      ⊢G≡G = escapeEq (proj₁ ([G]σ [σ])) (reflEq (proj₁ ([G]σ [σ])))
      ⊢ΠF▹G = Πⱼ lF≤ ▹ lG≤ ▹ un-univ (⊢F [σ]) ▹ un-univ (⊢G [σ])
  in Πᵣ′ rF lF lG lF≤ lG≤ (subst σ F) (subst (liftSubst σ) G)
         (idRed:*: (univ ⊢ΠF▹G)) (⊢F [σ]) (⊢G [σ]) (≅-univ (≅ₜ-Π-cong (⊢F [σ]) (≅-un-univ ⊢F≡F) (≅-un-univ ⊢G≡G)))
         (λ ρ ⊢Δ₁ → wk ρ ⊢Δ₁ [σF])
         (λ {ρ} {Δ₁} {a} [ρ] ⊢Δ₁ [a] →
            let [a]′ = irrelevanceTerm′
                         (wk-subst F) PE.refl PE.refl (wk [ρ] ⊢Δ₁ [σF])
                         (proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]))) [a]
            in  Gapp {F = F} {G = G} {σ = σ} [Γ] [F] [G] ⊢Δ [σ] a [ρ] ⊢Δ₁ [a]′)
         (λ {ρ} {Δ₁} {a} {b} [ρ] ⊢Δ₁ [a] [b] [a≡b] →
            let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]
                [a]′ = irrelevanceTerm′
                         (wk-subst F) PE.refl PE.refl (wk [ρ] ⊢Δ₁ [σF])
                         (proj₁ ([F] ⊢Δ₁ [ρσ])) [a]
                [b]′ = irrelevanceTerm′
                         (wk-subst F) PE.refl PE.refl (wk [ρ] ⊢Δ₁ [σF])
                         (proj₁ ([F] ⊢Δ₁ [ρσ])) [b]
                [a≡b]′ = irrelevanceEqTerm′
                           (wk-subst F) PE.refl PE.refl (wk [ρ] ⊢Δ₁ [σF])
                           (proj₁ ([F] ⊢Δ₁ [ρσ])) [a≡b]
            in  irrelevanceEq″
                  (PE.sym (singleSubstWkComp a σ G))
                  (PE.sym (singleSubstWkComp b σ G)) PE.refl PE.refl
                  (proj₁ (GappGen {F = F} {G = G} {σ = σ} [Γ] [F] [G] ⊢Δ [σ] a [ρ] ⊢Δ₁ [a]′)) 
                  (Gapp {F = F} {G = G} {σ = σ} [Γ] [F] [G] ⊢Δ [σ] a [ρ] ⊢Δ₁ [a]′)
                  (proj₂ (GappGen {F = F} {G = G} {σ = σ} [Γ] [F] [G] ⊢Δ [σ] a [ρ] ⊢Δ₁ [a]′)
                         ([ρσ] , [b]′)
                         (reflSubst [Γ] ⊢Δ₁ [ρσ] , [a≡b]′)))
  ,  (λ {σ′} [σ′] [σ≡σ′] →
        let var0 = var (⊢Δ ∙ ⊢F [σ])
                       (PE.subst (λ x → 0 ∷ x ^ [ rF , ι lF ] ∈ (Δ ∙ subst σ F ^ [ rF , ι lF ]))
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
        in  Π₌ _ _ (id (univ (Πⱼ lF≤ ▹ lG≤ ▹ un-univ (⊢F [σ′]) ▹ un-univ (⊢G [σ′]))))
               (≅-univ (≅ₜ-Π-cong (⊢F [σ])
                                  (≅-un-univ (escapeEq (proj₁ ([F] ⊢Δ [σ]))
                                    (proj₂ ([F] ⊢Δ [σ]) [σ′] [σ≡σ′])))
                                  (≅-un-univ (escapeEq (proj₁ ([G]σ [σ])) (proj₂ ([G]σ [σ])
                                  ([wk1σ′] , neuTerm [F][wk1σ′] (var 0) var0′ (~-var var0′))
                                  ([wk1σ≡wk1σ′] , neuEqTerm [F][wk1σ]
                                  (var 0) (var 0) var0 var0 (~-var var0)))))))
               (λ ρ ⊢Δ₁ → wkEq ρ ⊢Δ₁ [σF] (proj₂ ([F] ⊢Δ [σ]) [σ′] [σ≡σ′]))
               (λ {ρ} {Δ₁} {a} [ρ] ⊢Δ₁ [a] →
                  let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]
                      [ρσ′] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ′]
                      [a]′ = irrelevanceTerm′ (wk-subst F) PE.refl PE.refl (wk [ρ] ⊢Δ₁ [σF])
                                 (proj₁ ([F] ⊢Δ₁ [ρσ])) [a]
                      [a]″ = convTerm₁ (proj₁ ([F] ⊢Δ₁ [ρσ]))
                                        (proj₁ ([F] ⊢Δ₁ [ρσ′]))
                                        (proj₂ ([F] ⊢Δ₁ [ρσ]) [ρσ′]
                                               (wkSubstSEq [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ] [σ≡σ′]))
                                        [a]′
                      [ρσa≡ρσ′a] = consSubstSEq {t = a} {A = F} [Γ] ⊢Δ₁
                                                (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ])
                                                (wkSubstSEq [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ] [σ≡σ′])
                                                [F] [a]′
                  in  irrelevanceEq″ (PE.sym (singleSubstWkComp a σ G))
                                      (PE.sym (singleSubstWkComp a σ′ G)) PE.refl PE.refl
                                      (proj₁ (GappGen {F = F} {G = G} {σ = σ} [Γ] [F] [G] ⊢Δ [σ] a [ρ] ⊢Δ₁ [a]′))
                                      (Gapp {F = F} {G = G} {σ = σ} [Γ] [F] [G] ⊢Δ [σ] a [ρ] ⊢Δ₁ [a]′)
                                      (proj₂ (GappGen {F = F} {G = G} {σ = σ} [Γ] [F] [G] ⊢Δ [σ] a [ρ] ⊢Δ₁ [a]′)
                                             (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ′] , [a]″)
                                             [ρσa≡ρσ′a])))

-- Validity of Π-congurence.
Π-congᵛ : ∀ {F G H E Γ rF lF lG rΠ lΠ l}
          (lF≤ : lF ≤ lΠ)
          (lG≤ : lG ≤ lΠ)
          ([Γ] : ⊩ᵛ Γ)
          ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / [Γ])
          ([G] : Γ ∙ F ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ G ^ [ rΠ , ι lG ] / [Γ] ∙ [F])
          ([H] : Γ ⊩ᵛ⟨ l ⟩ H ^ [ rF , ι lF ] / [Γ])
          ([E] : Γ ∙ H ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ E ^ [ rΠ , ι lG ] / [Γ] ∙ [H])
          ([F≡H] : Γ ⊩ᵛ⟨ l ⟩ F ≡ H ^ [ rF , ι lF ] / [Γ] / [F])
          ([G≡E] : Γ ∙ F ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ G ≡ E ^ [ rΠ , ι lG ] / [Γ] ∙ [F] / [G])
        → Γ ⊩ᵛ⟨ l ⟩ Π F ^ rF ° lF ▹ G ° lG  ≡ Π H ^ rF ° lF ▹ E ° lG ^ [ rΠ , ι lΠ ] / [Γ] / Πᵛ {F} {G} lF≤ lG≤ [Γ] [F] [G]
Π-congᵛ {F} {G} {H} {E} lF≤ lG≤ [Γ] [F] [G] [H] [E] [F≡H] [G≡E] {σ = σ} ⊢Δ [σ] =
  let [ΠFG] = Πᵛ {F} {G} lF≤ lG≤ [Γ] [F] [G]
      [σΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
      _ , Πᵣ rF′ lF' lG' lF≤ lG≤ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′ = extractMaybeEmb (Π-elim [σΠFG])
      [σF] = proj₁ ([F] ⊢Δ [σ])
      ⊢σF = escape [σF]
      [σG] = proj₁ ([G] (⊢Δ ∙ ⊢σF) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
      ⊢σH = escape (proj₁ ([H] ⊢Δ [σ]))
      ⊢σE = escape (proj₁ ([E] (⊢Δ ∙ ⊢σH) (liftSubstS {F = H} [Γ] ⊢Δ [H] [σ])))
      ⊢σF≡σH = escapeEq [σF] ([F≡H] ⊢Δ [σ])
      ⊢σG≡σE = escapeEq [σG] ([G≡E] (⊢Δ ∙ ⊢σF) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))                                   
  in  Π₌ (subst σ H)
         (subst (liftSubst σ) E)
         (id (univ (Πⱼ lF≤ ▹ lG≤ ▹ (un-univ ⊢σH) ▹ (un-univ ⊢σE))))
         (≅-univ (≅ₜ-Π-cong ⊢σF (≅-un-univ ⊢σF≡σH) (≅-un-univ ⊢σG≡σE)))
         (λ ρ ⊢Δ₁ → let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]
                    in  irrelevanceEq″ (PE.sym (wk-subst F))
                                        (PE.sym (wk-subst H)) PE.refl PE.refl
                                        (proj₁ ([F] ⊢Δ₁ [ρσ]))
                                        ([F]′ ρ ⊢Δ₁)
                                        ([F≡H] ⊢Δ₁ [ρσ]))
         (λ {ρ} {Δ} {a} [ρ] ⊢Δ₁ [a] →
            let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]
                [a]′ = irrelevanceTerm′ (wk-subst F) PE.refl PE.refl 
                                        ([F]′ [ρ] ⊢Δ₁)
                                        (proj₁ ([F] ⊢Δ₁ [ρσ])) [a]
                [aρσ] = consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ [ρσ] [F] [a]′
            in irrelevanceEq″ (PE.sym (singleSubstWkComp a σ G))
                                (PE.sym (singleSubstWkComp a σ E)) PE.refl PE.refl
                                (proj₁ ([G] ⊢Δ₁ [aρσ]))
                                ([G]′ [ρ] ⊢Δ₁ [a])
                                ([G≡E] ⊢Δ₁ [aρσ])
                                )

-- Validity of Π as a term.

Πᵗᵛ₁ : ∀ {F G rF lF lG rΠ lΠ Γ} (lF≤ : lF ≤ lΠ)  (lG≤ : lG ≤ lΠ) ([Γ] : ⊩ᵛ Γ)→
      let l    = ∞
          [UF] = maybeEmbᵛ {A = Univ rF _} [Γ] (Uᵛ (proj₂ (levelBounded lF)) [Γ])
          [UΠ] = maybeEmbᵛ {A = Univ rΠ _} [Γ] (Uᵛ (proj₂ (levelBounded lΠ)) [Γ])
      in      
        ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / [Γ])
        ([UG] : Γ ∙ F ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ Univ rΠ lG ^ [ ! , next lG ] / [Γ] ∙ [F])
      → Γ ⊩ᵛ⟨ l ⟩ F ∷ Univ rF lF ^ [ ! , next lF ] / [Γ] / [UF]
      → Γ ∙ F ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ G ∷ Univ rΠ lG ^ [ ! , next lG ] / [Γ] ∙ [F] / (λ {Δ} {σ} → [UG] {Δ} {σ})
      → ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
      → Δ ⊩⟨ l ⟩ subst σ (Π F ^ rF ° lF ▹ G ° lG) ∷ subst σ (Univ rΠ lΠ) ^ [ ! , next lΠ ] / proj₁ ([UΠ] ⊢Δ [σ])
Πᵗᵛ₁ {F} {G} {rF} {lF} {lG} {rΠ} {lΠ = ¹} {Γ} lF≤ lG≤ [Γ] [F] [UG] [Fₜ] [Gₜ] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let
      l = ∞
      lΠ = ¹
      [UF] = maybeEmbᵛ {A = Univ rF _} [Γ] (Uᵛ (proj₂ (levelBounded lF)) [Γ])
      [UΠ] = maybeEmbᵛ {A = Univ rΠ _} [Γ] (Uᵛ (proj₂ (levelBounded lΠ)) [Γ])
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
      [F]₀ = univᵛ {F} [Γ] lF≤ [UF] [Fₜ]
      [UG]′ = S.irrelevance {A = Univ rΠ lG} {r = [ ! , next lG ]} (_∙_ {A = F} [Γ] [F]) (_∙_ {A = F} [Γ] [F]₀) (λ {Δ} {σ} → [UG] {Δ} {σ})
      [Gₜ]′ = S.irrelevanceTerm {l′ = ∞} {A = Univ rΠ lG} {t = G} 
                                (_∙_ {A = F} [Γ] [F]) (_∙_ {A = F} [Γ] [F]₀)
                                (λ {Δ} {σ} → [UG] {Δ} {σ})
                                (λ {Δ} {σ} → [UG]′ {Δ} {σ})
                                [Gₜ]
      [G]₀ = univᵛ {G} (_∙_ {A = F} [Γ] [F]₀) lG≤
                   (λ {Δ} {σ} → [UG]′ {Δ} {σ}) (λ {Δ} {σ} → [Gₜ]′ {Δ} {σ})
      [Guniv] = univᵛ {A = G} (_∙_ {A = F} [Γ] [F]₀) lG≤ (λ {Δ} {σ} → [UG]′ {Δ} {σ}) [Gₜ]′
  in  Uₜ (Π subst σ F ^ rF ° lF ▹ subst (liftSubst σ) G ° lG) (idRedTerm:*: (Πⱼ lF≤ ▹ lG≤ ▹ ⊢Fₜ ▹ ⊢Gₜ))  Πₙ (≅ₜ-Π-cong ⊢F ⊢F≡Fₜ ⊢G≡Gₜ) 
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
                            [wkFₜ]Type : ∀ {ρ₁ Δ₂} [ρ₁] ⊢Δ₂ → Δ₂ ⊩⟨ ι ¹ ⟩ U.wk ρ₁ (U.wk ρ (subst σ F)) ^ [ rF , ι lF ]
                            [wkFₜ]Type = λ {ρ₁} {Δ₂} [ρ₁] ⊢Δ₂ → let [wkFₜ]Type = univEq (wk [ρ₁] ⊢Δ₂ (wk [ρ] ⊢Δ₁ univΔ))
                                                                      (wkTerm [ρ₁] ⊢Δ₂ (wk [ρ] ⊢Δ₁ univΔ) [wkFₜ])
                                                   in maybeEmb′ lF≤ [wkFₜ]Type
                            in Πᵣ′ rF lF lG lF≤ lG≤ (U.wk ρ (subst σ F)) (U.wk (lift ρ) (subst (liftSubst σ) G))
                                  (idRed:*: (univ (Πⱼ lF≤ ▹ lG≤ ▹ ⊢Fₜ' ▹ ⊢Gₜ')))
                                  (univ ⊢Fₜ') (univ ⊢Gₜ') (≅-univ (≅ₜ-Π-cong (univ ⊢Fₜ') [⊢weakF≡Fₜ] [⊢weakG≡Gₜ]))
                                  [wkFₜ]Type
                                  (λ {ρ₁} {Δ₂} {a} [ρ₁] ⊢Δ₂ [a] →
                                    let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₂ ([ρ₁] •ₜ [ρ]) [σ]
                                        [a]′ = irrelevanceTerm′ (wk-subst2 {ρ} {ρ₁} {σ} F) PE.refl PE.refl ([wkFₜ]Type [ρ₁] ⊢Δ₂) 
                                               (proj₁ ([F]₀ ⊢Δ₂ [ρσ])) [a] 
                                        [Gapp] = Gapp {F = F} {G = G} {σ = σ} [Γ] [F]₀ [Guniv] ⊢Δ [σ] a ([ρ₁] •ₜ [ρ]) ⊢Δ₂ [a]′ 
                                    in PE.subst (λ X → _ ⊩⟨ ι ¹ ⟩ X ^ _) (wk-comp-subst _ _ (subst (liftSubst σ) G)) [Gapp])
                                  (λ {ρ₁} {Δ₂} {a} {b} [ρ₁] ⊢Δ₂ [a] [b] [a≡b] →
                                    let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₂ ([ρ₁] •ₜ [ρ]) [σ]
                                        [a]′ = irrelevanceTerm′ (wk-subst2 {ρ} {ρ₁} {σ} F) PE.refl PE.refl ([wkFₜ]Type [ρ₁] ⊢Δ₂)
                                               (proj₁ ([F]₀ ⊢Δ₂ [ρσ])) [a]
                                        [b]′ = irrelevanceTerm′ (wk-subst2 {ρ} {ρ₁} {σ} F) PE.refl PE.refl ([wkFₜ]Type [ρ₁] ⊢Δ₂)
                                               (proj₁ ([F]₀ ⊢Δ₂ [ρσ])) [b]
                                        [a≡b]′ = irrelevanceEqTerm′ (wk-subst2 {ρ} {ρ₁} {σ} F) PE.refl PE.refl ([wkFₜ]Type [ρ₁] ⊢Δ₂)
                                               (proj₁ ([F]₀ ⊢Δ₂ [ρσ])) [a≡b]
                                        [Gapp] = Gapp {F = F} {G = G} {σ = σ} [Γ]  [F]₀ [Guniv] ⊢Δ [σ] a ([ρ₁] •ₜ [ρ]) ⊢Δ₂ [a]′
                                     in irrelevanceEq″ (PE.trans (PE.sym (singleSubstWkComp a σ G)) (wk-comp-subst {a} ρ₁ ρ (subst (liftSubst σ) G)))
                                                       (PE.trans (PE.sym (singleSubstWkComp b σ G)) (wk-comp-subst {b} ρ₁ ρ (subst (liftSubst σ) G)))
                                                       PE.refl PE.refl 
                                                       (proj₁ (GappGen {F = F} {G = G} {σ = σ} [Γ]  [F]₀ [Guniv] ⊢Δ [σ] a ([ρ₁] •ₜ [ρ]) ⊢Δ₂ [a]′ )) 
                                                       (PE.subst (λ X → _ ⊩⟨ ι ¹ ⟩ X ^ _) (wk-comp-subst _ _ (subst (liftSubst σ) G)) [Gapp])
                                                       (proj₂ (GappGen {F = F} {G = G} {σ = σ} [Γ]  [F]₀ [Guniv] ⊢Δ [σ] a ([ρ₁] •ₜ [ρ]) ⊢Δ₂ [a]′ )
                                                         ([ρσ] , [b]′) (reflSubst [Γ] ⊢Δ₂ [ρσ] , [a≡b]′))))
Πᵗᵛ₁ {F} {G} {rF} {lF} {lG} {rΠ} {lΠ = ⁰} {Γ} lF≤ lG≤ [Γ] [F] [UG] [Fₜ] [Gₜ] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let
      l = ∞
      lΠ = ⁰
      [UF] = maybeEmbᵛ {A = Univ rF _} [Γ] (Uᵛ (proj₂ (levelBounded lF)) [Γ])
      [UΠ] = maybeEmbᵛ {A = Univ rΠ _} [Γ] (Uᵛ (proj₂ (levelBounded lΠ)) [Γ])
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
      [F]₀ = univᵛ {F} [Γ] lF≤ [UF] [Fₜ]
      [UG]′ = S.irrelevance {A = Univ rΠ lG} {r = [ ! , next lG ]} (_∙_ {A = F} [Γ] [F]) (_∙_ {A = F} [Γ] [F]₀) (λ {Δ} {σ} → [UG] {Δ} {σ})
      [Gₜ]′ = S.irrelevanceTerm {l′ = ∞} {A = Univ rΠ lG} {t = G} 
                                (_∙_ {A = F} [Γ] [F]) (_∙_ {A = F} [Γ] [F]₀)
                                (λ {Δ} {σ} → [UG] {Δ} {σ})
                                (λ {Δ} {σ} → [UG]′ {Δ} {σ})
                                [Gₜ]
      [G]₀ = univᵛ {G} (_∙_ {A = F} [Γ] [F]₀) lG≤
                   (λ {Δ} {σ} → [UG]′ {Δ} {σ}) (λ {Δ} {σ} → [Gₜ]′ {Δ} {σ})
      [Guniv] = univᵛ {A = G} (_∙_ {A = F} [Γ] [F]₀) lG≤ (λ {Δ} {σ} → [UG]′ {Δ} {σ}) [Gₜ]′
  in  Uₜ (Π subst σ F ^ rF ° lF ▹ subst (liftSubst σ) G ° lG) (idRedTerm:*: (Πⱼ lF≤ ▹ lG≤ ▹ ⊢Fₜ ▹ ⊢Gₜ))  Πₙ (≅ₜ-Π-cong ⊢F ⊢F≡Fₜ ⊢G≡Gₜ) 
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
                            [wkFₜ]Type : ∀ {ρ₁ Δ₂} [ρ₁] ⊢Δ₂ → Δ₂ ⊩⟨ ι ⁰ ⟩ U.wk ρ₁ (U.wk ρ (subst σ F)) ^ [ rF , ι lF ]
                            [wkFₜ]Type = λ {ρ₁} {Δ₂} [ρ₁] ⊢Δ₂ → let [wkFₜ]Type = univEq (wk [ρ₁] ⊢Δ₂ (wk [ρ] ⊢Δ₁ univΔ))
                                                                      (wkTerm [ρ₁] ⊢Δ₂ (wk [ρ] ⊢Δ₁ univΔ) [wkFₜ])
                                                   in maybeEmb′ lF≤ [wkFₜ]Type
                            in Πᵣ′ rF lF lG lF≤ lG≤ (U.wk ρ (subst σ F)) (U.wk (lift ρ) (subst (liftSubst σ) G))
                                  (idRed:*: (univ (Πⱼ lF≤ ▹ lG≤ ▹ ⊢Fₜ' ▹ ⊢Gₜ')))
                                  (univ ⊢Fₜ') (univ ⊢Gₜ') (≅-univ (≅ₜ-Π-cong (univ ⊢Fₜ') [⊢weakF≡Fₜ] [⊢weakG≡Gₜ]))
                                  [wkFₜ]Type
                                  (λ {ρ₁} {Δ₂} {a} [ρ₁] ⊢Δ₂ [a] →
                                    let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₂ ([ρ₁] •ₜ [ρ]) [σ]
                                        [a]′ = irrelevanceTerm′ (wk-subst2 {ρ} {ρ₁} {σ} F) PE.refl PE.refl ([wkFₜ]Type [ρ₁] ⊢Δ₂) 
                                               (proj₁ ([F]₀ ⊢Δ₂ [ρσ])) [a] 
                                        [Gapp] = Gapp {F = F} {G = G} {σ = σ} [Γ] [F]₀ [Guniv] ⊢Δ [σ] a ([ρ₁] •ₜ [ρ]) ⊢Δ₂ [a]′ 
                                    in PE.subst (λ X → _ ⊩⟨ ι ⁰ ⟩ X ^ _) (wk-comp-subst _ _ (subst (liftSubst σ) G)) [Gapp])
                                  (λ {ρ₁} {Δ₂} {a} {b} [ρ₁] ⊢Δ₂ [a] [b] [a≡b] →
                                    let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₂ ([ρ₁] •ₜ [ρ]) [σ]
                                        [a]′ = irrelevanceTerm′ (wk-subst2 {ρ} {ρ₁} {σ} F) PE.refl PE.refl ([wkFₜ]Type [ρ₁] ⊢Δ₂)
                                               (proj₁ ([F]₀ ⊢Δ₂ [ρσ])) [a]
                                        [b]′ = irrelevanceTerm′ (wk-subst2 {ρ} {ρ₁} {σ} F) PE.refl PE.refl ([wkFₜ]Type [ρ₁] ⊢Δ₂)
                                               (proj₁ ([F]₀ ⊢Δ₂ [ρσ])) [b]
                                        [a≡b]′ = irrelevanceEqTerm′ (wk-subst2 {ρ} {ρ₁} {σ} F) PE.refl PE.refl ([wkFₜ]Type [ρ₁] ⊢Δ₂)
                                               (proj₁ ([F]₀ ⊢Δ₂ [ρσ])) [a≡b]
                                        [Gapp] = Gapp {F = F} {G = G} {σ = σ} [Γ]  [F]₀ [Guniv] ⊢Δ [σ] a ([ρ₁] •ₜ [ρ]) ⊢Δ₂ [a]′
                                     in irrelevanceEq″ (PE.trans (PE.sym (singleSubstWkComp a σ G)) (wk-comp-subst {a} ρ₁ ρ (subst (liftSubst σ) G)))
                                                       (PE.trans (PE.sym (singleSubstWkComp b σ G)) (wk-comp-subst {b} ρ₁ ρ (subst (liftSubst σ) G)))
                                                       PE.refl PE.refl 
                                                       (proj₁ (GappGen {F = F} {G = G} {σ = σ} [Γ]  [F]₀ [Guniv] ⊢Δ [σ] a ([ρ₁] •ₜ [ρ]) ⊢Δ₂ [a]′ )) 
                                                       (PE.subst (λ X → _ ⊩⟨ ι ⁰ ⟩ X ^ _) (wk-comp-subst _ _ (subst (liftSubst σ) G)) [Gapp])
                                                       (proj₂ (GappGen {F = F} {G = G} {σ = σ} [Γ]  [F]₀ [Guniv] ⊢Δ [σ] a ([ρ₁] •ₜ [ρ]) ⊢Δ₂ [a]′ )
                                                         ([ρσ] , [b]′) (reflSubst [Γ] ⊢Δ₂ [ρσ] , [a≡b]′))))

 
Πᵗᵛ : ∀ {F G rF lF lG rΠ lΠ Γ} (lF≤ : lF ≤ lΠ)  (lG≤ : lG ≤ lΠ) ([Γ] : ⊩ᵛ Γ)→
      let l    = ∞
          [UF] = maybeEmbᵛ {A = Univ rF _} [Γ] (Uᵛ (proj₂ (levelBounded lF)) [Γ])
          [UΠ] = maybeEmbᵛ {A = Univ rΠ _} [Γ] (Uᵛ (proj₂ (levelBounded lΠ)) [Γ])
      in      
        ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / [Γ])
        ([UG] : Γ ∙ F ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ Univ rΠ lG ^ [ ! , next lG ] / [Γ] ∙ [F])
      → Γ ⊩ᵛ⟨ l ⟩ F ∷ Univ rF lF ^ [ ! , next lF ] / [Γ] / [UF]
      → Γ ∙ F ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ G ∷ Univ rΠ lG ^ [ ! , next lG ] / [Γ] ∙ [F] / (λ {Δ} {σ} → [UG] {Δ} {σ})
      → Γ ⊩ᵛ⟨ l ⟩ Π F ^ rF ° lF ▹ G ° lG ∷ Univ rΠ lΠ ^ [ ! , next lΠ ] / [Γ] / [UΠ]
Πᵗᵛ {F} {G} {rF} {lF} {lG} {rΠ} {lΠ = ¹} {Γ} lF≤ lG≤ [Γ] [F] [UG] [Fₜ] [Gₜ] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let l = ∞
      lΠ = ⁰
      [UF] = maybeEmbᵛ {A = Univ rF _} [Γ] (Uᵛ (proj₂ (levelBounded lF)) [Γ])
      [UΠ] = maybeEmbᵛ {A = Univ rΠ _} [Γ] (Uᵛ (proj₂ (levelBounded lΠ)) [Γ])
  in Πᵗᵛ₁ {F} {G} {rF} {lF} {lG} {rΠ} {¹} {Γ} lF≤ lG≤ [Γ] [F] (λ {Δ} {σ} → [UG] {Δ} {σ}) [Fₜ] [Gₜ] {Δ = Δ} {σ = σ} ⊢Δ [σ]
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
                         (PE.subst (λ x → 0 ∷ x ^ [ rF , ι lF ] ∈ (Δ ∙ subst σ F ^ [ rF , ι lF ]))
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
             [F]₀ = univᵛ {F} [Γ] lF≤ [UF] [Fₜ]
             [UG]′ = S.irrelevance {A = Univ rΠ lG} {r = [ ! , next lG ]} (_∙_ {A = F} [Γ] [F]) (_∙_ {A = F} [Γ] [F]₀) (λ {Δ} {σ} → [UG] {Δ} {σ})
             [Gₜ]′ = S.irrelevanceTerm {l′ = ∞} {A = Univ rΠ lG} {t = G} 
                                (_∙_ {A = F} [Γ] [F]) (_∙_ {A = F} [Γ] [F]₀)
                                (λ {Δ} {σ} → [UG] {Δ} {σ})
                                (λ {Δ} {σ} → [UG]′ {Δ} {σ})
                                [Gₜ]
             [G]₀ = univᵛ {G} (_∙_ {A = F} [Γ] [F]₀) lG≤
                   (λ {Δ} {σ} → [UG]′ {Δ} {σ}) (λ {Δ} {σ} → [Gₜ]′ {Δ} {σ})
             [ΠFG-cong] = Π-congᵛ {F} {G} {F} {G} lF≤ lG≤ [Γ] [F]₀ [G]₀ [F]₀ [G]₀
                                  (λ ⊢Δ₁ [σ]₁ → proj₂ ([F]₀ ⊢Δ₁ [σ]₁) [σ]₁ (reflSubst [Γ] ⊢Δ₁ [σ]₁))
                                  (λ {Δ₁} {σ₁} ⊢Δ₁ [σ]₁ → proj₂ ([G]₀ ⊢Δ₁ [σ]₁) [σ]₁ (reflSubst {σ₁} ((_∙_ {A = F} [Γ] [F]₀)) ⊢Δ₁ [σ]₁))
             [ΠFG]ᵗ  = Πᵗᵛ₁ {F} {G} {rF} {lF} {lG} {rΠ} {lΠ = ¹} {Γ} lF≤ lG≤ [Γ] [F] (λ {Δ} {σ} → [UG] {Δ} {σ}) [Fₜ] [Gₜ] {Δ = Δ} {σ = σ} ⊢Δ [σ]
             [ΠFG]ᵗ′ = Πᵗᵛ₁ {F} {G} {rF} {lF} {lG} {rΠ} {lΠ = ¹} {Γ} lF≤ lG≤ [Γ] [F] (λ {Δ} {σ} → [UG] {Δ} {σ}) [Fₜ] [Gₜ] {Δ = Δ} {σ = σ′} ⊢Δ [σ′]             
             [ΠFG]  = Πᵛ {F} {G} {Γ} {rF} {lF} {lG} {rΠ} {lΠ = ¹} lF≤ lG≤ [Γ] [F]₀ [G]₀
          in Uₜ₌ [ΠFG]ᵗ
                 [ΠFG]ᵗ′
                 (≅ₜ-Π-cong ⊢F ⊢F≡F′ ⊢G≡G′)
                 (λ {ρ} {Δ₁} [ρ] ⊢Δ₁ → let [ΠFG-cong]′ = [ΠFG-cong] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ])
                                           X = irrelevanceEq″ (PE.sym (wk-subst (Π F ^ rF ° lF ▹ G ° lG)))
                                                              (PE.sym (wk-subst (Π F ^ rF ° lF ▹ G ° lG)))
                                                              PE.refl PE.refl 
                                                              (proj₁ ([ΠFG] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]))) 
                                                              (LogRel._⊩¹U_∷_^_/_.[t] [ΠFG]ᵗ [ρ] ⊢Δ₁)
                                                              [ΠFG-cong]′
                                           [σΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
                                           _ , Πᵣ rF′ lF' lG' lF≤' lG≤' F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′ = extractMaybeEmb (Π-elim [σΠFG])
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
                                                            (PE.subst (λ x → 0 ∷ x ^ [ rF , ι lF ] ∈ (Δ₁ ∙ subst (ρ •ₛ σ) F ^ [ rF , ι lF ]))
                                                            (wk-subst F) here))
                                                       (≅-eq (escapeEq (proj₁ ([F] (⊢Δ₁ ∙ ⊢σF) [wk1σ]))
                                                            (proj₂ ([F] (⊢Δ₁ ∙ ⊢σF) [wk1σ]) [wk1σ′]
                                                            (wk1SubstSEq [Γ] ⊢Δ₁ ⊢σF [ρσ] [ρσ≡ρσ′]))))
                                           [liftσ′]′  : (Δ₁ ∙ subst (ρ •ₛ σ) F ^ [ rF , ι lF ]) ⊩ˢ liftSubst (ρ •ₛ σ′) ∷
                                                            Γ ∙ F ^ [ rF , ι lF ] / [Γ] ∙ [F] /
                                                        (⊢Δ₁ ∙ escape (proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]))))
                                           [liftσ′]′ = [wk1σ′]
                                                       , neuTerm (proj₁ ([F] (⊢Δ₁ ∙ ⊢σF) [wk1σ′])) (var 0)
                                                                 var0 (~-var var0)
                                           liftσ′ = liftSubstS {F = F} [Γ] ⊢Δ₁ [F] [ρσ′]
                                           univΔ₁G = proj₁ ([UG] (⊢Δ₁ ∙ ⊢σF) liftσ)
                                           [σG≡σE] = univEqEq univΔ₁G [σG]₀ (proj₂ ([Gₜ] {σ = liftSubst (ρ •ₛ σ)} (⊢Δ₁ ∙ ⊢σF) liftσ) [liftσ′]′
                                                             (liftSubstSEq {F = F} [Γ] ⊢Δ₁ [F] [ρσ] [ρσ≡ρσ′]))
                                           ⊢σG≡σE = escapeEq [σG]₀ [σG≡σE]                                   
                                           X = Π₌  (subst (ρ •ₛ σ′) F)
                                                   (subst (liftSubst (ρ •ₛ σ′)) G)
                                                   (id (univ (Πⱼ lF≤ ▹ lG≤ ▹ (un-univ ⊢σH) ▹ (un-univ ⊢σE))))
                                                   ((≅-univ (≅ₜ-Π-cong ⊢σF (≅-un-univ ⊢σF≡σH) (≅-un-univ ⊢σG≡σE))))
                                                   (λ {ρ₂} {Δ₂} [ρ₂] ⊢Δ₂ →
                                                   let
                                                       [ρσ₂] =  wkSubstS [Γ] ⊢Δ₁ ⊢Δ₂ [ρ₂] [ρσ] 
                                                       [ρσ₂F]₀ = proj₁ ([F]₀ ⊢Δ₂ [ρσ₂])
                                                       [σΠFG] = proj₁ ([ΠFG] ⊢Δ₁ [ρσ])
                                                       _ , Πᵣ rF′ lF' lG' lF≤' lG≤' F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′ = extractMaybeEmb (Π-elim [σΠFG])
                                                       ⊢ρσ₂F = escape [ρσ₂F]₀
                                                       [ρσ₂′] = wkSubstS [Γ] ⊢Δ₁ ⊢Δ₂ [ρ₂] [ρσ′]
                                                       ⊢σH = escape (proj₁ ([F]₀ ⊢Δ₂ [ρσ₂′]))
                                                       univΔ₂ = proj₁ ([UF] ⊢Δ₂ [ρσ₂])
                                                       [σF≡σH] = univEqEq univΔ₂ [ρσ₂F]₀ (proj₂ ([Fₜ]  ⊢Δ₂ [ρσ₂]) [ρσ₂′]
                                                                                 (wkSubstSEq [Γ] ⊢Δ₁ ⊢Δ₂ [ρ₂] [ρσ] [ρσ≡ρσ′])) 
                                                   in irrelevanceEq″ (PE.sym (wk-subst F))
                                                                      (PE.sym (wk-subst F)) PE.refl PE.refl
                                                                      [ρσ₂F]₀
                                                                      ([F]′ [ρ₂] ⊢Δ₂) 
                                                                      [σF≡σH]) 
                                                   (λ {ρ₂} {Δ₂} {a} [ρ₂] ⊢Δ₂ [a] →
                                                    let [ρσ₂] =  wkSubstS [Γ] ⊢Δ₁ ⊢Δ₂ [ρ₂] [ρσ] 
                                                        [ρσ₂F]₀ = proj₁ ([F]₀ ⊢Δ₂ [ρσ₂])
                                                        [σΠFG] = proj₁ ([ΠFG] ⊢Δ₁ [ρσ])
                                                        _ , Πᵣ rF′ lF' lG' lF≤' lG≤' F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′ = extractMaybeEmb (Π-elim [σΠFG])
                                                        ⊢ρσ₂F = escape [ρσ₂F]₀
                                                        [ρσ₂′] = wkSubstS [Γ] ⊢Δ₁ ⊢Δ₂ [ρ₂] [ρσ′]
                                                        ⊢σH = escape (proj₁ ([F]₀ ⊢Δ₂ [ρσ₂′]))
                                                        univΔ₂ = proj₁ ([UF] ⊢Δ₂ [ρσ₂])
                                                        [a]′ = irrelevanceTerm′
                                                                 (wk-subst F) PE.refl PE.refl (wk [ρ₂] ⊢Δ₂ [σF]₀)
                                                                 (proj₁ ([F]₀ ⊢Δ₂ [ρσ₂])) [a]
                                                        [a]″ = convTerm₁ (proj₁ ([F]₀ ⊢Δ₂ [ρσ₂]))
                                                                         (proj₁ ([F]₀ ⊢Δ₂ [ρσ₂′]))
                                                                         (proj₂ ([F]₀ ⊢Δ₂ [ρσ₂]) [ρσ₂′]
                                                                         (wkSubstSEq [Γ] ⊢Δ₁ ⊢Δ₂ [ρ₂] [ρσ] [ρσ≡ρσ′]))
                                                                         [a]′
                                                        [ρσa≡ρσ′a] = consSubstSEq {t = a} {A = F} [Γ] ⊢Δ₂
                                                                                   (wkSubstS [Γ] ⊢Δ₁ ⊢Δ₂ [ρ₂] [ρσ])
                                                                                   (wkSubstSEq [Γ] ⊢Δ₁ ⊢Δ₂ [ρ₂] [ρσ] [ρσ≡ρσ′])
                                                                                   [F]₀ [a]′  
                                                    in irrelevanceEq″
                                                         (PE.sym (singleSubstWkComp a (ρ •ₛ σ) G))
                                                         (PE.sym (singleSubstWkComp a (ρ •ₛ σ′) G)) PE.refl PE.refl
                                                         (proj₁ (GappGen {F = F} {G = G} {σ = _} [Γ] [F]₀ [G]₀ ⊢Δ₁ [ρσ] a [ρ₂] ⊢Δ₂ [a]′))
                                                         (Gapp {F = F} {G = G} {σ = _} [Γ] [F]₀ [G]₀ ⊢Δ₁ [ρσ] a [ρ₂] ⊢Δ₂ [a]′)
                                                         (proj₂ (GappGen {F = F} {G = G} {σ = _} [Γ] [F]₀ [G]₀ ⊢Δ₁ [ρσ] a [ρ₂] ⊢Δ₂ [a]′)
                                                                ([ρσ₂′] , [a]″) 
                                                                [ρσa≡ρσ′a] )) 
                                        in irrelevanceEq″ (PE.sym (wk-subst (Π F ^ rF ° lF ▹ G ° lG)))
                                                          (PE.sym (wk-subst (Π F ^ rF ° lF ▹ G ° lG)))
                                                          PE.refl PE.refl 
                                                          (proj₁ ([ΠFG] ⊢Δ₁ [ρσ])) 
                                                          (LogRel._⊩¹U_∷_^_/_.[t] [ΠFG]ᵗ [ρ] ⊢Δ₁)
                                                          X))
Πᵗᵛ {F} {G} {rF} {lF} {lG} {rΠ} {lΠ = ⁰} {Γ} lFΠ< lG≤ [Γ] [F] [UG] [Fₜ] [Gₜ] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let l = ∞
      lΠ = ⁰
      [UF] = maybeEmbᵛ {A = Univ rF _} [Γ] (Uᵛ (proj₂ (levelBounded lF)) [Γ])
      [UΠ] = maybeEmbᵛ {A = Univ rΠ _} [Γ] (Uᵛ (proj₂ (levelBounded lΠ)) [Γ])
  in Πᵗᵛ₁ {F} {G} {rF} {lF} {lG} {rΠ} {⁰} {Γ} lFΠ< lG≤ [Γ] [F] (λ {Δ} {σ} → [UG] {Δ} {σ}) [Fₜ] [Gₜ] {Δ = Δ} {σ = σ} ⊢Δ [σ]
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
                         (PE.subst (λ x → 0 ∷ x ^ [ rF , ι lF ] ∈ (Δ ∙ subst σ F ^ [ rF , ι lF ]))
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
             [F]₀ = univᵛ {F} [Γ] lFΠ< [UF] [Fₜ]
             [UG]′ = S.irrelevance {A = Univ rΠ lG} {r = [ ! , next lG ]} (_∙_ {A = F} [Γ] [F]) (_∙_ {A = F} [Γ] [F]₀) (λ {Δ} {σ} → [UG] {Δ} {σ})
             [Gₜ]′ = S.irrelevanceTerm {l′ = ∞} {A = Univ rΠ lG} {t = G} 
                                (_∙_ {A = F} [Γ] [F]) (_∙_ {A = F} [Γ] [F]₀)
                                (λ {Δ} {σ} → [UG] {Δ} {σ})
                                (λ {Δ} {σ} → [UG]′ {Δ} {σ})
                                [Gₜ]
             [G]₀ = univᵛ {G} (_∙_ {A = F} [Γ] [F]₀) lG≤
                   (λ {Δ} {σ} → [UG]′ {Δ} {σ}) (λ {Δ} {σ} → [Gₜ]′ {Δ} {σ})
             [ΠFG-cong] = Π-congᵛ {F} {G} {F} {G} lFΠ< lG≤ [Γ] [F]₀ [G]₀ [F]₀ [G]₀
                                  (λ ⊢Δ₁ [σ]₁ → proj₂ ([F]₀ ⊢Δ₁ [σ]₁) [σ]₁ (reflSubst [Γ] ⊢Δ₁ [σ]₁))
                                  (λ {Δ₁} {σ₁} ⊢Δ₁ [σ]₁ → proj₂ ([G]₀ ⊢Δ₁ [σ]₁) [σ]₁ (reflSubst {σ₁} ((_∙_ {A = F} [Γ] [F]₀)) ⊢Δ₁ [σ]₁))
             [ΠFG]ᵗ  = Πᵗᵛ₁ {F} {G} {rF} {lF} {lG} {rΠ} {lΠ = ⁰} {Γ} lFΠ< lG≤ [Γ] [F] (λ {Δ} {σ} → [UG] {Δ} {σ}) [Fₜ] [Gₜ] {Δ = Δ} {σ = σ} ⊢Δ [σ]
             [ΠFG]ᵗ′ = Πᵗᵛ₁ {F} {G} {rF} {lF} {lG} {rΠ} {lΠ = ⁰} {Γ} lFΠ< lG≤ [Γ] [F] (λ {Δ} {σ} → [UG] {Δ} {σ}) [Fₜ] [Gₜ] {Δ = Δ} {σ = σ′} ⊢Δ [σ′]             
             [ΠFG]  = Πᵛ {F} {G} {Γ} {rF} {lF} {lG} {rΠ} {lΠ = ⁰} lFΠ< lG≤ [Γ] [F]₀ [G]₀
          in Uₜ₌ [ΠFG]ᵗ
                 [ΠFG]ᵗ′
                 (≅ₜ-Π-cong ⊢F ⊢F≡F′ ⊢G≡G′)
                 (λ {ρ} {Δ₁} [ρ] ⊢Δ₁ → let [ΠFG-cong]′ = [ΠFG-cong] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ])
                                           X = irrelevanceEq″ (PE.sym (wk-subst (Π F ^ rF ° lF ▹ G ° lG)))
                                                              (PE.sym (wk-subst (Π F ^ rF ° lF ▹ G ° lG)))
                                                              PE.refl PE.refl 
                                                              (proj₁ ([ΠFG] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]))) 
                                                              (LogRel._⊩¹U_∷_^_/_.[t] [ΠFG]ᵗ [ρ] ⊢Δ₁)
                                                              [ΠFG-cong]′
                                           [σΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
                                           _ , Πᵣ rF′ lF' lG' lF≤' lG≤' F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′ = extractMaybeEmb (Π-elim [σΠFG])
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
                                                            (PE.subst (λ x → 0 ∷ x ^ [ rF , ι lF ] ∈ (Δ₁ ∙ subst (ρ •ₛ σ) F ^ [ rF , ι lF ]))
                                                            (wk-subst F) here))
                                                       (≅-eq (escapeEq (proj₁ ([F] (⊢Δ₁ ∙ ⊢σF) [wk1σ]))
                                                            (proj₂ ([F] (⊢Δ₁ ∙ ⊢σF) [wk1σ]) [wk1σ′]
                                                            (wk1SubstSEq [Γ] ⊢Δ₁ ⊢σF [ρσ] [ρσ≡ρσ′]))))
                                           [liftσ′]′  : (Δ₁ ∙ subst (ρ •ₛ σ) F ^ [ rF , ι lF ]) ⊩ˢ liftSubst (ρ •ₛ σ′) ∷
                                                            Γ ∙ F ^ [ rF , ι lF ] / [Γ] ∙ [F] /
                                                        (⊢Δ₁ ∙ escape (proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]))))
                                           [liftσ′]′ = [wk1σ′]
                                                       , neuTerm (proj₁ ([F] (⊢Δ₁ ∙ ⊢σF) [wk1σ′])) (var 0)
                                                                 var0 (~-var var0)
                                           liftσ′ = liftSubstS {F = F} [Γ] ⊢Δ₁ [F] [ρσ′]
                                           univΔ₁G = proj₁ ([UG] (⊢Δ₁ ∙ ⊢σF) liftσ)
                                           [σG≡σE] = univEqEq univΔ₁G [σG]₀ (proj₂ ([Gₜ] {σ = liftSubst (ρ •ₛ σ)} (⊢Δ₁ ∙ ⊢σF) liftσ) [liftσ′]′
                                                             (liftSubstSEq {F = F} [Γ] ⊢Δ₁ [F] [ρσ] [ρσ≡ρσ′]))
                                           ⊢σG≡σE = escapeEq [σG]₀ [σG≡σE]                                   
                                           X = Π₌  (subst (ρ •ₛ σ′) F)
                                                   (subst (liftSubst (ρ •ₛ σ′)) G)
                                                   (id (univ (Πⱼ lFΠ< ▹ lG≤ ▹ (un-univ ⊢σH) ▹ (un-univ ⊢σE))))
                                                   ((≅-univ (≅ₜ-Π-cong ⊢σF (≅-un-univ ⊢σF≡σH) (≅-un-univ ⊢σG≡σE))))
                                                   (λ {ρ₂} {Δ₂} [ρ₂] ⊢Δ₂ →
                                                   let
                                                       [ρσ₂] =  wkSubstS [Γ] ⊢Δ₁ ⊢Δ₂ [ρ₂] [ρσ] 
                                                       [ρσ₂F]₀ = proj₁ ([F]₀ ⊢Δ₂ [ρσ₂])
                                                       [σΠFG] = proj₁ ([ΠFG] ⊢Δ₁ [ρσ])
                                                       _ , Πᵣ rF′ lF' lG' lF≤' lG≤' F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′ = extractMaybeEmb (Π-elim [σΠFG])
                                                       ⊢ρσ₂F = escape [ρσ₂F]₀
                                                       [ρσ₂′] = wkSubstS [Γ] ⊢Δ₁ ⊢Δ₂ [ρ₂] [ρσ′]
                                                       ⊢σH = escape (proj₁ ([F]₀ ⊢Δ₂ [ρσ₂′]))
                                                       univΔ₂ = proj₁ ([UF] ⊢Δ₂ [ρσ₂])
                                                       [σF≡σH] = univEqEq univΔ₂ [ρσ₂F]₀ (proj₂ ([Fₜ]  ⊢Δ₂ [ρσ₂]) [ρσ₂′]
                                                                                 (wkSubstSEq [Γ] ⊢Δ₁ ⊢Δ₂ [ρ₂] [ρσ] [ρσ≡ρσ′])) 
                                                   in irrelevanceEq″ (PE.sym (wk-subst F))
                                                                      (PE.sym (wk-subst F)) PE.refl PE.refl
                                                                      [ρσ₂F]₀
                                                                      ([F]′ [ρ₂] ⊢Δ₂) 
                                                                      [σF≡σH]) 
                                                   (λ {ρ₂} {Δ₂} {a} [ρ₂] ⊢Δ₂ [a] →
                                                    let [ρσ₂] =  wkSubstS [Γ] ⊢Δ₁ ⊢Δ₂ [ρ₂] [ρσ] 
                                                        [ρσ₂F]₀ = proj₁ ([F]₀ ⊢Δ₂ [ρσ₂])
                                                        [σΠFG] = proj₁ ([ΠFG] ⊢Δ₁ [ρσ])
                                                        _ , Πᵣ rF′ lF' lG' lF≤' lG≤' F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′ = extractMaybeEmb (Π-elim [σΠFG])
                                                        ⊢ρσ₂F = escape [ρσ₂F]₀
                                                        [ρσ₂′] = wkSubstS [Γ] ⊢Δ₁ ⊢Δ₂ [ρ₂] [ρσ′]
                                                        ⊢σH = escape (proj₁ ([F]₀ ⊢Δ₂ [ρσ₂′]))
                                                        univΔ₂ = proj₁ ([UF] ⊢Δ₂ [ρσ₂])
                                                        [a]′ = irrelevanceTerm′
                                                                 (wk-subst F) PE.refl PE.refl (wk [ρ₂] ⊢Δ₂ [σF]₀)
                                                                 (proj₁ ([F]₀ ⊢Δ₂ [ρσ₂])) [a]
                                                        [a]″ = convTerm₁ (proj₁ ([F]₀ ⊢Δ₂ [ρσ₂]))
                                                                         (proj₁ ([F]₀ ⊢Δ₂ [ρσ₂′]))
                                                                         (proj₂ ([F]₀ ⊢Δ₂ [ρσ₂]) [ρσ₂′]
                                                                         (wkSubstSEq [Γ] ⊢Δ₁ ⊢Δ₂ [ρ₂] [ρσ] [ρσ≡ρσ′]))
                                                                         [a]′
                                                        [ρσa≡ρσ′a] = consSubstSEq {t = a} {A = F} [Γ] ⊢Δ₂
                                                                                   (wkSubstS [Γ] ⊢Δ₁ ⊢Δ₂ [ρ₂] [ρσ])
                                                                                   (wkSubstSEq [Γ] ⊢Δ₁ ⊢Δ₂ [ρ₂] [ρσ] [ρσ≡ρσ′])
                                                                                   [F]₀ [a]′  
                                                    in irrelevanceEq″
                                                         (PE.sym (singleSubstWkComp a (ρ •ₛ σ) G))
                                                         (PE.sym (singleSubstWkComp a (ρ •ₛ σ′) G)) PE.refl PE.refl
                                                         (proj₁ (GappGen {F = F} {G = G} {σ = _} [Γ] [F]₀ [G]₀ ⊢Δ₁ [ρσ] a [ρ₂] ⊢Δ₂ [a]′))
                                                         (Gapp {F = F} {G = G} {σ = _} [Γ] [F]₀ [G]₀ ⊢Δ₁ [ρσ] a [ρ₂] ⊢Δ₂ [a]′)
                                                         (proj₂ (GappGen {F = F} {G = G} {σ = _} [Γ] [F]₀ [G]₀ ⊢Δ₁ [ρσ] a [ρ₂] ⊢Δ₂ [a]′)
                                                                ([ρσ₂′] , [a]″) 
                                                                [ρσa≡ρσ′a] )) 
                                        in irrelevanceEq″ (PE.sym (wk-subst (Π F ^ rF ° lF ▹ G ° lG)))
                                                          (PE.sym (wk-subst (Π F ^ rF ° lF ▹ G ° lG)))
                                                          PE.refl PE.refl 
                                                          (proj₁ ([ΠFG] ⊢Δ₁ [ρσ])) 
                                                          (LogRel._⊩¹U_∷_^_/_.[t] [ΠFG]ᵗ [ρ] ⊢Δ₁)
                                                          X))
                                                          



-- Validity of Π-congurence as a term equality.
Π-congᵗᵛ : ∀ {F G H E rF lF lG rΠ lΠ Γ} (lF≤ : lF ≤ lΠ)  (lG≤ : lG ≤ lΠ) ([Γ] : ⊩ᵛ Γ) →
        let l    = ∞
            [UF] = maybeEmbᵛ {A = Univ rF _} [Γ] (Uᵛ (proj₂ (levelBounded lF)) [Γ])
            [UΠ] = maybeEmbᵛ {A = Univ rΠ _} [Γ] (Uᵛ (proj₂ (levelBounded lΠ)) [Γ])
        in      
           ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / [Γ])
           ([H] : Γ ⊩ᵛ⟨ l ⟩ H ^ [ rF , ι lF ] / [Γ])
           ([UG] : Γ ∙ F ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ Univ rΠ lG ^ [ ! , next lG ] / [Γ] ∙ [F])
           ([UE] : Γ ∙ H ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ Univ rΠ lG ^ [ ! , next lG ] / [Γ] ∙ [H])
           ([F]ₜ : Γ ⊩ᵛ⟨ l ⟩ F ∷ Univ rF lF ^ [ ! , next lF ] / [Γ] / [UF])
           ([G]ₜ : Γ ∙ F ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ G ∷ Univ rΠ lG ^ [ ! , next lG ] / [Γ] ∙ [F] / (λ {Δ} {σ} → [UG] {Δ} {σ}))
           ([H]ₜ : Γ ⊩ᵛ⟨ l ⟩ H ∷ Univ rF lF ^ [ ! , next lF ] / [Γ] / [UF])
           ([E]ₜ :  Γ ∙ H ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ E ∷ Univ rΠ lG ^ [ ! , next lG ] / [Γ] ∙ [H] / (λ {Δ} {σ} → [UE] {Δ} {σ}))
           ([F≡H]ₜ : Γ ⊩ᵛ⟨ l ⟩ F ≡ H ∷ Univ rF lF ^ [ ! , next lF ] / [Γ] / [UF])
           ([G≡E]ₜ : Γ ∙ F ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ G ≡ E ∷ Univ rΠ lG ^ [ ! , next lG ] / [Γ] ∙ [F]
                                  / (λ {Δ} {σ} → [UG] {Δ} {σ}))
         → Γ ⊩ᵛ⟨ l ⟩ Π F ^ rF ° lF ▹ G ° lG ≡ Π H ^ rF ° lF  ▹ E ° lG ∷ Univ rΠ lΠ ^ [ ! , next lΠ ] / [Γ] / [UΠ]
Π-congᵗᵛ {F} {G} {H} {E} {rF} {lF} {lG} {rΠ} {lΠ = ¹} {Γ}
         lF≤ lG≤ [Γ] [F] [H] [UG] [UE] [F]ₜ [G]ₜ [H]ₜ [E]ₜ [F≡H]ₜ [G≡E]ₜ {Δ} {σ} ⊢Δ [σ] =
  let l = ∞
      [UF] = maybeEmbᵛ {A = Univ rF _} [Γ] (Uᵛ (proj₂ (levelBounded lF)) [Γ])
      [ΠFG]ᵗ = Πᵗᵛ₁ {F} {G} {rF} {lF} {lG} {rΠ} {lΠ = ¹} {Γ} lF≤ lG≤ [Γ] [F] (λ {Δ} {σ} → [UG] {Δ} {σ}) [F]ₜ [G]ₜ {Δ = Δ} {σ = σ} ⊢Δ [σ]
      [ΠHE]ᵗ = Πᵗᵛ₁ {H} {E} {rF} {lF} {lG} {rΠ} {lΠ = ¹} {Γ} lF≤ lG≤ [Γ] [H] (λ {Δ} {σ} → [UE] {Δ} {σ}) [H]ₜ [E]ₜ {Δ = Δ} {σ = σ} ⊢Δ [σ]
      ⊢F = escape (proj₁ ([F] ⊢Δ [σ]))
      [liftσ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
      univΔ = proj₁ ([UF] ⊢Δ [σ]) 
      [G] = maybeEmbᵛ {A = G} (_∙_ {A = F} [Γ] [F]) (univᵛ {G} (_∙_ {A = F} [Γ] [F]) lG≤ (λ {Δ} {σ} → [UG] {Δ} {σ}) [G]ₜ)
      [E] = maybeEmbᵛ {A = E} (_∙_ {A = H} [Γ] [H]) (univᵛ {E} (_∙_ {A = H} [Γ] [H]) lG≤ (λ {Δ} {σ} → [UE] {Δ} {σ}) [E]ₜ)
      [F≡H] = univEqᵛ {F} {H} [Γ] [UF] [F] [F≡H]ₜ
      [G≡E] = univEqᵛ {G} {E} (_∙_ {A = F} [Γ] [F]) (λ {Δ} {σ} → [UG] {Δ} {σ}) [G] [G≡E]ₜ
  in Uₜ₌ [ΠFG]ᵗ [ΠHE]ᵗ (≅ₜ-Π-cong ⊢F (escapeTermEq univΔ ([F≡H]ₜ ⊢Δ [σ]))
                                    (escapeTermEq (proj₁ ([UG] (⊢Δ ∙ ⊢F) [liftσ]))
                                          ([G≡E]ₜ (⊢Δ ∙ ⊢F) [liftσ])))
         λ {ρ} {Δ₁} [ρ] ⊢Δ₁ → let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]
                                  X = Π-congᵛ {F} {G} {H} {E} {Γ} {rF} {lF} {lG} {rΠ} {¹}
                                              lF≤ lG≤ [Γ] [F] [G] [H] [E] [F≡H] [G≡E] ⊢Δ₁ [ρσ]
                              in irrelevanceEq″ (PE.sym (wk-subst (Π F ^ rF ° lF ▹ G ° lG)))
                                                (PE.sym (wk-subst (Π H ^ rF ° lF ▹ E ° lG))) PE.refl PE.refl
                                                (proj₁ (Πᵛ {F} {G} lF≤ lG≤ [Γ] [F] [G] ⊢Δ₁ [ρσ])) (LogRel._⊩¹U_∷_^_/_.[t] [ΠFG]ᵗ [ρ] ⊢Δ₁) X 
Π-congᵗᵛ {F} {G} {H} {E} {rF} {lF} {lG} {rΠ} {lΠ = ⁰} {Γ}
         lF≤ lG≤ [Γ] [F] [H] [UG] [UE] [F]ₜ [G]ₜ [H]ₜ [E]ₜ [F≡H]ₜ [G≡E]ₜ {Δ} {σ} ⊢Δ [σ] =
  let l = ∞
      [UF] = maybeEmbᵛ {A = Univ rF _} [Γ] (Uᵛ (proj₂ (levelBounded lF)) [Γ])
      [ΠFG]ᵗ = Πᵗᵛ₁ {F} {G} {rF} {lF} {lG} {rΠ} {lΠ = ⁰} {Γ} lF≤ lG≤ [Γ] [F] (λ {Δ} {σ} → [UG] {Δ} {σ}) [F]ₜ [G]ₜ {Δ = Δ} {σ = σ} ⊢Δ [σ]
      [ΠHE]ᵗ = Πᵗᵛ₁ {H} {E} {rF} {lF} {lG} {rΠ} {lΠ = ⁰} {Γ} lF≤ lG≤ [Γ] [H] (λ {Δ} {σ} → [UE] {Δ} {σ}) [H]ₜ [E]ₜ {Δ = Δ} {σ = σ} ⊢Δ [σ]
      ⊢F = escape (proj₁ ([F] ⊢Δ [σ]))
      [liftσ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
      univΔ = proj₁ ([UF] ⊢Δ [σ]) 
      [Fₜ]σ {σ′} [σ′] = [F]ₜ {σ = σ′} ⊢Δ [σ′]
      [σF] = proj₁ ([Fₜ]σ [σ])
      [G] = maybeEmbᵛ {A = G} (_∙_ {A = F} [Γ] [F]) (univᵛ {G} (_∙_ {A = F} [Γ] [F]) lG≤ (λ {Δ} {σ} → [UG] {Δ} {σ}) [G]ₜ)
      [E] = maybeEmbᵛ {A = E} (_∙_ {A = H} [Γ] [H]) (univᵛ {E} (_∙_ {A = H} [Γ] [H]) lG≤ (λ {Δ} {σ} → [UE] {Δ} {σ}) [E]ₜ)
      [F≡H] = univEqᵛ {F} {H} [Γ] [UF] [F] [F≡H]ₜ
      [G≡E] = univEqᵛ {G} {E} (_∙_ {A = F} [Γ] [F]) (λ {Δ} {σ} → [UG] {Δ} {σ}) [G] [G≡E]ₜ
  in Uₜ₌ [ΠFG]ᵗ [ΠHE]ᵗ (≅ₜ-Π-cong ⊢F (escapeTermEq univΔ ([F≡H]ₜ ⊢Δ [σ]))
                                    (escapeTermEq (proj₁ ([UG] (⊢Δ ∙ ⊢F) [liftσ]))
                                          ([G≡E]ₜ (⊢Δ ∙ ⊢F) [liftσ])))
         λ {ρ} {Δ₁} [ρ] ⊢Δ₁ → let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]
                                  X = Π-congᵛ {F} {G} {H} {E} {Γ} {rF} {lF} {lG} {rΠ} {⁰}
                                              lF≤ lG≤ [Γ] [F] [G] [H] [E] [F≡H] [G≡E] ⊢Δ₁ [ρσ]
                              in irrelevanceEq″ (PE.sym (wk-subst (Π F ^ rF ° lF ▹ G ° lG)))
                                                (PE.sym (wk-subst (Π H ^ rF ° lF ▹ E ° lG))) PE.refl PE.refl
                                                (proj₁ (Πᵛ {F} {G} lF≤ lG≤ [Γ] [F] [G] ⊢Δ₁ [ρσ])) (LogRel._⊩¹U_∷_^_/_.[t] [ΠFG]ᵗ [ρ] ⊢Δ₁) X 



-- Validity of non-dependent function types.
▹▹ᵛ : ∀ {F G rF lF lG rΠ lΠ Γ l}
      (lF< : lF ≤ lΠ)
      (lG< : lG ≤ lΠ)
      ([Γ] : ⊩ᵛ Γ)
      ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / [Γ])
    → Γ ⊩ᵛ⟨ l ⟩ G ^ [ rΠ , ι lG ] / [Γ]
    → Γ ⊩ᵛ⟨ l ⟩ F ^ rF ° lF ▹▹ G ° lG ^ [ rΠ , ι lΠ ] / [Γ]
▹▹ᵛ {F} {G} lF< lG< [Γ] [F] [G] =
  Πᵛ {F} {wk1 G} lF< lG< [Γ] [F] (wk1ᵛ {G} {F} [Γ] [F] [G])

-- Validity of non-dependent function type congurence.
▹▹-congᵛ : ∀ {F F′ G G′ rF lF lG rΠ lΠ Γ l}
           (lF≤ : lF ≤ lΠ)
           (lG≤ : lG ≤ lΠ)
           ([Γ] : ⊩ᵛ Γ)
           ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / [Γ])
           ([F′] : Γ ⊩ᵛ⟨ l ⟩ F′ ^ [ rF , ι lF ] / [Γ])
           ([F≡F′] : Γ ⊩ᵛ⟨ l ⟩ F ≡ F′ ^ [ rF , ι lF ] / [Γ] / [F])
           ([G] : Γ ⊩ᵛ⟨ l ⟩ G ^ [ rΠ , ι lG ] / [Γ])
           ([G′] : Γ ⊩ᵛ⟨ l ⟩ G′ ^ [ rΠ , ι lG ] / [Γ])
           ([G≡G′] : Γ ⊩ᵛ⟨ l ⟩ G ≡ G′ ^ [ rΠ , ι lG ] / [Γ] / [G])
         → Γ ⊩ᵛ⟨ l ⟩ F ^ rF ° lF ▹▹ G ° lG ≡ F′ ^ rF ° lF ▹▹ G′ ° lG ^ [ rΠ , ι lΠ ] / [Γ] / ▹▹ᵛ {F} {G} lF≤ lG≤ [Γ] [F] [G]
▹▹-congᵛ {F} {F′} {G} {G′} lF< lG< [Γ] [F] [F′] [F≡F′] [G] [G′] [G≡G′] =
  Π-congᵛ {F} {wk1 G} {F′} {wk1 G′} lF< lG< [Γ]
          [F] (wk1ᵛ {G} {F} [Γ] [F] [G])
          [F′] (wk1ᵛ {G′} {F′} [Γ] [F′] [G′])
          [F≡F′] (wk1Eqᵛ {G} {G′} {F} [Γ] [F] [G] [G≡G′])


