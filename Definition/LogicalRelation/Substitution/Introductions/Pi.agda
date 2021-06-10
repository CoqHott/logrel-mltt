{-# OPTIONS --without-K  #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Pi {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Weakening using (_∷_⊆_)
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Weakening
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Weakening
open import Definition.LogicalRelation.Substitution.Properties
import Definition.LogicalRelation.Substitution.Irrelevance as S
open import Definition.LogicalRelation.Substitution.Introductions.Universe

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE


-- Validity of Π.
Πᵛ : ∀ {F G Γ sF sG l}
     ([Γ] : ⊩ᵛ Γ)
     ([F] : Γ ⊩ᵛ⟨ l ⟩ F ⦂ sF / [Γ])
   → Γ ∙ F ⦂ sF ⊩ᵛ⟨ l ⟩ G ⦂ sG / [Γ] ∙ [F]
   → Γ ⊩ᵛ⟨ l ⟩ Π F ⦂ sF ▹ G ⦂ sG / [Γ]
Πᵛ {F} {G} {Γ} {sF} {sG} {l} [Γ] [F] [G] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [F]σ {σ′} [σ′] = [F] {σ = σ′} ⊢Δ [σ′]
      [σF] = proj₁ ([F]σ [σ])
      ⊢F {σ′} [σ′] = escape (proj₁ ([F]σ {σ′} [σ′]))
      ⊢F≡F = escapeEq [σF] (reflEq [σF])
      [G]σ {σ′} [σ′] = [G] {σ = liftSubst σ′} (⊢Δ ∙ ⊢F [σ′])
                           (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ′])
      ⊢G {σ′} [σ′] = escape (proj₁ ([G]σ {σ′} [σ′]))
      ⊢G≡G = escapeEq (proj₁ ([G]σ [σ])) (reflEq (proj₁ ([G]σ [σ])))
      ⊢ΠF▹G = Πⱼ ⊢F [σ] ▹ ⊢G [σ]
      [G]a : ∀ {ρ Δ₁} a ([ρ] : ρ ∷ Δ₁ ⊆ Δ) (⊢Δ₁ : ⊢ Δ₁)
             ([a] : Δ₁ ⊩⟨ l ⟩ a ∷ subst (ρ •ₛ σ) F ⦂ sF
                / proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ])))
           → Σ (Δ₁ ⊩⟨ l ⟩ subst (consSubst (ρ •ₛ σ) a) G ⦂ sG)
               (λ [Aσ] →
               {σ′ : Nat → Term} →
               (Σ (Δ₁ ⊩ˢ tail σ′ ∷ Γ / [Γ] / ⊢Δ₁)
               (λ [tailσ] →
                  Δ₁ ⊩⟨ l ⟩ head σ′ ∷ subst (tail σ′) F ⦂ sF / proj₁ ([F] ⊢Δ₁ [tailσ]))) →
               Δ₁ ⊩ˢ consSubst (ρ •ₛ σ) a ≡ σ′ ∷ Γ ∙ F ⦂ sF /
               [Γ] ∙ [F] / ⊢Δ₁ /
               consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]) [F]
               [a] →
               Δ₁ ⊩⟨ l ⟩ subst (consSubst (ρ •ₛ σ) a) G ≡
               subst σ′ G ⦂ sG / [Aσ])
      [G]a {ρ} a [ρ] ⊢Δ₁ [a] = ([G] {σ = consSubst (ρ •ₛ σ) a} ⊢Δ₁
                              (consSubstS {t = a} {A = F} [Γ] ⊢Δ₁
                                          (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ])
                                          [F] [a]))
      [G]a′ : ∀ {ρ Δ₁} a ([ρ] : ρ ∷ Δ₁ ⊆ Δ) (⊢Δ₁ : ⊢ Δ₁)
            → Δ₁ ⊩⟨ l ⟩ a ∷ subst (ρ •ₛ σ) F ⦂ sF
                 / proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]))
            → Δ₁ ⊩⟨ l ⟩ U.wk (lift ρ) (subst (liftSubst σ) G) [ a ] ⦂ sG
      [G]a′ a ρ ⊢Δ₁ [a] = irrelevance′ (PE.sym (singleSubstWkComp a σ G))
                                   (proj₁ ([G]a a ρ ⊢Δ₁ [a]))
  in Πᵣ′ sF (subst σ F) (subst (liftSubst σ) G)
         (idRed:*: ⊢ΠF▹G) (⊢F [σ]) (⊢G [σ]) (≅-Π-cong (⊢F [σ]) ⊢F≡F ⊢G≡G)
         (λ ρ ⊢Δ₁ → wk ρ ⊢Δ₁ [σF])
         (λ {ρ} {Δ₁} {a} [ρ] ⊢Δ₁ [a] →
            let [a]′ = irrelevanceTerm′
                         (wk-subst F) PE.refl (wk [ρ] ⊢Δ₁ [σF])
                         (proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]))) [a]
            in  [G]a′ a [ρ] ⊢Δ₁ [a]′)
         (λ {ρ} {Δ₁} {a} {b} [ρ] ⊢Δ₁ [a] [b] [a≡b] →
            let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]
                [a]′ = irrelevanceTerm′
                         (wk-subst F) PE.refl (wk [ρ] ⊢Δ₁ [σF])
                         (proj₁ ([F] ⊢Δ₁ [ρσ])) [a]
                [b]′ = irrelevanceTerm′
                         (wk-subst F) PE.refl (wk [ρ] ⊢Δ₁ [σF])
                         (proj₁ ([F] ⊢Δ₁ [ρσ])) [b]
                [a≡b]′ = irrelevanceEqTerm′
                           (wk-subst F) PE.refl (wk [ρ] ⊢Δ₁ [σF])
                           (proj₁ ([F] ⊢Δ₁ [ρσ])) [a≡b]
            in  irrelevanceEq″
                  (PE.sym (singleSubstWkComp a σ G))
                  (PE.sym (singleSubstWkComp b σ G))
                  (proj₁ ([G]a a [ρ] ⊢Δ₁ [a]′))
                  ([G]a′ a [ρ] ⊢Δ₁ [a]′)
                  (proj₂ ([G]a a [ρ] ⊢Δ₁ [a]′)
                         ([ρσ] , [b]′)
                         (reflSubst [Γ] ⊢Δ₁ [ρσ] , [a≡b]′)))
  ,  (λ {σ′} [σ′] [σ≡σ′] →
        let var0 = var (⊢Δ ∙ ⊢F [σ])
                       (PE.subst (λ x → 0 ∷ x ⦂ sF ∈ (Δ ∙ subst σ F ⦂ sF))
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
        in  Π₌ _ _ (id (Πⱼ ⊢F [σ′] ▹ ⊢G [σ′]))
               (≅-Π-cong (⊢F [σ])
                       (escapeEq (proj₁ ([F] ⊢Δ [σ]))
                                    (proj₂ ([F] ⊢Δ [σ]) [σ′] [σ≡σ′]))
                       (escapeEq (proj₁ ([G]σ [σ])) (proj₂ ([G]σ [σ])
                         ([wk1σ′] , neuTerm [F][wk1σ′] (var 0) var0′ (~-var var0′))
                         ([wk1σ≡wk1σ′] , neuEqTerm [F][wk1σ]
                           (var 0) (var 0) var0 var0 (~-var var0)))))
               (λ ρ ⊢Δ₁ → wkEq ρ ⊢Δ₁ [σF] (proj₂ ([F] ⊢Δ [σ]) [σ′] [σ≡σ′]))
               (λ {ρ} {Δ₁} {a} [ρ] ⊢Δ₁ [a] →
                  let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]
                      [ρσ′] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ′]
                      [a]′ = irrelevanceTerm′ (wk-subst F) PE.refl (wk [ρ] ⊢Δ₁ [σF])
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
                                      (PE.sym (singleSubstWkComp a σ′ G))
                                      (proj₁ ([G]a a [ρ] ⊢Δ₁ [a]′))
                                      ([G]a′ a [ρ] ⊢Δ₁ [a]′)
                                      (proj₂ ([G]a a [ρ] ⊢Δ₁ [a]′)
                                             (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ′] , [a]″)
                                             [ρσa≡ρσ′a])))

-- Validity of Π-congurence.
Π-congᵛ : ∀ {F G H E Γ sF sG l}
          ([Γ] : ⊩ᵛ Γ)
          ([F] : Γ ⊩ᵛ⟨ l ⟩ F ⦂ sF / [Γ])
          ([G] : Γ ∙ F ⦂ sF ⊩ᵛ⟨ l ⟩ G ⦂ sG / [Γ] ∙ [F])
          ([H] : Γ ⊩ᵛ⟨ l ⟩ H ⦂ sF / [Γ])
          ([E] : Γ ∙ H ⦂ sF ⊩ᵛ⟨ l ⟩ E ⦂ sG / [Γ] ∙ [H])
          ([F≡H] : Γ ⊩ᵛ⟨ l ⟩ F ≡ H ⦂ sF / [Γ] / [F])
          ([G≡E] : Γ ∙ F ⦂ sF ⊩ᵛ⟨ l ⟩ G ≡ E ⦂ sG / [Γ] ∙ [F] / [G])
        → Γ ⊩ᵛ⟨ l ⟩ Π F ⦂ sF ▹ G ≡ Π H ⦂ sF ▹ E ⦂ sG / [Γ] / Πᵛ {F} {G} [Γ] [F] [G]
Π-congᵛ {F} {G} {H} {E} [Γ] [F] [G] [H] [E] [F≡H] [G≡E] {σ = σ} ⊢Δ [σ] =
  let [ΠFG] = Πᵛ {F} {G} [Γ] [F] [G]
      [σΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
      _ , Πᵣ sF′ F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′ = extractMaybeEmb (Π-elim [σΠFG])
      [σF] = proj₁ ([F] ⊢Δ [σ])
      ⊢σF = escape [σF]
      [σG] = proj₁ ([G] (⊢Δ ∙ ⊢σF) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
      ⊢σH = escape (proj₁ ([H] ⊢Δ [σ]))
      ⊢σE = escape (proj₁ ([E] (⊢Δ ∙ ⊢σH) (liftSubstS {F = H} [Γ] ⊢Δ [H] [σ])))
      ⊢σF≡σH = escapeEq [σF] ([F≡H] ⊢Δ [σ])
      ⊢σG≡σE = escapeEq [σG] ([G≡E] (⊢Δ ∙ ⊢σF) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
  in  Π₌ (subst σ H)
         (subst (liftSubst σ) E)
         (id (Πⱼ ⊢σH ▹ ⊢σE))
         (≅-Π-cong ⊢σF ⊢σF≡σH ⊢σG≡σE)
         (λ ρ ⊢Δ₁ → let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]
                    in  irrelevanceEq″ (PE.sym (wk-subst F))
                                        (PE.sym (wk-subst H))
                                        (proj₁ ([F] ⊢Δ₁ [ρσ]))
                                        ([F]′ ρ ⊢Δ₁)
                                        ([F≡H] ⊢Δ₁ [ρσ]))
         (λ {ρ} {Δ} {a} [ρ] ⊢Δ₁ [a] →
            let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]
                [a]′ = irrelevanceTerm′ (wk-subst F) PE.refl
                                        ([F]′ [ρ] ⊢Δ₁)
                                        (proj₁ ([F] ⊢Δ₁ [ρσ])) [a]
                [aρσ] = consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ [ρσ] [F] [a]′
            in  irrelevanceEq″ (PE.sym (singleSubstWkComp a σ G))
                                (PE.sym (singleSubstWkComp a σ E))
                                (proj₁ ([G] ⊢Δ₁ [aρσ]))
                                ([G]′ [ρ] ⊢Δ₁ [a])
                                ([G≡E] ⊢Δ₁ [aρσ]))

-- Validity of Π as a term.
Πᵗᵛ : ∀ {F G sF sG Γ} ([Γ] : ⊩ᵛ Γ)
      ([F] : Γ ⊩ᵛ⟨ ¹ ⟩ F ⦂ sF / [Γ])
      ([U] : Γ ∙ F ⦂ sF ⊩ᵛ⟨ ¹ ⟩ Univ sG ⦂ 𝕥y / [Γ] ∙ [F])
    → Γ ⊩ᵛ⟨ ¹ ⟩ F ∷ Univ sF ⦂ 𝕥y / [Γ] / Uᵛ [Γ]
    → Γ ∙ F ⦂ sF ⊩ᵛ⟨ ¹ ⟩ G ∷ Univ sG ⦂ 𝕥y / [Γ] ∙ [F] / (λ {Δ} {σ} → [U] {Δ} {σ})
    → Γ ⊩ᵛ⟨ ¹ ⟩ Π F ⦂ sF ▹ G ∷ Univ sG ⦂ 𝕥y / [Γ] / Uᵛ [Γ]
Πᵗᵛ {F} {G} {sF} {sG} {Γ} [Γ] [F] [U] [Fₜ] [Gₜ] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [liftσ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
      ⊢F = escape (proj₁ ([F] ⊢Δ [σ]))
      ⊢Fₜ = escapeTerm (Uᵣ′ _ ⁰ 0<1 ⊢Δ) (proj₁ ([Fₜ] ⊢Δ [σ]))
      ⊢F≡Fₜ = escapeTermEq (Uᵣ′ _ ⁰ 0<1 ⊢Δ)
                               (reflEqTerm (Uᵣ′ _ ⁰ 0<1 ⊢Δ) (proj₁ ([Fₜ] ⊢Δ [σ])))
      ⊢Gₜ = escapeTerm (proj₁ ([U] (⊢Δ ∙ ⊢F) [liftσ]))
                           (proj₁ ([Gₜ] (⊢Δ ∙ ⊢F) [liftσ]))
      ⊢G≡Gₜ = escapeTermEq (proj₁ ([U] (⊢Δ ∙ ⊢F) [liftσ]))
                               (reflEqTerm (proj₁ ([U] (⊢Δ ∙ ⊢F) [liftσ]))
                                           (proj₁ ([Gₜ] (⊢Δ ∙ ⊢F) [liftσ])))
      [F]₀ = univᵛ {F} [Γ] (Uᵛ [Γ]) [Fₜ]
      [Gₜ]′ = S.irrelevanceTerm {A = Univ sG} {t = G}
                                (_∙_ {A = F} [Γ] [F]) (_∙_ {A = F} [Γ] [F]₀)
                                (λ {Δ} {σ} → [U] {Δ} {σ})
                                (λ {Δ} {σ} → Uᵛ (_∙_ {A = F} [Γ] [F]₀) {Δ} {σ})
                                [Gₜ]
      [G]₀ = univᵛ {G} (_∙_ {A = F} [Γ] [F]₀)
                   (λ {Δ} {σ} → Uᵛ (_∙_ {A = F} [Γ] [F]₀) {Δ} {σ})
                   (λ {Δ} {σ} → [Gₜ]′ {Δ} {σ})
      [ΠFG] = (Πᵛ {F} {G} [Γ] [F]₀ [G]₀) ⊢Δ [σ]
  in  Uₜ (Π subst σ F ⦂ sF ▹ subst (liftSubst σ) G) (idRedTerm:*: (Πⱼ ⊢Fₜ ▹ ⊢Gₜ))
         Πₙ (≅ₜ-Π-cong ⊢F ⊢F≡Fₜ ⊢G≡Gₜ) (proj₁ [ΠFG])
  ,   (λ {σ′} [σ′] [σ≡σ′] →
         let [liftσ′] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ′]
             [wk1σ] = wk1SubstS [Γ] ⊢Δ ⊢F [σ]
             [wk1σ′] = wk1SubstS [Γ] ⊢Δ ⊢F [σ′]
             var0 = conv (var (⊢Δ ∙ ⊢F)
                         (PE.subst (λ x → 0 ∷ x ⦂ sF ∈ (Δ ∙ subst σ F ⦂ sF))
                                   (wk-subst F) here))
                    (≅-eq (escapeEq (proj₁ ([F] (⊢Δ ∙ ⊢F) [wk1σ]))
                                        (proj₂ ([F] (⊢Δ ∙ ⊢F) [wk1σ]) [wk1σ′]
                                               (wk1SubstSEq [Γ] ⊢Δ ⊢F [σ] [σ≡σ′]))))
             [liftσ′]′ = [wk1σ′]
                       , neuTerm (proj₁ ([F] (⊢Δ ∙ ⊢F) [wk1σ′])) (var 0)
                                 var0 (~-var var0)
             ⊢F′ = escape (proj₁ ([F] ⊢Δ [σ′]))
             ⊢Fₜ′ = escapeTerm (Uᵣ′ _ ⁰ 0<1 ⊢Δ) (proj₁ ([Fₜ] ⊢Δ [σ′]))
             ⊢Gₜ′ = escapeTerm (proj₁ ([U] (⊢Δ ∙ ⊢F′) [liftσ′]))
                                  (proj₁ ([Gₜ] (⊢Δ ∙ ⊢F′) [liftσ′]))
             ⊢F≡F′ = escapeTermEq (Uᵣ′ _ ⁰ 0<1 ⊢Δ)
                                     (proj₂ ([Fₜ] ⊢Δ [σ]) [σ′] [σ≡σ′])
             ⊢G≡G′ = escapeTermEq (proj₁ ([U] (⊢Δ ∙ ⊢F) [liftσ]))
                                     (proj₂ ([Gₜ] (⊢Δ ∙ ⊢F) [liftσ]) [liftσ′]′
                                            (liftSubstSEq {F = F} [Γ] ⊢Δ [F] [σ] [σ≡σ′]))
             [ΠFG]′ = (Πᵛ {F} {G} [Γ] [F]₀ [G]₀) ⊢Δ [σ′]
         in  Uₜ₌ (Π subst σ F ⦂ sF ▹ subst (liftSubst σ) G)
                 (Π subst σ′ F ⦂ sF ▹ subst (liftSubst σ′) G)
                 (idRedTerm:*: (Πⱼ ⊢Fₜ ▹ ⊢Gₜ))
                 (idRedTerm:*: (Πⱼ ⊢Fₜ′ ▹ ⊢Gₜ′))
                 Πₙ Πₙ (≅ₜ-Π-cong ⊢F ⊢F≡F′ ⊢G≡G′)
                 (proj₁ [ΠFG]) (proj₁ [ΠFG]′) (proj₂ [ΠFG] [σ′] [σ≡σ′]))

-- Validity of Π-congurence as a term equality.
Π-congᵗᵛ : ∀ {F G H E sF sG Γ}
           ([Γ] : ⊩ᵛ Γ)
           ([F] : Γ ⊩ᵛ⟨ ¹ ⟩ F ⦂ sF / [Γ])
           ([H] : Γ ⊩ᵛ⟨ ¹ ⟩ H ⦂ sF / [Γ])
           ([UF] : Γ ∙ F ⦂ sF ⊩ᵛ⟨ ¹ ⟩ Univ sG ⦂ 𝕥y / [Γ] ∙ [F])
           ([UH] : Γ ∙ H ⦂ sF ⊩ᵛ⟨ ¹ ⟩ Univ sG ⦂ 𝕥y / [Γ] ∙ [H])
           ([F]ₜ : Γ ⊩ᵛ⟨ ¹ ⟩ F ∷ Univ sF ⦂ 𝕥y / [Γ] / Uᵛ [Γ])
           ([G]ₜ : Γ ∙ F ⦂ sF ⊩ᵛ⟨ ¹ ⟩ G ∷ Univ sG ⦂ 𝕥y / [Γ] ∙ [F]
                                / (λ {Δ} {σ} → [UF] {Δ} {σ}))
           ([H]ₜ : Γ ⊩ᵛ⟨ ¹ ⟩ H ∷ Univ sF ⦂ 𝕥y / [Γ] / Uᵛ [Γ])
           ([E]ₜ : Γ ∙ H ⦂ sF ⊩ᵛ⟨ ¹ ⟩ E ∷ Univ sG ⦂ 𝕥y / [Γ] ∙ [H]
                                / (λ {Δ} {σ} → [UH] {Δ} {σ}))
           ([F≡H]ₜ : Γ ⊩ᵛ⟨ ¹ ⟩ F ≡ H ∷ Univ sF ⦂ 𝕥y / [Γ] / Uᵛ [Γ])
           ([G≡E]ₜ : Γ ∙ F ⦂ sF ⊩ᵛ⟨ ¹ ⟩ G ≡ E ∷ Univ sG ⦂ 𝕥y / [Γ] ∙ [F]
                                  / (λ {Δ} {σ} → [UF] {Δ} {σ}))
         → Γ ⊩ᵛ⟨ ¹ ⟩ Π F ⦂ sF ▹ G ≡ Π H ⦂ sF ▹ E ∷ Univ sG ⦂ 𝕥y / [Γ] / Uᵛ [Γ]
Π-congᵗᵛ {F} {G} {H} {E} {sF} {sG}
         [Γ] [F] [H] [UF] [UH] [F]ₜ [G]ₜ [H]ₜ [E]ₜ [F≡H]ₜ [G≡E]ₜ {Δ} {σ} ⊢Δ [σ] =
  let ⊢F = escape (proj₁ ([F] ⊢Δ [σ]))
      ⊢H = escape (proj₁ ([H] ⊢Δ [σ]))
      [liftFσ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
      [liftHσ] = liftSubstS {F = H} [Γ] ⊢Δ [H] [σ]
      [F]ᵤ = univᵛ {F} [Γ] (Uᵛ [Γ]) [F]ₜ
      [G]ᵤ₁ = univᵛ {G} {l′ = ⁰} (_∙_ {A = F} [Γ] [F])
                    (λ {Δ} {σ} → [UF] {Δ} {σ}) [G]ₜ
      [G]ᵤ = S.irrelevance {A = G} (_∙_ {A = F} [Γ] [F])
                           (_∙_ {A = F} [Γ] [F]ᵤ) [G]ᵤ₁
      [H]ᵤ = univᵛ {H} [Γ] (Uᵛ [Γ]) [H]ₜ
      [E]ᵤ = S.irrelevance {A = E} (_∙_ {A = H} [Γ] [H]) (_∙_ {A = H} [Γ] [H]ᵤ)
                           (univᵛ {E} {l′ = ⁰} (_∙_ {A = H} [Γ] [H])
                                  (λ {Δ} {σ} → [UH] {Δ} {σ}) [E]ₜ)
      [F≡H]ᵤ = univEqᵛ {F} {H} [Γ] (Uᵛ [Γ]) [F]ᵤ [F≡H]ₜ
      [G≡E]ᵤ = S.irrelevanceEq {A = G} {B = E} (_∙_ {A = F} [Γ] [F])
                               (_∙_ {A = F} [Γ] [F]ᵤ) [G]ᵤ₁ [G]ᵤ
                 (univEqᵛ {G} {E} (_∙_ {A = F} [Γ] [F])
                          (λ {Δ} {σ} → [UF] {Δ} {σ}) [G]ᵤ₁ [G≡E]ₜ)
      ΠFGₜ = Πⱼ escapeTerm {l = ¹} (Uᵣ′ _ ⁰ 0<1 ⊢Δ) (proj₁ ([F]ₜ ⊢Δ [σ]))
             ▹  escapeTerm (proj₁ ([UF] (⊢Δ ∙ ⊢F) [liftFσ]))
                           (proj₁ ([G]ₜ (⊢Δ ∙ ⊢F) [liftFσ]))
      ΠHEₜ = Πⱼ escapeTerm {l = ¹} (Uᵣ′ _ ⁰ 0<1 ⊢Δ) (proj₁ ([H]ₜ ⊢Δ [σ]))
             ▹  escapeTerm (proj₁ ([UH] (⊢Δ ∙ ⊢H) [liftHσ]))
                           (proj₁ ([E]ₜ (⊢Δ ∙ ⊢H) [liftHσ]))
  in  Uₜ₌ (Π subst σ F ⦂ sF ▹ subst (liftSubst σ) G)
          (Π subst σ H ⦂ sF ▹ subst (liftSubst σ) E)
          (idRedTerm:*: ΠFGₜ) (idRedTerm:*: ΠHEₜ)
          Πₙ Πₙ
          (≅ₜ-Π-cong ⊢F (escapeTermEq (Uᵣ′ _ ⁰ 0<1 ⊢Δ) ([F≡H]ₜ ⊢Δ [σ]))
                        (escapeTermEq (proj₁ ([UF] (⊢Δ ∙ ⊢F) [liftFσ]))
                                          ([G≡E]ₜ (⊢Δ ∙ ⊢F) [liftFσ])))
          (proj₁ (Πᵛ {F} {G} [Γ] [F]ᵤ [G]ᵤ ⊢Δ [σ]))
          (proj₁ (Πᵛ {H} {E} [Γ] [H]ᵤ [E]ᵤ ⊢Δ [σ]))
          (Π-congᵛ {F} {G} {H} {E} [Γ] [F]ᵤ [G]ᵤ [H]ᵤ [E]ᵤ [F≡H]ᵤ [G≡E]ᵤ ⊢Δ [σ])

-- Validity of non-dependent function types.
▹▹ᵛ : ∀ {F G sF sG Γ l}
      ([Γ] : ⊩ᵛ Γ)
      ([F] : Γ ⊩ᵛ⟨ l ⟩ F ⦂ sF / [Γ])
    → Γ ⊩ᵛ⟨ l ⟩ G ⦂ sG / [Γ]
    → Γ ⊩ᵛ⟨ l ⟩ F ⦂ sF ▹▹ G ⦂ sG / [Γ]
▹▹ᵛ {F} {G} [Γ] [F] [G] =
  Πᵛ {F} {wk1 G} [Γ] [F] (wk1ᵛ {G} {F} [Γ] [F] [G])

-- Validity of non-dependent function type congurence.
▹▹-congᵛ : ∀ {F F′ G G′ sF sG Γ l}
           ([Γ] : ⊩ᵛ Γ)
           ([F] : Γ ⊩ᵛ⟨ l ⟩ F ⦂ sF / [Γ])
           ([F′] : Γ ⊩ᵛ⟨ l ⟩ F′ ⦂ sF / [Γ])
           ([F≡F′] : Γ ⊩ᵛ⟨ l ⟩ F ≡ F′ ⦂ sF / [Γ] / [F])
           ([G] : Γ ⊩ᵛ⟨ l ⟩ G ⦂ sG / [Γ])
           ([G′] : Γ ⊩ᵛ⟨ l ⟩ G′ ⦂ sG / [Γ])
           ([G≡G′] : Γ ⊩ᵛ⟨ l ⟩ G ≡ G′ ⦂ sG / [Γ] / [G])
         → Γ ⊩ᵛ⟨ l ⟩ F ⦂ sF ▹▹ G ≡ F′ ⦂ sF ▹▹ G′ ⦂ sG / [Γ] / ▹▹ᵛ {F} {G} [Γ] [F] [G]
▹▹-congᵛ {F} {F′} {G} {G′} [Γ] [F] [F′] [F≡F′] [G] [G′] [G≡G′] =
  Π-congᵛ {F} {wk1 G} {F′} {wk1 G′} [Γ]
          [F] (wk1ᵛ {G} {F} [Γ] [F] [G])
          [F′] (wk1ᵛ {G′} {F′} [Γ] [F′] [G′])
          [F≡F′] (wk1Eqᵛ {G} {G′} {F} [Γ] [F] [G] [G≡G′])
