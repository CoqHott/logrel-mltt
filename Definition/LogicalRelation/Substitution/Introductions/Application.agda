{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Application {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Application
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Definition.LogicalRelation.Substitution.Introductions.Pi
open import Definition.LogicalRelation.Substitution.Introductions.Lambda
open import Definition.LogicalRelation.Substitution.Introductions.Universe
open import Definition.LogicalRelation.Substitution.Weakening
open import Definition.LogicalRelation.Substitution.Reflexivity
open import Definition.LogicalRelation.Substitution.MaybeEmbed
import Definition.LogicalRelation.Substitution.Irrelevance as S

open import Tools.Nat

open import Tools.Product
import Tools.PropositionalEquality as PE

import Data.Nat as Nat

-- Application of valid terms.
appᵛ : ∀ {F G rF lF lG lΠ t u Γ l}
       ([Γ] : ⊩ᵛ Γ)
       ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / [Γ])
       ([G] : Γ ∙ F ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ G ^ [ ! , ι lG ] / [Γ] ∙ [F])
       ([ΠFG] : Γ ⊩ᵛ⟨ l ⟩ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ [ ! , ι lΠ ] / [Γ])
       ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ [ ! , ι lΠ ] / [Γ] / [ΠFG])
       ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ F ^ [ rF , ι lF ] / [Γ] / [F])
     → Γ ⊩ᵛ⟨ l ⟩ t ∘ u ^ lΠ ∷ G [ u ] ^ [ ! , ι lG ] / [Γ] / substSΠ {F} {G} {u} [Γ] [F] [ΠFG] [u]
appᵛ {F} {G} {rF} {lF} {lG} {lΠ} {t} {u} [Γ] [F] [G] [ΠFG] [t] [u] {σ = σ} ⊢Δ [σ] =
  let [G[u]] = substSΠ {F} {G} {u} [Γ] [F] [ΠFG] [u]
      [σF] = proj₁ ([F] ⊢Δ [σ])
      [liftσ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
      [σG] = proj₁ ([G] (⊢Δ ∙ escape [σF]) [liftσ])
      [σΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
      [σt] = proj₁ ([t] ⊢Δ [σ])
      [σu] = proj₁ ([u] ⊢Δ [σ])
      [σG[u]]  = proj₁ ([G[u]] ⊢Δ [σ])
      [σG[u]]′ = irrelevance′ (singleSubstLift G u) [σG[u]]
  in  irrelevanceTerm′ (PE.sym (singleSubstLift G u)) PE.refl PE.refl
                       [σG[u]]′ [σG[u]]
                       (appTerm PE.refl [σF] [σG[u]]′ [σΠFG] [σt] [σu] (un-univ (escape [σG])))
  ,   (λ [σ′] [σ≡σ′] →
         let [σu′] = convTerm₂ [σF] (proj₁ ([F] ⊢Δ [σ′]))
                               (proj₂ ([F] ⊢Δ [σ]) [σ′] [σ≡σ′])
                               (proj₁ ([u] ⊢Δ [σ′]))
         in  irrelevanceEqTerm′ (PE.sym (singleSubstLift G u)) PE.refl PE.refl
                                [σG[u]]′ [σG[u]]
                                (app-congTerm [σF] [σG[u]]′ [σΠFG]
                                              (proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′])
                                              [σu] [σu′]
                                              (proj₂ ([u] ⊢Δ [σ]) [σ′] [σ≡σ′]) (un-univ (escape [σG]))))


-- Application congurence of valid terms.
app-congᵛ : ∀ {F G rF lF lG lΠ t u a b Γ l}
            ([Γ] : ⊩ᵛ Γ)
            ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / [Γ])
            ([G] : Γ ∙ F ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ G ^ [ ! , ι lG ] / [Γ] ∙ [F])
            ([ΠFG] : Γ ⊩ᵛ⟨ l ⟩ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ [ ! , ι lΠ ] / [Γ])
            ([t≡u] : Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ [ ! , ι lΠ ] / [Γ] / [ΠFG])
            ([a] : Γ ⊩ᵛ⟨ l ⟩ a ∷ F ^ [ rF , ι lF ] / [Γ] / [F])
            ([b] : Γ ⊩ᵛ⟨ l ⟩ b ∷ F ^ [ rF , ι lF ] / [Γ] / [F])
            ([a≡b] : Γ ⊩ᵛ⟨ l ⟩ a ≡ b ∷ F ^ [ rF , ι lF ] / [Γ] / [F])
          → Γ ⊩ᵛ⟨ l ⟩ t ∘ a ^ lΠ ≡ u ∘ b ^ lΠ ∷ G [ a ] ^ [ ! , ι lG ] / [Γ]
              / substSΠ {F} {G} {a} [Γ] [F] [ΠFG] [a]
app-congᵛ {F} {G} {rF} {lF} {lG} {a = a} [Γ] [F] [G] [ΠFG] [t≡u] [a] [b] [a≡b] ⊢Δ [σ] =
  let [σF] = proj₁ ([F] ⊢Δ [σ])
      [liftσ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
      [σG] = proj₁ ([G] (⊢Δ ∙ escape [σF]) [liftσ])
      [G[a]]  = proj₁ (substSΠ {F} {G} {a} [Γ] [F] [ΠFG] [a] ⊢Δ [σ])
      [G[a]]′ = irrelevance′ (singleSubstLift G a) [G[a]]
      [σΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
      [σa] = proj₁ ([a] ⊢Δ [σ])
      [σb] = proj₁ ([b] ⊢Δ [σ])
  in  irrelevanceEqTerm′ (PE.sym (singleSubstLift G a)) PE.refl PE.refl [G[a]]′ [G[a]]
                         (app-congTerm [σF] [G[a]]′ [σΠFG] ([t≡u] ⊢Δ [σ])
                                       [σa] [σb] ([a≡b] ⊢Δ [σ]) (un-univ (escape [σG])))

appᵛ↑ : ∀ {F F' G rF rF' lF lF' lG lΠ t u Γ l}
       (lF≤ : lF ≤ lΠ)
       (lG≤ : lG ≤ lΠ)
       ([Γ] : ⊩ᵛ Γ)
       ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / [Γ])
       ([F'] : Γ ⊩ᵛ⟨ l ⟩ F' ^ [ rF' , ι lF' ] / [Γ])
       ([G] : Γ ∙ F ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ G ^ [ ! , ι lG ] / [Γ] ∙ [F]) 
       ([ΠFG] : Γ ⊩ᵛ⟨ l ⟩ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ [ ! , ι lΠ ] / [Γ])  
       ([t] : Γ ∙ F' ^ [ rF' , ι lF' ] ⊩ᵛ⟨ l ⟩ t ∷ wk1 (Π F ^ rF ° lF ▹ G ° lG ° lΠ) ^ [ ! , ι lΠ ] / [Γ] ∙ [F'] / wk1ᵛ {A = Π F ^ rF ° lF ▹ G ° lG ° lΠ} {F = F'} [Γ] [F'] [ΠFG])
       ([u] : Γ ∙ F' ^ [ rF' , ι lF' ] ⊩ᵛ⟨ l ⟩ u ∷ wk1 F ^ [ rF , ι lF ] / [Γ] ∙ [F'] / wk1ᵛ {A = F} {F = F'} [Γ] [F'] [F])
         → Γ ∙ F' ^ [ rF' , ι lF' ] ⊩ᵛ⟨ l ⟩ t ∘ u ^ lΠ ∷ G [ u ]↑ ^ [ ! , ι lG ] / [Γ] ∙ [F'] / subst↑S {F'} {G} {u} {F' = F} [Γ] [F'] [F] [G] [u]
appᵛ↑ {F} {F'} {G} {rF} {rF'} {lF} {lF'} {lG} {lΠ} {t} {u} lF≤ lG≤ [Γ] [F] [F'] [G] [ΠFG] [t] [u] =
  let [G[u]] = subst↑S {F'} {G} {u} {F' = F} [Γ] [F'] [F] [G] [u]
      [wF] = wk1ᵛ {A = F} {F = F'} [Γ] [F'] [F]
      [wG] = wk1dᵛ {F = F} {F' = F'} {G = G} [Γ] [F] [F'] [G]
      [wΠFG] = wk1ᵛ {A = Π F ^ rF ° lF ▹ G ° lG ° lΠ} {F = F'} [Γ] [F'] [ΠFG]
      [app] = appᵛ {F = wk1 F} {G = wk1d G} {t = t} {u = u} (_∙_ {A = F'} [Γ] [F']) [wF] [wG] [wΠFG] [t] [u]
  in S.irrelevanceTerm′ {A = wk1d G [ u ]} {A′ =  G [ u ]↑} {t = t ∘ u ^ lΠ} (PE.sym (wk1d[]-[]↑ G u)) PE.refl (_∙_ {A = F'} [Γ] [F']) (_∙_ {A = F'} [Γ] [F'])
                        (substSΠ {wk1 F} {wk1d G} {u} (_∙_ {A = F'} [Γ] [F']) [wF] [wΠFG] [u]) [G[u]] [app]

¹max : (i : Level) → i ≤ ¹
¹max ⁰ = <is≤ 0<1
¹max ¹ = ≡is≤ PE.refl


GappGen' : ∀ {F G Γ rF lF lG rΠ l Δ σ}
         ([Γ] : ⊩ᵛ Γ)
         ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / [Γ])
         → Γ ∙ F ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ G ^ [ rΠ , ι lG ] / [Γ] ∙ [F]  
         → ∀ ⊢Δ [σ] a 
         ([a] : Δ ⊩⟨ l ⟩ a ∷ subst σ F ^ [ rF , ι lF ]
                / proj₁ ([F] ⊢Δ [σ]))
         → Σ (Δ ⊩⟨ l ⟩ subst (consSubst σ a) G ^ [ rΠ , ι lG ])
               (λ [Aσ] →
               {σ′ : Nat → Term} →
               (Σ (Δ ⊩ˢ tail σ′ ∷ Γ / [Γ] / ⊢Δ)
               (λ [tailσ] →
                  Δ ⊩⟨ l ⟩ head σ′ ∷ subst (tail σ′) F ^ [ rF , ι lF ] / proj₁ ([F] ⊢Δ [tailσ]))) →
               Δ ⊩ˢ consSubst σ a ≡ σ′ ∷ Γ ∙ F ^ [ rF , ι lF ] /
               [Γ] ∙ [F] / ⊢Δ /
               consSubstS {t = a} {A = F} [Γ] ⊢Δ [σ] [F]
               [a] →
               Δ ⊩⟨ l ⟩ subst (consSubst σ a) G ≡
               subst σ′ G ^ [ rΠ , ι lG ] / [Aσ])
GappGen' {F} {G} {Γ} {rF} {lF} {lG} {rΠ} {l} {Δ} {σ} [Γ] [F] [G] ⊢Δ [σ] a [a] =
 [G] {σ = consSubst σ a} ⊢Δ (consSubstS {t = a} {A = F} [Γ] ⊢Δ [σ] [F] [a])


appirrᵛ : ∀ {F G rF lF t u Γ l} →
       ([Γ] : ⊩ᵛ Γ)
       ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / [Γ])
       ([G] :  Γ ∙ F ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ G ^ [ % , ι ⁰ ] / [Γ] ∙ [F])
       ([ΠFG] : Γ ⊩ᵛ⟨ l ⟩ Π F ^ rF ° lF ▹ G ° ⁰ ° ⁰ ^ [ % , ι ⁰ ] / [Γ])
       ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Π F ^ rF ° lF ▹ G ° ⁰ ° ⁰ ^ [ % , ι ⁰ ] / [Γ] / [ΠFG])
       ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ F ^ [ rF , ι lF ] / [Γ] / [F])
     → Γ ⊩ᵛ⟨ l ⟩ t ∘ u ^ ⁰ ∷ G [ u ] ^ [ % , ι ⁰ ] / [Γ] / substS {F} {G} {u} [Γ] [F] [G] [u]
appirrᵛ {F} {G} {rF} {lF} {t} {u} [Γ] [F] [G] [ΠFG] [t] [u] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [σF] = proj₁ ([F] ⊢Δ [σ])
      ⊢F = escape [σF]
      [G[u]] = substS {F} {G} {u} [Γ] [F] [G] [u]
      [σΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
      [σt] = proj₁ ([t] ⊢Δ [σ])
      [σu] = proj₁ ([u] ⊢Δ [σ])
      [liftσ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
      [σG]  = proj₁ ([G] (⊢Δ ∙ ⊢F) [liftσ]) 
      [σG[u]]  = proj₁ ([G[u]] ⊢Δ [σ])
      [σG[u]]′ = irrelevance′ (singleSubstLift G u) [σG[u]]
  in  irrelevanceTerm′ (PE.sym (singleSubstLift G u)) PE.refl PE.refl
                       [σG[u]]′ [σG[u]]
                       (appTermirr PE.refl [σF] [σG[u]]′ [σΠFG] [σt] [σu] (un-univ (escape [σG])))
  ,   (λ {σ′ = σ′} [σ′] [σ≡σ′] →
         let [σu′] = convTerm₂ [σF] (proj₁ ([F] ⊢Δ [σ′]))
                               (proj₂ ([F] ⊢Δ [σ]) [σ′] [σ≡σ′])
                               (proj₁ ([u] ⊢Δ [σ′]))
             [[uσ]≡[uσ]] = proj₂ ([u] ⊢Δ [σ]) [σ′] [σ≡σ′]
             [Gapp] = (GappGen' {F = F} {G = G} [Γ] [F] [G] ⊢Δ [σ] (subst σ u) (proj₁ ([u] ⊢Δ [σ])))
             [Gapp]₂ = proj₂ [Gapp] {σ′ = consSubst σ (subst σ′ u)} ([σ] , [σu′]) ((reflSubst [Γ] ⊢Δ [σ]) , [[uσ]≡[uσ]])
             irr = irrelevance′ (singleSubstLift G u) (proj₁ ([G[u]] ⊢Δ [σ]))
         in  irrelevanceEqTerm′ (PE.sym (singleSubstLift G u)) PE.refl PE.refl
                                [σG[u]]′ [σG[u]]
                                (app-congTermirr [σF] [σG[u]]′ [σΠFG]
                                              (proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′])
                                              [σu] [σu′]
                                              (irrelevanceEq″ (PE.sym (singleSubstComp (subst σ u) σ G)) (PE.sym (singleSubstComp (subst σ′ u) σ G))
                                                              PE.refl PE.refl (proj₁ [Gapp]) irr [Gapp]₂)
                                              (un-univ (escape [σG]))))

