-- {-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Application {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Application
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Definition.LogicalRelation.Substitution.Introductions.Pi
open import Definition.LogicalRelation.Substitution.Weakening
import Definition.LogicalRelation.Substitution.Irrelevance as S

open import Tools.Product
import Tools.PropositionalEquality as PE

import Data.Nat as Nat

-- Application of valid terms.
appᵛ : ∀ {F G rF lF lG rΠ lΠ t u Γ l}
       ([Γ] : ⊩ᵛ Γ)
       ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / [Γ])
       ([ΠFG] : Γ ⊩ᵛ⟨ l ⟩ Π F ^ rF ° lF ▹ G ° lG ^ [ rΠ , ι lΠ ] / [Γ])
       ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Π F ^ rF ° lF ▹ G ° lG ^ [ rΠ , ι lΠ ] / [Γ] / [ΠFG])
       ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ F ^ [ rF , ι lF ] / [Γ] / [F])
     → Γ ⊩ᵛ⟨ l ⟩ t ∘ u ∷ G [ u ] ^ [ rΠ , ι lG ] / [Γ] / substSΠ {F} {G} {u} [Γ] [F] [ΠFG] [u]
appᵛ {F} {G} {rF} {lF} {lG} {rΠ} {lΠ} {t} {u} [Γ] [F] [ΠFG] [t] [u] {σ = σ} ⊢Δ [σ] =
  let [G[u]] = substSΠ {F} {G} {u} [Γ] [F] [ΠFG] [u]
      [σF] = proj₁ ([F] ⊢Δ [σ])
      [σΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
      [σt] = proj₁ ([t] ⊢Δ [σ])
      [σu] = proj₁ ([u] ⊢Δ [σ])
      [σG[u]]  = proj₁ ([G[u]] ⊢Δ [σ])
      [σG[u]]′ = irrelevance′ (singleSubstLift G u) [σG[u]]
  in  irrelevanceTerm′ (PE.sym (singleSubstLift G u)) PE.refl PE.refl
                       [σG[u]]′ [σG[u]]
                       (appTerm PE.refl [σF] [σG[u]]′ [σΠFG] [σt] [σu])
  ,   (λ [σ′] [σ≡σ′] →
         let [σu′] = convTerm₂ [σF] (proj₁ ([F] ⊢Δ [σ′]))
                               (proj₂ ([F] ⊢Δ [σ]) [σ′] [σ≡σ′])
                               (proj₁ ([u] ⊢Δ [σ′]))
         in  irrelevanceEqTerm′ (PE.sym (singleSubstLift G u)) PE.refl PE.refl
                                [σG[u]]′ [σG[u]]
                                (app-congTerm [σF] [σG[u]]′ [σΠFG]
                                              (proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′])
                                              [σu] [σu′]
                                              (proj₂ ([u] ⊢Δ [σ]) [σ′] [σ≡σ′])))

-- Application congurence of valid terms.
app-congᵛ : ∀ {F G rF lF lG rΠ lΠ t u a b Γ l}
            ([Γ] : ⊩ᵛ Γ)
            ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / [Γ])
            ([ΠFG] : Γ ⊩ᵛ⟨ l ⟩ Π F ^ rF ° lF ▹ G ° lG ^ [ rΠ , ι lΠ ] / [Γ])
            ([t≡u] : Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ Π F ^ rF ° lF ▹ G ° lG ^ [ rΠ , ι lΠ ] / [Γ] / [ΠFG])
            ([a] : Γ ⊩ᵛ⟨ l ⟩ a ∷ F ^ [ rF , ι lF ] / [Γ] / [F])
            ([b] : Γ ⊩ᵛ⟨ l ⟩ b ∷ F ^ [ rF , ι lF ] / [Γ] / [F])
            ([a≡b] : Γ ⊩ᵛ⟨ l ⟩ a ≡ b ∷ F ^ [ rF , ι lF ] / [Γ] / [F])
          → Γ ⊩ᵛ⟨ l ⟩ t ∘ a ≡ u ∘ b ∷ G [ a ] ^ [ rΠ , ι lG ] / [Γ]
              / substSΠ {F} {G} {a} [Γ] [F] [ΠFG] [a]
app-congᵛ {F} {G} {rF} {lF} {lG} {rΠ} {a = a} [Γ] [F] [ΠFG] [t≡u] [a] [b] [a≡b] ⊢Δ [σ] =
  let [σF] = proj₁ ([F] ⊢Δ [σ])
      [G[a]]  = proj₁ (substSΠ {F} {G} {a} [Γ] [F] [ΠFG] [a] ⊢Δ [σ])
      [G[a]]′ = irrelevance′ (singleSubstLift G a) [G[a]]
      [σΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
      [σa] = proj₁ ([a] ⊢Δ [σ])
      [σb] = proj₁ ([b] ⊢Δ [σ])
  in  irrelevanceEqTerm′ (PE.sym (singleSubstLift G a)) PE.refl PE.refl [G[a]]′ [G[a]]
                         (app-congTerm [σF] [G[a]]′ [σΠFG] ([t≡u] ⊢Δ [σ])
                                       [σa] [σb] ([a≡b] ⊢Δ [σ]))

appᵛ↑ : ∀ {F F' G rF rF' lF lF' lG rΠ lΠ t u Γ l}
       (lF≤ : lF ≤ lΠ)
       (lG≤ : lG ≤ lΠ)
       ([Γ] : ⊩ᵛ Γ)
       ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / [Γ])
       ([F'] : Γ ⊩ᵛ⟨ l ⟩ F' ^ [ rF' , ι lF' ] / [Γ])
       ([G] : Γ ∙ F ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ G ^ [ rΠ , ι lG ] / [Γ] ∙ [F]) 
       ([ΠFG] : Γ ⊩ᵛ⟨ l ⟩ Π F ^ rF ° lF ▹ G ° lG ^ [ rΠ , ι lΠ ] / [Γ])  
       ([t] : Γ ∙ F' ^ [ rF' , ι lF' ] ⊩ᵛ⟨ l ⟩ t ∷ wk1 (Π F ^ rF ° lF ▹ G ° lG) ^ [ rΠ , ι lΠ ] / [Γ] ∙ [F'] / wk1ᵛ {A = Π F ^ rF ° lF ▹ G ° lG} {F = F'} [Γ] [F'] [ΠFG])
       ([u] : Γ ∙ F' ^ [ rF' , ι lF' ] ⊩ᵛ⟨ l ⟩ u ∷ wk1 F ^ [ rF , ι lF ] / [Γ] ∙ [F'] / wk1ᵛ {A = F} {F = F'} [Γ] [F'] [F])
         → Γ ∙ F' ^ [ rF' , ι lF' ] ⊩ᵛ⟨ l ⟩ t ∘ u ∷ G [ u ]↑ ^ [ rΠ , ι lG ] / [Γ] ∙ [F'] / subst↑S {F'} {G} {u} {F' = F} [Γ] [F'] [F] [G] [u]
appᵛ↑ {F} {F'} {G} {rF} {rF'} {lF} {lF'} {lG} {rΠ} {lΠ} {t} {u} lF≤ lG≤ [Γ] [F] [F'] [G] [ΠFG] [t] [u] =
  let [G[u]] = subst↑S {F'} {G} {u} {F' = F} [Γ] [F'] [F] [G] [u]
      [wF] = wk1ᵛ {A = F} {F = F'} [Γ] [F'] [F]
      [wΠFG] = wk1ᵛ {A = Π F ^ rF ° lF ▹ G ° lG} {F = F'} [Γ] [F'] [ΠFG]
      [app] = appᵛ {F = wk1 F} {G = wk1d G} {t = t} {u = u} (_∙_ {A = F'} [Γ] [F']) [wF] [wΠFG] [t] [u]
  in S.irrelevanceTerm′ {A = wk1d G [ u ]} {A′ =  G [ u ]↑} {t = t ∘ u} (PE.sym (wk1d[]-[]↑ G u)) PE.refl (_∙_ {A = F'} [Γ] [F']) (_∙_ {A = F'} [Γ] [F'])
                        (substSΠ {wk1 F} {wk1d G} {u} (_∙_ {A = F'} [Γ] [F']) [wF] [wΠFG] [u]) [G[u]] [app]
