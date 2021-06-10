{-# OPTIONS --without-K  #-}

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

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Application of valid terms.
appᵛ : ∀ {F G sF sG t u Γ l}
       ([Γ] : ⊩ᵛ Γ)
       ([F] : Γ ⊩ᵛ⟨ l ⟩ F ⦂ sF / [Γ])
       ([ΠFG] : Γ ⊩ᵛ⟨ l ⟩ Π F ⦂ sF ▹ G ⦂ sG / [Γ])
       ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ Π F ⦂ sF ▹ G ⦂ sG / [Γ] / [ΠFG])
       ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ F ⦂ sF / [Γ] / [F])
     → Γ ⊩ᵛ⟨ l ⟩ t ∘ u ∷ G [ u ] ⦂ sG / [Γ] / substSΠ {F} {G} {u} [Γ] [F] [ΠFG] [u]
appᵛ {F} {G} {sF} {sG} {t} {u} [Γ] [F] [ΠFG] [t] [u] {σ = σ} ⊢Δ [σ] =
  let [G[u]] = substSΠ {F} {G} {u} [Γ] [F] [ΠFG] [u]
      [σF] = proj₁ ([F] ⊢Δ [σ])
      [σΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
      [σt] = proj₁ ([t] ⊢Δ [σ])
      [σu] = proj₁ ([u] ⊢Δ [σ])
      [σG[u]]  = proj₁ ([G[u]] ⊢Δ [σ])
      [σG[u]]′ = irrelevance′ (singleSubstLift G u) [σG[u]]
  in  irrelevanceTerm′ (PE.sym (singleSubstLift G u)) PE.refl
                       [σG[u]]′ [σG[u]]
                       (appTerm PE.refl [σF] [σG[u]]′ [σΠFG] [σt] [σu])
  ,   (λ [σ′] [σ≡σ′] →
         let [σu′] = convTerm₂ [σF] (proj₁ ([F] ⊢Δ [σ′]))
                               (proj₂ ([F] ⊢Δ [σ]) [σ′] [σ≡σ′])
                               (proj₁ ([u] ⊢Δ [σ′]))
         in  irrelevanceEqTerm′ (PE.sym (singleSubstLift G u)) PE.refl
                                [σG[u]]′ [σG[u]]
                                (app-congTerm [σF] [σG[u]]′ [σΠFG]
                                              (proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′])
                                              [σu] [σu′]
                                              (proj₂ ([u] ⊢Δ [σ]) [σ′] [σ≡σ′])))

-- Application congurence of valid terms.
app-congᵛ : ∀ {F G sF sG t u a b Γ l}
            ([Γ] : ⊩ᵛ Γ)
            ([F] : Γ ⊩ᵛ⟨ l ⟩ F ⦂ sF / [Γ])
            ([ΠFG] : Γ ⊩ᵛ⟨ l ⟩ Π F ⦂ sF ▹ G ⦂ sG / [Γ])
            ([t≡u] : Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ Π F ⦂ sF ▹ G ⦂ sG / [Γ] / [ΠFG])
            ([a] : Γ ⊩ᵛ⟨ l ⟩ a ∷ F ⦂ sF / [Γ] / [F])
            ([b] : Γ ⊩ᵛ⟨ l ⟩ b ∷ F ⦂ sF / [Γ] / [F])
            ([a≡b] : Γ ⊩ᵛ⟨ l ⟩ a ≡ b ∷ F ⦂ sF / [Γ] / [F])
          → Γ ⊩ᵛ⟨ l ⟩ t ∘ a ≡ u ∘ b ∷ G [ a ] ⦂ sG / [Γ]
              / substSΠ {F} {G} {a} [Γ] [F] [ΠFG] [a]
app-congᵛ {F} {G} {sF} {sG} {a = a} [Γ] [F] [ΠFG] [t≡u] [a] [b] [a≡b] ⊢Δ [σ] =
  let [σF] = proj₁ ([F] ⊢Δ [σ])
      [G[a]]  = proj₁ (substSΠ {F} {G} {a} [Γ] [F] [ΠFG] [a] ⊢Δ [σ])
      [G[a]]′ = irrelevance′ (singleSubstLift G a) [G[a]]
      [σΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
      [σa] = proj₁ ([a] ⊢Δ [σ])
      [σb] = proj₁ ([b] ⊢Δ [σ])
  in  irrelevanceEqTerm′ (PE.sym (singleSubstLift G a)) PE.refl [G[a]]′ [G[a]]
                         (app-congTerm [σF] [G[a]]′ [σΠFG] ([t≡u] ⊢Δ [σ])
                                       [σa] [σb] ([a≡b] ⊢Δ [σ]))
