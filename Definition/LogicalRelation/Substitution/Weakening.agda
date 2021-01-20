{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Weakening {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Substitution

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Weakening of valid types by one.
wk1ᵛ : ∀ {A F rA rF Γ l}
      ([Γ] : ⊩ᵛ Γ)
      ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ rF / [Γ])
    → Γ ⊩ᵛ⟨ l ⟩ A ^ rA / [Γ]
    → Γ ∙ F ^ rF ⊩ᵛ⟨ l ⟩ wk1 A ^ rA / ([Γ] ∙ [F])
wk1ᵛ {A} [Γ] [F] [A] ⊢Δ [σ] =
  let [σA] = proj₁ ([A] ⊢Δ (proj₁ [σ]))
      [σA]′ = irrelevance′ (PE.sym (subst-wk A)) [σA]
  in  [σA]′
  ,   (λ [σ′] [σ≡σ′] →
         irrelevanceEq″ (PE.sym (subst-wk A))
                        (PE.sym (subst-wk A))
                        [σA] [σA]′
                        (proj₂ ([A] ⊢Δ (proj₁ [σ])) (proj₁ [σ′]) (proj₁ [σ≡σ′])))

-- Weakening of valid type equality by one.
wk1Eqᵛ : ∀ {A B F rA rF Γ l}
         ([Γ] : ⊩ᵛ Γ)
         ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ rF / [Γ])
         ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ rA / [Γ])
         ([A≡B] : Γ ⊩ᵛ⟨ l ⟩ A ≡ B ^ rA / [Γ] / [A])
       → Γ ∙ F ^ rF ⊩ᵛ⟨ l ⟩ wk1 A ≡ wk1 B ^ rA / [Γ] ∙ [F] / wk1ᵛ {A} {F} [Γ] [F] [A]
wk1Eqᵛ {A} {B} [Γ] [F] [A] [A≡B] ⊢Δ [σ] =
  let [σA] = proj₁ ([A] ⊢Δ (proj₁ [σ]))
      [σA]′ = irrelevance′ (PE.sym (subst-wk A)) [σA]
  in  irrelevanceEq″ (PE.sym (subst-wk A))
                     (PE.sym (subst-wk B))
                     [σA] [σA]′
                     ([A≡B] ⊢Δ (proj₁ [σ]))
