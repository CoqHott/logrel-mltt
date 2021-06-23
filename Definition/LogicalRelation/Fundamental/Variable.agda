{-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Fundamental.Variable {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped hiding (tt)
open import Definition.Untyped.Properties
open import Definition.Typed 
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution

open import Tools.Product
import Tools.PropositionalEquality as PE



-- Fundamental theorem for variables.
fundamentalVar : ∀ {Γ A rA x}
               → x ∷ A ^ rA ∈ Γ
               → ([Γ] : ⊩ᵛ Γ)
               → ∃ λ ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ rA / [Γ])
               → Γ ⊩ᵛ⟨ ∞ ⟩ var x ∷ A ^ rA / [Γ] / [A]
fundamentalVar here (_∙_ {A = A} {rA = rA} {l = l} [Γ] [A]) =
    (λ ⊢Δ [σ] →
       let [σA]  = proj₁ ([A] ⊢Δ (proj₁ [σ]))
           [σA′] = maybeEmb (irrelevance′ (PE.sym (subst-wk A)) [σA])
       in  [σA′]
       ,   (λ [σ′] [σ≡σ′] →
              irrelevanceEq″ (PE.sym (subst-wk A)) (PE.sym (subst-wk A)) PE.refl PE.refl 
                              [σA] [σA′] (proj₂ ([A] ⊢Δ (proj₁ [σ]))
                                                (proj₁ [σ′]) (proj₁ [σ≡σ′]))))
    , (λ ⊢Δ [σ] →
         let [σA]  = proj₁ ([A] ⊢Δ (proj₁ [σ]))
             [σA′] = maybeEmb (irrelevance′ (PE.sym (subst-wk A)) [σA])
         in  irrelevanceTerm′ (PE.sym (subst-wk A)) PE.refl PE.refl [σA] [σA′] (proj₂ [σ])
    , (λ [σ′] [σ≡σ′] → irrelevanceEqTerm′ (PE.sym (subst-wk A)) PE.refl PE.refl 
                                          [σA] [σA′] (proj₂ [σ≡σ′])))
fundamentalVar (there {A = A} h) ([Γ] ∙ [B]) =
    (λ ⊢Δ [σ] →
       let [h]   = proj₁ (fundamentalVar h [Γ]) ⊢Δ (proj₁ [σ])
           [σA]  = proj₁ [h]
           [σA′] = irrelevance′ (PE.sym (subst-wk A)) [σA]
       in  [σA′]
       ,   (λ [σ′] [σ≡σ′] →
              irrelevanceEq″ (PE.sym (subst-wk A)) (PE.sym (subst-wk A)) PE.refl PE.refl
                              [σA] [σA′]
                              (proj₂ [h] (proj₁ [σ′]) (proj₁ [σ≡σ′]))))
    , (λ ⊢Δ [σ] →
         let [h]   = (proj₁ (fundamentalVar h [Γ])) ⊢Δ (proj₁ [σ])
             [σA]  = proj₁ [h]
             [σA′] = irrelevance′ (PE.sym (subst-wk A)) [σA]
             [h′] = (proj₂ (fundamentalVar h [Γ])) ⊢Δ (proj₁ [σ])
         in  irrelevanceTerm′ (PE.sym (subst-wk A)) PE.refl PE.refl [σA] [σA′] (proj₁ [h′])
         ,   (λ [σ′] [σ≡σ′] →
                irrelevanceEqTerm′ (PE.sym (subst-wk A)) PE.refl PE.refl [σA] [σA′]
                                   (proj₂ [h′] (proj₁ [σ′]) (proj₁ [σ≡σ′]))))
