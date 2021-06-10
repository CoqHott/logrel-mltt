{-# OPTIONS --without-K  #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Reducibility {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties

open import Tools.Product


-- Valid types are reducible.
reducibleᵛ : ∀ {A sA Γ l}
             ([Γ] : ⊩ᵛ Γ)
           → Γ ⊩ᵛ⟨ l ⟩ A ⦂ sA / [Γ]
           → Γ ⊩⟨ l ⟩ A ⦂ sA
reducibleᵛ [Γ] [A] =
  let ⊢Γ = soundContext [Γ]
      [id] = idSubstS [Γ]
  in  irrelevance′ (subst-id _) (proj₁ ([A] ⊢Γ [id]))

-- Valid type equality is reducible.
reducibleEqᵛ : ∀ {A B sA Γ l}
               ([Γ] : ⊩ᵛ Γ)
               ([A] : Γ ⊩ᵛ⟨ l ⟩ A ⦂ sA / [Γ])
             → Γ ⊩ᵛ⟨ l ⟩ A ≡ B ⦂ sA / [Γ] / [A]
             → Γ ⊩⟨ l ⟩ A ≡ B ⦂ sA / reducibleᵛ [Γ] [A]
reducibleEqᵛ {A = A} [Γ] [A] [A≡B] =
  let [σA] = reducibleᵛ {A = A} [Γ] [A]
      ⊢Γ = soundContext [Γ]
      [id] = idSubstS [Γ]
  in  irrelevanceEq″ (subst-id _) (subst-id _)
                      (proj₁ ([A] ⊢Γ [id])) [σA] ([A≡B] ⊢Γ [id])

-- Valid terms are reducible.
reducibleTermᵛ : ∀ {t A sA Γ l}
                 ([Γ] : ⊩ᵛ Γ)
                 ([A] : Γ ⊩ᵛ⟨ l ⟩ A ⦂ sA / [Γ])
               → Γ ⊩ᵛ⟨ l ⟩ t ∷ A ⦂ sA / [Γ] / [A]
               → Γ ⊩⟨ l ⟩ t ∷ A ⦂ sA / reducibleᵛ [Γ] [A]
reducibleTermᵛ {A = A} [Γ] [A] [t] =
  let [σA] = reducibleᵛ {A = A} [Γ] [A]
      ⊢Γ = soundContext [Γ]
      [id] = idSubstS [Γ]
  in  irrelevanceTerm″ (subst-id _) (subst-id _)
                        (proj₁ ([A] ⊢Γ [id])) [σA] (proj₁ ([t] ⊢Γ [id]))

-- Valid term equality is reducible.
reducibleEqTermᵛ : ∀ {t u A sA Γ l}
                   ([Γ] : ⊩ᵛ Γ)
                   ([A] : Γ ⊩ᵛ⟨ l ⟩ A ⦂ sA / [Γ])
                 → Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A ⦂ sA / [Γ] / [A]
                 → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ⦂ sA / reducibleᵛ [Γ] [A]
reducibleEqTermᵛ {A = A} [Γ] [A] [t≡u] =
  let [σA] = reducibleᵛ {A = A} [Γ] [A]
      ⊢Γ = soundContext [Γ]
      [id] = idSubstS [Γ]
  in  irrelevanceEqTerm″ (subst-id _) (subst-id _) (subst-id _)
                          (proj₁ ([A] ⊢Γ [id])) [σA] ([t≡u] ⊢Γ [id])
