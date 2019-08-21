{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Reduction {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution

open import Tools.Product


-- Weak head expansion of valid terms.
redSubstTermᵛ : ∀ {A t u rA l Γ}
              → ([Γ] : ⊩ᵛ Γ)
              → Γ ⊩ᵛ t ⇒ u ∷ A ^ rA / [Γ]
              → ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ rA / [Γ])
              → Γ ⊩ᵛ⟨ l ⟩ u ∷ A ^ rA / [Γ] / [A]
              → Γ ⊩ᵛ⟨ l ⟩ t ∷ A ^ rA / [Γ] / [A]
              × Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A ^ rA / [Γ] / [A]
redSubstTermᵛ [Γ] t⇒u [A] [u] =
  (λ ⊢Δ [σ] →
     let [σA] = proj₁ ([A] ⊢Δ [σ])
         [σt] , [σt≡σu] = redSubstTerm (t⇒u ⊢Δ [σ])
                                       (proj₁ ([A] ⊢Δ [σ]))
                                       (proj₁ ([u] ⊢Δ [σ]))
     in  [σt]
     ,   (λ [σ′] [σ≡σ′] →
            let [σ′A] = proj₁ ([A] ⊢Δ [σ′])
                [σA≡σ′A] = proj₂ ([A] ⊢Δ [σ]) [σ′] [σ≡σ′]
                [σ′t] , [σ′t≡σ′u] = redSubstTerm (t⇒u ⊢Δ [σ′])
                                                 (proj₁ ([A] ⊢Δ [σ′]))
                                                 (proj₁ ([u] ⊢Δ [σ′]))
            in  transEqTerm [σA] [σt≡σu]
                            (transEqTerm [σA] ((proj₂ ([u] ⊢Δ [σ])) [σ′] [σ≡σ′])
                                         (convEqTerm₂ [σA] [σ′A] [σA≡σ′A]
                                                      (symEqTerm [σ′A] [σ′t≡σ′u])))))
  , (λ ⊢Δ [σ] → proj₂ (redSubstTerm (t⇒u ⊢Δ [σ])
                                    (proj₁ ([A] ⊢Δ [σ]))
                                    (proj₁ ([u] ⊢Δ [σ]))))
