{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.MaybeEmbed {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution

open import Tools.Product


-- Any level can be embedded into the highest level (validity variant).
maybeEmbᵛ : ∀ {l A r Γ}
            ([Γ] : ⊩ᵛ Γ)
          → Γ ⊩ᵛ⟨ l ⟩ A ^ r / [Γ]
          → Γ ⊩ᵛ⟨ ∞ ⟩ A ^ r / [Γ]
maybeEmbᵛ {ι ⁰} [Γ] [A] ⊢Δ [σ] =
  let [σA]  = proj₁ ([A] ⊢Δ [σ])
      [σA]′ = maybeEmb (proj₁ ([A] ⊢Δ [σ]))
  in  [σA]′
  ,   (λ [σ′] [σ≡σ′] → irrelevanceEq [σA] [σA]′ (proj₂ ([A] ⊢Δ [σ]) [σ′] [σ≡σ′]))
maybeEmbᵛ {ι ¹} [Γ] [A] ⊢Δ [σ] =
  let [σA]  = proj₁ ([A] ⊢Δ [σ])
      [σA]′ = maybeEmb (proj₁ ([A] ⊢Δ [σ]))
  in  [σA]′
  ,   (λ [σ′] [σ≡σ′] → irrelevanceEq [σA] [σA]′ (proj₂ ([A] ⊢Δ [σ]) [σ′] [σ≡σ′]))
maybeEmbᵛ {∞} [Γ] [A] ⊢Δ [σ] = [A] ⊢Δ [σ]

-- The lowest level can be embedded in any level (validity variant).
maybeEmbₛ′ : ∀ {l A r Γ}
             ([Γ] : ⊩ᵛ Γ)
           → Γ ⊩ᵛ⟨ ι ⁰ ⟩ A ^ r / [Γ]
           → Γ ⊩ᵛ⟨ l ⟩ A ^ r / [Γ]
maybeEmbₛ′ {ι ⁰} [Γ] [A] = [A]
maybeEmbₛ′ {ι ¹} [Γ] [A] ⊢Δ [σ] =
  let [σA]  = proj₁ ([A] ⊢Δ [σ])
      [σA]′ = maybeEmb′ (proj₁ ([A] ⊢Δ [σ]))
  in  [σA]′
  ,   (λ [σ′] [σ≡σ′] → irrelevanceEq [σA] [σA]′ (proj₂ ([A] ⊢Δ [σ]) [σ′] [σ≡σ′]))
maybeEmbₛ′ {∞} [Γ] [A] ⊢Δ [σ] =
  let [σA]  = proj₁ ([A] ⊢Δ [σ])
      [σA]′ = maybeEmb′ (proj₁ ([A] ⊢Δ [σ]))
  in  [σA]′
  ,   (λ [σ′] [σ≡σ′] → irrelevanceEq [σA] [σA]′ (proj₂ ([A] ⊢Δ [σ]) [σ′] [σ≡σ′]))
