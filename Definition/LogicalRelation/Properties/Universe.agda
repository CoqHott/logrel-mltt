{-# OPTIONS --without-K  #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Universe {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance


-- Helper function for reducible terms of type U for specific type derivations.
univEq′ : ∀ {l Γ A s} ([U] : Γ ⊩⟨ l ⟩U s) → Γ ⊩⟨ l ⟩ A ∷ Univ s ⦂ 𝕥y / U-intr [U] → Γ ⊩⟨ ⁰ ⟩ A ⦂ s
univEq′ (noemb (Uᵣ .⁰ 0<1 ⊢Γ)) (Uₜ A₁ d typeA A≡A [A]) = [A]
univEq′ (emb 0<1 x) [A] = univEq′ x [A]

-- Reducible terms of type U are reducible types.
univEq : ∀ {l Γ A s} ([U] : Γ ⊩⟨ l ⟩ Univ s ⦂ 𝕥y) → Γ ⊩⟨ l ⟩ A ∷ Univ s ⦂ 𝕥y / [U] → Γ ⊩⟨ ⁰ ⟩ A ⦂ s
univEq [U] [A] = univEq′ (U-elim [U])
                         (irrelevanceTerm [U] (U-intr (U-elim [U])) [A])

-- Helper function for reducible term equality of type U for specific type derivations.
univEqEq′ : ∀ {l l′ Γ A B s} ([U] : Γ ⊩⟨ l ⟩U s) ([A] : Γ ⊩⟨ l′ ⟩ A ⦂ s)
         → Γ ⊩⟨ l ⟩ A ≡ B ∷ Univ s ⦂ 𝕥y / U-intr [U]
         → Γ ⊩⟨ l′ ⟩ A ≡ B  ⦂ s / [A]
univEqEq′ (noemb (Uᵣ .⁰ 0<1 ⊢Γ)) [A]
          (Uₜ₌ A₁ B₁ d d′ typeA typeB A≡B [t] [u] [t≡u]) =
  irrelevanceEq [t] [A] [t≡u]
univEqEq′ (emb 0<1 x) [A] [A≡B] = univEqEq′ x [A] [A≡B]

-- Reducible term equality of type U is reducible type equality.
univEqEq : ∀ {l l′ Γ A B s} ([U] : Γ ⊩⟨ l ⟩ Univ s ⦂ 𝕥y) ([A] : Γ ⊩⟨ l′ ⟩ A ⦂ s)
         → Γ ⊩⟨ l ⟩ A ≡ B ∷ Univ s ⦂ 𝕥y / [U]
         → Γ ⊩⟨ l′ ⟩ A ≡ B ⦂ s / [A]
univEqEq [U] [A] [A≡B] =
  let [A≡B]′ = irrelevanceEqTerm [U] (U-intr (U-elim [U])) [A≡B]
  in  univEqEq′ (U-elim [U]) [A] [A≡B]′
