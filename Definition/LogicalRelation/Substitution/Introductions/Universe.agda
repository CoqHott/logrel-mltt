{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Universe {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution

open import Tools.Product
open import Tools.Empty

import Definition.LogicalRelation.Weakening as wkLR
import Tools.PropositionalEquality as PE
import Data.Nat as Nat

-- Validity of the universe type.
U¹ᵛ : ∀ {Γ rU l} → (ι ¹ <∞ l) → ([Γ] : ⊩ᵛ Γ)
      → Γ ⊩ᵛ⟨ l ⟩ Univ rU ¹ ^ [ ! , ∞ ] / [Γ]
U¹ᵛ {Γ} {rU} l< [Γ] ⊢Δ [σ] =
  (Uᵣ (Uᵣ rU ¹ l< PE.refl [[ Uⱼ ⊢Δ , Uⱼ ⊢Δ , id (Uⱼ ⊢Δ) ]]))
  , (λ [σ′] [σ≡σ′] → id (Uⱼ ⊢Δ))

U⁰ⱼ : ∀ {r Γ} → ⊢ Γ → Γ ⊢ Univ r ⁰ ^ [ ! , ι ¹ ]
U⁰ⱼ ⊢Γ = univ (univ 0<1 ⊢Γ)

U⁰ᵛ : ∀ {Γ rU l' l} → (⁰ ≤ l') → (ι l' <∞ l) → ([Γ] : ⊩ᵛ Γ)
      → Γ ⊩ᵛ⟨ l ⟩ Univ rU ⁰ ^ [ ! , ι ¹ ] / [Γ]
U⁰ᵛ {Γ} {rU} (<is≤ 0<1) ∞< [Γ] ⊢Δ [σ] = emb ∞< (Uᵣ (Uᵣ rU ⁰ emb< PE.refl [[ U⁰ⱼ ⊢Δ , U⁰ⱼ ⊢Δ , id (U⁰ⱼ ⊢Δ) ]])) , (λ [σ′] [σ≡σ′] → id (U⁰ⱼ ⊢Δ))
U⁰ᵛ {Γ} {rU} (≡is≤ PE.refl) l< [Γ] ⊢Δ [σ] = 
  Uᵣ (Uᵣ rU ⁰ l< PE.refl [[ U⁰ⱼ ⊢Δ , U⁰ⱼ ⊢Δ , id (U⁰ⱼ ⊢Δ) ]])
  , (λ [σ′] [σ≡σ′] → id (U⁰ⱼ ⊢Δ))

Uᵛgen : ∀ {Γ rU lU lU' l} → (lU ≤ lU') → (ι lU' <∞ l) → ([Γ] : ⊩ᵛ Γ)
     → Γ ⊩ᵛ⟨ l ⟩ Univ rU lU ^ [ ! , next lU ] / [Γ]
Uᵛgen {lU = ⁰} = U⁰ᵛ
Uᵛgen {lU = ¹} (≡is≤ PE.refl) = U¹ᵛ

Uᵛ : ∀ {Γ rU lU l} → (ι lU <∞ l) → ([Γ] : ⊩ᵛ Γ)
     → Γ ⊩ᵛ⟨ l ⟩ Univ rU lU ^ [ ! , next lU ] / [Γ]
Uᵛ = Uᵛgen (≡is≤ PE.refl)

-- Valid terms of type U are valid types.
univᵛ : ∀ {A Γ rU lU lU' l} ([Γ] : ⊩ᵛ Γ)
        (lU< : lU ≤ lU')
        ([U] : Γ ⊩ᵛ⟨ l ⟩ Univ rU lU ^ [ ! , next lU ] / [Γ])
      → Γ ⊩ᵛ⟨ l ⟩ A ∷ Univ rU lU ^ [ ! , next lU ] / [Γ] / [U]
      → Γ ⊩ᵛ⟨ ι lU' ⟩ A ^ [ rU , ι lU ] / [Γ]
univᵛ {lU = lU} {l = l} [Γ] lU< [U] [A] ⊢Δ [σ] =
  let [A]₁ = irrelevance-≤ lU< (univEq (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ]))) in
  [A]₁ , λ [σ′] [σ≡σ′] → univEqEq (proj₁ ([U] ⊢Δ [σ])) [A]₁
                                  ((proj₂ ([A] ⊢Δ [σ])) [σ′] [σ≡σ′])

-- Valid term equality of type U is valid type equality.
univEqᵛ : ∀ {A B Γ rU lU l l′} ([Γ] : ⊩ᵛ Γ)
          ([U] : Γ ⊩ᵛ⟨ l′ ⟩ Univ rU lU ^ [ ! , next lU ] / [Γ])
          ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ [ rU , ι lU ] / [Γ])
        → Γ ⊩ᵛ⟨ l′ ⟩ A ≡ B ∷ Univ rU lU ^ [ ! , next lU ] / [Γ] / [U]
        → Γ ⊩ᵛ⟨ l ⟩ A ≡ B ^ [ rU , ι lU ] / [Γ] / [A]
univEqᵛ {A} [Γ] [U] [A] [t≡u] ⊢Δ [σ] =
  univEqEq (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])) ([t≡u] ⊢Δ [σ])
