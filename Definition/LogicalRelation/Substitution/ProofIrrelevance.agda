{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.ProofIrrelevance {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties using (wkSingleSubstId)
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution


open import Tools.Product
open import Tools.Unit
open import Tools.Empty
open import Tools.Nat

import Tools.PropositionalEquality as PE

~-quasirefl : ∀ {Γ n n′ A r} → Γ ⊢ n ~ n′ ∷ A ^ r → Γ ⊢ n ~ n ∷ A ^ r
~-quasirefl p = ~-trans p (~-sym p)

≅-quasirefl : ∀ {Γ n n′ A r} → Γ ⊢ n ≅ n′ ∷ A ^ r → Γ ⊢ n ≅ n ∷ A ^ r
≅-quasirefl p = ≅ₜ-trans p (≅ₜ-sym p)

proof-irrelevanceRel : ∀ {Γ A t u l} ([A] : Γ ⊩⟨ l ⟩ A ^ %)
                   → Γ ⊩⟨ l ⟩ t ∷ A ^ % / [A]
                   → Γ ⊩⟨ l ⟩ u ∷ A ^ % / [A]
                   → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ % / [A]
proof-irrelevanceRel (Emptyᵣ x)
                   (Emptyₜ (ne ⊢t))
                   (Emptyₜ (ne ⊢t₁)) = Emptyₜ₌ (ne ⊢t ⊢t₁)

proof-irrelevanceRel (ne x)
                   (neₜ ⊢t)
                   (neₜ ⊢t₁) =
                   neₜ₌ ⊢t  ⊢t₁
proof-irrelevanceRel {Γ} {l = l} (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) [f] [f₁] =
  [f] , [f₁]
proof-irrelevanceRel {Γ} {l = l} (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) [f] [f₁] =
  [f] , [f₁]

proof-irrelevanceRel (emb 0<1 [A]) [t] [u] = proof-irrelevanceRel [A] [t] [u]

proof-irrelevanceᵛ : ∀ {Γ A t u l} ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ % / [Γ])
                   → Γ ⊩ᵛ⟨ l ⟩ t ∷ A ^ % / [Γ] / [A]
                   → Γ ⊩ᵛ⟨ l ⟩ u ∷ A ^ % / [Γ] / [A]
                   → Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A ^ % / [Γ] / [A]
proof-irrelevanceᵛ [Γ] [A] [t] [u] {σ = σ} ⊢Δ [σ] =
  proof-irrelevanceRel (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ])) (proj₁ ([u] ⊢Δ [σ]))
