{-# OPTIONS --without-K  #-}

module Definition.Typed.Consequences.Consistency where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.EqRelInstance
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Fundamental.Reducibility

open import Tools.Empty
open import Tools.Product
import Tools.PropositionalEquality as PE


zero≢one′ : ∀ {Γ l} ([ℕ] : Γ ⊩⟨ l ⟩ℕ ℕ)
           → Γ ⊩⟨ l ⟩ zero ≡ suc zero ∷ ℕ ⦂ 𝕥y / ℕ-intr [ℕ] → ⊥
zero≢one′ (noemb x) (ℕₜ₌ .(suc _) .(suc _) d d′ k≡k′ (sucᵣ x₁)) =
  zero≢suc (whnfRed*Term (redₜ d) zeroₙ)
zero≢one′ (noemb x) (ℕₜ₌ .zero .zero d d′ k≡k′ zeroᵣ) =
  zero≢suc (PE.sym (whnfRed*Term (redₜ d′) sucₙ))
zero≢one′ (noemb x) (ℕₜ₌ k k′ d d′ k≡k′ (ne (neNfₜ₌ neK neM k≡m))) =
  zero≢ne neK (whnfRed*Term (redₜ d) zeroₙ)
zero≢one′ (emb 0<1 [ℕ]) n = zero≢one′ [ℕ] n

-- Zero cannot be judgmentally equal to one.
zero≢one : ∀ {Γ} → Γ ⊢ zero ≡ suc zero ∷ ℕ ⦂ 𝕥y → ⊥
zero≢one 0≡1 =
  let [ℕ] , [0≡1] = reducibleEqTerm 0≡1
  in  zero≢one′ (ℕ-elim [ℕ]) (irrelevanceEqTerm [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [0≡1])
