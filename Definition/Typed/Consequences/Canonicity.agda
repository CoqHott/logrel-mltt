{-# OPTIONS --without-K  #-}

module Definition.Typed.Consequences.Canonicity where

open import Definition.Untyped

open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.Typed.EqRelInstance
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Fundamental.Reducibility

open import Tools.Empty
open import Tools.Nat
open import Tools.Product


-- Turns a natural number into its term representation
sucᵏ : Nat → Term
sucᵏ 0 = zero
sucᵏ (1+ n) = suc (sucᵏ n)

-- Helper function for canonicity for reducible natural properties
canonicity″ : ∀ {t}
              → Natural-prop ε t
              → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ ⦂ 𝕥y
canonicity″ (sucᵣ (ℕₜ n₁ d n≡n prop)) =
  let a , b = canonicity″ prop
  in  1+ a , suc-cong (trans (subset*Term (redₜ d)) b)
canonicity″ zeroᵣ = 0 , refl (zeroⱼ ε)
canonicity″ (ne (neNfₜ neK ⊢k k≡k)) = ⊥-elim (noNe ⊢k neK)

-- Helper function for canonicity for specific reducible natural numbers
canonicity′ : ∀ {t l}
             → ([ℕ] : ε ⊩⟨ l ⟩ℕ ℕ)
             → ε ⊩⟨ l ⟩ t ∷ ℕ ⦂ 𝕥y / ℕ-intr [ℕ]
             → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ ⦂ 𝕥y
canonicity′ (noemb [ℕ]) (ℕₜ n d n≡n prop) =
  let a , b = canonicity″ prop
  in  a , trans (subset*Term (redₜ d)) b
canonicity′ (emb 0<1 [ℕ]) [t] = canonicity′ [ℕ] [t]

-- Canonicity of natural numbers
canonicity : ∀ {t} → ε ⊢ t ∷ ℕ ⦂ 𝕥y → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ ⦂ 𝕥y
canonicity ⊢t with reducibleTerm ⊢t
canonicity ⊢t | [ℕ] , [t] =
  canonicity′ (ℕ-elim [ℕ]) (irrelevanceTerm [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [t])

-- Canonicity for Empty

¬Empty′ : ∀ {n} → ε ⊩Empty n ∷Empty → ⊥
¬Empty′ (Emptyₜ n _ n≡n (ne (neNfₜ neN ⊢n _))) =
  noNe ⊢n neN

¬Empty : ∀ {n} → ε ⊢ n ∷ Empty ⦂ 𝕥y → ⊥
¬Empty {n} ⊢n =
  let [Empty] , [n] = reducibleTerm ⊢n
      [Empty]′ = Emptyᵣ {l = ¹} ([ Emptyⱼ ε , Emptyⱼ ε , id (Emptyⱼ ε) ])
      [n]′ = irrelevanceTerm [Empty] [Empty]′ [n]

  in ¬Empty′ [n]′
