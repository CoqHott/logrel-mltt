-- {-# OPTIONS - #-}

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

-- No neutral terms are well-formed in an empty context

-- we need to postulate consistency

postulate noEmpty : ∀ {t} → ε ⊢ t ∷ Empty ^ % → ⊥

noNe : ∀ {t A r} → ε ⊢ t ∷ A ^ r → Neutral t → ⊥
noNe (var x₁ ()) (var x)
noNe (conv ⊢t x) (var n) = noNe ⊢t (var n)
noNe (⊢t ∘ⱼ ⊢t₁) (∘ₙ neT) = noNe ⊢t neT
noNe (conv ⊢t x) (∘ₙ neT) = noNe ⊢t (∘ₙ neT)
noNe (natrecⱼ x ⊢t ⊢t₁ ⊢t₂) (natrecₙ neT) = noNe ⊢t₂ neT
noNe (Emptyrecⱼ A ⊢e) Emptyrecₙ = noEmpty ⊢e
noNe (conv ⊢t x) (natrecₙ neT) = noNe ⊢t (natrecₙ neT)
noNe (conv ⊢t x) Emptyrecₙ = noNe ⊢t Emptyrecₙ


-- Helper function for canonicity for reducible natural properties
canonicity″ : ∀ {t}
              → Natural-prop ε t
              → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ ^ !
canonicity″ (sucᵣ (ℕₜ n₁ d n≡n prop)) =
  let a , b = canonicity″ prop
  in  1+ a , suc-cong (trans (subset*Term (redₜ d)) b)
canonicity″ zeroᵣ = 0 , refl (zeroⱼ ε)
canonicity″ (ne (neNfₜ neK ⊢k k≡k)) = ⊥-elim (noNe ⊢k neK)

-- Helper function for canonicity for specific reducible natural numbers
canonicity′ : ∀ {t l}
             → ([ℕ] : ε ⊩⟨ l ⟩ℕ ℕ)
             → ε ⊩⟨ l ⟩ t ∷ ℕ ^ ! / ℕ-intr [ℕ]
             → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ ^ !
canonicity′ (noemb [ℕ]) (ℕₜ n d n≡n prop) =
  let a , b = canonicity″ prop
  in  a , trans (subset*Term (redₜ d)) b
canonicity′ (emb 0<1 [ℕ]) [t] = canonicity′ [ℕ] [t]

-- Canonicity of natural numbers
canonicity : ∀ {t} → ε ⊢ t ∷ ℕ ^ ! → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ ^ !
canonicity ⊢t with reducibleTerm ⊢t
canonicity ⊢t | [ℕ] , [t] =
  canonicity′ (ℕ-elim [ℕ]) (irrelevanceTerm [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [t])

-- Canonicity for Empty

¬Empty′ : ∀ {n} → ε ⊩Empty n ∷Empty → ⊥
¬Empty′ (Emptyₜ (ne ⊢n)) = noEmpty ⊢n

¬Empty : ∀ {n} → ε ⊢ n ∷ Empty ^ % → ⊥
¬Empty {n} ⊢n =
  let [Empty] , [n] = reducibleTerm ⊢n
      [Empty]′ = Emptyᵣ {l = ¹} ([ Emptyⱼ ε , Emptyⱼ ε , id (Emptyⱼ ε) ])
      [n]′ = irrelevanceTerm [Empty] [Empty]′ [n]

  in ¬Empty′ [n]′
