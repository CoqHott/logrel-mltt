{-# OPTIONS --without-K #-}

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

consistent : Con Term → Set
consistent = λ Γ → ∀ t → Γ ⊢ t ∷ Empty ^ % →  ⊥

-- consider only propositional contexts

data prop-ctx : Con Term → Set where
  prop-ctx-ε : prop-ctx ε
  prop-ctx-· : ∀ {Γ A} → prop-ctx Γ → prop-ctx (Γ ∙ A ^ %)

prop-ctx-var : ∀ {Γ t A} → prop-ctx Γ → t ∷ A ^ ! ∈ Γ → ⊥
prop-ctx-var prop-ctx-ε ()
prop-ctx-var (prop-ctx-· p) (there m) = prop-ctx-var p m

-- A neutral is an SProp in a propositional consistent context

neSProp : ∀ {Γ t A} → prop-ctx Γ → consistent Γ → Neutral t → Γ ⊢ t ∷ A ^ ! → ⊥
neSProp pΓ e (var n) (var ⊢Γ ⊢n) = prop-ctx-var pΓ ⊢n
neSProp pΓ e (var n) (conv ⊢t x) = neSProp pΓ e (var n) ⊢t
neSProp pΓ e (∘ₙ n) (⊢f ∘ⱼ ⊢a) = neSProp pΓ e n ⊢f
neSProp pΓ e (∘ₙ n) (conv ⊢t x) = neSProp pΓ e (∘ₙ n) ⊢t
neSProp pΓ e (natrecₙ n) (natrecⱼ ⊢P ⊢p0 ⊢pL ⊢m) = neSProp pΓ e n ⊢m
neSProp pΓ e (natrecₙ n) (conv ⊢t x) = neSProp pΓ e (natrecₙ n) ⊢t
neSProp pΓ e (Emptyrecₙ) (Emptyrecⱼ {_} {_} {e₁} x ⊢t) = e e₁ ⊢t
neSProp pΓ e (Emptyrecₙ {e₁}) (conv ⊢t x) = neSProp pΓ e Emptyrecₙ ⊢t

-- Helper function for canonicity for reducible natural properties
canonicity″ : ∀ {Γ t}
               → ⊢ Γ
               → prop-ctx Γ
               → consistent Γ
               → Natural-prop Γ t
               → ∃ λ k → Γ ⊢ t ≡ sucᵏ k ∷ ℕ ^ !
canonicity″ ⊢Γ p e (sucᵣ (ℕₜ n₁ d n≡n prop)) =
  let a , b = canonicity″ ⊢Γ p e prop
  in  1+ a , suc-cong (trans (subset*Term (redₜ d)) b)
canonicity″ ⊢Γ p _ zeroᵣ = 0 , refl (zeroⱼ ⊢Γ)
canonicity″ ⊢Γ p e (ne (neNfₜ neK ⊢k k≡k)) = ⊥-elim (neSProp p e neK ⊢k)

-- Helper function for canonicity for specific reducible natural numbers
canonicity′ : ∀ {Γ t l}
              → prop-ctx Γ
              → consistent Γ
              → ([ℕ] : Γ ⊩⟨ l ⟩ℕ ℕ)
              → Γ ⊩⟨ l ⟩ t ∷ ℕ ^ ! / ℕ-intr [ℕ]
              → ∃ λ k → Γ ⊢ t ≡ sucᵏ k ∷ ℕ ^ !
canonicity′ p e (noemb [ℕ]) (ℕₜ n d n≡n prop) =
  let a , b = canonicity″ (wfEqTerm n≡n) p e prop
  in  a , trans (subset*Term (redₜ d)) b
canonicity′ p e (emb 0<1 [ℕ]) [t] = canonicity′ p e [ℕ] [t]

-- Canonicity of natural numbers
canonicity : ∀ {Γ t} → prop-ctx Γ → consistent Γ → Γ ⊢ t ∷ ℕ ^ ! → ∃ λ k → Γ ⊢ t ≡ sucᵏ k ∷ ℕ ^ !
canonicity p e ⊢t with reducibleTerm ⊢t
canonicity p e ⊢t | [ℕ] , [t] =
  canonicity′ p e (ℕ-elim [ℕ]) (irrelevanceTerm [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [t])

-- Canonicity for Empty

-- we need to postulate consistency

postulate noEmpty : ∀ {t} → ε ⊢ t ∷ Empty ^ % → ⊥

¬Empty′ : ∀ {n} → ε ⊩Empty n ∷Empty → ⊥
¬Empty′ (Emptyₜ (ne ⊢n)) = noEmpty ⊢n

¬Empty : ∀ {n} → ε ⊢ n ∷ Empty ^ % → ⊥
¬Empty {n} ⊢n =
  let [Empty] , [n] = reducibleTerm ⊢n
      [Empty]′ = Emptyᵣ {l = ¹} ([ Emptyⱼ ε , Emptyⱼ ε , id (Emptyⱼ ε) ])
      [n]′ = irrelevanceTerm [Empty] [Empty]′ [n]

  in ¬Empty′ [n]′
