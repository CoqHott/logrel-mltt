{-# OPTIONS --safe #-}

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

noNeSPropAx : Set
noNeSPropAx = ∀ {t A l} → ε ⊢ t ∷ A ^ [ % , ι l ] → ⊥

noNe : ∀ {t A r} → noNeSPropAx → ε ⊢ t ∷ A ^ r → Neutral t → ⊥

noNe noNeSProp (⊢t ∘ⱼ ⊢t₁) (∘ₙ neT) = noNe noNeSProp  ⊢t neT
noNe noNeSProp (natrecⱼ x ⊢t ⊢t₁ ⊢t₂) (natrecₙ neT) = noNe noNeSProp ⊢t₂ neT
noNe noNeSProp (Emptyrecⱼ A ⊢e) Emptyrecₙ = noNeSProp ⊢e
noNe noNeSProp (var x₁ ()) (var x)
noNe noNeSProp (Idⱼ [A] [A]₁ [A]₂) (Idₙ neT) = noNe noNeSProp [A] neT
noNe noNeSProp (Idⱼ [A] [A]₁ [A]₂) (Idℕₙ neT) = noNe noNeSProp [A]₁ neT
noNe noNeSProp (Idⱼ [A] [A]₁ [A]₂) (Idℕ0ₙ neT) = noNe noNeSProp [A]₂ neT
noNe noNeSProp (Idⱼ [A] [A]₁ [A]₂) (IdℕSₙ neT) = noNe noNeSProp [A]₂ neT
noNe noNeSProp (Idⱼ [A] [A]₁ [A]₂) (IdUₙ neT) = noNe noNeSProp [A]₁ neT
noNe noNeSProp (Idⱼ [A] [A]₁ [A]₂) (IdUℕₙ neT) = noNe noNeSProp [A]₂ neT
noNe noNeSProp (Idⱼ [A] [A]₁ [A]₂) (IdUΠₙ neT) = noNe noNeSProp [A]₂ neT
noNe noNeSProp (castⱼ [A] [A]₁ [A]₂ [A]₃) (castₙ neT) = noNe noNeSProp [A] neT
noNe noNeSProp (castⱼ [A] [A]₁ [A]₂ [A]₃) (castℕₙ neT) = noNe noNeSProp [A]₁ neT
noNe noNeSProp (castⱼ [A] [A]₁ [A]₂ [A]₃) (castΠₙ neT) = noNe noNeSProp [A]₁ neT
noNe noNeSProp (castⱼ [A] [A]₁ [A]₂ [A]₃) (castℕℕₙ neT) = noNe noNeSProp [A]₃ neT
noNe noNeSProp (castⱼ {r = !} [A] [A]₁ [A]₂ [A]₃) castℕΠₙ = noNeSProp [A]₂
noNe noNeSProp (castⱼ {r = %} [A] [A]₁ [A]₂ [A]₃) castℕΠₙ = noNeSProp [A]₂
noNe noNeSProp (castⱼ [A] [A]₁ [A]₂ [A]₃) castΠℕₙ = noNeSProp [A]₂
noNe noNeSProp (castⱼ [A] [A]₁ [A]₂ [A]₃) castΠΠ%!ₙ = noNeSProp [A]₂
noNe noNeSProp (castⱼ [A] [A]₁ [A]₂ [A]₃) castΠΠ!%ₙ = noNeSProp [A]₂
noNe noNeSProp (conv ⊢t x) (var n) = noNe noNeSProp ⊢t (var n)
noNe noNeSProp (conv ⊢t x) (∘ₙ neT) = noNe noNeSProp ⊢t (∘ₙ neT)
noNe noNeSProp (conv ⊢t x) (natrecₙ neT) = noNe noNeSProp ⊢t (natrecₙ neT)
noNe noNeSProp (conv ⊢t x) (Idₙ neT) = noNe noNeSProp ⊢t (Idₙ neT)
noNe noNeSProp (conv ⊢t x) (Idℕₙ neT) = noNe noNeSProp ⊢t (Idℕₙ neT)
noNe noNeSProp (conv ⊢t x) (Idℕ0ₙ neT) = noNe noNeSProp ⊢t (Idℕ0ₙ neT)
noNe noNeSProp (conv ⊢t x) (IdℕSₙ neT) = noNe noNeSProp ⊢t (IdℕSₙ neT)
noNe noNeSProp (conv ⊢t x) (IdUₙ neT) = noNe noNeSProp ⊢t (IdUₙ neT)
noNe noNeSProp (conv ⊢t x) (IdUℕₙ neT) = noNe noNeSProp ⊢t (IdUℕₙ neT)
noNe noNeSProp (conv ⊢t x) (IdUΠₙ neT) = noNe noNeSProp ⊢t (IdUΠₙ neT)
noNe noNeSProp (conv ⊢t x) (castₙ neT) = noNe noNeSProp ⊢t (castₙ neT)
noNe noNeSProp (conv ⊢t x) (castℕₙ neT) = noNe noNeSProp ⊢t (castℕₙ neT)
noNe noNeSProp (conv ⊢t x) (castΠₙ neT) = noNe noNeSProp ⊢t (castΠₙ neT)
noNe noNeSProp (conv ⊢t x) (castℕℕₙ neT) = noNe noNeSProp ⊢t (castℕℕₙ neT)
noNe noNeSProp (conv ⊢t x) castℕΠₙ = noNe noNeSProp ⊢t castℕΠₙ
noNe noNeSProp (conv ⊢t x) castΠℕₙ = noNe noNeSProp ⊢t castΠℕₙ
noNe noNeSProp (conv ⊢t x) castΠΠ%!ₙ = noNe noNeSProp ⊢t castΠΠ%!ₙ
noNe noNeSProp (conv ⊢t x) castΠΠ!%ₙ = noNe noNeSProp ⊢t castΠΠ!%ₙ
noNe noNeSProp (conv ⊢t x) Emptyrecₙ = noNe noNeSProp ⊢t Emptyrecₙ

-- Helper function for canonicity for reducible natural properties
canonicity″ : ∀ {t}
              → noNeSPropAx
              → Natural-prop ε t
              → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ ^ [ ! , ι ⁰ ]
canonicity″ noNeSProp (sucᵣ (ℕₜ n₁ d n≡n prop)) =
  let a , b = canonicity″ noNeSProp prop
  in  1+ a , suc-cong (trans (subset*Term (redₜ d)) b)
canonicity″ noNeSProp zeroᵣ = 0 , refl (zeroⱼ ε)
canonicity″ noNeSProp (ne (neNfₜ neK ⊢k k≡k)) = ⊥-elim (noNe noNeSProp ⊢k neK)

-- Helper function for canonicity for specific reducible natural numbers
canonicity′ : ∀ {t l}
             → noNeSPropAx
             → ([ℕ] : ε ⊩⟨ l ⟩ℕ ℕ)
             → ε ⊩⟨ l ⟩ t ∷ ℕ ^ [ ! , ι ⁰ ] / ℕ-intr [ℕ]
             → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ ^ [ ! , ι ⁰ ]
canonicity′ noNeSProp (noemb [ℕ]) (ℕₜ n d n≡n prop) = let a , b = canonicity″ noNeSProp prop
                                          in  a , trans (subset*Term (redₜ d)) b
canonicity′ noNeSProp (emb emb< [ℕ]) [t] = canonicity′ noNeSProp [ℕ] [t]
canonicity′ noNeSProp (emb ∞< [ℕ]) [t] = canonicity′ noNeSProp [ℕ] [t]

-- Canonicity of natural numbers
canonicity : ∀ {t} →
             noNeSPropAx →
             ε ⊢ t ∷ ℕ ^ [ ! , ι ⁰ ] →
             ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ ^ [ ! , ι ⁰ ]
canonicity noNeSProp ⊢t with reducibleTerm ⊢t
canonicity noNeSProp ⊢t | [ℕ] , [t] =
  canonicity′ noNeSProp (ℕ-elim [ℕ]) (irrelevanceTerm [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [t])
