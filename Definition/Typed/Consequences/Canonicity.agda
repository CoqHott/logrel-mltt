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

postulate noNeSProp : ∀ {t A l} → ε ⊢ t ∷ A ^ [ % , ι l ] → ⊥

noNe : ∀ {t A r} → ε ⊢ t ∷ A ^ r → Neutral t → ⊥

noNe (⊢t ∘ⱼ ⊢t₁) (∘ₙ neT) = noNe ⊢t neT
noNe (natrecⱼ x ⊢t ⊢t₁ ⊢t₂) (natrecₙ neT) = noNe ⊢t₂ neT
noNe (Emptyrecⱼ A ⊢e) Emptyrecₙ = noNeSProp ⊢e
noNe (var x₁ ()) (var x)
noNe (Idⱼ [A] [A]₁ [A]₂) (Idₙ neT) = noNe [A] neT
noNe (Idⱼ [A] [A]₁ [A]₂) (Idℕₙ neT) = noNe [A]₁ neT
noNe (Idⱼ [A] [A]₁ [A]₂) (Idℕ0ₙ neT) = noNe [A]₂ neT
noNe (Idⱼ [A] [A]₁ [A]₂) (IdℕSₙ neT) = noNe [A]₂ neT
noNe (Idⱼ [A] [A]₁ [A]₂) (IdUₙ neT) = noNe [A]₁ neT
noNe (Idⱼ [A] [A]₁ [A]₂) (IdUℕₙ neT) = noNe [A]₂ neT
noNe (Idⱼ [A] [A]₁ [A]₂) (IdUΠₙ neT) = noNe [A]₂ neT
noNe (castⱼ [A] [A]₁ [A]₂ [A]₃) (castₙ neT) = noNe [A] neT
noNe (castⱼ [A] [A]₁ [A]₂ [A]₃) (castℕₙ neT) = noNe [A]₁ neT
noNe (castⱼ [A] [A]₁ [A]₂ [A]₃) (castΠₙ neT) = noNe [A]₁ neT
noNe (castⱼ [A] [A]₁ [A]₂ [A]₃) (castℕℕₙ neT) = noNe [A]₃ neT
noNe (castⱼ {r = !} [A] [A]₁ [A]₂ [A]₃) castℕΠₙ = noNeSProp [A]₂
noNe (castⱼ {r = %} [A] [A]₁ [A]₂ [A]₃) castℕΠₙ = noNeSProp [A]₂
noNe (castⱼ [A] [A]₁ [A]₂ [A]₃) castΠℕₙ = noNeSProp [A]₂
noNe (castⱼ [A] [A]₁ [A]₂ [A]₃) castΠΠ%!ₙ = noNeSProp [A]₂
noNe (castⱼ [A] [A]₁ [A]₂ [A]₃) castΠΠ!%ₙ = noNeSProp [A]₂
noNe (conv ⊢t x) (var n) = noNe ⊢t (var n)
noNe (conv ⊢t x) (∘ₙ neT) = noNe ⊢t (∘ₙ neT)
noNe (conv ⊢t x) (natrecₙ neT) = noNe ⊢t (natrecₙ neT)
noNe (conv ⊢t x) (Idₙ neT) = noNe ⊢t (Idₙ neT)
noNe (conv ⊢t x) (Idℕₙ neT) = noNe ⊢t (Idℕₙ neT)
noNe (conv ⊢t x) (Idℕ0ₙ neT) = noNe ⊢t (Idℕ0ₙ neT)
noNe (conv ⊢t x) (IdℕSₙ neT) = noNe ⊢t (IdℕSₙ neT)
noNe (conv ⊢t x) (IdUₙ neT) = noNe ⊢t (IdUₙ neT)
noNe (conv ⊢t x) (IdUℕₙ neT) = noNe ⊢t (IdUℕₙ neT)
noNe (conv ⊢t x) (IdUΠₙ neT) = noNe ⊢t (IdUΠₙ neT)
noNe (conv ⊢t x) (castₙ neT) = noNe ⊢t (castₙ neT)
noNe (conv ⊢t x) (castℕₙ neT) = noNe ⊢t (castℕₙ neT)
noNe (conv ⊢t x) (castΠₙ neT) = noNe ⊢t (castΠₙ neT)
noNe (conv ⊢t x) (castℕℕₙ neT) = noNe ⊢t (castℕℕₙ neT)
noNe (conv ⊢t x) castℕΠₙ = noNe ⊢t castℕΠₙ
noNe (conv ⊢t x) castΠℕₙ = noNe ⊢t castΠℕₙ
noNe (conv ⊢t x) castΠΠ%!ₙ = noNe ⊢t castΠΠ%!ₙ
noNe (conv ⊢t x) castΠΠ!%ₙ = noNe ⊢t castΠΠ!%ₙ
noNe (conv ⊢t x) Emptyrecₙ = noNe ⊢t Emptyrecₙ

-- Helper function for canonicity for reducible natural properties
canonicity″ : ∀ {t}
              → Natural-prop ε t
              → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ ^ [ ! , ι ⁰ ]
canonicity″ (sucᵣ (ℕₜ n₁ d n≡n prop)) =
  let a , b = canonicity″ prop
  in  1+ a , suc-cong (trans (subset*Term (redₜ d)) b)
canonicity″ zeroᵣ = 0 , refl (zeroⱼ ε)
canonicity″ (ne (neNfₜ neK ⊢k k≡k)) = ⊥-elim (noNe ⊢k neK)

-- Helper function for canonicity for specific reducible natural numbers
canonicity′ : ∀ {t l}
             → ([ℕ] : ε ⊩⟨ l ⟩ℕ ℕ)
             → ε ⊩⟨ l ⟩ t ∷ ℕ ^ [ ! , ι ⁰ ] / ℕ-intr [ℕ]
             → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ ^ [ ! , ι ⁰ ]
canonicity′ (noemb [ℕ]) (ℕₜ n d n≡n prop) = let a , b = canonicity″ prop
                                          in  a , trans (subset*Term (redₜ d)) b
canonicity′ (emb emb< [ℕ]) [t] = canonicity′ [ℕ] [t]
canonicity′ (emb ∞< [ℕ]) [t] = canonicity′ [ℕ] [t]

-- Canonicity of natural numbers
canonicity : ∀ {t} → ε ⊢ t ∷ ℕ ^ [ ! , ι ⁰ ] → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ ^ [ ! , ι ⁰ ]
canonicity ⊢t with reducibleTerm ⊢t
canonicity ⊢t | [ℕ] , [t] =
  canonicity′ (ℕ-elim [ℕ]) (irrelevanceTerm [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [t])

-- Canonicity for Empty

¬Empty′ : ∀ {n l} → ε ⊩Empty n ∷Empty^ l → ⊥
¬Empty′ (Emptyₜ (ne ⊢n)) = noNeSProp ⊢n

¬Empty : ∀ {n l} → ε ⊢ n ∷ Empty ^ [ % , ι l ] → ⊥
¬Empty {n} {l} ⊢n =
  let [Empty] , [n] = reducibleTerm ⊢n
      [Empty]′ = Emptyᵣ {l = next l} ([[ univ (Emptyⱼ ε) , univ (Emptyⱼ ε) , id (univ (Emptyⱼ ε)) ]])
      [n]′ = irrelevanceTerm [Empty] [Empty]′ [n]

  in ¬Empty′ [n]′
