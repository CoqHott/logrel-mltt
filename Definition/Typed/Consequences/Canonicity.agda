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
-- as we have several uninhabited propositions, we build an predicate
-- to characterize them

-- Note that we could also have defined reductions to Empty of other
-- forms of unihabited types

data isFalse : Term → Set where
  isEmpty : ∀ {lEmpty} → isFalse (Empty lEmpty)
  isIdℕΠ : ∀ {r A rA B} → isFalse (Id (Univ r ⁰) ℕ (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰))
  isIdΠℕ : ∀ {r A rA B} → isFalse (Id (Univ r ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰) ℕ)
  isIdΠΠ%! : ∀ {r A B A' B'} → isFalse (Id (Univ r ⁰) (Π A ^ % ° ⁰ ▹ B ° ⁰ ° ⁰) (Π A' ^ ! ° ⁰ ▹ B' ° ⁰ ° ⁰))
  isIdΠΠ!% : ∀ {r A B A' B'} → isFalse (Id (Univ r ⁰) (Π A ^ ! ° ⁰ ▹ B ° ⁰ ° ⁰) (Π A' ^ % ° ⁰ ▹ B' ° ⁰ ° ⁰))

consistency = ∀ {t A l} → isFalse A → ε ⊢ t ∷ A ^ [ % , l ] → ⊥

noNe : ∀ {t A r} → consistency → ε ⊢ t ∷ A ^ r → Neutral t → ⊥

-- impossible cases thanks to consistency
noNe consistency (Emptyrecⱼ A ⊢e) Emptyrecₙ = consistency isEmpty ⊢e
noNe consistency (castⱼ [A] [A]₁ [A]₂ [A]₃) castℕΠₙ = consistency isIdℕΠ [A]₂
noNe consistency (castⱼ [A] [A]₁ [A]₂ [A]₃) castΠℕₙ = consistency isIdΠℕ [A]₂
noNe consistency (castⱼ [A] [A]₁ [A]₂ [A]₃) castΠΠ%!ₙ = consistency isIdΠΠ%! [A]₂
noNe consistency (castⱼ [A] [A]₁ [A]₂ [A]₃) castΠΠ!%ₙ = consistency isIdΠΠ!% [A]₂

-- possible cases proven by induction 
noNe consistency (_ ▹ _ ▹ _ ▹ ⊢t ∘ⱼ ⊢t₁) (∘ₙ neT) = noNe consistency  ⊢t neT
noNe consistency (natrecⱼ x _ ⊢t ⊢t₁ ⊢t₂) (natrecₙ neT) = noNe consistency ⊢t₂ neT
noNe consistency (var x₁ ()) (var x)
noNe consistency (Idⱼ [A] [A]₁ [A]₂) (Idₙ neT) = noNe consistency [A] neT
noNe consistency (Idⱼ [A] [A]₁ [A]₂) (Idℕₙ neT) = noNe consistency [A]₁ neT
noNe consistency (Idⱼ [A] [A]₁ [A]₂) (Idℕ0ₙ neT) = noNe consistency [A]₂ neT
noNe consistency (Idⱼ [A] [A]₁ [A]₂) (IdℕSₙ neT) = noNe consistency [A]₂ neT
noNe consistency (Idⱼ [A] [A]₁ [A]₂) (IdUₙ neT) = noNe consistency [A]₁ neT
noNe consistency (Idⱼ [A] [A]₁ [A]₂) (IdUℕₙ neT) = noNe consistency [A]₂ neT
noNe consistency (Idⱼ [A] [A]₁ [A]₂) (IdUΠₙ neT) = noNe consistency [A]₂ neT
noNe consistency (castⱼ [A] [A]₁ [A]₂ [A]₃) (castₙ neT) = noNe consistency [A] neT
noNe consistency (castⱼ [A] [A]₁ [A]₂ [A]₃) (castℕₙ neT) = noNe consistency [A]₁ neT
noNe consistency (castⱼ [A] [A]₁ [A]₂ [A]₃) (castΠₙ neT) = noNe consistency [A]₁ neT
noNe consistency (castⱼ [A] [A]₁ [A]₂ [A]₃) (castℕℕₙ neT) = noNe consistency [A]₃ neT
noNe consistency (conv ⊢t x) (var n) = noNe consistency ⊢t (var n)
noNe consistency (conv ⊢t x) (∘ₙ neT) = noNe consistency ⊢t (∘ₙ neT)
noNe consistency (conv ⊢t x) (natrecₙ neT) = noNe consistency ⊢t (natrecₙ neT)
noNe consistency (conv ⊢t x) (Idₙ neT) = noNe consistency ⊢t (Idₙ neT)
noNe consistency (conv ⊢t x) (Idℕₙ neT) = noNe consistency ⊢t (Idℕₙ neT)
noNe consistency (conv ⊢t x) (Idℕ0ₙ neT) = noNe consistency ⊢t (Idℕ0ₙ neT)
noNe consistency (conv ⊢t x) (IdℕSₙ neT) = noNe consistency ⊢t (IdℕSₙ neT)
noNe consistency (conv ⊢t x) (IdUₙ neT) = noNe consistency ⊢t (IdUₙ neT)
noNe consistency (conv ⊢t x) (IdUℕₙ neT) = noNe consistency ⊢t (IdUℕₙ neT)
noNe consistency (conv ⊢t x) (IdUΠₙ neT) = noNe consistency ⊢t (IdUΠₙ neT)
noNe consistency (conv ⊢t x) (castₙ neT) = noNe consistency ⊢t (castₙ neT)
noNe consistency (conv ⊢t x) (castℕₙ neT) = noNe consistency ⊢t (castℕₙ neT)
noNe consistency (conv ⊢t x) (castΠₙ neT) = noNe consistency ⊢t (castΠₙ neT)
noNe consistency (conv ⊢t x) (castℕℕₙ neT) = noNe consistency ⊢t (castℕℕₙ neT)
noNe consistency (conv ⊢t x) castℕΠₙ = noNe consistency ⊢t castℕΠₙ
noNe consistency (conv ⊢t x) castΠℕₙ = noNe consistency ⊢t castΠℕₙ
noNe consistency (conv ⊢t x) castΠΠ%!ₙ = noNe consistency ⊢t castΠΠ%!ₙ
noNe consistency (conv ⊢t x) castΠΠ!%ₙ = noNe consistency ⊢t castΠΠ!%ₙ
noNe consistency (conv ⊢t x) Emptyrecₙ = noNe consistency ⊢t Emptyrecₙ

-- Helper function for canonicity for reducible natural properties
canonicity″ : ∀ {t}
              → consistency
              → Natural-prop ε t
              → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ ^ [ ! , ι ⁰ ]
canonicity″ consistency (sucᵣ (ℕₜ n₁ d n≡n prop)) =
  let a , b = canonicity″ consistency prop
  in  1+ a , suc-cong (trans (subset*Term (redₜ d)) b)
canonicity″ consistency zeroᵣ = 0 , refl (zeroⱼ ε)
canonicity″ consistency (ne (neNfₜ neK ⊢k k≡k)) = ⊥-elim (noNe consistency ⊢k neK)

-- Helper function for canonicity for specific reducible natural numbers
canonicity′ : ∀ {t l}
             → consistency
             → ([ℕ] : ε ⊩⟨ l ⟩ℕ ℕ)
             → ε ⊩⟨ l ⟩ t ∷ ℕ ^ [ ! , ι ⁰ ] / ℕ-intr [ℕ]
             → ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ ^ [ ! , ι ⁰ ]
canonicity′ consistency (noemb [ℕ]) (ℕₜ n d n≡n prop) = let a , b = canonicity″ consistency prop
                                          in  a , trans (subset*Term (redₜ d)) b
canonicity′ consistency (emb emb< [ℕ]) [t] = canonicity′ consistency [ℕ] [t]
canonicity′ consistency (emb ∞< [ℕ]) [t] = canonicity′ consistency [ℕ] [t]

-- Canonicity of natural numbers
canonicity : ∀ {t} →
             consistency →
             ε ⊢ t ∷ ℕ ^ [ ! , ι ⁰ ] →
             ∃ λ k → ε ⊢ t ≡ sucᵏ k ∷ ℕ ^ [ ! , ι ⁰ ]
canonicity consistency ⊢t with reducibleTerm ⊢t
canonicity consistency ⊢t | [ℕ] , [t] =
  canonicity′ consistency (ℕ-elim [ℕ]) (irrelevanceTerm [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [t])

