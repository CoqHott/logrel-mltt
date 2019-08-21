{-# OPTIONS --without-K --safe #-}

module Definition.Typed.Consequences.Reduction where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.EqRelInstance
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Fundamental.Reducibility

open import Tools.Product


-- Helper function where all reducible types can be reduced to WHNF.
whNorm′ : ∀ {A rA Γ l} ([A] : Γ ⊩⟨ l ⟩ A ^ rA)
                → ∃ λ B → Whnf B × Γ ⊢ A :⇒*: B ^ rA
whNorm′ (Uᵣ′ _ .⁰ 0<1 ⊢Γ) = Univ _ , Uₙ , idRed:*: (Uⱼ ⊢Γ)
whNorm′ (ℕᵣ D) = ℕ , ℕₙ , D
whNorm′ (Emptyᵣ D) = Empty , Emptyₙ , D
whNorm′ (ne′ K D neK K≡K) = K , ne neK , D
whNorm′ (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) = Π F ^ rF ▹ G , Πₙ , D
whNorm′ (emb 0<1 [A]) = whNorm′ [A]

-- Well-formed types can all be reduced to WHNF.
whNorm : ∀ {A rA Γ} → Γ ⊢ A ^ rA → ∃ λ B → Whnf B × Γ ⊢ A :⇒*: B ^ rA
whNorm A = whNorm′ (reducible A)

-- Helper function where reducible all terms can be reduced to WHNF.
whNormTerm′ : ∀ {a A rA Γ l} ([A] : Γ ⊩⟨ l ⟩ A ^ rA) → Γ ⊩⟨ l ⟩ a ∷ A ^ rA / [A]
                → ∃ λ b → Whnf b × Γ ⊢ a :⇒*: b ∷ A ^ rA
whNormTerm′ (Uᵣ x) (Uₜ A d typeA A≡A [t]) = A , typeWhnf typeA , d
whNormTerm′ (ℕᵣ x) (ℕₜ n d n≡n prop) =
  let natN = natural prop
  in  n , naturalWhnf natN , convRed:*: d (sym (subset* (red x)))
whNormTerm′ (Emptyᵣ x) (Emptyₜ n d n≡n prop) =
  let emptyN = empty prop
  in  n , ne emptyN , convRed:*: d (sym (subset* (red x)))
whNormTerm′ (ne (ne K D neK K≡K)) (neₜ k d (neNfₜ neK₁ ⊢k k≡k)) =
  k , ne neK₁ , convRed:*: d (sym (subset* (red D)))
whNormTerm′ (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Πₜ f d funcF f≡f [f] [f]₁) =
  f , functionWhnf funcF , convRed:*: d (sym (subset* (red D)))
whNormTerm′ (emb 0<1 [A]) [a] = whNormTerm′ [A] [a]

-- Well-formed terms can all be reduced to WHNF.
whNormTerm : ∀ {a A rA Γ} → Γ ⊢ a ∷ A ^ rA → ∃ λ b → Whnf b × Γ ⊢ a :⇒*: b ∷ A ^ rA
whNormTerm {a} {A} ⊢a =
  let [A] , [a] = reducibleTerm ⊢a
  in  whNormTerm′ [A] [a]
