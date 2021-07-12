{-# OPTIONS --safe #-}

module Definition.Typed.Consequences.Reduction where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.EqRelInstance
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Fundamental.Reducibility
import Tools.PropositionalEquality as PE

open import Tools.Product


-- Helper function where all reducible types can be reduced to WHNF.
whNorm′ : ∀ {A rA Γ l} ([A] : Γ ⊩⟨ l ⟩ A ^ rA)
                → ∃ λ B → Whnf B × Γ ⊢ A :⇒*: B ^ rA
whNorm′ (Uᵣ′ _ _ r l _ e d) = Univ r l , Uₙ , PE.subst (λ ll → _ ⊢ _ :⇒*: Univ r l ^ [ ! , ll ]) e d 
whNorm′ (ℕᵣ D) = ℕ , ℕₙ , D
whNorm′ (Emptyᵣ D) = Empty , Emptyₙ , D
whNorm′ (ne′ K D neK K≡K) = K , ne neK , D
whNorm′ (Πᵣ′ rF lF lG lF≤ lG≤ F G D ⊢F ⊢G A≡A [F] [G] G-ext) = Π F ^ rF ° lF ▹ G ° lG , Πₙ , D
whNorm′ (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) = ∃ F ▹ G , ∃ₙ , D
whNorm′ (emb emb< [A]) = whNorm′ [A]
whNorm′ (emb ∞< [A]) = whNorm′ [A]

-- Well-formed types can all be reduced to WHNF.
whNorm : ∀ {A rA Γ} → Γ ⊢ A ^ rA → ∃ λ B → Whnf B × Γ ⊢ A :⇒*: B ^ rA
whNorm A = whNorm′ (reducible A)


-- Helper function where reducible all terms can be reduced to WHNF.
whNormTerm′ : ∀ {a A Γ l lA} ([A] : Γ ⊩⟨ l ⟩ A ^ [ ! , lA ]) → Γ ⊩⟨ l ⟩ a ∷ A ^ [ ! , lA ] / [A]
                → ∃ λ b → Whnf b × Γ ⊢ a :⇒*: b ∷ A ^ lA 
whNormTerm′ (Uᵣ′ _ _ r l _ e dU) (Uₜ A d typeA A≡A [t]) = A , typeWhnf typeA ,
  conv:⇒*: (PE.subst (λ ll → _ ⊢ _ :⇒*: _ ∷ _ ^ ll) e d)
    (sym (subset* (red (PE.subst (λ ll → _ ⊢ _ :⇒*: Univ r l ^ [ ! , ll ]) e dU)))) 
whNormTerm′ (ℕᵣ x) (ℕₜ n d n≡n prop) =
  let natN = natural prop
  in  n , naturalWhnf natN , convRed:*: d (sym (subset* (red x)))
whNormTerm′ (ne (ne K D neK K≡K)) (neₜ k d (neNfₜ neK₁ ⊢k k≡k)) =
  k , ne neK₁ , convRed:*: d (sym (subset* (red D)))
whNormTerm′ (Πᵣ′ rF lF lG lF≤ lG≤  F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Πₜ f d funcF f≡f [f] [f]₁) =
  f , functionWhnf funcF , convRed:*: d (sym (subset* (red D)))
whNormTerm′ (emb emb< [A]) [a] = whNormTerm′ [A] [a]
whNormTerm′ (emb ∞< [A]) [a] = whNormTerm′ [A] [a]


-- Well-formed terms can all be reduced to WHNF.
whNormTerm : ∀ {a A Γ lA} → Γ ⊢ a ∷ A ^ [ ! , lA ] → ∃ λ b → Whnf b × Γ ⊢ a :⇒*: b ∷ A ^ lA 
whNormTerm {a} {A} ⊢a =
  let [A] , [a] = reducibleTerm ⊢a
  in  whNormTerm′ [A] [a]

