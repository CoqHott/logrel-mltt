{-# OPTIONS --without-K --safe #-}

module Definition.Typed.EqRelInstance where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Reduction
open import Definition.Typed.EqualityRelation

open import Tools.Function


-- Judgmental instance of the equality relation

private
  proof-irrelevance′ : ∀ {a b A Γ} → Γ ⊢ a ∷ A ^ % → Γ ⊢ b ∷ A ^ %
                     → Γ ⊢ a ≡ a ∷ A ^ %
                     → Γ ⊢ b ≡ b ∷ A ^ %
                     → Γ ⊢ a ≡ b ∷ A ^ %
  proof-irrelevance′ ⊢a ⊢b _ _ = proof-irrelevance ⊢a ⊢b

instance eqRelInstance : EqRelSet
eqRelInstance = eqRel _⊢_≡_^_ _⊢_≡_∷_^_ _⊢_≡_∷_^_
                      idᶠ idᶠ idᶠ univ
                      sym sym sym trans trans trans
                      conv conv wkEq wkEqTerm wkEqTerm
                      reduction reductionₜ
                      (refl ∘ᶠ Uⱼ) (refl ∘ᶠ ℕⱼ) (refl ∘ᶠ ℕⱼ)
                      (refl ∘ᶠ Emptyⱼ) (refl ∘ᶠ Emptyⱼ)
                      Π-cong Π-cong
                      Box-cong Box-cong
                      (refl ∘ᶠ zeroⱼ) suc-cong
                      (λ x x₁ x₂ x₃ x₄ x₅ → η-eq x x₁ x₂ x₅)
                      refl app-cong natrec-cong Emptyrec-cong
                      box-cong Boxrec-cong
                      proof-irrelevance′
