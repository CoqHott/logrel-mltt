{-# OPTIONS --without-K  #-}

module Definition.Typed.EqRelInstance where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.Typed.Reduction
open import Definition.Typed.EqualityRelation

open import Tools.Function
import Tools.PropositionalEquality as PE

cstr-cong-univ : {a a' : Term} {k : constructors} {Γ : Con Term} {s : 𝕊}
               → cstr-cod k PE.≡ Univ s
               → Γ ⊢ a ≡ a' ∷ wkAll Γ (cstr-dom k) ⦂ cstr-dom-sort k
               → Γ ⊢ cstr k a ≡ cstr k a' ⦂ s
cstr-cong-univ {a} {a'} {k} {Γ} kcodU a≡a =
  univ (PE.subst₂ (λ x s → Γ ⊢ cstr k a ≡ cstr k a' ∷ x ⦂ s)
                  (cstr-codU-substS kcodU)
                  (cstr-cod-Univ-sort kcodU)
                  (cstr-cong a≡a))

-- Judgmental instance of the equality relation

instance eqRelInstance : EqRelSet
eqRelInstance = eqRel _⊢_≡_⦂_ _⊢_≡_∷_⦂_ _⊢_≡_∷_⦂_
                      idᶠ idᶠ idᶠ univ
                      sym sym sym trans trans trans
                      conv conv wkEq wkEqTerm wkEqTerm
                      reduction reductionₜ
                      (refl ∘ᶠ Uⱼ) (refl ∘ᶠ ℕⱼ) (refl ∘ᶠ ℕⱼ)
                      (refl ∘ᶠ Emptyⱼ) (refl ∘ᶠ Emptyⱼ)
                      Π-cong Π-cong Box-cong Box-cong
                      (refl ∘ᶠ zeroⱼ) suc-cong
                      (λ x x₁ x₂ x₃ x₄ x₅ → η-eq x x₁ x₂ x₅)
                      box-cong  cstr-cong-univ  cstr-cong
                      refl app-cong natrec-cong Emptyrec-cong
                      Boxrec-cong dstr-cong
