{-# OPTIONS --without-K --safe #-}

module Definition.Typed.EqRelInstance where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Reduction
open import Definition.Typed.EqualityRelation

open import Tools.Function


-- Judgmental instance of the equality relation

genSym : ∀ {k l A Γ r} → Γ ⊢ k ≡ l ∷ A ^ r → Γ ⊢ l ≡ k ∷ A ^ r
genSym {r = !} = sym
genSym {r = %} (proof-irrelevance x x₁) = proof-irrelevance x₁ x

genTrans : ∀ {k l m A r Γ} → Γ ⊢ k ≡ l ∷ A ^ r → Γ ⊢ l ≡ m ∷ A ^ r → Γ ⊢ k ≡ m ∷ A ^ r
genTrans {r = !} = trans
genTrans {r = %} (proof-irrelevance x y) (proof-irrelevance x' z) = proof-irrelevance x z

genVar : ∀ {x A Γ r} → Γ ⊢ var x ∷ A ^ r → Γ ⊢ var x ≡ var x ∷ A ^ r
genVar {r = !} = refl
genVar {r = %} d = proof-irrelevance d d

instance eqRelInstance : EqRelSet
eqRelInstance = eqRel _⊢_≡_^_ _⊢_≡_∷_^_ _⊢_≡_∷_^_
                      idᶠ idᶠ idᶠ univ
                      sym genSym genSym trans genTrans genTrans
                      conv conv wkEq wkEqTerm wkEqTerm
                      reduction reductionₜ
                      (refl ∘ᶠ Uⱼ) (refl ∘ᶠ ℕⱼ) (refl ∘ᶠ ℕⱼ)
                      (refl ∘ᶠ Emptyⱼ) (refl ∘ᶠ Emptyⱼ)
                      Π-cong Π-cong (refl ∘ᶠ zeroⱼ) suc-cong
                      (λ x x₁ x₂ x₃ x₄ x₅ → η-eq x x₁ x₂ x₅)
                      genVar app-cong natrec-cong Emptyrec-cong
                      proof-irrelevance
