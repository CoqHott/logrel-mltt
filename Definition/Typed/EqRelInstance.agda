{-# OPTIONS --safe #-}

module Definition.Typed.EqRelInstance where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.Typed.Reduction
open import Definition.Typed.EqualityRelation

open import Tools.Function

Urefl   : ∀ {r l Γ} → ⊢ Γ → Γ ⊢ (Univ r l) ≡ (Univ r l) ^ [ ! , next l ]
Urefl {l = ⁰} ⊢Γ = refl (univ (univ 0<1 ⊢Γ))
Urefl {l = ¹} ⊢Γ = refl (Uⱼ ⊢Γ)

instance eqRelInstance : EqRelSet
eqRelInstance = eqRel _⊢_≡_^_ _⊢_≡_∷_^_ _⊢_≡_∷_^_
                      idᶠ idᶠ idᶠ univ un-univ≡
                      sym genSym genSym trans genTrans genTrans
                      conv conv wkEq wkEqTerm wkEqTerm
                      reduction reductionₜ
                      Urefl (refl ∘ᶠ univ 0<1) (refl ∘ᶠ ℕⱼ) (refl ∘ᶠ Emptyⱼ)
                      Π-cong ∃-cong (refl ∘ᶠ zeroⱼ) suc-cong
                      (λ lF lG x x₁ x₂ x₃ x₄ x₅ → η-eq lF lG x x₁ x₂ x₅)
                      genVar app-cong natrec-cong Emptyrec-cong
                      Id-cong
                      (λ ⊢Γ → Id-cong (refl (ℕⱼ ⊢Γ)))
                      (λ ⊢Γ → Id-cong (refl (ℕⱼ ⊢Γ)) (refl (zeroⱼ ⊢Γ)))
                      (λ ⊢Γ t → Id-cong (refl (ℕⱼ ⊢Γ)) (suc-cong t))
                      (λ ⊢Γ → Id-cong (refl (univ 0<1 ⊢Γ)))
                      (λ ⊢Γ → Id-cong (refl (univ 0<1 ⊢Γ)) (refl (ℕⱼ ⊢Γ)))
                      (λ ⊢A B → Id-cong (refl (univ 0<1 (wfEq (univ ⊢A)))) ⊢A B) 
                      cast-cong (λ A≡A t≡t e e' → cast-cong A≡A (refl (ℕⱼ (wfTerm e))) t≡t e e') cast-cong
                      (λ A t~u ⊢t ⊢e → trans (cast-refl A ⊢e ⊢t) (conv t~u (univ A)))
                      (λ t~u ⊢t ⊢e → trans (cast-refl (refl (ℕⱼ (wfTerm ⊢t))) ⊢e ⊢t) t~u)
                      (λ ⊢Γ → cast-cong (refl (ℕⱼ ⊢Γ)))
                      (λ ⊢Γ → cast-cong (refl (ℕⱼ ⊢Γ)) (refl (ℕⱼ ⊢Γ)))
                      cast-cong
                      (λ ⊢A ⊢P P → cast-cong (refl (ℕⱼ (wf (univ ⊢A)))) P)
                      (λ ⊢A ⊢P P → cast-cong P (refl (ℕⱼ (wf (univ ⊢A)))))
                      (λ ⊢A ⊢P P ⊢A' ⊢P' P' → cast-cong P P')
                      (λ ⊢A ⊢P P ⊢A' ⊢P' P' → cast-cong P P')
                      proof-irrelevance
