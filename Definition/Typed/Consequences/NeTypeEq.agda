{-# OPTIONS --without-K  #-}

module Definition.Typed.Consequences.NeTypeEq where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.Substitution

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Helper function for the same variable instance of a context have equal types.
vasTypeEq′ : ∀ {n R sR T sT Γ} → n ∷ R ⦂ sR ∈ Γ → n ∷ T ⦂ sT ∈ Γ → R PE.≡ T × sR PE.≡ sT
vasTypeEq′ here here = PE.refl , PE.refl
vasTypeEq′ (there n∷R) (there n∷T) with vasTypeEq′ n∷R n∷T
... | PE.refl , PE.refl = PE.refl , PE.refl

-- The same variable instance of a context have equal types.
vasTypeEq : ∀ {x A B sA sB Γ} → Γ ⊢ A ⦂ sA → Γ ⊢ B ⦂ sB
          → x ∷ A ⦂ sA ∈ Γ
          → x ∷ B ⦂ sB ∈ Γ
          → Γ ⊢ A ≡ B ⦂ sA × sA PE.≡ sB
vasTypeEq A B x∷A x∷B with vasTypeEq′ x∷A x∷B
... | PE.refl , PE.refl = refl A , PE.refl

-- The same neutral term have equal types.
-- to use this with different relevances sA sB we need unicity of relevance for types
neTypeEq : ∀ {t A B sA Γ} → Neutral t → Γ ⊢ t ∷ A ⦂ sA → Γ ⊢ t ∷ B ⦂ sA → Γ ⊢ A ≡ B ⦂ sA
neTypeEq (var x) (var x₁ x₂) (var x₃ x₄) =
  proj₁ (vasTypeEq (syntacticTerm (var x₃ x₂)) (syntacticTerm (var x₃ x₄)) x₂ x₄)
neTypeEq (∘ₙ neT) (t∷A ∘ⱼ t∷A₁) (t∷B ∘ⱼ t∷B₁) with neTypeEq neT t∷A t∷B
... | q = let _ , _ , w = injectivity q
          in  substTypeEq w (refl t∷A₁)
neTypeEq (natrecₙ neT) (natrecⱼ x t∷A t∷A₁ t∷A₂) (natrecⱼ x₁ t∷B t∷B₁ t∷B₂) =
  refl (substType x₁ t∷B₂)
neTypeEq (Emptyrecₙ neT) (Emptyrecⱼ x t∷A) (Emptyrecⱼ x₁ t∷B) =
  refl x₁
neTypeEq x (conv t∷A x₁) t∷B = let q = neTypeEq x t∷A t∷B
                               in  trans (sym x₁) q
neTypeEq x t∷A (conv t∷B x₃) = let q = neTypeEq x t∷A t∷B
                               in  trans q x₃
