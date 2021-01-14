{-# OPTIONS --without-K --safe #-}

module Definition.Typed.Consequences.NeTypeEq where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.Substitution

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Helper function for the same variable instance of a context have equal types.
varTypeEq′ : ∀ {n R rR T rT Γ} → n ∷ R ^ rR ∈ Γ → n ∷ T ^ rT ∈ Γ → R PE.≡ T × rR PE.≡ rT
varTypeEq′ here here = PE.refl , PE.refl
varTypeEq′ (there n∷R) (there n∷T) with varTypeEq′ n∷R n∷T
... | PE.refl , PE.refl = PE.refl , PE.refl

-- The same variable instance of a context have equal types.
varTypeEq : ∀ {x A B rA rB Γ} → Γ ⊢ A ^ rA → Γ ⊢ B ^ rB
          → x ∷ A ^ rA ∈ Γ
          → x ∷ B ^ rB ∈ Γ
          → Γ ⊢ A ≡ B ^ rA × rA PE.≡ rB
varTypeEq A B x∷A x∷B with varTypeEq′ x∷A x∷B
... | PE.refl , PE.refl = refl A , PE.refl

-- The same neutral term have equal types.
-- to use this with different relevances rA rB we need unicity of relevance for types
neTypeEq : ∀ {t A B rA Γ} → Neutral t → Γ ⊢ t ∷ A ^ rA → Γ ⊢ t ∷ B ^ rA → Γ ⊢ A ≡ B ^ rA
neTypeEq (var x) (var x₁ x₂) (var x₃ x₄) =
  proj₁ (varTypeEq (syntacticTerm (var x₃ x₂)) (syntacticTerm (var x₃ x₄)) x₂ x₄)
neTypeEq (∘ₙ neT) (t∷A ∘ⱼ t∷A₁) (t∷B ∘ⱼ t∷B₁) with neTypeEq neT t∷A t∷B
... | q = let _ , _ , w = injectivity q
          in  substTypeEq w (genRefl t∷A₁)
neTypeEq (natrecₙ neT) (natrecⱼ x t∷A t∷A₁ t∷A₂) (natrecⱼ x₁ t∷B t∷B₁ t∷B₂) =
  refl (substType x₁ t∷B₂)
neTypeEq Emptyrecₙ (Emptyrecⱼ x t∷A) (Emptyrecⱼ x₁ t∷B) =
  refl x₁
neTypeEq x (conv t∷A x₁) t∷B = let q = neTypeEq x t∷A t∷B
                               in  trans (sym x₁) q
neTypeEq x t∷A (conv t∷B x₃) = let q = neTypeEq x t∷A t∷B
                               in  trans q x₃

transport : ∀ {l} {A : Set l} (P : A → Set l) {x : A} (t : P x) {y : A} (e : x PE.≡ y) → P y
transport P t PE.refl = t

natTypeEq : ∀ {A rA Γ} → Γ ⊢ ℕ ∷ A ^ rA → rA PE.≡ ! × Γ ⊢ A ≡ U ^ !
natTypeEq (ℕⱼ x) = PE.refl , refl (Uⱼ x)
natTypeEq (conv X x) = let eqrA , eqAU = natTypeEq X in eqrA , trans (sym (transport (λ r → _ ⊢ _ ≡ _ ^ r) x eqrA)) eqAU 

emptyTypeEq : ∀ {A rA Γ} → Γ ⊢ Empty ∷ A ^ rA → rA PE.≡ ! × Γ ⊢ A ≡ SProp ^ !
emptyTypeEq (Emptyⱼ x) = PE.refl , refl (Uⱼ x)
emptyTypeEq (conv X x) = let eqrA , eqAU = emptyTypeEq X in eqrA , trans (sym (transport (λ r → _ ⊢ _ ≡ _ ^ r) x eqrA)) eqAU 
