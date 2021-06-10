{-# OPTIONS --without-K  #-}

module Definition.Conversion.Conversion where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.RedSteps
open import Definition.Typed.Properties
open import Definition.Conversion
open import Definition.Conversion.Stability
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.Equality
open import Definition.Typed.Consequences.Reduction

open import Tools.Product
import Tools.PropositionalEquality as PE


mutual
  -- Conversion of algorithmic equality.
  convConv↑Term : ∀ {t u A B s Γ Δ}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B ⦂ s
                → Γ ⊢ t [conv↑] u ∷ A ⦂ s
                → Δ ⊢ t [conv↑] u ∷ B ⦂ s
  convConv↑Term Γ≡Δ A≡B ([↑]ₜ B₁ t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) =
    let _ , ⊢B = syntacticEq A≡B
        B′ , whnfB′ , D′ = whNorm ⊢B
        B₁≡B′ = trans (sym (subset* D)) (trans A≡B (subset* (red D′)))
    in  [↑]ₜ B′ t′ u′ (stabilityRed* Γ≡Δ (red D′))
             (stabilityRed*Term Γ≡Δ (conv* d B₁≡B′))
             (stabilityRed*Term Γ≡Δ (conv* d′ B₁≡B′)) whnfB′ whnft′ whnfu′
             (convConv↓Term Γ≡Δ B₁≡B′ whnfB′ t<>u)

  -- Conversion of algorithmic equality with terms and types in WHNF.
  convConv↓Term : ∀ {t u A B s Γ Δ}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B ⦂ s
                → Whnf B
                → Γ ⊢ t [conv↓] u ∷ A ⦂ s
                → Δ ⊢ t [conv↓] u ∷ B ⦂ s
  convConv↓Term Γ≡Δ A≡B whnfB (ℕ-ins x) rewrite ℕ≡A A≡B whnfB =
    ℕ-ins (stability~↓𝕥y Γ≡Δ x)
  convConv↓Term Γ≡Δ A≡B whnfB (Empty-ins x) rewrite Empty≡A A≡B whnfB =
    Empty-ins (stability~↓𝕥y Γ≡Δ x)
  convConv↓Term Γ≡Δ A≡B whnfB (ne-ins t u x x₁) with ne≡A x A≡B whnfB
  convConv↓Term Γ≡Δ A≡B whnfB (ne-ins t u x x₁) | B , neB , PE.refl =
    ne-ins (stabilityTerm Γ≡Δ (conv t A≡B)) (stabilityTerm Γ≡Δ (conv u A≡B))
           neB (stability~↓ Γ≡Δ x₁)
  convConv↓Term Γ≡Δ A≡B whnfB (univ x x₁ x₂) rewrite U≡A A≡B =
    univ (stabilityTerm Γ≡Δ x) (stabilityTerm Γ≡Δ x₁) (stabilityConv↓ Γ≡Δ x₂)
  convConv↓Term Γ≡Δ A≡B whnfB (zero-refl x) rewrite ℕ≡A A≡B whnfB =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  zero-refl ⊢Δ
  convConv↓Term Γ≡Δ A≡B whnfB (suc-cong x) rewrite ℕ≡A A≡B whnfB =
    suc-cong (stabilityConv↑Term Γ≡Δ x)
  convConv↓Term Γ≡Δ A≡B whnfB (η-eq x x₁ x₂ y y₁ x₃) with Π≡A A≡B whnfB
  convConv↓Term Γ≡Δ A≡B whnfB (η-eq x x₁ x₂ y y₁ x₃) | F′ , G′ , PE.refl =
    let F≡F′ , sF≡sF′ , G≡G′ = injectivity A≡B
        ⊢F , ⊢F′ = syntacticEq F≡F′
    in  η-eq (stability Γ≡Δ ⊢F′) (stabilityTerm Γ≡Δ (conv x₁ A≡B))
             (stabilityTerm Γ≡Δ (conv x₂ A≡B)) y y₁
             (convConv↑Term (Γ≡Δ ∙ F≡F′) G≡G′ x₃)

-- Conversion of algorithmic equality with the same context.
convConvTerm : ∀ {t u A B s Γ}
              → Γ ⊢ t [conv↑] u ∷ A ⦂ s
              → Γ ⊢ A ≡ B ⦂ s
              → Γ ⊢ t [conv↑] u ∷ B ⦂ s
convConvTerm t<>u A≡B = convConv↑Term (reflConEq (wfEq A≡B)) A≡B t<>u
