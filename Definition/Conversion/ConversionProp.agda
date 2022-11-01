{-# OPTIONS --safe #-}

module Definition.Conversion.ConversionProp where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.RedSteps
open import Definition.Typed.Properties
open import Definition.Conversion
open import Definition.Conversion.Stability
open import Definition.Conversion.StabilityProp
open import Definition.Conversion.Conversion
open import Definition.Conversion.ConvSize
open import Definition.Conversion.Soundness
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.Equality
open import Definition.Typed.Consequences.Reduction

open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Nat as Nat

sizeSubst-gen :  ∀ {A a b}
              → (P : A → Set)
              → (size : ∀ {a} → P a → Nat)
              → (t : P a)
              → (e : a PE.≡ b)
              → size (PE.subst P e t) PE.≡ size t
sizeSubst-gen _ _ _ PE.refl = PE.refl              

mutual

  -- Conversion of algorithmic equality.
  convConv↑TermSize : ∀ {t u A B Γ Δ l}
                → (Γ≡Δ : ⊢ Γ ≡ Δ)
                → (A≡B : Γ ⊢ A ≡ B ^ [ ! , l ])
                → (t~u : Γ ⊢ t [conv↑] u ∷ A ^ l)
                → sizeConv↑Term (convConv↑Term Γ≡Δ A≡B t~u) PE.≡ sizeConv↑Term t~u
  convConv↑TermSize Γ≡Δ A≡B ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) =
    let ⊢B , _ = syntacticEqTerm (soundnessConv↓Term t<>u)
        eq = convConv↓TermSize Γ≡Δ _ _ t<>u
    in PE.cong 1+ eq

  convConv↓TermSize : ∀ {t u A B Γ Δ l}
                → (Γ≡Δ : ⊢ Γ ≡ Δ)
                → (A≡B : Γ ⊢ A ≡ B ^ [ ! , l ])
                → (whnfB : Whnf B)
                → (t~u : Γ ⊢ t [conv↓] u ∷ A ^ l)
                → sizeConv↓Term (convConv↓Term Γ≡Δ A≡B whnfB t~u) PE.≡ sizeConv↓Term t~u
  convConv↓TermSize Γ≡Δ A≡B whnfB (U-refl x x₁) rewrite U≡A-whnf A≡B whnfB = PE.refl
  convConv↓TermSize Γ≡Δ A≡B whnfB (ne x) rewrite U≡A-whnf A≡B whnfB = PE.cong 1+ (stabilitySize~↓! Γ≡Δ x)
  convConv↓TermSize Γ≡Δ A≡B whnfB (ℕ-refl x) rewrite U≡A-whnf A≡B whnfB = PE.refl
  convConv↓TermSize Γ≡Δ A≡B whnfB (Empty-refl x) rewrite U≡A-whnf A≡B whnfB = PE.refl
  convConv↓TermSize Γ≡Δ A≡B whnfB (Π-cong lΠ rF lF lG l< l<' x x₁ x₂) rewrite U≡A-whnf A≡B whnfB = PE.cong₂ (λ n m → 1 + (n + m))
    (stabilitySizeConv↑Term Γ≡Δ x₁)
    (stabilitySizeConv↑Term (Γ≡Δ ∙ refl x) x₂)
  convConv↓TermSize Γ≡Δ A≡B whnfB (∃-cong x x₁ x₂) rewrite U≡A-whnf A≡B whnfB = PE.cong₂ (λ n m → 1 + (n + m))
    (stabilitySizeConv↑Term Γ≡Δ x₁)
    (stabilitySizeConv↑Term (Γ≡Δ ∙ refl x) x₂)
  convConv↓TermSize Γ≡Δ A≡B whnfB (ℕ-ins x) rewrite ℕ≡A A≡B whnfB =
    PE.cong 1+ (stabilitySize~↓! Γ≡Δ x)
  convConv↓TermSize Γ≡Δ A≡B whnfB (ne-ins t u x x₁) with ne≡A x A≡B whnfB
  convConv↓TermSize Γ≡Δ A≡B whnfB (ne-ins t u x x₁) | B , neB , PE.refl =
    PE.cong 1+ (stabilitySize~↓! Γ≡Δ x₁)
  convConv↓TermSize Γ≡Δ A≡B whnfB (zero-refl x) rewrite ℕ≡A A≡B whnfB = PE.refl
  convConv↓TermSize Γ≡Δ A≡B whnfB (suc-cong x) rewrite ℕ≡A A≡B whnfB =
    PE.cong 1+ (stabilitySizeConv↑Term Γ≡Δ x)
  convConv↓TermSize Γ≡Δ A≡B whnfB (η-eq l< l<' x x₁ x₂ y y₁ x₃) =
    let F′ , G′ , eqΠ = Π≡A A≡B whnfB
        A≡B' = PE.subst (λ X → _ ⊢ _ ≡ X ^ _) eqΠ A≡B
        F≡F′ , rF≡rF′ , _ , _ , G≡G′ = injectivity A≡B'
    in PE.trans (sizeSubst-gen (λ X → _ ⊢ _ [conv↓] _ ∷ X ^ _) sizeConv↓Term _ (PE.sym (proj₂ (proj₂ (Π≡A A≡B whnfB)))))
                (PE.cong 1+ (convConv↑TermSize (Γ≡Δ ∙ F≡F′) G≡G′ x₃)) 
