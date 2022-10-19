{-# OPTIONS --safe #-}

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
  convConv↑Term : ∀ {t u A B Γ Δ l}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B ^ [ ! , l ]
                → Γ ⊢ t [conv↑] u ∷ A ^ l
                → Δ ⊢ t [conv↑] u ∷ B ^ l
  convConv↑Term Γ≡Δ A≡B ([↑]ₜ B₁ t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) =
    let _ , ⊢B = syntacticEq A≡B
        B′ , whnfB′ , D′ = whNorm ⊢B
        B₁≡B′ = trans (sym (subset* D)) (trans A≡B (subset* (red D′)))
    in  [↑]ₜ B′ t′ u′ (stabilityRed* Γ≡Δ (red D′))
             (stabilityRed*Term Γ≡Δ (conv* d B₁≡B′))
             (stabilityRed*Term Γ≡Δ (conv* d′ B₁≡B′)) whnfB′ whnft′ whnfu′
             (convConv↓Term Γ≡Δ B₁≡B′ whnfB′ t<>u)

  -- Conversion of algorithmic equality with terms and types in WHNF.
  convConv↓Term : ∀ {t u A B Γ Δ l}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B ^ [ ! , l ]
                → Whnf B
                → Γ ⊢ t [conv↓] u ∷ A ^ l
                → Δ ⊢ t [conv↓] u ∷ B ^ l
  convConv↓Term Γ≡Δ A≡B whnfB (ℕ-ins x) =
    let eqN = ℕ≡A A≡B whnfB 
    in PE.subst (λ x → _ ⊢ _ [conv↓] _ ∷ x ^ _) (PE.sym eqN) 
                (ℕ-ins (stability~↓! Γ≡Δ x))
  convConv↓Term Γ≡Δ A≡B whnfB (ne x) =
    let eqU = U≡A-whnf A≡B whnfB
    in PE.subst (λ x → _ ⊢ _ [conv↓] _ ∷ x ^ _) (PE.sym eqU) (ne (stability~↓! Γ≡Δ x))
  convConv↓Term Γ≡Δ A≡B whnfB (ne-ins t u x x₁) with ne≡A x A≡B whnfB
  convConv↓Term Γ≡Δ A≡B whnfB (ne-ins t u x x₁) | B , neB , PE.refl =
    ne-ins (stabilityTerm Γ≡Δ (conv t A≡B)) (stabilityTerm Γ≡Δ (conv u A≡B))
           neB (stability~↓! Γ≡Δ x₁)
  convConv↓Term Γ≡Δ A≡B whnfB (zero-refl x) =
    let eqN = ℕ≡A A≡B whnfB 
        _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in PE.subst (λ x → _ ⊢ _ [conv↓] _ ∷ x ^ _) (PE.sym eqN) 
       (zero-refl ⊢Δ)
  convConv↓Term Γ≡Δ A≡B whnfB (suc-cong x) =
    let eqN = ℕ≡A A≡B whnfB 
    in PE.subst (λ x → _ ⊢ _ [conv↓] _ ∷ x ^ _) (PE.sym eqN) 
                (suc-cong (stabilityConv↑Term Γ≡Δ x))
  convConv↓Term Γ≡Δ A≡B whnfB (η-eq l< l<' x x₁ x₂ y y₁ x₃) with Π≡A A≡B whnfB
  convConv↓Term Γ≡Δ A≡B whnfB (η-eq l< l<' x x₁ x₂ y y₁ x₃) | F′ , G′ , PE.refl =
    let F≡F′ , rF≡rF′ , _ , _ , G≡G′ = injectivity A≡B
        ⊢F , ⊢F′ = syntacticEq F≡F′
    in  η-eq l< l<'
             (stability Γ≡Δ ⊢F′) (stabilityTerm Γ≡Δ (conv x₁ A≡B))
             (stabilityTerm Γ≡Δ (conv x₂ A≡B)) y y₁
             (convConv↑Term (Γ≡Δ ∙ F≡F′) G≡G′ x₃)
  convConv↓Term Γ≡Δ A≡B whnfB (U-refl x x₁) =
    let eqU = U≡A-whnf A≡B whnfB
        _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in PE.subst (λ x → _ ⊢ _ [conv↓] _ ∷ x ^ ∞) (PE.sym eqU) (U-refl  x ⊢Δ)
  convConv↓Term Γ≡Δ A≡B whnfB (ℕ-refl x) =
    let eqU = U≡A-whnf A≡B whnfB
        _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in PE.subst (λ x → _ ⊢ _ [conv↓] _ ∷ x ^ _) (PE.sym eqU) (ℕ-refl ⊢Δ)
  convConv↓Term Γ≡Δ A≡B whnfB (Empty-refl _) =
    let eqU = U≡A-whnf A≡B whnfB
        _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in PE.subst (λ x → _ ⊢ _ [conv↓] _ ∷ x ^ _) (PE.sym eqU) (Empty-refl ⊢Δ)
  convConv↓Term Γ≡Δ A≡B whnfB (Π-cong lΠ rF lF lG l< l<' x x₁ x₂) =
    let eqU = U≡A-whnf A≡B whnfB
    in PE.subst (λ x → _ ⊢ _ [conv↓] _ ∷ x ^ _) (PE.sym eqU)
                (Π-cong lΠ rF lF lG l< l<' (stability Γ≡Δ x) (stabilityConv↑Term Γ≡Δ x₁) (stabilityConv↑Term (Γ≡Δ ∙ refl x) x₂))
  convConv↓Term Γ≡Δ A≡B whnfB (∃-cong x x₁ x₂) =
    let eqU = U≡A-whnf A≡B whnfB
    in PE.subst (λ x → _ ⊢ _ [conv↓] _ ∷ x ^ _) (PE.sym eqU)
                (∃-cong (stability Γ≡Δ x) (stabilityConv↑Term Γ≡Δ x₁) (stabilityConv↑Term (Γ≡Δ ∙ refl x) x₂))

-- Conversion of algorithmic equality with the same context.
convConvTerm : ∀ {t u A B Γ l}
              → Γ ⊢ t [conv↑] u ∷ A ^ l
              → Γ ⊢ A ≡ B ^ [ ! , l ]
              → Γ ⊢ t [conv↑] u ∷ B ^ l
convConvTerm t<>u A≡B = convConv↑Term (reflConEq (wfEq A≡B)) A≡B t<>u



conv~↑% : ∀ {t u A B Γ l}
              -- → ⊢ Γ ≡ Δ
              → Γ ⊢ t ~ u ↑% A ^ l
              → Γ ⊢ A ≡ B ^ [ % , l ]
              → Γ ⊢ t ~ u ↑% B ^ l
conv~↑% (%~↑ ⊢k ⊢l) e = %~↑ (conv ⊢k e) (conv ⊢l e)
--(stabilityTerm ⊢Γ≡Δ (conv ⊢k e)) (stabilityTerm ⊢Γ≡Δ (conv ⊢l e))

convConvTerm%! : ∀ {t u A B Γ r l}
              → Γ ⊢ t [genconv↑] u ∷ A ^ [ r , l ]
              → Γ ⊢ A ≡ B ^ [ r , l ]
              → Γ ⊢ t [genconv↑] u ∷ B ^ [ r , l ]
convConvTerm%! {r = !} = convConvTerm
convConvTerm%! {r = %} = conv~↑%
