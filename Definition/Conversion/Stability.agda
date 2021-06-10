{-# OPTIONS --without-K  #-}

module Definition.Conversion.Stability where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Conversion
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Equality of contexts.
data ⊢_≡_ : (Γ Δ : Con Term) → Set where
  ε : ⊢ ε ≡ ε
  _∙_ : ∀ {Γ Δ A B s} → ⊢ Γ ≡ Δ → Γ ⊢ A ≡ B ⦂ s → ⊢ Γ ∙ A ⦂ s ≡ Δ ∙ B ⦂ s

mutual
  -- Syntactic validity and conversion substitution of a context equality.
  contextConvSubst : ∀ {Γ Δ} → ⊢ Γ ≡ Δ → ⊢ Γ × ⊢ Δ × Δ ⊢ˢ idSubst ∷ Γ
  contextConvSubst ε = ε , ε , id
  contextConvSubst (_∙_ {Γ} {Δ} {A} {B} Γ≡Δ A≡B) =
    let ⊢Γ , ⊢Δ , [σ] = contextConvSubst Γ≡Δ
        ⊢A , ⊢B = syntacticEq A≡B
        Δ⊢B = stability Γ≡Δ ⊢B
    in  ⊢Γ ∙ ⊢A , ⊢Δ ∙ Δ⊢B
        , (wk1Subst′ ⊢Γ ⊢Δ Δ⊢B [σ]
        , conv (var (⊢Δ ∙ Δ⊢B) here)
               (PE.subst (λ x → _ ⊢ _ ≡ x ⦂ _)
                         (wk1-tailId A)
                         (wkEq (step id) (⊢Δ ∙ Δ⊢B) (stabilityEq Γ≡Δ (sym A≡B)))))

  -- Stability of types under equal contexts.
  stability : ∀ {A sA Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ A ⦂ sA → Δ ⊢ A ⦂ sA
  stability Γ≡Δ A =
    let ⊢Γ , ⊢Δ , σ = contextConvSubst Γ≡Δ
        q = substitution A σ ⊢Δ
    in  PE.subst (λ x → _ ⊢ x ⦂ _) (subst-id _) q

  -- Stability of type equality.
  stabilityEq : ∀ {A B sA Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ A ≡ B ⦂ sA → Δ ⊢ A ≡ B ⦂ sA
  stabilityEq Γ≡Δ A≡B =
    let ⊢Γ , ⊢Δ , σ = contextConvSubst Γ≡Δ
        q = substitutionEq A≡B (substRefl σ) ⊢Δ
    in  PE.subst₂ (λ x y → _ ⊢ x ≡ y ⦂ _) (subst-id _) (subst-id _) q

-- Reflexivity of context equality.
reflConEq : ∀ {Γ} → ⊢ Γ → ⊢ Γ ≡ Γ
reflConEq ε = ε
reflConEq (⊢Γ ∙ ⊢A) = reflConEq ⊢Γ ∙ refl ⊢A

-- Symmetry of context equality.
symConEq : ∀ {Γ Δ} → ⊢ Γ ≡ Δ → ⊢ Δ ≡ Γ
symConEq ε = ε
symConEq (Γ≡Δ ∙ A≡B) = symConEq Γ≡Δ ∙ stabilityEq Γ≡Δ (sym A≡B)

-- Stability of terms.
stabilityTerm : ∀ {t A sA Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ t ∷ A ⦂ sA → Δ ⊢ t ∷ A ⦂ sA
stabilityTerm Γ≡Δ t =
  let ⊢Γ , ⊢Δ , σ = contextConvSubst Γ≡Δ
      q = substitutionTerm t σ ⊢Δ
  in  PE.subst₂ (λ x y → _ ⊢ x ∷ y ⦂ _) (subst-id _) (subst-id _) q

-- Stability of term reduction.
stabilityRedTerm : ∀ {t u A sA Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ t ⇒ u ∷ A ⦂ sA → Δ ⊢ t ⇒ u ∷ A ⦂ sA
stabilityRedTerm Γ≡Δ (conv d x) =
  conv (stabilityRedTerm Γ≡Δ d) (stabilityEq Γ≡Δ x)
stabilityRedTerm Γ≡Δ (app-subst d x) =
  app-subst (stabilityRedTerm Γ≡Δ d) (stabilityTerm Γ≡Δ x)
stabilityRedTerm Γ≡Δ (β-red x x₁ x₂) =
  β-red (stability Γ≡Δ x) (stabilityTerm (Γ≡Δ ∙ refl x) x₁)
        (stabilityTerm Γ≡Δ x₂)
stabilityRedTerm Γ≡Δ (natrec-subst x x₁ x₂ d) =
  let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
  in  natrec-subst (stability (Γ≡Δ ∙ refl (ℕⱼ ⊢Γ)) x) (stabilityTerm Γ≡Δ x₁)
                   (stabilityTerm Γ≡Δ x₂) (stabilityRedTerm Γ≡Δ d)
stabilityRedTerm Γ≡Δ (natrec-zero x x₁ x₂) =
  let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
  in  natrec-zero (stability (Γ≡Δ ∙ refl (ℕⱼ ⊢Γ)) x) (stabilityTerm Γ≡Δ x₁)
                  (stabilityTerm Γ≡Δ x₂)
stabilityRedTerm Γ≡Δ (natrec-suc x x₁ x₂ x₃) =
  let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
  in  natrec-suc (stabilityTerm Γ≡Δ x) (stability (Γ≡Δ ∙ refl (ℕⱼ ⊢Γ)) x₁)
                 (stabilityTerm Γ≡Δ x₂) (stabilityTerm Γ≡Δ x₃)
stabilityRedTerm Γ≡Δ (Emptyrec-subst x d) =
  Emptyrec-subst (stability Γ≡Δ x) (stabilityRedTerm Γ≡Δ d)

-- Stability of type reductions.
stabilityRed : ∀ {A B s Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ A ⇒ B ⦂ s → Δ ⊢ A ⇒ B ⦂ s
stabilityRed Γ≡Δ (univ x) = univ (stabilityRedTerm Γ≡Δ x)

-- Stability of type reduction closures.
stabilityRed* : ∀ {A B s Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ A ⇒* B ⦂ s → Δ ⊢ A ⇒* B ⦂ s
stabilityRed* Γ≡Δ (id x) = id (stability Γ≡Δ x)
stabilityRed* Γ≡Δ (x ⇨ D) = stabilityRed Γ≡Δ x ⇨ stabilityRed* Γ≡Δ D

-- Stability of term reduction closures.
stabilityRed*Term : ∀ {t u A sA Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ t ⇒* u ∷ A ⦂ sA → Δ ⊢ t ⇒* u ∷ A ⦂ sA
stabilityRed*Term Γ≡Δ (id x) = id (stabilityTerm Γ≡Δ x)
stabilityRed*Term Γ≡Δ (x ⇨ d) = stabilityRedTerm Γ≡Δ x ⇨ stabilityRed*Term Γ≡Δ d

mutual
  -- Stability of algorithmic equality of neutrals.
  stability~↑𝕥y : ∀ {k l A Γ Δ}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ k ~ l ↑𝕥y A
              → Δ ⊢ k ~ l ↑𝕥y A
  stability~↑𝕥y Γ≡Δ (var-refl x x≡y) =
    var-refl (stabilityTerm Γ≡Δ x) x≡y
  stability~↑𝕥y Γ≡Δ (app-cong k~l x) =
    app-cong (stability~↓𝕥y Γ≡Δ k~l) (stabilityConv↑Term Γ≡Δ x)
  stability~↑𝕥y Γ≡Δ (natrec-cong x₁ x₂ x₃ k~l) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
    in natrec-cong (stabilityConv↑ (Γ≡Δ ∙ (refl (ℕⱼ ⊢Γ))) x₁)
                   (stabilityConv↑Term Γ≡Δ x₂)
                   (stabilityConv↑Term Γ≡Δ x₃)
                   (stability~↓𝕥y Γ≡Δ k~l)
  stability~↑𝕥y Γ≡Δ (Emptyrec-cong x₁ k~l) =
    Emptyrec-cong (stabilityConv↑ Γ≡Δ x₁)
                (stability~↓𝕥y Γ≡Δ k~l)

  stability~↑𝕥y : ∀ {k l A Γ Δ}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ k ~ l ↑𝕥y A
              → Δ ⊢ k ~ l ↑𝕥y A
  stability~↑𝕥y Γ≡Δ (𝕥y~↑ neK neL ⊢k ⊢l) = 𝕥y~↑ neK neL (stabilityTerm Γ≡Δ ⊢k) (stabilityTerm Γ≡Δ ⊢l)

  stability~↑ : ∀ {k l A sA Γ Δ}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ k ~ l ↑ A ⦂ sA
              → Δ ⊢ k ~ l ↑ A ⦂ sA
  stability~↑ Γ≡Δ (~↑𝕥y x) = ~↑𝕥y (stability~↑𝕥y Γ≡Δ x)
  stability~↑ Γ≡Δ (~↑𝕥y x) = ~↑𝕥y (stability~↑𝕥y Γ≡Δ x)

  -- Stability of algorithmic equality of neutrals of types in WHNF.
  stability~↓𝕥y : ∀ {k l A Γ Δ}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ k ~ l ↓𝕥y A
              → Δ ⊢ k ~ l ↓𝕥y A
  stability~↓𝕥y Γ≡Δ ([~] A D whnfA k~l) =
    [~] A (stabilityRed* Γ≡Δ D) whnfA (stability~↑𝕥y Γ≡Δ k~l)

  stability~↓𝕥y : ∀ {k l A Γ Δ}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ k ~ l ↓𝕥y A
              → Δ ⊢ k ~ l ↓𝕥y A
  stability~↓𝕥y Γ≡Δ ([~] A D whnfA k~l) =
    [~] A (stabilityRed* Γ≡Δ D) whnfA (stability~↑𝕥y Γ≡Δ k~l)

  stability~↓ : ∀ {k l A sA Γ Δ}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ k ~ l ↓ A ⦂ sA
              → Δ ⊢ k ~ l ↓ A ⦂ sA
  stability~↓ Γ≡Δ (~↓𝕥y x) = ~↓𝕥y (stability~↓𝕥y Γ≡Δ x)
  stability~↓ Γ≡Δ (~↓𝕥y x) = ~↓𝕥y (stability~↓𝕥y Γ≡Δ x)

  -- Stability of algorithmic equality of types.
  stabilityConv↑ : ∀ {A B s Γ Δ}
                 → ⊢ Γ ≡ Δ
                 → Γ ⊢ A [conv↑] B ⦂ s
                 → Δ ⊢ A [conv↑] B ⦂ s
  stabilityConv↑ Γ≡Δ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) =
    [↑] A′ B′ (stabilityRed* Γ≡Δ D) (stabilityRed* Γ≡Δ D′) whnfA′ whnfB′
        (stabilityConv↓ Γ≡Δ A′<>B′)

  -- Stability of algorithmic equality of types in WHNF.
  stabilityConv↓ : ∀ {A B s Γ Δ}
                 → ⊢ Γ ≡ Δ
                 → Γ ⊢ A [conv↓] B ⦂ s
                 → Δ ⊢ A [conv↓] B ⦂ s
  stabilityConv↓ Γ≡Δ (U-refl PE.refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  U-refl PE.refl ⊢Δ
  stabilityConv↓ Γ≡Δ (ℕ-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  ℕ-refl ⊢Δ
  stabilityConv↓ Γ≡Δ (Empty-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  Empty-refl ⊢Δ
  stabilityConv↓ Γ≡Δ (ne x) =
    ne (stability~↓𝕥y Γ≡Δ x)
  stabilityConv↓ Γ≡Δ (Π-cong PE.refl F A<>B A<>B₁) =
    Π-cong PE.refl (stability Γ≡Δ F) (stabilityConv↑ Γ≡Δ A<>B)
           (stabilityConv↑ (Γ≡Δ ∙ refl F) A<>B₁)

  -- Stability of algorithmic equality of terms.
  stabilityConv↑Term : ∀ {t u A sA Γ Δ}
                     → ⊢ Γ ≡ Δ
                     → Γ ⊢ t [conv↑] u ∷ A ⦂ sA
                     → Δ ⊢ t [conv↑] u ∷ A ⦂ sA
  stabilityConv↑Term Γ≡Δ ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) =
    [↑]ₜ B t′ u′ (stabilityRed* Γ≡Δ D) (stabilityRed*Term Γ≡Δ d)
                 (stabilityRed*Term Γ≡Δ d′) whnfB whnft′ whnfu′
                 (stabilityConv↓Term Γ≡Δ t<>u)

  -- Stability of algorithmic equality of terms in WHNF.
  stabilityConv↓Term : ∀ {t u A sA Γ Δ}
                     → ⊢ Γ ≡ Δ
                     → Γ ⊢ t [conv↓] u ∷ A ⦂ sA
                     → Δ ⊢ t [conv↓] u ∷ A ⦂ sA
  stabilityConv↓Term Γ≡Δ (ℕ-ins x) =
    ℕ-ins (stability~↓𝕥y Γ≡Δ x)
  stabilityConv↓Term Γ≡Δ (Empty-ins x) =
    Empty-ins (stability~↓𝕥y Γ≡Δ x)
  stabilityConv↓Term Γ≡Δ (ne-ins t u neN x) =
    ne-ins (stabilityTerm Γ≡Δ t) (stabilityTerm Γ≡Δ u) neN (stability~↓ Γ≡Δ x)
  stabilityConv↓Term Γ≡Δ (univ x x₁ x₂) =
    univ (stabilityTerm Γ≡Δ x) (stabilityTerm Γ≡Δ x₁) (stabilityConv↓ Γ≡Δ x₂)
  stabilityConv↓Term Γ≡Δ (zero-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  zero-refl ⊢Δ
  stabilityConv↓Term Γ≡Δ (suc-cong t<>u) = suc-cong (stabilityConv↑Term Γ≡Δ t<>u)
  stabilityConv↓Term Γ≡Δ (η-eq F x x₁ y y₁ t<>u) =
    η-eq (stability Γ≡Δ F) (stabilityTerm Γ≡Δ x) (stabilityTerm Γ≡Δ x₁)
         y y₁ (stabilityConv↑Term (Γ≡Δ ∙ refl F) t<>u)
