{-# OPTIONS --without-K --safe #-}

module Definition.Conversion.Symmetry where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Conversion
open import Definition.Conversion.Stability
open import Definition.Conversion.Soundness
open import Definition.Conversion.Conversion
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Equality
open import Definition.Typed.Consequences.Reduction
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.Substitution
open import Definition.Typed.Consequences.SucCong

open import Tools.Product
import Tools.PropositionalEquality as PE


mutual
  -- Symmetry of algorithmic equality of neutrals.
  sym~↑! : ∀ {t u A Γ Δ} → ⊢ Γ ≡ Δ
        → Γ ⊢ t ~ u ↑! A
        → ∃ λ B → Γ ⊢ A ≡ B ^ ! × Δ ⊢ u ~ t ↑! B
  sym~↑! Γ≡Δ (var-refl x x≡y) =
    let ⊢A = syntacticTerm x
    in  _ , refl ⊢A
     ,  var-refl (PE.subst (λ y → _ ⊢ var y ∷ _ ^ _) x≡y (stabilityTerm Γ≡Δ x))
                 (PE.sym x≡y)
  sym~↑! Γ≡Δ (app-cong t~u x) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        B , whnfB , A≡B , u~t = sym~↓! Γ≡Δ t~u
        F′ , G′ , ΠF′G′≡B = Π≡A A≡B whnfB
        F≡F′ , rF≡rF′ , G≡G′ = injectivity (PE.subst (λ x → _ ⊢ _ ≡ x ^ _) ΠF′G′≡B A≡B)
    in  _ , substTypeEq G≡G′ (soundnessConv↑Term x)
    ,   app-cong (PE.subst (λ x → _ ⊢ _ ~ _ ↓! x) ΠF′G′≡B u~t)
                 (convConvTerm (symConv↑Term Γ≡Δ x) (stabilityEq Γ≡Δ F≡F′))
  sym~↑! Γ≡Δ (app-cong% t~u x) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        B , whnfB , A≡B , u~t = sym~↓! Γ≡Δ t~u
        F′ , G′ , ΠF′G′≡B = Π≡A A≡B whnfB
        F≡F′ , rF≡rF′ , G≡G′ = injectivity (PE.subst (λ x → _ ⊢ _ ≡ x ^ _) ΠF′G′≡B A≡B)
    in  _ , substTypeEq G≡G′ (soundness~↑% x)
    ,   app-cong% (PE.subst (λ x → _ ⊢ _ ~ _ ↓! x) ΠF′G′≡B u~t)
                  (sym~↑% Γ≡Δ (conv~↑% x (stabilityEq (reflConEq ⊢Γ) F≡F′)))
  sym~↑! Γ≡Δ (natrec-cong x x₁ x₂ t~u) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        B , whnfB , A≡B , u~t = sym~↓! Γ≡Δ t~u
        B≡ℕ = ℕ≡A A≡B whnfB
        F≡G = stabilityEq (Γ≡Δ ∙ refl (ℕⱼ ⊢Γ)) (soundnessConv↑ x)
        F[0]≡G[0] = substTypeEq F≡G (refl (zeroⱼ ⊢Δ))
    in  _ , substTypeEq (soundnessConv↑ x) (soundness~↓! t~u)
    ,   natrec-cong (symConv↑ (Γ≡Δ ∙ (refl (ℕⱼ ⊢Γ))) x)
                    (convConvTerm (symConv↑Term Γ≡Δ x₁) F[0]≡G[0])
                    (convConvTerm (symConv↑Term Γ≡Δ x₂) (sucCong F≡G))
                    (PE.subst (λ x → _ ⊢ _ ~ _ ↓! x) B≡ℕ u~t)
  sym~↑! Γ≡Δ (Emptyrec-cong x t~u) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        B , whnfB , A≡B , u~t = sym~↓% Γ≡Δ t~u
        B≡Empty = Empty≡A A≡B whnfB
        F≡G = stabilityEq Γ≡Δ (soundnessConv↑ x)
        u~t′ = PE.subst (λ x₁ → _ ⊢ _ ~ _ ↓% x₁) B≡Empty u~t
    in  _ , soundnessConv↑ x
    , Emptyrec-cong (symConv↑ Γ≡Δ x) u~t′

  sym~↑% : ∀ {t u A Γ Δ} → ⊢ Γ ≡ Δ
         → Γ ⊢ t ~ u ↑% A
         → Δ ⊢ u ~ t ↑% A
  sym~↑% Γ≡Δ (%~↑ ⊢k ⊢l) = %~↑ (stabilityTerm Γ≡Δ ⊢l) (stabilityTerm Γ≡Δ ⊢k)

  sym~↑ : ∀ {t u A rA Γ Δ} → ⊢ Γ ≡ Δ
        → Γ ⊢ t ~ u ↑ A ^ rA
        → ∃ λ B → Γ ⊢ A ≡ B ^ rA × Δ ⊢ u ~ t ↑ B ^ rA
  sym~↑ Γ≡Δ (~↑! x) =
    let B , A≡B , x′ = sym~↑! Γ≡Δ x
    in B , A≡B , ~↑! x′
  sym~↑ {A = A} Γ≡Δ (~↑% x) =
    let x′ = sym~↑% Γ≡Δ x
        ⊢A , _ , _ = syntacticEqTerm (soundness~↑% x)
    in A , refl ⊢A , ~↑% x′

  -- Symmetry of algorithmic equality of neutrals of types in WHNF.
  sym~↓! : ∀ {t u A Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ t ~ u ↓! A
         → ∃ λ B → Whnf B × Γ ⊢ A ≡ B ^ ! × Δ ⊢ u ~ t ↓! B
  sym~↓! Γ≡Δ ([~] A₁ D whnfA k~l) =
    let B , A≡B , k~l′ = sym~↑! Γ≡Δ k~l
        _ , ⊢B = syntacticEq A≡B
        B′ , whnfB′ , D′ = whNorm ⊢B
        A≡B′ = trans (sym (subset* D)) (trans A≡B (subset* (red D′)))
    in  B′ , whnfB′ , A≡B′ , [~] B (stabilityRed* Γ≡Δ (red D′)) whnfB′ k~l′

  sym~↓% : ∀ {t u A Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ t ~ u ↓% A
         → ∃ λ B → Whnf B × Γ ⊢ A ≡ B ^ % × Δ ⊢ u ~ t ↓% B
  sym~↓% Γ≡Δ ([~] A D whnfA k~l) =
    let k~l′ = sym~↑% Γ≡Δ k~l
        B′ , whnfB′ , D′ = whNorm (proj₁ (syntacticRed D))
        A≡B′ = trans (sym (subset* D)) (subset* (red D′))
    in  B′ , whnfB′ , A≡B′ , [~] A (stabilityRed* Γ≡Δ (red D′)) whnfB′ k~l′

  sym~↓ : ∀ {t u A rA Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ t ~ u ↓ A ^ rA
         → ∃ λ B → Whnf B × Γ ⊢ A ≡ B ^ rA × Δ ⊢ u ~ t ↓ B ^ rA
  sym~↓ Γ≡Δ (~↓! x) =
    let B , wB , A≡B , x′ = sym~↓! Γ≡Δ x
    in B , wB , A≡B , ~↓! x′
  sym~↓ Γ≡Δ (~↓% x) =
    let B , wB , A≡B , x′ = sym~↓% Γ≡Δ x
    in B , wB , A≡B , ~↓% x′

  -- Symmetry of algorithmic equality of types.
  symConv↑ : ∀ {A B r Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ A [conv↑] B ^ r → Δ ⊢ B [conv↑] A ^ r
  symConv↑ Γ≡Δ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) =
    [↑] B′ A′ (stabilityRed* Γ≡Δ D′) (stabilityRed* Γ≡Δ D) whnfB′ whnfA′
        (symConv↓ Γ≡Δ A′<>B′)

  -- Symmetry of algorithmic equality of types in WHNF.
  symConv↓ : ∀ {A B r Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ A [conv↓] B ^ r → Δ ⊢ B [conv↓] A ^ r
  symConv↓ Γ≡Δ (U-refl PE.refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  U-refl PE.refl ⊢Δ
  symConv↓ Γ≡Δ (ℕ-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  ℕ-refl ⊢Δ
  symConv↓ Γ≡Δ (Empty-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  Empty-refl ⊢Δ
  symConv↓ Γ≡Δ (ne A~B) =
    let B , whnfB , U≡B , B~A = sym~↓! Γ≡Δ A~B
        B≡U = U≡A U≡B
    in  ne (PE.subst (λ x → _ ⊢ _ ~ _ ↓! x) B≡U B~A)
  symConv↓ Γ≡Δ (Π-cong PE.refl x A<>B A<>B₁) =
    let F≡H = soundnessConv↑ A<>B
        _ , ⊢H = syntacticEq (stabilityEq Γ≡Δ F≡H)
    in  Π-cong PE.refl ⊢H (symConv↑ Γ≡Δ A<>B)
                  (symConv↑ (Γ≡Δ ∙ F≡H) A<>B₁)

  -- Symmetry of algorithmic equality of terms.
  symConv↑Term : ∀ {t u A Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ t [conv↑] u ∷ A  → Δ ⊢ u [conv↑] t ∷ A 
  symConv↑Term Γ≡Δ ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) =
    [↑]ₜ B u′ t′ (stabilityRed* Γ≡Δ D) (stabilityRed*Term Γ≡Δ d′)
         (stabilityRed*Term Γ≡Δ d) whnfB whnfu′ whnft′ (symConv↓Term Γ≡Δ t<>u)

  -- Symmetry of algorithmic equality of terms in WHNF.
  symConv↓Term : ∀ {t u A Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ t [conv↓] u ∷ A  → Δ ⊢ u [conv↓] t ∷ A 
  symConv↓Term Γ≡Δ (ℕ-ins t~u) =
    let B , whnfB , A≡B , u~t = sym~↓! Γ≡Δ t~u
        B≡ℕ = ℕ≡A A≡B whnfB
    in  ℕ-ins (PE.subst (λ x → _ ⊢ _ ~ _ ↓! x) B≡ℕ u~t)
  -- symConv↓Term Γ≡Δ (Empty-ins t~u) =
  --   let B , whnfB , A≡B , u~t = sym~↓% Γ≡Δ t~u
  --       B≡Empty = Empty≡A A≡B whnfB
  --   in  Empty-ins (PE.subst (λ x → _ ⊢ _ ~ _ ↓% x) B≡Empty u~t)
  symConv↓Term Γ≡Δ (ne-ins t u x t~u) =
    let B , whnfB , A≡B , u~t = sym~↓ Γ≡Δ t~u
    in  ne-ins (stabilityTerm Γ≡Δ u) (stabilityTerm Γ≡Δ t) x u~t
  symConv↓Term Γ≡Δ (univ x x₁ x₂) =
    univ (stabilityTerm Γ≡Δ x₁) (stabilityTerm Γ≡Δ x) (symConv↓ Γ≡Δ x₂)
  symConv↓Term Γ≡Δ (zero-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  zero-refl ⊢Δ
  symConv↓Term Γ≡Δ (suc-cong t<>u) = suc-cong (symConv↑Term Γ≡Δ t<>u)
  symConv↓Term Γ≡Δ (η-eq x x₁ x₂ y y₁ t<>u) =
    η-eq (stability Γ≡Δ x) (stabilityTerm Γ≡Δ x₂) (stabilityTerm Γ≡Δ x₁)
         y₁ y (symConv↑Term (Γ≡Δ ∙ refl x) t<>u)

-- Symmetry of algorithmic equality of types with preserved context.
symConv : ∀ {A B r Γ} → Γ ⊢ A [conv↑] B ^ r → Γ ⊢ B [conv↑] A ^ r
symConv A<>B =
  let ⊢Γ = wfEq (soundnessConv↑ A<>B)
  in  symConv↑ (reflConEq ⊢Γ) A<>B

-- Symmetry of algorithmic equality of terms with preserved context.
symConvTerm : ∀ {t u A Γ} → Γ ⊢ t [conv↑] u ∷ A  → Γ ⊢ u [conv↑] t ∷ A 
symConvTerm t<>u =
  let ⊢Γ = wfEqTerm (soundnessConv↑Term t<>u)
  in  symConv↑Term (reflConEq ⊢Γ) t<>u
