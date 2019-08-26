{-# OPTIONS --without-K --safe #-}

module Definition.Conversion.Weakening where

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Conversion

import Tools.PropositionalEquality as PE

mutual
  -- Weakening of algorithmic equality of neutrals.
  wk~↑! : ∀ {ρ t u A Γ Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) → ⊢ Δ
      → Γ ⊢ t ~ u ↑! A
      → Δ ⊢ U.wk ρ t ~ U.wk ρ u ↑! U.wk ρ A
  wk~↑! {ρ} [ρ] ⊢Δ (var-refl x₁ x≡y) = var-refl (wkTerm [ρ] ⊢Δ x₁) (PE.cong (wkVar ρ) x≡y)
  wk~↑! ρ ⊢Δ (app-cong {G = G} t~u x) =
    PE.subst (λ x → _ ⊢ _ ~ _ ↑! x) (PE.sym (wk-β G))
             (app-cong (wk~↓! ρ ⊢Δ t~u) (wkConv↑Term ρ ⊢Δ x))
  wk~↑! {ρ} {Δ = Δ} [ρ] ⊢Δ (natrec-cong {k} {l} {h} {g} {a₀} {b₀} {F} {G} x x₁ x₂ t~u) =
    PE.subst (λ x → _ ⊢ U.wk ρ (natrec F a₀ h k) ~ _ ↑! x) (PE.sym (wk-β F))
             (natrec-cong (wkConv↑ (lift [ρ]) (⊢Δ ∙ ℕⱼ ⊢Δ) x)
                          (PE.subst (λ x → _ ⊢ _ [conv↑] _ ∷ x ^ _) (wk-β F)
                                    (wkConv↑Term [ρ] ⊢Δ x₁))
                          (PE.subst (λ x → Δ ⊢ U.wk ρ h [conv↑] U.wk ρ g ∷ x ^ !)
                                    (wk-β-natrec _ F !) (wkConv↑Term [ρ] ⊢Δ x₂))
                          (wk~↓! [ρ] ⊢Δ t~u))
  wk~↑! {ρ} {Δ = Δ} [ρ] ⊢Δ (Emptyrec-cong {k} {l} {F} {G} x t~u) =
    Emptyrec-cong (wkConv↑ [ρ] ⊢Δ x) (wk~↓% [ρ] ⊢Δ t~u)

  wk~↑% : ∀ {ρ t u A Γ Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) → ⊢ Δ
        → Γ ⊢ t ~ u ↑% A
        → Δ ⊢ U.wk ρ t ~ U.wk ρ u ↑% U.wk ρ A
  wk~↑% [ρ] ⊢Δ (%~↑ neK neL ⊢k ⊢l) =
    %~↑ (wkNeutral _ neK) (wkNeutral _ neL)
    (wkTerm [ρ] ⊢Δ ⊢k) (wkTerm [ρ] ⊢Δ ⊢l)

  wk~↑ : ∀ {ρ t u A rA Γ Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) → ⊢ Δ
      → Γ ⊢ t ~ u ↑ A ^ rA
      → Δ ⊢ U.wk ρ t ~ U.wk ρ u ↑ U.wk ρ A ^ rA
  wk~↑ [ρ] ⊢Δ (~↑! x) = ~↑! (wk~↑! [ρ] ⊢Δ x)
  wk~↑ [ρ] ⊢Δ (~↑% x) = ~↑% (wk~↑% [ρ] ⊢Δ x)

  -- Weakening of algorithmic equality of neutrals in WHNF.
  wk~↓! : ∀ {ρ t u A Γ Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) → ⊢ Δ
      → Γ ⊢ t ~ u ↓! A
      → Δ ⊢ U.wk ρ t ~ U.wk ρ u ↓! U.wk ρ A
  wk~↓! {ρ} [ρ] ⊢Δ ([~] A₁ D whnfA k~l) =
    [~] (U.wk ρ A₁) (wkRed* [ρ] ⊢Δ D) (wkWhnf ρ whnfA) (wk~↑! [ρ] ⊢Δ k~l)

  wk~↓% : ∀ {ρ t u A Γ Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) → ⊢ Δ
      → Γ ⊢ t ~ u ↓% A
      → Δ ⊢ U.wk ρ t ~ U.wk ρ u ↓% U.wk ρ A
  wk~↓% {ρ} [ρ] ⊢Δ ([~] A₁ D whnfA k~l) =
    [~] (U.wk ρ A₁) (wkRed* [ρ] ⊢Δ D) (wkWhnf ρ whnfA) (wk~↑% [ρ] ⊢Δ k~l)

  wk~↓ : ∀ {ρ t u A rA Γ Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) → ⊢ Δ
      → Γ ⊢ t ~ u ↓ A ^ rA
      → Δ ⊢ U.wk ρ t ~ U.wk ρ u ↓ U.wk ρ A ^ rA
  wk~↓ [ρ] ⊢Δ (~↓! x) = ~↓! (wk~↓! [ρ] ⊢Δ x)
  wk~↓ [ρ] ⊢Δ (~↓% x) = ~↓% (wk~↓% [ρ] ⊢Δ x)

  -- Weakening of algorithmic equality of types.
  wkConv↑ : ∀ {ρ A B rA Γ Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) → ⊢ Δ
          → Γ ⊢ A [conv↑] B ^ rA
          → Δ ⊢ U.wk ρ A [conv↑] U.wk ρ B ^ rA
  wkConv↑ {ρ} [ρ] ⊢Δ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) =
    [↑] (U.wk ρ A′) (U.wk ρ B′) (wkRed* [ρ] ⊢Δ D) (wkRed* [ρ] ⊢Δ D′)
        (wkWhnf ρ whnfA′) (wkWhnf ρ whnfB′) (wkConv↓ [ρ] ⊢Δ A′<>B′)

  -- Weakening of algorithmic equality of types in WHNF.
  wkConv↓ : ∀ {ρ A B rA Γ Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) → ⊢ Δ
         → Γ ⊢ A [conv↓] B ^ rA
         → Δ ⊢ U.wk ρ A [conv↓] U.wk ρ B ^ rA
  wkConv↓ ρ ⊢Δ (U-refl eqr x) = U-refl eqr ⊢Δ
  wkConv↓ ρ ⊢Δ (ℕ-refl x) = ℕ-refl ⊢Δ
  wkConv↓ ρ ⊢Δ (Empty-refl x) = Empty-refl ⊢Δ
  wkConv↓ ρ ⊢Δ (ne x) = ne (wk~↓! ρ ⊢Δ x)
  wkConv↓ ρ ⊢Δ (Π-cong eqr x A<>B A<>B₁) =
    let ⊢ρF = wk ρ ⊢Δ x
    in  Π-cong eqr ⊢ρF (wkConv↑ ρ ⊢Δ A<>B) (wkConv↑ (lift ρ) (⊢Δ ∙ ⊢ρF) A<>B₁)

  -- Weakening of algorithmic equality of terms.
  wkConv↑Term : ∀ {ρ t u A rA Γ Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) → ⊢ Δ
             → Γ ⊢ t [conv↑] u ∷ A ^ rA
             → Δ ⊢ U.wk ρ t [conv↑] U.wk ρ u ∷ U.wk ρ A ^ rA
  wkConv↑Term {ρ} [ρ] ⊢Δ ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) =
    [↑]ₜ (U.wk ρ B) (U.wk ρ t′) (U.wk ρ u′)
         (wkRed* [ρ] ⊢Δ D) (wkRed*Term [ρ] ⊢Δ d) (wkRed*Term [ρ] ⊢Δ d′)
         (wkWhnf ρ whnfB) (wkWhnf ρ whnft′) (wkWhnf ρ whnfu′)
         (wkConv↓Term [ρ] ⊢Δ t<>u)

  -- Weakening of algorithmic equality of terms in WHNF.
  wkConv↓Term : ∀ {ρ t u A rA Γ Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) → ⊢ Δ
             → Γ ⊢ t [conv↓] u ∷ A ^ rA
             → Δ ⊢ U.wk ρ t [conv↓] U.wk ρ u ∷ U.wk ρ A ^ rA
  wkConv↓Term ρ ⊢Δ (ℕ-ins x) =
    ℕ-ins (wk~↓! ρ ⊢Δ x)
  wkConv↓Term ρ ⊢Δ (Empty-ins x) =
    Empty-ins (wk~↓% ρ ⊢Δ x)
  wkConv↓Term {ρ} [ρ] ⊢Δ (ne-ins t u x x₁) =
    ne-ins (wkTerm [ρ] ⊢Δ t) (wkTerm [ρ] ⊢Δ u) (wkNeutral ρ x) (wk~↓ [ρ] ⊢Δ x₁)
  wkConv↓Term ρ ⊢Δ (univ x x₁ x₂) =
    univ (wkTerm ρ ⊢Δ x) (wkTerm ρ ⊢Δ x₁) (wkConv↓ ρ ⊢Δ x₂)
  wkConv↓Term ρ ⊢Δ (zero-refl x) = zero-refl ⊢Δ
  wkConv↓Term ρ ⊢Δ (suc-cong t<>u) = suc-cong (wkConv↑Term ρ ⊢Δ t<>u)
  wkConv↓Term {ρ} {Δ = Δ} [ρ] ⊢Δ (η-eq {F = F} {G = G} {rF = rF} {rG = rG} x x₁ x₂ y y₁ t<>u) =
    let ⊢ρF = wk [ρ] ⊢Δ x
    in  η-eq ⊢ρF (wkTerm [ρ] ⊢Δ x₁) (wkTerm [ρ] ⊢Δ x₂)
             (wkFunction ρ y) (wkFunction ρ y₁)
             (PE.subst₃ (λ x y z → Δ ∙ U.wk ρ F ^ rF ⊢ x [conv↑] y ∷ z ^ rG)
                        (PE.cong₂ _∘_ (PE.sym (wk1-wk≡lift-wk1 _ _)) PE.refl)
                        (PE.cong₂ _∘_ (PE.sym (wk1-wk≡lift-wk1 _ _)) PE.refl)
                        PE.refl
                        (wkConv↑Term (lift [ρ]) (⊢Δ ∙ ⊢ρF) t<>u))
