-- {-# OPTIONS --safe #-}
{-# OPTIONS --allow-unsolved-metas #-}

module Definition.Conversion.SymmetrySize where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Conversion
open import Definition.Conversion.Stability
open import Definition.Conversion.Soundness
open import Definition.Conversion.Conversion
open import Definition.Conversion.Whnf
open import Definition.Conversion.ConvSize
open import Definition.Conversion.Symmetry
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Equality
open import Definition.Typed.Consequences.Reduction
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.Substitution
open import Definition.Typed.Consequences.SucCong

open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Nat


mutual
  -- Symmetry of algorithmic equality of neutrals
  size-sym~↑! : ∀ {t u A Γ Δ l} (Γ≡Δ : ⊢ Γ ≡ Δ)
        (t~u : Γ ⊢ t ~ u ↑! A ^ l) → size~↑! (proj₂ (proj₂ (sym~↑! Γ≡Δ t~u))) PE.≡ size~↑! t~u
  size-sym~↑! Γ≡Δ (var-refl x x₁) = PE.refl
  size-sym~↑! Γ≡Δ (app-cong {rF = !} x x₁) =
    let ex = size-sym~↓!  Γ≡Δ x
        ex' = size-symConv↑Term Γ≡Δ x₁
    in {!PE.subst₂ (λ X Y → (X + Y) PE.≡ size~↑! _) ex ex' ?!}
  size-sym~↑! Γ≡Δ (app-cong {rF = %} x x₁) = {!!}
  size-sym~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) = {!!}
  size-sym~↑! Γ≡Δ (Emptyrec-cong x x₁) = {!!}
  size-sym~↑! Γ≡Δ (Id-cong x x₁ x₂) = {!!}
  size-sym~↑! Γ≡Δ (Id-ℕ x x₁) = {!!}
  size-sym~↑! Γ≡Δ (Id-ℕ0 x) = {!!}
  size-sym~↑! Γ≡Δ (Id-ℕS x x₁) = {!!}
  size-sym~↑! Γ≡Δ (Id-U x x₁) = {!!}
  size-sym~↑! Γ≡Δ (Id-Uℕ x) = {!!}
  size-sym~↑! Γ≡Δ (Id-UΠ x x₁) = {!!}
  size-sym~↑! Γ≡Δ (cast-cong x x₁ x₂ x₃ x₄) = {!!}
  size-sym~↑! Γ≡Δ (cast-refl x x₁ x₂) = {!!}
  size-sym~↑! Γ≡Δ (castℕ-refl x x₁) = {!!}
  size-sym~↑! Γ≡Δ (cast-refl' x x₁ x₂) = {!!}
  size-sym~↑! Γ≡Δ (castℕ-refl' x x₁) = {!!}
  size-sym~↑! Γ≡Δ (cast-neℕ x x₁ x₂ x₃) = {!!}
  size-sym~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) = {!!}
  size-sym~↑! Γ≡Δ (cast-neΠ x x₁ x₂ x₃ x₄) = {!!}
  size-sym~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) = {!!}
  size-sym~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) = {!!}
  size-sym~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) = {!!}
  size-sym~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) = {!!}
  size-sym~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) = {!!}

  size-sym~↓! : ∀ {t u A Γ Δ l} (Γ≡Δ : ⊢ Γ ≡ Δ)
        (t~u : Γ ⊢ t ~ u ↓! A ^ l) → size~↓! (proj₂ (proj₂ (proj₂ (sym~↓! Γ≡Δ t~u)))) PE.≡ size~↓! t~u
  size-sym~↓! Γ≡Δ ([~] A D whnfB k~l) = PE.cong 1+ (size-sym~↑! Γ≡Δ k~l)

  size-symConv↑Term : ∀ {t u A Γ Δ l} (Γ≡Δ : ⊢ Γ ≡ Δ)
        (t~u : Γ ⊢ t [conv↑] u ∷ A ^ l) → sizeConv↑Term (symConv↑Term Γ≡Δ t~u) PE.≡ sizeConv↑Term t~u
  size-symConv↑Term Γ≡Δ t~u = {!!}

  size-symConv↑ : ∀ {A B Γ Δ l} (Γ≡Δ : ⊢ Γ ≡ Δ)
        (A~B : Γ ⊢ A [conv↑] B ^ l) → sizeConv↑ (symConv↑ Γ≡Δ A~B) PE.≡ sizeConv↑ A~B
  size-symConv↑ Γ≡Δ A~B = {!!}

  size-symConv↓Term : ∀ {t u A Γ Δ l} (Γ≡Δ : ⊢ Γ ≡ Δ)
        (t~u : Γ ⊢ t [conv↓] u ∷ A ^ l) → sizeConv↓Term (symConv↓Term Γ≡Δ t~u) PE.≡ sizeConv↓Term t~u
  size-symConv↓Term Γ≡Δ t~u = {!!}

  size-symConv↓ : ∀ {A B Γ Δ l} (Γ≡Δ : ⊢ Γ ≡ Δ)
        (A~B : Γ ⊢ A [conv↓] B ^ l) → sizeConv↓ (symConv↓ Γ≡Δ A~B) PE.≡ sizeConv↓ A~B
  size-symConv↓ Γ≡Δ A~B = {!!}

