-- Algorithmic equality.

{-# OPTIONS --safe #-}

module Definition.Conversion.ConvSize where

open import Definition.Untyped
open import Definition.Typed

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Definition.Conversion



mutual
  -- Neutral equality.
  size~↑! : ∀ {t u A Γ l} → Γ ⊢ t ~ u ↑! A ^ l → Nat

  size~↑! (var-refl x x₁) = 1
  size~↑! (app-cong x x₁) = size~↓! x + size[genconv↑] x₁
  size~↑! (natrec-cong x x₁ x₂ x₃) = 1 + sizeConv↑ x + sizeConv↑Term x₁ + sizeConv↑Term x₂ + size~↓! x₃
  size~↑! (Emptyrec-cong x x₁) = 1 + sizeConv↑ x
  size~↑! (Id-cong x x₁ x₂) = 1 + size~↓! x + sizeConv↑Term  x₁ + sizeConv↑Term x₂ 
  size~↑! (Id-ℕ x x₁) = 1 + size~↓! x + sizeConv↑Term  x₁
  size~↑! (Id-ℕ0 x) = 1 + size~↓! x 
  size~↑! (Id-ℕS x x₁) = 1 + sizeConv↑Term x + size~↓! x₁
  size~↑! (Id-U x x₁) = 1 + size~↓! x + sizeConv↑Term x₁
  size~↑! (Id-Uℕ x) = 1 + size~↓! x 
  size~↑! (Id-UΠ x x₁) = 1 + sizeConv↑Term x + size~↓! x₁
  size~↑! (cast-cong x x₁ x₂ x₃ x₄ x₅ x₆) = 1 + size~↓! x + size~↓! x₁ + sizeConv↓Term x₄
  size~↑! (cast-refl x x₁ x₂ x₃ x₄) = 1 + size~↓! x + sizeConv↓Term x₃
  size~↑! (castℕ-refl x x₁) = 1 + size~↓! x 
  size~↑! (cast-refl' x x₁ x₂ x₃ x₄) = 1 + size~↓! x + sizeConv↓Term x₃
  size~↑! (castℕ-refl' x x₁) = 1 + size~↓! x 
  size~↑! (cast-neℕ x x₁ x₂ x₃) = 1 + size~↓! x + sizeConv↑Term x₁
  size~↑! (cast-ℕ x x₁ x₂ x₃) = 1 + size~↓! x + sizeConv↑Term x₁
  size~↑! (cast-ℕℕ x x₁ x₂) = 1 + size~↓! x
  size~↑! (cast-neΠ x x₁ x₂ x₃ x₄) = 1 + size~↓! x₁ + sizeConv↑Term x₂
  size~↑! (cast-Π x x₁ x₂ x₃ x₄) = 1 + sizeConv↑Term x + size~↓! x₁ + sizeConv↑Term x₂
  size~↑! (cast-Πℕ x x₁ x₂ x₃) = 1 + sizeConv↑Term x + sizeConv↑Term x₁
  size~↑! (cast-ℕΠ x x₁ x₂ x₃) = 1 + sizeConv↑Term x + sizeConv↑Term x₁
  size~↑! (cast-ΠΠ%! x x₁ x₂ x₃ x₄) = 1 + sizeConv↑Term x + sizeConv↑Term x₁ + sizeConv↑Term x₂
  size~↑! (cast-ΠΠ!% x x₁ x₂ x₃ x₄) = 1 + sizeConv↑Term x + sizeConv↑Term x₁ + sizeConv↑Term x₂
  
  size~↑ : ∀ {t u A Γ l} → Γ ⊢ t ~ u ↑ A ^ l → Nat
  size~↑ (~↑! x) = size~↑! x
  size~↑ (~↑% x) = 1

  size~↓! : ∀ {t u A Γ l} → Γ ⊢ t ~ u ↓! A ^ l → Nat
  size~↓! ([~] A D whnfB k~l) = 1+ (size~↑! k~l)
  
  sizeConv↑ : ∀ {A B Γ l} → Γ ⊢ A [conv↑] B ^ l → Nat
  sizeConv↑ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) = 1 + sizeConv↓ A′<>B′

  sizeConv↑Term : ∀ {t u A Γ l} → Γ ⊢ t [conv↑] u ∷ A ^ l → Nat
  sizeConv↑Term ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) = 1 + sizeConv↓Term t<>u

  size[genconv↑] : ∀ {t u A Γ l} → Γ ⊢ t [genconv↑] u ∷ A ^ l → Nat
  size[genconv↑] {l = [ ! , l ]} X = sizeConv↑Term X
  size[genconv↑] {l = [ % , l ]} X = 1

  sizeConv↓Term : ∀ {t u A Γ l} → Γ ⊢ t [conv↓] u ∷ A ^ l → Nat
  sizeConv↓Term (U-refl x x₁) = 1
  sizeConv↓Term (ne x) = 1 + size~↓! x
  sizeConv↓Term (ℕ-refl x) = 1
  sizeConv↓Term (Empty-refl x) = 1
  sizeConv↓Term (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = 1 + sizeConv↑Term x₇ + sizeConv↑Term x₈
  sizeConv↓Term (∃-cong x x₁ x₂) = 1 + sizeConv↑Term x₁ + sizeConv↑Term x₂
  sizeConv↓Term (ℕ-ins x) = 1 + size~↓! x
  sizeConv↓Term (ne-ins x x₁ x₂ x₃) = 1 + size~↓! x₃ 
  sizeConv↓Term (zero-refl x) = 1
  sizeConv↓Term (suc-cong x) = 1 + sizeConv↑Term x
  sizeConv↓Term (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) = 1 + sizeConv↑Term x₇

  sizeConv↓ : ∀ {A B Γ l} → Γ ⊢ A [conv↓] B ^ l → Nat
  sizeConv↓ (U-refl x x₁) = 1
  sizeConv↓ (univ x) = 1 + sizeConv↓Term x


