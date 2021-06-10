{-# OPTIONS --without-K  #-}

module Definition.Conversion.Whnf where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Conversion

open import Tools.Product


mutual
  -- Extraction of neutrality from algorithmic equality of neutrals.
  ne~↑𝕥y : ∀ {t u A Γ}
       → Γ ⊢ t ~ u ↑𝕥y A
       → Neutral t × Neutral u
  ne~↑𝕥y (var-refl x₁ x≡y) = var _ , var _
  ne~↑𝕥y (app-cong x x₁) = let _ , q , w = ne~↓𝕥y x
                         in  ∘ₙ q , ∘ₙ w
  ne~↑𝕥y (natrec-cong x x₁ x₂ x₃) = let _ , q , w = ne~↓𝕥y x₃
                                  in  natrecₙ q , natrecₙ w
  ne~↑𝕥y (Emptyrec-cong x x₁) = let _ , q , w = ne~↓𝕥y x₁
                              in Emptyrecₙ q , Emptyrecₙ w

  ne~↑𝕥y : ∀ {t u A Γ}
        → Γ ⊢ t ~ u ↑𝕥y A
        → Neutral t × Neutral u
  ne~↑𝕥y (𝕥y~↑ neK neL ⊢k ⊢l) = neK , neL

  ne~↑ : ∀ {t u A sA Γ}
       → Γ ⊢ t ~ u ↑ A ⦂ sA
       → Neutral t × Neutral u
  ne~↑ (~↑𝕥y x) = ne~↑𝕥y x
  ne~↑ (~↑𝕥y x) = ne~↑𝕥y x

  ne~↓𝕥y : ∀ {t u A Γ}
        → Γ ⊢ t ~ u ↓𝕥y A
        → Whnf A × Neutral t × Neutral u
  ne~↓𝕥y ([~] A D whnfB k~l) = whnfB , ne~↑𝕥y k~l

  ne~↓𝕥y : ∀ {t u A Γ}
        → Γ ⊢ t ~ u ↓𝕥y A
        → Whnf A × Neutral t × Neutral u
  ne~↓𝕥y ([~] A D whnfB k~l) = whnfB , ne~↑𝕥y k~l

  -- Extraction of neutrality and WHNF from algorithmic equality of neutrals
  -- with type in WHNF.
  ne~↓ : ∀ {t u A sA Γ}
       → Γ ⊢ t ~ u ↓ A ⦂ sA
       → Whnf A × Neutral t × Neutral u
  ne~↓ (~↓𝕥y ([~] A₁ D whnfB k~l)) = whnfB , ne~↑𝕥y k~l
  ne~↓ (~↓𝕥y ([~] A D whnfB k~l)) = whnfB , ne~↑𝕥y k~l

-- Extraction of WHNF from algorithmic equality of types in WHNF.
whnfConv↓ : ∀ {A B sA Γ}
          → Γ ⊢ A [conv↓] B ⦂ sA
          → Whnf A × Whnf B
whnfConv↓ (U-refl _ x) = Uₙ , Uₙ
whnfConv↓ (ℕ-refl x) = ℕₙ , ℕₙ
whnfConv↓ (Empty-refl x) = Emptyₙ , Emptyₙ
whnfConv↓ (ne x) = let _ , neA , neB = ne~↓𝕥y x
                   in  ne neA , ne neB
whnfConv↓ (Π-cong _ x x₁ x₂) = Πₙ , Πₙ

-- Extraction of WHNF from algorithmic equality of terms in WHNF.
whnfConv↓Term : ∀ {t u A sA Γ}
              → Γ ⊢ t [conv↓] u ∷ A ⦂ sA
              → Whnf A × Whnf t × Whnf u
whnfConv↓Term (ℕ-ins x) = let _ , neT , neU = ne~↓𝕥y x
                          in ℕₙ , ne neT , ne neU
whnfConv↓Term (Empty-ins x) = let _ , neT , neU = ne~↓𝕥y x
                          in Emptyₙ , ne neT , ne neU
whnfConv↓Term (ne-ins t u x x₁) =
  let _ , neT , neU = ne~↓ x₁
  in ne x , ne neT , ne neU
whnfConv↓Term (univ x x₁ x₂) = Uₙ , whnfConv↓ x₂
whnfConv↓Term (zero-refl x) = ℕₙ , zeroₙ , zeroₙ
whnfConv↓Term (suc-cong x) = ℕₙ , sucₙ , sucₙ
whnfConv↓Term (η-eq x x₁ x₂ y y₁ x₃) = Πₙ , functionWhnf y , functionWhnf y₁
