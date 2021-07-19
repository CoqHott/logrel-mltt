{-# OPTIONS --safe #-}

module Definition.Conversion.Whnf where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Conversion

open import Tools.Product


mutual
  -- Extraction of neutrality from algorithmic equality of neutrals.
  ne~↑! : ∀ {t u A Γ l}
       → Γ ⊢ t ~ u ↑! A ^ l
       → Neutral t × Neutral u
  ne~↑! (var-refl x₁ x≡y) = var _ , var _
  ne~↑! (app-cong x x₁) = let _ , q , w = ne~↓! x
                         in  ∘ₙ q , ∘ₙ w
  ne~↑! (natrec-cong x x₁ x₂ x₃) = let _ , q , w = ne~↓! x₃
                                  in  natrecₙ q , natrecₙ w
  ne~↑! (Emptyrec-cong x x₁) = Emptyrecₙ , Emptyrecₙ
  ne~↑! (Id-cong X x x₁) = let nt , nu = ne~↑! X in Idₙ nt , Idₙ nu
  ne~↑! (Id-ℕ X x) = let nt , nu = ne~↑! X in Idℕₙ nt , Idℕₙ nu
  ne~↑! (Id-ℕ0 X) = let nt , nu = ne~↑! X in Idℕ0ₙ nt , Idℕ0ₙ nu
  ne~↑! (Id-ℕS x X) = let nt , nu = ne~↑! X in IdℕSₙ nt , IdℕSₙ nu
  ne~↑! (Id-U X x) = let nt , nu = ne~↑! X in IdUₙ nt , IdUₙ nu
  ne~↑! (Id-Uℕ X) = let nt , nu = ne~↑! X in IdUℕₙ nt , IdUℕₙ nu
  ne~↑! (Id-UΠ x X) = let nt , nu = ne~↑! X in IdUΠₙ nt , IdUΠₙ nu
  ne~↑! (cast-cong X x x₁ x₂ x₃) = let nt , nu = ne~↑! X in castₙ nt , castₙ nu
  ne~↑! (cast-ℕ X x x₁ x₂) = let nt , nu = ne~↑! X in castℕₙ nt , castℕₙ nu
  ne~↑! (cast-ℕℕ X x x₁) = let nt , nu = ne~↑! X in castℕℕₙ nt , castℕℕₙ nu
  ne~↑! (cast-Π x X x₁ x₂ x₃) = let nt , nu = ne~↑! X in castΠₙ nt , castΠₙ nu
  ne~↑! (cast-Πℕ x x₁ x₂ x₃) = castΠℕₙ , castΠℕₙ
  ne~↑! (cast-ℕΠ x x₁ x₂ x₃) = castℕΠₙ , castℕΠₙ
  ne~↑! (cast-ΠΠ%! x x₁ x₂ x₃ x₄) = castΠΠ%!ₙ , castΠΠ%!ₙ 
  ne~↑! (cast-ΠΠ!% x x₁ x₂ x₃ x₄) = castΠΠ!%ₙ , castΠΠ!%ₙ

  ne~↓! : ∀ {t u A Γ l}
        → Γ ⊢ t ~ u ↓! A ^ l
        → Whnf A × Neutral t × Neutral u
  ne~↓! ([~] A r D whnfB k~l) = whnfB , ne~↑! k~l

-- Extraction of WHNF from algorithmic equality of types in WHNF.
whnfConv↓ : ∀ {A B rA Γ}
          → Γ ⊢ A [conv↓] B ^ rA
          → Whnf A × Whnf B
whnfConv↓ (U-refl _ _ x) = Uₙ , Uₙ
whnfConv↓ (ℕ-refl x) = ℕₙ , ℕₙ
whnfConv↓ (Empty-refl x) = Emptyₙ , Emptyₙ
whnfConv↓ (ne x) = let _ , neA , neB = ne~↓! x
                   in  ne neA , ne neB
whnfConv↓ (Π-cong _ x x₁ x₂) = Πₙ , Πₙ

-- Extraction of WHNF from algorithmic equality of terms in WHNF.
whnfConv↓Term : ∀ {t u A Γ l}
              → Γ ⊢ t [conv↓] u ∷ A ^ l
              → Whnf A × Whnf t × Whnf u
whnfConv↓Term (ℕ-ins x) = let _ , neT , neU = ne~↓! x
                          in ℕₙ , ne neT , ne neU
-- whnfConv↓Term (Empty-ins x) = let _ , neT , neU = ne~↓% x
--                           in Emptyₙ , ne neT , ne neU
whnfConv↓Term (ne-ins t u x x₁) =
  let _ , neT , neU = ne~↓! x₁
  in ne x , ne neT , ne neU
whnfConv↓Term (univ x x₁ x₂) = Uₙ , whnfConv↓ x₂
whnfConv↓Term (zero-refl x) = ℕₙ , zeroₙ , zeroₙ
whnfConv↓Term (suc-cong x) = ℕₙ , sucₙ , sucₙ
whnfConv↓Term (η-eq x x₁ x₂ y y₁ x₃) = Πₙ , functionWhnf y , functionWhnf y₁
