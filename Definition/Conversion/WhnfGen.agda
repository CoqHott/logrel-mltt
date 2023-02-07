{-# OPTIONS --safe #-}

module Definition.Conversion.WhnfGen where

open import Definition.Untyped
open import Definition.Typed
open import Definition.ConversionGen
open import Definition.Typed.Consequences.Inversion

open import Tools.Product

mutual
  -- Extraction of neutrality from algorithmic equality of neutrals.
  ne~↑! : ∀ {t u A Γ l}
       → Γ ⊢⊢ t ~ u ↑! A ^ l
       → Neutral t × Neutral u
  ne~↑! (var-refl x₁ x≡y) = var _ , var _
  ne~↑! (app-cong x x₁) = let _ , q , w = ne~↓! x
                         in  ∘ₙ q , ∘ₙ w
  ne~↑! (natrec-cong x x₁ x₂ x₃) = let _ , q , w = ne~↓! x₃
                                  in  natrecₙ q , natrecₙ w
  ne~↑! (Emptyrec-cong x x₁) = Emptyrecₙ , Emptyrecₙ
  ne~↑! (cast-cong X x x₁ x₂ x₃ neCast neCast') = neCast , neCast'
  ne~↑! (cast-refl x x₁ x₂ neCast neCast') =  neCast , neCast'
  ne~↑! (cast-refl' x x₁ x₂ neCast neCast') = neCast' , neCast

  ne~↓! : ∀ {t u A Γ l}
        → Γ ⊢⊢ t ~ u ↓! A ^ l
        → Whnf A × Neutral t × Neutral u
  ne~↓! ([~] A D whnfB k~l) = whnfB , ne~↑! k~l

-- Extraction of WHNF from algorithmic equality of terms in WHNF.
  whnfConv↓Term : ∀ {t u A Γ l}
                → Γ ⊢⊢ t [conv↓] u ∷ A ^ l
                → Whnf A × Whnf t × Whnf u
  whnfConv↓Term (ℕ-ins x) = let _ , neT , neU = ne~↓! x
                            in ℕₙ , ne neT , ne neU
  whnfConv↓Term (ne x) = let wA , nt , nu = ne~↓! x in wA , ne nt , ne nu
  whnfConv↓Term (ne-ins t u x x₁) =
    let _ , neT , neU = ne~↓! x₁
    in ne x , ne neT , ne neU
  whnfConv↓Term (ℕ-refl x) = Uₙ , ℕₙ , ℕₙ
  whnfConv↓Term (Empty-refl x) = Uₙ , Emptyₙ , Emptyₙ
  whnfConv↓Term (Π-cong _ _ _ _ _ _ x₁ x₂) = Uₙ , Πₙ , Πₙ
  whnfConv↓Term (Id-cong x x₁ x₂) = Uₙ , Idₙ , Idₙ
  whnfConv↓Term (U-refl _ _) = Uₙ , Uₙ , Uₙ
  whnfConv↓Term (zero-refl x) = ℕₙ , zeroₙ , zeroₙ
  whnfConv↓Term (suc-cong x) = ℕₙ , sucₙ , sucₙ
  whnfConv↓Term (η-eq _ _ x x₁ x₂ y y₁ x₃) = Πₙ , functionWhnf y , functionWhnf y₁
  
  -- Extraction of WHNF from algorithmic equality of types in WHNF.
  whnfConv↓ : ∀ {A B rA Γ}
            → Γ ⊢⊢ A [conv↓] B ^ rA
            → Whnf A × Whnf B
  whnfConv↓ (U-refl _ _) = Uₙ , Uₙ
  whnfConv↓ (univ x₂) = let _ , A , B = whnfConv↓Term x₂ in A , B
  

-- Extraction of Neutrals from algorithmic equality of terms in WHNF, when the type is neutral.
  whnfConv↓TermNe : ∀ {t u A Γ l}
                → Neutral A
                → Γ ⊢⊢ t [conv↓] u ∷ A ^ l
                → Neutral t × Neutral u
  whnfConv↓TermNe neA (ne-ins x x₁ x₂ x₃) =
    let _ , neT , neU = ne~↓! x₃
    in neT , neU
