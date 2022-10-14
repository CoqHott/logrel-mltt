{-# OPTIONS --sized-types #-}

module Definition.Conversion.Whnf where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Conversion
open import Definition.Typed.Consequences.Inversion

open import Tools.Product


mutual
  -- Extraction of neutrality from algorithmic equality of neutrals.
  ne~↑! : ∀ {size t u A Γ l}
       → Γ # size ⊢ t ~ u ↑! A ^ l
       → Neutral t × Neutral u
  ne~↑! (var-refl x₁ x≡y) = var _ , var _
  ne~↑! (app-cong x x₁) = let _ , q , w = ne~↓! x
                         in  ∘ₙ q , ∘ₙ w
  ne~↑! (natrec-cong x x₁ x₂ x₃) = let _ , q , w = ne~↓! x₃
                                  in  natrecₙ q , natrecₙ w
  ne~↑! (Emptyrec-cong x x₁) = Emptyrecₙ , Emptyrecₙ
  ne~↑! (Id-cong X x x₁) = let _ , nt , nu = ne~↓! X in Idₙ nt , Idₙ nu
  ne~↑! (Id-ℕ X x) = let _ , nt , nu = ne~↓! X in Idℕₙ nt , Idℕₙ nu
  ne~↑! (Id-ℕ0 X) = let _ , nt , nu = ne~↓! X in Idℕ0ₙ nt , Idℕ0ₙ nu
  ne~↑! (Id-ℕS x X) = let _ , nt , nu = ne~↓! X in IdℕSₙ nt , IdℕSₙ nu
  ne~↑! (Id-U X x) = let _ , nt , nu = ne~↓! X in IdUₙ nt , IdUₙ nu
  ne~↑! (Id-Uℕ X) = let _ , nt , nu = ne~↓! X in IdUℕₙ nt , IdUℕₙ nu
  ne~↑! (Id-UΠ x X) = let _ , nt , nu = ne~↓! X in IdUΠₙ nt , IdUΠₙ nu
  ne~↑! (cast-cong X x ⊢t ⊢t' x₁ x₂ x₃) =
    let _ , nX , nX' = ne~↓! X
        _ , nx , nx' = ne~↓! x
        _ , nt , nt' = whnfConv↓Term x₁
    in castₙ nX nx (inversion-ne nX nt ⊢t) , castₙ nX' nx' (inversion-ne nX' nt' ⊢t')
  ne~↑! (cast-ℕ X x x₁ x₂) = let _ , nt , nu = ne~↓! X in castℕₙ nt , castℕₙ nu
  ne~↑! (cast-ℕℕ X x x₁) = let _ , nt , nu = ne~↓! X in castℕℕₙ nt , castℕℕₙ nu
  ne~↑! (cast-Π x X x₁ x₂ x₃) = let _ , nt , nu = ne~↓! X in castΠₙ nt , castΠₙ nu
  ne~↑! (cast-Πℕ x x₁ x₂ x₃) = castΠℕₙ , castΠℕₙ
  ne~↑! (cast-ℕΠ x x₁ x₂ x₃) = castℕΠₙ , castℕΠₙ
  ne~↑! (cast-ΠΠ%! x x₁ x₂ x₃ x₄) = castΠΠ%!ₙ , castΠΠ%!ₙ
  ne~↑! (cast-ΠΠ!% x x₁ x₂ x₃ x₄) = castΠΠ!%ₙ , castΠΠ!%ₙ
  ne~↑! (cast-refl x ⊢t ⊢t' x₁ x₂) =
    let _ , nA , nB = ne~↓! x
        _ , nt , nt' = whnfConv↓Term x₁
     in castₙ nA nB (inversion-ne nA nt ⊢t) , inversion-ne nA nt' ⊢t'
  ne~↑! (castℕ-refl x x₁) = let _ , nt , nu = ne~↓! x in castℕℕₙ nt , nu
  ne~↑! (cast-refl' x ⊢t ⊢t' x₁ x₂) =
    let _ , nA , nB = ne~↓! x
        _ , nt , nt' = whnfConv↓Term x₁
    in inversion-ne nA nt ⊢t , castₙ nA nB (inversion-ne nA nt' ⊢t')
  ne~↑! (castℕ-refl' x x₁) = let _ , nt , nu = ne~↓! x in nt , castℕℕₙ nu
  ne~↑! (cast-neℕ x x₁ x₂ x₃) = let _ , nA , nB = ne~↓! x in castnℕₙ nA , castnℕₙ nB
  ne~↑! (cast-neΠ x x₁ x₂ x₃ x₄) = let _ , nA , nB = ne~↓! x₁ in castnΠₙ nA , castnΠₙ nB

  ne~↓! : ∀ {size t u A Γ l}
        → Γ # size ⊢ t ~ u ↓! A ^ l
        → Whnf A × Neutral t × Neutral u
  ne~↓! ([~] A D whnfB k~l) = whnfB , ne~↑! k~l

-- Extraction of WHNF from algorithmic equality of terms in WHNF.
  whnfConv↓Term : ∀ {t u A Γ l}
                → Γ ⊢ t [conv↓] u ∷ A ^ l
                → Whnf A × Whnf t × Whnf u
  whnfConv↓Term (ℕ-ins x) = let _ , neT , neU = ne~↓! x
                            in ℕₙ , ne neT , ne neU
  whnfConv↓Term (ne x) = let wA , nt , nu = ne~↓! x in wA , ne nt , ne nu
  whnfConv↓Term (ne-ins t u x x₁) =
    let _ , neT , neU = ne~↓! x₁
    in ne x , ne neT , ne neU
  whnfConv↓Term (ℕ-refl x) = Uₙ , ℕₙ , ℕₙ
  whnfConv↓Term (Empty-refl x) = Uₙ , Emptyₙ , Emptyₙ
  whnfConv↓Term (Π-cong _ _ _ _ _ _ x x₁ x₂) = Uₙ , Πₙ , Πₙ
  whnfConv↓Term (∃-cong x x₁ x₂) = Uₙ , ∃ₙ , ∃ₙ
  whnfConv↓Term (U-refl _ _) = Uₙ , Uₙ , Uₙ
  whnfConv↓Term (zero-refl x) = ℕₙ , zeroₙ , zeroₙ
  whnfConv↓Term (suc-cong x) = ℕₙ , sucₙ , sucₙ
  whnfConv↓Term (η-eq _ _ x x₁ x₂ y y₁ x₃) = Πₙ , functionWhnf y , functionWhnf y₁
  
  -- Extraction of WHNF from algorithmic equality of types in WHNF.
  whnfConv↓ : ∀ {A B rA Γ}
            → Γ ⊢ A [conv↓] B ^ rA
            → Whnf A × Whnf B
  whnfConv↓ (U-refl _ _) = Uₙ , Uₙ
  whnfConv↓ (univ x₂) = let _ , A , B = whnfConv↓Term x₂ in A , B
  
