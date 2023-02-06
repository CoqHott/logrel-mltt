-- Algorithmic equality.

{-# OPTIONS --safe #-}

module Definition.Conversion.ConversionGenEquiv where

open import Definition.Untyped
open import Definition.Typed

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Definition.Conversion
open import Definition.ConversionGen
open import Definition.Conversion.Whnf
open import Definition.Conversion.Soundness
open import Definition.Conversion.SoundnessGen as SG
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Inversion
open import Definition.Typed.Consequences.Equality
open import Definition.Typed.Consequences.Inequality
open import Definition.Typed.Properties
open import Definition.Conversion.Symmetry
open import Definition.Conversion.Stability

open import Tools.Empty


{-
mutual
  ⊢is⊢⊢~! : ∀ {Γ A t u l} → Γ ⊢ t ~ u ↑! A ^ l → Γ ⊢⊢ t ~ u ↑! A ^ l
  ⊢is⊢⊢~% : ∀ {Γ A t u l} → Γ ⊢ t ~ u ↑% A ^ l → Γ ⊢⊢ t ~ u ↑% A ^ l
  ⊢is⊢⊢~↓! : ∀ {Γ A t u l} → Γ ⊢ t ~ u ↓! A ^ l → Γ ⊢⊢ t ~ u ↓! A ^ l
  ⊢is⊢⊢~ : ∀ {Γ A t u l} → Γ ⊢ t ~ u ↑ A ^ l → Γ ⊢⊢ t ~ u ↑ A ^ l
  ⊢is⊢⊢conv↑ : ∀ {Γ A B l} → Γ ⊢ A [conv↑] B ^ l → Γ ⊢⊢ A [conv↑] B ^ l
  ⊢is⊢⊢conv↓ : ∀ {Γ A B l} → Γ ⊢ A [conv↓] B ^ l → Γ ⊢⊢ A [conv↓] B ^ l
  ⊢is⊢⊢conv↑Term : ∀ {Γ A t u l} → Γ ⊢ t [conv↑] u ∷ A ^ l → Γ ⊢⊢ t [conv↑] u ∷ A ^ l
  ⊢is⊢⊢conv↓Term : ∀ {Γ A t u l} → Γ ⊢ t [conv↓] u ∷ A ^ l → Γ ⊢⊢ t [conv↓] u ∷ A ^ l
  ⊢is⊢⊢genconv↑ : ∀ {Γ A t u l} → Γ ⊢ t [genconv↑] u ∷ A ^ l → Γ ⊢⊢ t [genconv↑] u ∷ A ^ l

  ⊢is⊢⊢~! (var-refl x x₁) = var-refl x x₁
  ⊢is⊢⊢~! (app-cong x x₁) = app-cong (⊢is⊢⊢~↓! x) (⊢is⊢⊢genconv↑ x₁)
  ⊢is⊢⊢~! (natrec-cong x x₁ x₂ x₃) = natrec-cong (⊢is⊢⊢conv↑ x) (⊢is⊢⊢conv↑Term x₁) (⊢is⊢⊢conv↑Term x₂) (⊢is⊢⊢~↓! x₃)
  ⊢is⊢⊢~! (Emptyrec-cong x x₁) = Emptyrec-cong (⊢is⊢⊢conv↑ x) (⊢is⊢⊢~% x₁)
  ⊢is⊢⊢~! (cast-cong x x₁ x₂ x₃ x₄) =
    let _ , neA , neA' = ne~↓! x
        _ , neB , neB' = ne~↓! x₁
        t=t = soundnessConv↓Term x₂
        ⊢A , ⊢t , ⊢t' = syntacticEqTerm t=t
        _ , net , net' = whnfConv↓Term x₂
    in cast-cong (ne (⊢is⊢⊢~↓! x)) (ne (⊢is⊢⊢~↓! x₁))
                 ([↑]ₜ _ _ _ (id ⊢A) (id ⊢t) (id ⊢t') (ne neA) net net' (⊢is⊢⊢conv↓Term x₂))
                 x₃ x₄ (castₙ neA neB' (inversion-ne neA net ⊢t))
                                           (castₙ neA' neB (inversion-ne neA net' ⊢t'))
  ⊢is⊢⊢~! (cast-refl x x₁ x₂) =
    let _ , neA , neA' = ne~↓! x
        t=t = soundnessConv↓Term x₁
        _ , ⊢t , ⊢t' = syntacticEqTerm t=t
        _ , net , net' = whnfConv↓Term x₁
    in cast-refl (ne (⊢is⊢⊢~↓! x)) (⊢is⊢⊢conv↓Term x₁) x₂ (castₙ neA neA' (inversion-ne neA net ⊢t))
  ⊢is⊢⊢~! (castℕ-refl x x₁) =
    let t=t = soundness~↓! x
        _ , ⊢t , ⊢t' = syntacticEqTerm t=t
        _ , net , net' = ne~↓! x
    in cast-refl (ℕ-refl (wfTerm ⊢t)) (ℕ-ins (⊢is⊢⊢~↓! x)) x₁ (castℕℕₙ net)
  ⊢is⊢⊢~! (cast-refl' x x₁ x₂) =
    let _ , neA , neA' = ne~↓! x
        t=t = soundnessConv↓Term x₁
        _ , ⊢t , ⊢t' = syntacticEqTerm t=t
        _ , net , net' = whnfConv↓Term x₁
    in cast-refl' (ne (⊢is⊢⊢~↓! x)) (⊢is⊢⊢conv↓Term x₁) x₂ (castₙ neA' neA (inversion-ne neA' net' ⊢t'))
  ⊢is⊢⊢~! (castℕ-refl' x x₁) =
    let t=t = soundness~↓! x
        _ , ⊢t , ⊢t' = syntacticEqTerm t=t
        _ , net , net' = ne~↓! x
    in cast-refl' (ℕ-refl (wfTerm ⊢t)) (ℕ-ins (⊢is⊢⊢~↓! x)) x₁ (castℕℕₙ net')
  ⊢is⊢⊢~! (cast-neℕ x x₁ x₂ x₃) =
    let _ , neA , neA' = ne~↓! x
        t=t = soundnessConv↑Term x₁
        _ , ⊢t , ⊢t' = syntacticEqTerm t=t
    in cast-cong (ne (⊢is⊢⊢~↓! x)) (ℕ-refl (wfTerm ⊢t)) (⊢is⊢⊢conv↑Term x₁) x₂ x₃
                 (castnℕₙ neA) (castnℕₙ neA')
  ⊢is⊢⊢~! (cast-ℕ x x₁ x₂ x₃) =
    let _ , neA , neA' = ne~↓! x
        t=t = soundnessConv↑Term x₁
        _ , ⊢t , ⊢t' = syntacticEqTerm t=t
        B , whnfB , B=B , x' = sym~↓! (reflConEq (wfTerm ⊢t)) x
        B=U = U≡A-whnf B=B whnfB
    in cast-cong (ℕ-refl (wfTerm ⊢t)) (ne (⊢is⊢⊢~↓! (PE.subst (λ X → _ ⊢ _ ~ _ ↓! X ^ ι ¹) B=U x'))) (⊢is⊢⊢conv↑Term x₁) x₂ x₃
                 (castℕₙ neA) (castℕₙ neA')
  ⊢is⊢⊢~! (cast-neΠ ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) x₁ x₂ x₃ x₄) =
    let _ , neA , neA' = ne~↓! x₁
        t=t = soundnessConv↑Term x₂
        _ , ⊢t , ⊢t' = syntacticEqTerm t=t
        Π=Π = whnfRed*Term d Πₙ
        Π=Π' = whnfRed*Term d′ Πₙ
        U=U = whnfRed* D Uₙ
    in cast-cong (ne (⊢is⊢⊢~↓! x₁))
                 (PE.subst₃ (λ X Y Z → _ ⊢⊢ X [conv↓] Y ∷ Z ^ ι ¹) (PE.sym Π=Π') (PE.sym Π=Π) (PE.sym  U=U)
                            (⊢is⊢⊢conv↓Term (symConv↓Term (reflConEq (wfTerm ⊢t)) t<>u)))
                 (⊢is⊢⊢conv↑Term x₂) x₃ x₄
                 (castnΠₙ neA) (castnΠₙ neA') 
  ⊢is⊢⊢~! (cast-Π x x₁ x₂ x₃ x₄) = {!!}
  ⊢is⊢⊢~! (cast-Πℕ x x₁ x₂ x₃) = {!!}
  ⊢is⊢⊢~! (cast-ℕΠ x x₁ x₂ x₃) = {!!}
  ⊢is⊢⊢~! (cast-ΠΠ%! ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
                     ([↑]ₜ B' t′' u′' D' d' d′' whnfB' whnft′' whnfu′' t<>u') x₂ x₃ x₄) =
    let Π=Π = whnfRed*Term d Πₙ
        Π=Π' = whnfRed*Term d′ Πₙ
        U=U = whnfRed* D Uₙ
        Π==Π = whnfRed*Term d' Πₙ
        Π==Π' = whnfRed*Term d′' Πₙ
        U==U = whnfRed* D' Uₙ
    in cast-cong (PE.subst₃ (λ X Y Z → _ ⊢⊢ X [conv↓] Y ∷ Z ^ ι ¹) (PE.sym Π=Π) (PE.sym Π=Π') (PE.sym U=U)
                            (⊢is⊢⊢conv↓Term t<>u))
                 (PE.subst₃ (λ X Y Z → _ ⊢⊢ X [conv↓] Y ∷ Z ^ ι ¹) (PE.sym Π==Π') (PE.sym Π==Π) (PE.sym U==U)
                            (⊢is⊢⊢conv↓Term (symConv↓Term (reflConEq (wfTerm x₃)) t<>u')))
                 (⊢is⊢⊢conv↑Term x₂) x₃ x₄ castΠΠ%!ₙ castΠΠ%!ₙ
  ⊢is⊢⊢~! (cast-ΠΠ!% ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
                     ([↑]ₜ B' t′' u′' D' d' d′' whnfB' whnft′' whnfu′' t<>u') x₂ x₃ x₄) =
    let Π=Π = whnfRed*Term d Πₙ
        Π=Π' = whnfRed*Term d′ Πₙ
        U=U = whnfRed* D Uₙ
        Π==Π = whnfRed*Term d' Πₙ
        Π==Π' = whnfRed*Term d′' Πₙ
        U==U = whnfRed* D' Uₙ
    in cast-cong (PE.subst₃ (λ X Y Z → _ ⊢⊢ X [conv↓] Y ∷ Z ^ ι ¹) (PE.sym Π=Π) (PE.sym Π=Π') (PE.sym U=U)
                            (⊢is⊢⊢conv↓Term t<>u))
                 (PE.subst₃ (λ X Y Z → _ ⊢⊢ X [conv↓] Y ∷ Z ^ ι ¹) (PE.sym Π==Π') (PE.sym Π==Π) (PE.sym U==U)
                            (⊢is⊢⊢conv↓Term (symConv↓Term (reflConEq (wfTerm x₃)) t<>u')))
                 (⊢is⊢⊢conv↑Term x₂) x₃ x₄ castΠΠ!%ₙ castΠΠ!%ₙ
  ⊢is⊢⊢~% (%~↑ ⊢k ⊢l) = %~↑ ⊢k ⊢l
  ⊢is⊢⊢~ (~↑! x) = ~↑! (⊢is⊢⊢~! x)
  ⊢is⊢⊢~ (~↑% x) = ~↑% (⊢is⊢⊢~% x)
  ⊢is⊢⊢~↓! ([~] A D whnfB k~l) = [~] A D whnfB (⊢is⊢⊢~! k~l)
  ⊢is⊢⊢conv↑ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) = [↑] A′ B′ D D′ whnfA′ whnfB′ (⊢is⊢⊢conv↓ A′<>B′)
  ⊢is⊢⊢conv↓ (U-refl x x₁) = U-refl x x₁
  ⊢is⊢⊢conv↓ (univ x) = univ (⊢is⊢⊢conv↓Term x)
  ⊢is⊢⊢conv↑Term ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) = [↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ (⊢is⊢⊢conv↓Term t<>u) 
  ⊢is⊢⊢conv↓Term X = {!!}
  ⊢is⊢⊢genconv↑ {l = [ ! , l ]} X = ⊢is⊢⊢conv↑Term X
  ⊢is⊢⊢genconv↑ {l = [ % , l ]} X = ⊢is⊢⊢~% X

-}

mutual
  ⊢⊢is⊢~! : ∀ {Γ A t u l} → Γ ⊢⊢ t ~ u ↑! A ^ l → Γ ⊢ t ~ u ↑! A ^ l
  ⊢⊢is⊢~% : ∀ {Γ A t u l} → Γ ⊢⊢ t ~ u ↑% A ^ l → Γ ⊢ t ~ u ↑% A ^ l
  ⊢⊢is⊢~↓! : ∀ {Γ A t u l} → Γ ⊢⊢ t ~ u ↓! A ^ l → Γ ⊢ t ~ u ↓! A ^ l
  ⊢⊢is⊢~ : ∀ {Γ A t u l} → Γ ⊢⊢ t ~ u ↑ A ^ l → Γ ⊢ t ~ u ↑ A ^ l
  ⊢⊢is⊢conv↑ : ∀ {Γ A B l} → Γ ⊢⊢ A [conv↑] B ^ l → Γ ⊢ A [conv↑] B ^ l
  ⊢⊢is⊢conv↓ : ∀ {Γ A B l} → Γ ⊢⊢ A [conv↓] B ^ l → Γ ⊢ A [conv↓] B ^ l
  ⊢⊢is⊢conv↑Term : ∀ {Γ A t u l} → Γ ⊢⊢ t [conv↑] u ∷ A ^ l → Γ ⊢ t [conv↑] u ∷ A ^ l
  ⊢⊢is⊢conv↓Term : ∀ {Γ A t u l} → Γ ⊢⊢ t [conv↓] u ∷ A ^ l → Γ ⊢ t [conv↓] u ∷ A ^ l
  ⊢⊢is⊢genconv↑ : ∀ {Γ A t u l} → Γ ⊢⊢ t [genconv↑] u ∷ A ^ l → Γ ⊢ t [genconv↑] u ∷ A ^ l

  ⊢⊢is⊢~! (var-refl x x₁) = var-refl x x₁
  ⊢⊢is⊢~! (app-cong x x₁) = {!!}
  ⊢⊢is⊢~! (natrec-cong x x₁ x₂ x₃) = {!!}
  ⊢⊢is⊢~! (Emptyrec-cong x x₁) = {!!}
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castₙ x₅ x₇ x₈) (castₙ x₆ x₉ x₁₀)) = {!!}
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castₙ x₅ x₇ x₈) (castnℕₙ x₆)) = ⊥-elim (ℕ≢ne! x₇ {!!})
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castₙ x₅ x₇ x₈) (castnΠₙ x₆)) = {!!}
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castₙ x₅ x₇ x₈) (castℕₙ x₆)) = {!!}
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castₙ x₅ x₇ x₈) (castΠₙ x₆)) = {!!}
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castₙ x₅ x₇ x₈) (castℕℕₙ x₆)) = {!!}
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castₙ x₅ x₇ x₈) castℕΠₙ) = {!!}
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castₙ x₅ x₇ x₈) castΠℕₙ) = {!!}
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castₙ x₅ x₇ x₈) castΠΠ%!ₙ) = {!!}
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castₙ x₅ x₇ x₈) castΠΠ!%ₙ) = {!!}
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castnℕₙ x₅) x₆) = {!!}
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castnΠₙ x₅) x₆) = {!!}
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castℕₙ x₅) x₆) = {!!}
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castΠₙ x₅) x₆) = {!!}
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castℕℕₙ x₅) x₆) = {!!}
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castℕΠₙ x₆) = {!!}
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠℕₙ x₆) = {!!}
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠΠ%!ₙ x₆) = {!!}
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠΠ!%ₙ x₆) = {!!}
  ⊢⊢is⊢~! (cast-refl x x₁ x₂ x₃) = {!!}
  ⊢⊢is⊢~! (cast-refl' x x₁ x₂ x₃) = {!!}
  ⊢⊢is⊢~% X = {!!}
  ⊢⊢is⊢~↓! X = {!!}
  ⊢⊢is⊢~ X = {!!}
  ⊢⊢is⊢conv↑ X = {!!}
  ⊢⊢is⊢conv↓ X = {!!}
  ⊢⊢is⊢conv↑Term X = {!!}
  ⊢⊢is⊢conv↓Term X = {!!}
  ⊢⊢is⊢genconv↑ X = {!!}

