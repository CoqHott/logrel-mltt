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
open import Definition.Conversion.Whnf as W
open import Definition.Conversion.WhnfGen as WG
open import Definition.Conversion.Soundness as S
open import Definition.Conversion.SoundnessGen as SG
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Inversion
open import Definition.Typed.Consequences.Equality
open import Definition.Typed.Consequences.TypeUnicity
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.Inequality as I
open import Definition.Typed.Properties
open import Definition.Conversion.Symmetry
open import Definition.Conversion.Stability

open import Tools.Empty

inversion-whnf-conv :  ∀ {Γ t t' A l} → Whnf A → Whnf t → Whnf t' → Γ ⊢⊢ t [conv↑] t' ∷ A ^ l → Γ ⊢⊢ t [conv↓] t' ∷ A ^ l
inversion-whnf-conv neA net net' ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) with whnfRed* D neA | whnfRed*Term d net | whnfRed*Term d′ net'
... | PE.refl | PE.refl | PE.refl = t<>u

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
    let _ , neA , neA' = W.ne~↓! x
        _ , neB , neB' = W.ne~↓! x₁
        t=t = S.soundnessConv↓Term x₂
        ⊢A , ⊢t , ⊢t' = syntacticEqTerm t=t
        _ , net , net' = W.whnfConv↓Term x₂
    in cast-cong (ne (⊢is⊢⊢~↓! x)) (ne (⊢is⊢⊢~↓! x₁))
                 ([↑]ₜ _ _ _ (id ⊢A) (id ⊢t) (id ⊢t') (ne neA) net net' (⊢is⊢⊢conv↓Term x₂))
                 x₃ x₄ (castₙ neA neB' (inversion-ne neA net ⊢t))
                                           (castₙ neA' neB (inversion-ne neA net' ⊢t'))
  ⊢is⊢⊢~! (cast-refl x x₁ x₂) =
    let _ , neA , neA' = W.ne~↓! x
        t=t = S.soundnessConv↓Term x₁
        _ , ⊢t , ⊢t' = syntacticEqTerm t=t
        _ , net , net' = W.whnfConv↓Term x₁
    in cast-refl (ne (⊢is⊢⊢~↓! x)) (⊢is⊢⊢conv↓Term x₁) x₂ (castₙ neA neA' (inversion-ne neA net ⊢t)) (inversion-ne neA net' ⊢t')
  ⊢is⊢⊢~! (castℕ-refl x x₁) =
    let t=t = S.soundness~↓! x
        _ , ⊢t , ⊢t' = syntacticEqTerm t=t
        _ , net , net' = W.ne~↓! x
    in cast-refl (ℕ-refl (wfTerm ⊢t)) (ℕ-ins (⊢is⊢⊢~↓! x)) x₁ (castℕℕₙ net) net'
  ⊢is⊢⊢~! (cast-refl' x x₁ x₂) =
    let _ , neA , neA' = W.ne~↓! x
        t=t = S.soundnessConv↓Term x₁
        _ , ⊢t , ⊢t' = syntacticEqTerm t=t
        _ , net , net' = W.whnfConv↓Term x₁
    in cast-refl' (ne (⊢is⊢⊢~↓! x)) (⊢is⊢⊢conv↓Term x₁) x₂ (castₙ neA' neA (inversion-ne neA' net' ⊢t')) (inversion-ne neA' net ⊢t)
  ⊢is⊢⊢~! (castℕ-refl' x x₁) =
    let t=t = S.soundness~↓! x
        _ , ⊢t , ⊢t' = syntacticEqTerm t=t
        _ , net , net' = W.ne~↓! x
    in cast-refl' (ℕ-refl (wfTerm ⊢t)) (ℕ-ins (⊢is⊢⊢~↓! x)) x₁ (castℕℕₙ net') net
  ⊢is⊢⊢~! (cast-neℕ x x₁ x₂ x₃) =
    let _ , neA , neA' = W.ne~↓! x
        t=t = S.soundnessConv↑Term x₁
        _ , ⊢t , ⊢t' = syntacticEqTerm t=t
    in cast-cong (ne (⊢is⊢⊢~↓! x)) (ℕ-refl (wfTerm ⊢t)) (⊢is⊢⊢conv↑Term x₁) x₂ x₃
                 (castnℕₙ neA) (castnℕₙ neA')
  ⊢is⊢⊢~! (cast-ℕ x x₁ x₂ x₃) =
    let _ , neA , neA' = W.ne~↓! x
        t=t = S.soundnessConv↑Term x₁
        _ , ⊢t , ⊢t' = syntacticEqTerm t=t
    in cast-cong (ℕ-refl (wfTerm ⊢t)) (ne (⊢is⊢⊢~↓! x)) (⊢is⊢⊢conv↑Term x₁) x₂ x₃
                 (castℕₙ neA') (castℕₙ neA)
  ⊢is⊢⊢~! (cast-neΠ ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) x₁ x₂ x₃ x₄) =
    let _ , neA , neA' = W.ne~↓! x₁
        t=t = S.soundnessConv↑Term x₂
        _ , ⊢t , ⊢t' = syntacticEqTerm t=t
        Π=Π = whnfRed*Term d Πₙ
        Π=Π' = whnfRed*Term d′ Πₙ
        U=U = whnfRed* D Uₙ
    in cast-cong (ne (⊢is⊢⊢~↓! x₁))
                 (PE.subst₃ (λ X Y Z → _ ⊢⊢ X [conv↓] Y ∷ Z ^ ι ¹) (PE.sym Π=Π) (PE.sym Π=Π') (PE.sym U=U)
                            (⊢is⊢⊢conv↓Term t<>u))
                 (⊢is⊢⊢conv↑Term x₂) x₃ x₄
                 (castnΠₙ neA) (castnΠₙ neA') 
  ⊢is⊢⊢~! (cast-Π x x₁ x₂ x₃ x₄) =
    let _ , neA , neA' = W.ne~↓! x₁
    in cast-cong (inversion-whnf-conv Uₙ Πₙ Πₙ (⊢is⊢⊢conv↑Term x)) (ne (⊢is⊢⊢~↓! x₁)) (⊢is⊢⊢conv↑Term x₂) x₃ x₄ (castΠₙ neA') (castΠₙ neA)
  ⊢is⊢⊢~! (cast-Πℕ x x₁ x₂ x₃) = cast-cong (inversion-whnf-conv Uₙ Πₙ Πₙ (⊢is⊢⊢conv↑Term x)) (ℕ-refl (wfTerm x₂)) (⊢is⊢⊢conv↑Term x₁) x₂ x₃ castΠℕₙ castΠℕₙ
  ⊢is⊢⊢~! (cast-ℕΠ x x₁ x₂ x₃) = cast-cong (ℕ-refl (wfTerm x₂)) (inversion-whnf-conv Uₙ Πₙ Πₙ (⊢is⊢⊢conv↑Term x)) (⊢is⊢⊢conv↑Term x₁) x₂ x₃ castℕΠₙ castℕΠₙ
  ⊢is⊢⊢~! (cast-ΠΠ%! ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
                     ([↑]ₜ B' t′' u′' D' d' d′' whnfB' whnft′' whnfu′' t<>u') x₂ x₃ x₄) =
    let Π=Π = whnfRed*Term d Πₙ
        Π=Π' = whnfRed*Term d′ Πₙ
        U=U = whnfRed* D Uₙ
        Π==Π = whnfRed*Term d' Πₙ
        Π==Π' = whnfRed*Term d′' Πₙ
        U==U = whnfRed* D' Uₙ
        foo = ⊢is⊢⊢conv↓Term t<>u' 
    in cast-cong (PE.subst₃ (λ X Y Z → _ ⊢⊢ X [conv↓] Y ∷ Z ^ ι ¹) (PE.sym Π=Π) (PE.sym Π=Π') (PE.sym U=U)
                            (⊢is⊢⊢conv↓Term t<>u))
                  (PE.subst₃ (λ X Y Z → _ ⊢⊢ X [conv↓] Y ∷ Z ^ ι ¹) (PE.sym Π==Π) (PE.sym Π==Π') (PE.sym U==U) foo)
                 (⊢is⊢⊢conv↑Term x₂) x₃ x₄ castΠΠ%!ₙ castΠΠ%!ₙ
  ⊢is⊢⊢~! (cast-ΠΠ!% ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
                     ([↑]ₜ B' t′' u′' D' d' d′' whnfB' whnft′' whnfu′' t<>u') x₂ x₃ x₄) = 
    let Π=Π = whnfRed*Term d Πₙ
        Π=Π' = whnfRed*Term d′ Πₙ
        U=U = whnfRed* D Uₙ
        Π==Π = whnfRed*Term d' Πₙ
        Π==Π' = whnfRed*Term d′' Πₙ
        U==U = whnfRed* D' Uₙ
        foo = ⊢is⊢⊢conv↓Term t<>u'
    in cast-cong (PE.subst₃ (λ X Y Z → _ ⊢⊢ X [conv↓] Y ∷ Z ^ ι ¹) (PE.sym Π=Π) (PE.sym Π=Π') (PE.sym U=U)
                            (⊢is⊢⊢conv↓Term t<>u))
                 (PE.subst₃ (λ X Y Z → _ ⊢⊢ X [conv↓] Y ∷ Z ^ ι ¹) (PE.sym Π==Π) (PE.sym Π==Π') (PE.sym U==U) foo)
                 (⊢is⊢⊢conv↑Term x₂) x₃ x₄ castΠΠ!%ₙ castΠΠ!%ₙ 
  ⊢is⊢⊢~% (%~↑ ⊢k ⊢l) = %~↑ ⊢k ⊢l
  ⊢is⊢⊢~ (~↑! x) = ~↑! (⊢is⊢⊢~! x)
  ⊢is⊢⊢~ (~↑% x) = ~↑% (⊢is⊢⊢~% x)
  ⊢is⊢⊢~↓! ([~] A D whnfB k~l) = [~] A D whnfB (⊢is⊢⊢~! k~l)
  ⊢is⊢⊢conv↑ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) = [↑] A′ B′ D D′ whnfA′ whnfB′ (⊢is⊢⊢conv↓ A′<>B′)
  ⊢is⊢⊢conv↓ (U-refl x x₁) = U-refl x x₁
  ⊢is⊢⊢conv↓ (univ x) = univ (⊢is⊢⊢conv↓Term x)
  ⊢is⊢⊢conv↑Term ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) = [↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ (⊢is⊢⊢conv↓Term t<>u) 
  ⊢is⊢⊢conv↓Term (U-refl x x₁) = U-refl x x₁
  ⊢is⊢⊢conv↓Term (ne x) = ne (⊢is⊢⊢~↓! x)
  ⊢is⊢⊢conv↓Term (ℕ-refl x) = ℕ-refl x
  ⊢is⊢⊢conv↓Term (Empty-refl x) = Empty-refl x
  ⊢is⊢⊢conv↓Term (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = Π-cong x x₁ x₂ x₃ x₄ x₅ (⊢is⊢⊢conv↑Term x₇) (⊢is⊢⊢conv↑Term x₈)
  ⊢is⊢⊢conv↓Term (Id-cong x x₁ x₂) = Id-cong (⊢is⊢⊢conv↑Term x) (⊢is⊢⊢conv↑Term x₁) (⊢is⊢⊢conv↑Term x₂)
  ⊢is⊢⊢conv↓Term (ℕ-ins x) = ℕ-ins (⊢is⊢⊢~↓! x)
  ⊢is⊢⊢conv↓Term (ne-ins x x₁ x₂ x₃) = ne-ins x x₁ x₂ (⊢is⊢⊢~↓! x₃)
  ⊢is⊢⊢conv↓Term (zero-refl x) = zero-refl x
  ⊢is⊢⊢conv↓Term (suc-cong x) = suc-cong (⊢is⊢⊢conv↑Term x)
  ⊢is⊢⊢conv↓Term (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) = η-eq x x₁ x₂ x₃ x₄ x₅ x₆ (⊢is⊢⊢conv↑Term x₇)
  ⊢is⊢⊢genconv↑ {l = [ ! , l ]} X = ⊢is⊢⊢conv↑Term X
  ⊢is⊢⊢genconv↑ {l = [ % , l ]} X = ⊢is⊢⊢~% X

inversion-ne-U :  ∀ {Γ A A' r l lU} → Neutral A → Γ ⊢ A [conv↓] A' ∷ Univ r lU ^ l →  Γ ⊢ A ~ A' ↓! Univ r lU ^ l
inversion-ne-U neA (ne x) = x

inversion-whnf-conv' :  ∀ {Γ t t' A l} → Whnf A → Whnf t → Whnf t' → Γ ⊢ t [conv↑] t' ∷ A ^ l → Γ ⊢ t [conv↓] t' ∷ A ^ l
inversion-whnf-conv' neA net net' ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) with whnfRed* D neA | whnfRed*Term d net | whnfRed*Term d′ net'
... | PE.refl | PE.refl | PE.refl = t<>u

inversion-ne-ℕ :  ∀ {Γ t u l} → Neutral t → Neutral u → Γ ⊢ t [conv↓] u ∷ ℕ ^ l →  Γ ⊢ t ~ u ↓! ℕ ^ l
inversion-ne-ℕ net neu (ℕ-ins x) = x

injectivityGen : ∀ {Γ F G H E rF lF lH lG lE rH lΠ r r'} →
              Γ ⊢ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ r ≡ Π H ^ rH ° lH ▹ E ° lE ° lΠ ^ r' ^ [ ! , ι lΠ ]
            → Γ ⊢ F ≡ H ^ [ rF , ι lF ]
            × rF PE.≡ rH
            × lF PE.≡ lH
            × lG PE.≡ lE
            × Γ ∙ F ^ [ rF , ι lF ] ⊢ G ≡ E ^ [ ! , ι lG ]
            × r PE.≡ !
            × r' PE.≡ !
injectivityGen Π=Π =
    let _ , ⊢Π , ⊢Π' = syntacticEqTerm (un-univ≡ Π=Π)
        rG , _ , _ , _ , _ , U=U , err , _ = inversion-Π ⊢Π
        r=r , _ = Univ-PE-injectivity (U≡A-whnf U=U Uₙ)
        rG' , _ , _ , _ , _ , U=U' , err' , _ = inversion-Π ⊢Π'
        r=r' , _ = Univ-PE-injectivity (U≡A-whnf U=U' Uₙ)
        eqr = PE.trans (PE.sym err) r=r
        eqr' = PE.trans (PE.sym err') r=r'
        a , b , c , d , e = injectivity (PE.subst₂ (λ X Y → _ ⊢ Π _ ^ _ ° _ ▹ _ ° _ ° _ ^ X ≡  Π _ ^ _ ° _ ▹ _ ° _ ° _ ^ Y ^ [ ! , ι _ ]) eqr eqr' Π=Π)
     in a , b , c , d , e , eqr , eqr'

0ismin : ∀ {l} → l ≤ ⁰ → l PE.≡ ⁰ 
0ismin (≡is≤ e) = e

injectivityGen0 : ∀ {Γ F G H E rF lF lH lG lE rH r r'} →
              Γ ⊢ Π F ^ rF ° lF ▹ G ° lG ° ⁰ ^ r ≡ Π H ^ rH ° lH ▹ E ° lE ° ⁰ ^ r' ^ [ ! , ι ⁰ ]
            → Γ ⊢ F ≡ H ^ [ rF , ι lF ]
            × rF PE.≡ rH
            × lF PE.≡ ⁰
            × lH PE.≡ ⁰
            × lG PE.≡ ⁰
            × lE PE.≡ ⁰
            × Γ ∙ F ^ [ rF , ι lF ] ⊢ G ≡ E ^ [ ! , ι lG ]
            × r PE.≡ !
            × r' PE.≡ !
injectivityGen0 Π=Π = 
  let a , b , c , d , e , f , g  = injectivityGen Π=Π
      ⊢Π , ⊢Π' = syntacticEq Π=Π
      _ , er , _ , _ , _ , _ , er' , _ = inversion-Π (un-univ ⊢Π)
      elF , elG = er (PE.trans er' f)
      _ , er'' , _ , _ , _ , _ , er''' , _ = inversion-Π (un-univ ⊢Π')
      elF' , elG' = er'' (PE.trans er''' g)
  in a , b , 0ismin elF , 0ismin elF' , 0ismin elG , 0ismin elG' , e , f , g

subst7 : ∀ {A B C D E F G : Set} {a a′ b b′ c c′ d d′ e e′ f f′ g g′} (F : A → B → C → D → E → F → G → Set)
       → a PE.≡ a′ → b PE.≡ b′ → c PE.≡ c′ → d PE.≡ d′ → e PE.≡ e′ → f PE.≡ f′ → g PE.≡ g′ → F a b c d e f g → F a′ b′ c′ d′ e′ f′ g′
subst7 F PE.refl PE.refl PE.refl PE.refl PE.refl PE.refl PE.refl f = f

mutual
  ⊢⊢is⊢~! : ∀ {Γ A t u l} → Γ ⊢⊢ t ~ u ↑! A ^ l → Γ ⊢ t ~ u ↑! A ^ l
  ⊢⊢is⊢~% : ∀ {Γ A t u l} → Γ ⊢⊢ t ~ u ↑% A ^ l → Γ ⊢ t ~ u ↑% A ^ l
  ⊢⊢is⊢~↓! : ∀ {Γ A t u l} → Γ ⊢⊢ t ~ u ↓! A ^ l → Γ ⊢ t ~ u ↓! A ^ l
  ⊢⊢is⊢conv↑ : ∀ {Γ A B l} → Γ ⊢⊢ A [conv↑] B ^ l → Γ ⊢ A [conv↑] B ^ l
  ⊢⊢is⊢conv↓ : ∀ {Γ A B l} → Γ ⊢⊢ A [conv↓] B ^ l → Γ ⊢ A [conv↓] B ^ l
  ⊢⊢is⊢conv↑Term : ∀ {Γ A t u l} → Γ ⊢⊢ t [conv↑] u ∷ A ^ l → Γ ⊢ t [conv↑] u ∷ A ^ l
  ⊢⊢is⊢conv↓Term : ∀ {Γ A t u l} → Γ ⊢⊢ t [conv↓] u ∷ A ^ l → Γ ⊢ t [conv↓] u ∷ A ^ l
  ⊢⊢is⊢genconv↑ : ∀ {Γ A t u l} → Γ ⊢⊢ t [genconv↑] u ∷ A ^ l → Γ ⊢ t [genconv↑] u ∷ A ^ l

  ⊢⊢is⊢~! (var-refl x x₁) = var-refl x x₁
  ⊢⊢is⊢~! (app-cong x x₁) = app-cong (⊢⊢is⊢~↓! x) (⊢⊢is⊢genconv↑ x₁) 
  ⊢⊢is⊢~! (natrec-cong x x₁ x₂ x₃) = natrec-cong (⊢⊢is⊢conv↑ x) (⊢⊢is⊢genconv↑ x₁) (⊢⊢is⊢genconv↑ x₂) (⊢⊢is⊢~↓! x₃)
  ⊢⊢is⊢~! (Emptyrec-cong x x₁) = Emptyrec-cong (⊢⊢is⊢conv↑ x)  (⊢⊢is⊢~% x₁)

  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castₙ x₅ x₇ x₈) (castₙ x₆ x₉ x₁₀)) =
    cast-cong (inversion-ne-U x₅ (⊢⊢is⊢conv↓Term x)) (inversion-ne-U x₉ (⊢⊢is⊢conv↓Term x₁)) (inversion-whnf-conv' (ne x₅) (ne x₈) (ne x₁₀) (⊢⊢is⊢conv↑Term x₂)) x₃ x₄
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castₙ x₅ x₇ x₈) (castnℕₙ x₆)) = ⊥-elim (ℕ≢ne! x₇ (univ (SG.soundnessConv↓Term x₁)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castₙ x₅ x₇ x₈) (castnΠₙ x₆)) = ⊥-elim (I.Π≢ne x₇ (univ (SG.soundnessConv↓Term x₁)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castₙ x₅ x₇ x₈) (castℕₙ x₆)) = ⊥-elim (ℕ≢ne! x₅ (sym (univ (SG.soundnessConv↓Term x))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castₙ x₅ x₇ x₈) (castΠₙ x₆)) = ⊥-elim (I.Π≢ne x₅ (univ (sym (SG.soundnessConv↓Term x))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castₙ x₅ x₇ x₈) (castℕℕₙ x₆)) = ⊥-elim (ℕ≢ne! x₇ (univ (SG.soundnessConv↓Term x₁)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castₙ x₅ x₇ x₈) castℕΠₙ) = ⊥-elim (ℕ≢ne! x₅ (sym (univ (SG.soundnessConv↓Term x))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castₙ x₅ x₇ x₈) castΠℕₙ) = ⊥-elim (ℕ≢ne! x₇ (univ (SG.soundnessConv↓Term x₁)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castₙ x₅ x₇ x₈) castΠΠ%!ₙ) = ⊥-elim (I.Π≢ne x₇ (univ (SG.soundnessConv↓Term x₁)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castₙ x₅ x₇ x₈) castΠΠ!%ₙ) = ⊥-elim (I.Π≢ne x₇ (univ (SG.soundnessConv↓Term x₁)))

  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castnℕₙ x₅) (castₙ x₆ x₇ x₈)) = ⊥-elim (ℕ≢ne! x₇ (sym (univ (SG.soundnessConv↓Term x₁))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castnℕₙ x₅) (castnℕₙ x₆)) = cast-neℕ (inversion-ne-U x₅ (⊢⊢is⊢conv↓Term x)) (⊢⊢is⊢conv↑Term x₂) x₃ x₄
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castnℕₙ x₅) (castnΠₙ x₆)) = ⊥-elim (ℕ≢Π! (sym (univ (SG.soundnessConv↓Term x₁))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castnℕₙ x₅) (castℕₙ x₆)) = ⊥-elim (ℕ≢ne! x₅ (univ (sym (SG.soundnessConv↓Term x))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castnℕₙ x₅) (castΠₙ x₆)) = ⊥-elim (ℕ≢ne! x₆ (univ (sym (SG.soundnessConv↓Term x₁))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castnℕₙ x₅) (castℕℕₙ x₆)) = ⊥-elim (ℕ≢ne! x₅ (univ (sym (SG.soundnessConv↓Term x))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castnℕₙ x₅) castℕΠₙ) = ⊥-elim (ℕ≢ne! x₅ (univ (sym (SG.soundnessConv↓Term x))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castnℕₙ x₅) castΠℕₙ) = ⊥-elim (I.Π≢ne x₅ (univ (sym (SG.soundnessConv↓Term x))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castnℕₙ x₅) castΠΠ%!ₙ) = ⊥-elim (ℕ≢Π! (sym (univ (SG.soundnessConv↓Term x₁))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castnℕₙ x₅) castΠΠ!%ₙ) = ⊥-elim (ℕ≢Π! (sym (univ (SG.soundnessConv↓Term x₁))))

  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castnΠₙ x₅) (castₙ x₆ x₇ x₈)) = ⊥-elim (I.Π≢ne x₇ (univ (sym (SG.soundnessConv↓Term x₁))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castnΠₙ x₅) (castnℕₙ x₆)) = ⊥-elim (ℕ≢Π! (univ (SG.soundnessConv↓Term x₁)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castnΠₙ x₅) (castnΠₙ x₆)) =
    let Π=Π = univ (SG.soundnessConv↓Term x₁)
        _ , er , elF , elF' , elG , elG' ,  _ , er' , er'' = injectivityGen0 Π=Π
        foo = subst7 (λ X Y Z T U V W → _ ⊢ Π _ ^ X ° Y ▹ _ ° Z ° ⁰ ^ U [conv↓] Π _ ^ _ ° V ▹ _ ° W ° ⁰ ^ T ∷ _ ^ ι ¹)
                    er elF elG er'' er' elF' elG' 
                    (⊢⊢is⊢conv↓Term x₁)
        ⊢Π , ⊢Π' = syntacticEq Π=Π
    in subst7 (λ X Y Z T U V W → _ ⊢ cast ⁰ _ (Π _ ^ _ ° V ▹ _ ° W ° ⁰ ^ T) _ _ ~
      cast ⁰ _ (Π _ ^ X ° Y ▹ _ ° Z ° ⁰ ^ U) _ _ ↑!
      Π _ ^ _ ° V ▹ _ ° W ° ⁰ ^ T ^ ι ⁰) (PE.sym er) (PE.sym elF) (PE.sym elG) (PE.sym er'') (PE.sym  er') (PE.sym elF') (PE.sym elG')
      (cast-neΠ ([↑]ₜ _ _ _ (id (Ugenⱼ (wfTerm x₃)))
                      (id (un-univ (PE.subst₄  (λ X Y Z W → _ ⊢ Π _ ^ W ° X ▹ _ ° Y ° ⁰ ^ Z ^ [ _ , _ ]) elF elG er' er ⊢Π)))
                      (id (un-univ (PE.subst₃  (λ X Y Z → _ ⊢ Π _ ^ _ ° X ▹ _ ° Y ° ⁰ ^ Z ^ [ _ , _ ]) elF' elG' er'' ⊢Π')))
                      Uₙ Πₙ Πₙ foo)
                (inversion-ne-U x₅ (⊢⊢is⊢conv↓Term x))
                (⊢⊢is⊢conv↑Term x₂)
                (PE.subst₃  (λ X Y Z → _ ⊢ _ ∷ Id (U ⁰) _ (Π _ ^ _ ° X ▹ _ ° Y ° ⁰ ^ Z) ^ [ % , ι ⁰ ]) elF' elG' er'' x₃)
                (PE.subst₄  (λ X Y Z W → _ ⊢ _ ∷ Id (U ⁰) _ (Π _ ^ W ° X ▹ _ ° Y ° ⁰ ^ Z) ^ [ % , ι ⁰ ]) elF elG er' er x₄))                
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castnΠₙ x₅) (castℕₙ x₆)) = ⊥-elim (I.Π≢ne x₆ (univ (sym (SG.soundnessConv↓Term x₁))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castnΠₙ x₅) (castΠₙ x₆)) = ⊥-elim (I.Π≢ne x₅ (univ (sym (SG.soundnessConv↓Term x))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castnΠₙ x₅) (castℕℕₙ x₆)) = ⊥-elim (ℕ≢Π! (univ (SG.soundnessConv↓Term x₁)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castnΠₙ x₅) castℕΠₙ) = ⊥-elim (ℕ≢ne! x₅ (univ (sym (SG.soundnessConv↓Term x))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castnΠₙ x₅) castΠℕₙ) = ⊥-elim (I.Π≢ne x₅ (univ (sym (SG.soundnessConv↓Term x))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castnΠₙ x₅) castΠΠ%!ₙ) = ⊥-elim (I.Π≢ne x₅ (univ (sym (SG.soundnessConv↓Term x))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castnΠₙ x₅) castΠΠ!%ₙ) = ⊥-elim (I.Π≢ne x₅ (univ (sym (SG.soundnessConv↓Term x))))

  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castℕₙ x₅) (castₙ x₆ x₇ x₈)) = ⊥-elim (ℕ≢ne! x₆ (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castℕₙ x₅) (castnℕₙ x₆)) = ⊥-elim (ℕ≢ne! x₆ (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castℕₙ x₅) (castnΠₙ x₆)) = ⊥-elim (ℕ≢ne! x₆ (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castℕₙ x₅) (castℕₙ x₆)) = cast-ℕ (inversion-ne-U x₆ (⊢⊢is⊢conv↓Term x₁))  (⊢⊢is⊢conv↑Term x₂) x₃ x₄
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castℕₙ x₅) (castΠₙ x₆)) = ⊥-elim (ℕ≢Π! (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castℕₙ x₅) (castℕℕₙ x₆)) = ⊥-elim (ℕ≢ne! x₅ (univ (SG.soundnessConv↓Term x₁)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castℕₙ x₅) castℕΠₙ) = ⊥-elim (I.Π≢ne x₅ (univ (SG.soundnessConv↓Term x₁)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castℕₙ x₅) castΠℕₙ) = ⊥-elim (ℕ≢Π! (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castℕₙ x₅) castΠΠ%!ₙ) = ⊥-elim (ℕ≢Π! (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castℕₙ x₅) castΠΠ!%ₙ) = ⊥-elim (ℕ≢Π! (univ (SG.soundnessConv↓Term x)))

  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castΠₙ x₅) (castₙ x₆ x₇ x₈)) = ⊥-elim (I.Π≢ne x₆ (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castΠₙ x₅) (castnℕₙ x₆)) = ⊥-elim (I.Π≢ne x₆ (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castΠₙ x₅) (castnΠₙ x₆)) = ⊥-elim (I.Π≢ne x₅ (univ (SG.soundnessConv↓Term x₁)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castΠₙ x₅) (castℕₙ x₆)) = ⊥-elim (ℕ≢Π! (sym (univ (SG.soundnessConv↓Term x))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castΠₙ x₅) (castΠₙ x₆)) =
    let Π=Π = univ (SG.soundnessConv↓Term x)
        _ , er , elF , elF' , elG , elG' ,  _ , er' , er'' = injectivityGen0 Π=Π
        foo = subst7 (λ X Y Z T U V W → _ ⊢ Π _ ^ X ° Y ▹ _ ° Z ° ⁰ ^ U [conv↓] Π _ ^ _ ° V ▹ _ ° W ° ⁰ ^ T ∷ _ ^ ι ¹)
                    er elF elG er'' er' elF' elG' 
                    (⊢⊢is⊢conv↓Term x)
        ⊢Π , ⊢Π' = syntacticEq Π=Π
    in subst7 (λ X Y Z T U V W → _ ⊢ cast ⁰ (Π _ ^ X ° V ▹ _ ° W ° ⁰ ^ T) _ _ _ ~
                                     cast ⁰ (Π _ ^ _ ° Y ▹ _ ° Z ° ⁰ ^ U) _ _ _ ↑! _ ^ ι ⁰)
           (PE.sym er) (PE.sym elF') (PE.sym elG') (PE.sym er') (PE.sym er'') (PE.sym elF) (PE.sym elG)
      (cast-Π ([↑]ₜ _ _ _ (id (Ugenⱼ (wfTerm x₃)))
                      (id (un-univ (PE.subst₄  (λ X Y Z W → _ ⊢ Π _ ^ W ° X ▹ _ ° Y ° ⁰ ^ Z ^ [ _ , _ ]) elF elG er' er ⊢Π)))
                      (id (un-univ (PE.subst₃ (λ X Y Z → _ ⊢ Π _ ^ _ ° X ▹ _ ° Y ° ⁰ ^ Z ^ [ _ , _ ]) elF' elG' er'' ⊢Π')))
                      Uₙ Πₙ Πₙ foo)
                (inversion-ne-U x₆ (⊢⊢is⊢conv↓Term x₁))
                (PE.subst₄  (λ X Y Z W → _ ⊢ _ [conv↑] _ ∷ Π _ ^ W ° X ▹ _ ° Y ° ⁰ ^ Z ^ _) elF elG er' er (⊢⊢is⊢conv↑Term x₂))
                (PE.subst₄  (λ X Y Z W → _ ⊢ _ ∷ Id (U ⁰) (Π _ ^ W ° X ▹ _ ° Y ° ⁰ ^ Z) _ ^ [ % , ι ⁰ ]) elF elG er' er x₃)                
                (PE.subst₃  (λ X Y Z → _ ⊢ _ ∷ Id (U ⁰) (Π _ ^ _ ° X ▹ _ ° Y ° ⁰ ^ Z) _ ^ [ % , ι ⁰ ]) elF' elG' er'' x₄))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castΠₙ x₅) (castℕℕₙ x₆)) = ⊥-elim (ℕ≢Π! (sym (univ (SG.soundnessConv↓Term x))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castΠₙ x₅) castℕΠₙ) = ⊥-elim (ℕ≢Π! (sym (univ (SG.soundnessConv↓Term x))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castΠₙ x₅) castΠℕₙ) =  ⊥-elim (ℕ≢ne! x₅ (univ (SG.soundnessConv↓Term x₁)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castΠₙ x₅) castΠΠ%!ₙ) = ⊥-elim (I.Π≢ne x₅ (univ (SG.soundnessConv↓Term x₁)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castΠₙ x₅) castΠΠ!%ₙ) = ⊥-elim (I.Π≢ne x₅ (univ (SG.soundnessConv↓Term x₁)))

  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castℕℕₙ x₅) (castₙ x₆ x₇ x₈)) = ⊥-elim (ℕ≢ne! x₆ (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castℕℕₙ x₅) (castnℕₙ x₆)) = ⊥-elim (ℕ≢ne! x₆ (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castℕℕₙ x₅) (castnΠₙ x₆)) = ⊥-elim (ℕ≢Π! (sym (univ (SG.soundnessConv↓Term x₁))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castℕℕₙ x₅) (castℕₙ x₆)) = ⊥-elim (ℕ≢ne! x₆ (sym (univ (SG.soundnessConv↓Term x₁))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castℕℕₙ x₅) (castΠₙ x₆)) = ⊥-elim (ℕ≢Π! (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castℕℕₙ x₅) (castℕℕₙ x₆)) = castℕ-refl ([~] _ (id (univ (ℕⱼ (wfTerm x₃)))) ℕₙ
          (castℕ-refl' (inversion-ne-ℕ x₅ x₆ (inversion-whnf-conv' ℕₙ (ne x₅) (ne x₆) (⊢⊢is⊢conv↑Term x₂)) ) x₄)) x₃
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castℕℕₙ x₅) castℕΠₙ) = ⊥-elim (ℕ≢Π! (sym (univ (SG.soundnessConv↓Term x₁))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castℕℕₙ x₅) castΠℕₙ) = ⊥-elim (ℕ≢Π! (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castℕℕₙ x₅) castΠΠ%!ₙ) = ⊥-elim (ℕ≢Π! (sym (univ (SG.soundnessConv↓Term x₁))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ (castℕℕₙ x₅) castΠΠ!%ₙ) = ⊥-elim (ℕ≢Π! (sym (univ (SG.soundnessConv↓Term x₁))))

  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castℕΠₙ (castₙ x₆ x₇ x₈)) = ⊥-elim (ℕ≢ne! x₆ (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castℕΠₙ (castnℕₙ x₆)) = ⊥-elim (ℕ≢ne! x₆ (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castℕΠₙ (castnΠₙ x₆)) = ⊥-elim (ℕ≢ne! x₆ (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castℕΠₙ (castℕₙ x₆)) = ⊥-elim (I.Π≢ne x₆ (sym (univ (SG.soundnessConv↓Term x₁))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castℕΠₙ (castΠₙ x₆)) = ⊥-elim (ℕ≢Π! (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castℕΠₙ (castℕℕₙ x₆)) = ⊥-elim (ℕ≢Π! (univ (SG.soundnessConv↓Term x₁)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castℕΠₙ castℕΠₙ) =
    let Π=Π = univ (SG.soundnessConv↓Term x₁)
        _ , er , elF , elF' , elG , elG' ,  _ , er' , er'' = injectivityGen0 Π=Π
        foo = PE.subst₃ (λ X T U → _ ⊢ Π _ ^ X ° _ ▹ _ ° _ ° ⁰ ^ U [conv↓] Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ T ∷ _ ^ ι ¹)
                        er er'' er'
                        (⊢⊢is⊢conv↓Term x₁)
        ⊢Π , ⊢Π' = syntacticEq Π=Π
    in 
    PE.subst₃ (λ X T U → _ ⊢ cast ⁰ ℕ (Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ T) _ _ ~
      cast ⁰ ℕ (Π _ ^ X ° _ ▹ _ ° _ ° ⁰ ^ U) _ _ ↑!
               Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ T ^ ι ⁰) (PE.sym er) (PE.sym er'') (PE.sym  er')
      (cast-ℕΠ  ([↑]ₜ _ _ _ (id (Ugenⱼ (wfTerm x₃)))
                      (id (un-univ (PE.subst₂  (λ Z W → _ ⊢ Π _ ^ W ° _ ▹ _ ° _ ° ⁰ ^ Z ^ [ _ , _ ]) er' er ⊢Π)))
                      (id (un-univ (PE.subst  (λ Z → _ ⊢ Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ Z ^ [ _ , _ ]) er'' ⊢Π')))
                      Uₙ Πₙ Πₙ foo)               
                (⊢⊢is⊢conv↑Term x₂)
                (PE.subst (λ Z → _ ⊢ _ ∷ Id (U ⁰) _ (Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ Z) ^ [ % , ι ⁰ ]) er'' x₃)
                (PE.subst₂ (λ Z W → _ ⊢ _ ∷ Id (U ⁰) _ (Π _ ^ W ° _ ▹ _ ° _ ° ⁰ ^ Z) ^ [ % , ι ⁰ ]) er' er x₄))                 
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castℕΠₙ castΠℕₙ) = ⊥-elim (ℕ≢Π! (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castℕΠₙ castΠΠ%!ₙ) = ⊥-elim (ℕ≢Π! (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castℕΠₙ castΠΠ!%ₙ) = ⊥-elim (ℕ≢Π! (univ (SG.soundnessConv↓Term x)))

  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠℕₙ (castₙ x₆ x₇ x₈)) = ⊥-elim (I.Π≢ne x₆ (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠℕₙ (castnℕₙ x₆)) = ⊥-elim (I.Π≢ne x₆ (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠℕₙ (castnΠₙ x₆)) = ⊥-elim (I.Π≢ne x₆ (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠℕₙ (castℕₙ x₆)) = ⊥-elim (ℕ≢Π! (sym (univ (SG.soundnessConv↓Term x))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠℕₙ (castΠₙ x₆)) = ⊥-elim (ℕ≢ne! x₆ (sym (univ (SG.soundnessConv↓Term x₁))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠℕₙ (castℕℕₙ x₆)) = ⊥-elim (ℕ≢Π! (sym (univ (SG.soundnessConv↓Term x))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠℕₙ castℕΠₙ) = ⊥-elim (ℕ≢Π! (sym (univ (SG.soundnessConv↓Term x))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠℕₙ castΠℕₙ) = 
    let Π=Π = univ (SG.soundnessConv↓Term x)
        _ , er , elF , elF' , elG , elG' ,  _ , er' , er'' = injectivityGen0 Π=Π
        foo = PE.subst₃ (λ X T U → _ ⊢ Π _ ^ X ° _ ▹ _ ° _ ° ⁰ ^ U [conv↓] Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ T ∷ _ ^ ι ¹)
                    er er'' er' 
                    (⊢⊢is⊢conv↓Term x)
        ⊢Π , ⊢Π' = syntacticEq Π=Π
    in PE.subst₃ (λ X T U  → _ ⊢ cast ⁰ (Π _ ^ X ° _ ▹ _ ° _ ° ⁰ ^ T) _ _ _ ~
                                 cast ⁰ (Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ U) _ _ _ ↑! _ ^ ι ⁰)
           (PE.sym er) (PE.sym er') (PE.sym er'')
      (cast-Πℕ ([↑]ₜ _ _ _ (id (Ugenⱼ (wfTerm x₃)))
                      (id (un-univ (PE.subst₂  (λ Z W → _ ⊢ Π _ ^ W ° _ ▹ _ ° _ ° ⁰ ^ Z ^ [ _ , _ ]) er' er ⊢Π)))
                      (id (un-univ (PE.subst (λ Z → _ ⊢ Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ Z ^ [ _ , _ ]) er'' ⊢Π')))
                      Uₙ Πₙ Πₙ foo)
                (PE.subst₂  (λ Z W → _ ⊢ _ [conv↑] _ ∷ Π _ ^ W ° _ ▹ _ ° _ ° ⁰ ^ Z ^ _) er' er (⊢⊢is⊢conv↑Term x₂))
                (PE.subst₂  (λ Z W → _ ⊢ _ ∷ Id (U ⁰) (Π _ ^ W ° _ ▹ _ ° _ ° ⁰ ^ Z) _ ^ [ % , ι ⁰ ]) er' er x₃)                
                (PE.subst   (λ Z → _ ⊢ _ ∷ Id (U ⁰) (Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ Z) _ ^ [ % , ι ⁰ ]) er'' x₄))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠℕₙ castΠΠ%!ₙ) = ⊥-elim (ℕ≢Π! (sym (univ (SG.soundnessConv↓Term x₁))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠℕₙ castΠΠ!%ₙ) = ⊥-elim (ℕ≢Π! (sym (univ (SG.soundnessConv↓Term x₁))))

  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠΠ%!ₙ (castₙ x₆ x₇ x₈)) = ⊥-elim (I.Π≢ne x₆ (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠΠ%!ₙ (castnℕₙ x₆)) = ⊥-elim (I.Π≢ne x₆ (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠΠ%!ₙ (castnΠₙ x₆)) = ⊥-elim (I.Π≢ne x₆ (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠΠ%!ₙ (castℕₙ x₆)) = ⊥-elim (I.Π≢ne x₆ (sym (univ (SG.soundnessConv↓Term x₁))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠΠ%!ₙ (castΠₙ x₆)) = ⊥-elim (I.Π≢ne x₆ (sym (univ (SG.soundnessConv↓Term x₁))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠΠ%!ₙ (castℕℕₙ x₆)) = ⊥-elim (ℕ≢Π! (univ (SG.soundnessConv↓Term x₁)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠΠ%!ₙ castℕΠₙ) = ⊥-elim (ℕ≢Π! (sym (univ (SG.soundnessConv↓Term x))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠΠ%!ₙ castΠℕₙ) = ⊥-elim (ℕ≢Π! (univ (SG.soundnessConv↓Term x₁)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠΠ%!ₙ castΠΠ%!ₙ) =
    let Π=Π = SG.soundnessConv↓Term x
        _ , _ , _ , _ , _ , er , er' = injectivityGen (univ Π=Π)
        Π=Π' = SG.soundnessConv↓Term x₁
        _ , _ , _ , _ , _ , e , e' = injectivityGen (univ Π=Π')
        ⊢Π , ⊢Π' = syntacticEq (univ Π=Π)
        ⊢Π'' , ⊢Π''' = syntacticEq (univ Π=Π')
        foo = PE.subst₂ (λ T U → _ ⊢ Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ U [conv↓] Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ T ∷ _ ^ ι ¹)
                    er' er 
                    (⊢⊢is⊢conv↓Term x)
        foo' = PE.subst₂ (λ T U → _ ⊢ Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ U [conv↓] Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ T ∷ _ ^ ι ¹)
                    e' e 
                    (⊢⊢is⊢conv↓Term x₁)
    in PE.subst₄ (λ X T U V → _ ⊢ cast ⁰ (Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ X) (Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ T)  _ _ ~
                                  cast ⁰ (Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ U) (Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ V) _ _ ↑! (Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ T) ^ ι ⁰)
           (PE.sym er) (PE.sym e') (PE.sym er') (PE.sym e)
      (cast-ΠΠ%! ([↑]ₜ _ _ _ (id (Ugenⱼ (wfTerm x₃)))
                      (id (un-univ (PE.subst (λ Z → _ ⊢ Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ Z ^ [ _ , _ ]) er ⊢Π)))
                      (id (un-univ (PE.subst (λ Z → _ ⊢ Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ Z ^ [ _ , _ ]) er' ⊢Π')))
                      Uₙ Πₙ Πₙ foo)
                 (([↑]ₜ _ _ _ (id (Ugenⱼ (wfTerm x₃)))
                      (id (un-univ (PE.subst (λ Z → _ ⊢ Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ Z ^ [ _ , _ ]) e ⊢Π'')))
                      (id (un-univ (PE.subst (λ Z → _ ⊢ Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ Z ^ [ _ , _ ]) e' ⊢Π''')))
                      Uₙ Πₙ Πₙ foo'))
                 (PE.subst (λ Z → _ ⊢ _ [conv↑] _ ∷ Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ Z ^ _) er (⊢⊢is⊢conv↑Term x₂))
                 (PE.subst₂ (λ X Y → _ ⊢ _ ∷ Id (U ⁰) (Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ X) (Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ Y) ^ [ % , ι ⁰ ]) er e' x₃)
                 (PE.subst₂ (λ X Y → _ ⊢ _ ∷ Id (U ⁰) (Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ X) (Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ Y) ^ [ % , ι ⁰ ]) er' e x₄))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠΠ%!ₙ castΠΠ!%ₙ) =
    let Π=Π = SG.soundnessConv↓Term x
        _ , erF , _ = injectivityGen (univ Π=Π)
    in ⊥-elim (!≢% (PE.sym erF))

  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠΠ!%ₙ (castₙ x₆ x₇ x₈)) = ⊥-elim (I.Π≢ne x₆ (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠΠ!%ₙ (castnℕₙ x₆)) = ⊥-elim (I.Π≢ne x₆ (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠΠ!%ₙ (castnΠₙ x₆)) = ⊥-elim (I.Π≢ne x₆ (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠΠ!%ₙ (castℕₙ x₆)) = ⊥-elim (I.Π≢ne x₆ (sym (univ (SG.soundnessConv↓Term x₁))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠΠ!%ₙ (castΠₙ x₆)) = ⊥-elim (I.Π≢ne x₆ (sym (univ (SG.soundnessConv↓Term x₁))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠΠ!%ₙ (castℕℕₙ x₆)) = ⊥-elim (ℕ≢Π! (univ (SG.soundnessConv↓Term x₁)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠΠ!%ₙ castℕΠₙ) = ⊥-elim (ℕ≢Π! (sym (univ (SG.soundnessConv↓Term x))))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠΠ!%ₙ castΠℕₙ) = ⊥-elim (ℕ≢Π! (univ (SG.soundnessConv↓Term x₁)))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠΠ!%ₙ castΠΠ!%ₙ) =
    let Π=Π = SG.soundnessConv↓Term x
        _ , _ , _ , _ , _ , er , er' = injectivityGen (univ Π=Π)
        Π=Π' = SG.soundnessConv↓Term x₁
        _ , _ , _ , _ , _ , e , e' = injectivityGen (univ Π=Π')
        ⊢Π , ⊢Π' = syntacticEq (univ Π=Π)
        ⊢Π'' , ⊢Π''' = syntacticEq (univ Π=Π')
        foo = PE.subst₂ (λ T U → _ ⊢ Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ U [conv↓] Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ T ∷ _ ^ ι ¹)
                    er' er 
                    (⊢⊢is⊢conv↓Term x)
        foo' = PE.subst₂ (λ T U → _ ⊢ Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ U [conv↓] Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ T ∷ _ ^ ι ¹)
                    e' e 
                    (⊢⊢is⊢conv↓Term x₁)
    in PE.subst₄ (λ X T U V → _ ⊢ cast ⁰ (Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ X) (Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ T)  _ _ ~
                                  cast ⁰ (Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ U) (Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ V) _ _ ↑! (Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ T) ^ ι ⁰)
           (PE.sym er) (PE.sym e') (PE.sym er') (PE.sym e)
      (cast-ΠΠ!% ([↑]ₜ _ _ _ (id (Ugenⱼ (wfTerm x₃)))
                      (id (un-univ (PE.subst (λ Z → _ ⊢ Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ Z ^ [ _ , _ ]) er ⊢Π)))
                      (id (un-univ (PE.subst (λ Z → _ ⊢ Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ Z ^ [ _ , _ ]) er' ⊢Π')))
                      Uₙ Πₙ Πₙ foo)
                 (([↑]ₜ _ _ _ (id (Ugenⱼ (wfTerm x₃)))
                      (id (un-univ (PE.subst (λ Z → _ ⊢ Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ Z ^ [ _ , _ ]) e ⊢Π'')))
                      (id (un-univ (PE.subst (λ Z → _ ⊢ Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ Z ^ [ _ , _ ]) e' ⊢Π''')))
                      Uₙ Πₙ Πₙ foo'))
                 (PE.subst (λ Z → _ ⊢ _ [conv↑] _ ∷ Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ Z ^ _) er (⊢⊢is⊢conv↑Term x₂))
                 (PE.subst₂ (λ X Y → _ ⊢ _ ∷ Id (U ⁰) (Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ X) (Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ Y) ^ [ % , ι ⁰ ]) er e' x₃)
                 (PE.subst₂ (λ X Y → _ ⊢ _ ∷ Id (U ⁰) (Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ X) (Π _ ^ _ ° _ ▹ _ ° _ ° ⁰ ^ Y) ^ [ % , ι ⁰ ]) er' e x₄))
  ⊢⊢is⊢~! (cast-cong x x₁ x₂ x₃ x₄ castΠΠ!%ₙ castΠΠ%!ₙ) =
    let Π=Π = SG.soundnessConv↓Term x
        _ , erF , _ = injectivityGen (univ Π=Π)
    in ⊥-elim (!≢% erF)

  ⊢⊢is⊢~! (cast-refl x x₁ x₂ (castₙ x₃ x₄ x₅) cast) = cast-refl (inversion-ne-U x₃ (⊢⊢is⊢conv↓Term x)) (⊢⊢is⊢conv↓Term x₁) x₂
  ⊢⊢is⊢~! (cast-refl x x₁ x₂ (castnℕₙ x₃) cast) = ⊥-elim (ℕ≢ne! x₃ (univ (sym (SG.soundnessConv↓Term x))))
  ⊢⊢is⊢~! (cast-refl x x₁ x₂ (castnΠₙ x₃) cast) = ⊥-elim (I.Π≢ne x₃ (univ (sym (SG.soundnessConv↓Term x))))
  ⊢⊢is⊢~! (cast-refl x x₁ x₂ (castℕₙ x₃) cast) = ⊥-elim (ℕ≢ne! x₃ (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-refl x x₁ x₂ (castΠₙ x₃) cast) = ⊥-elim (I.Π≢ne x₃ (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-refl x x₁ x₂ (castℕℕₙ x₃) cast) = castℕ-refl (inversion-ne-ℕ x₃ cast (⊢⊢is⊢conv↓Term x₁)) x₂
  ⊢⊢is⊢~! (cast-refl x x₁ x₂ castℕΠₙ cast) = ⊥-elim (ℕ≢Π! (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-refl x x₁ x₂ castΠℕₙ cast) = ⊥-elim (ℕ≢Π! (sym (univ (SG.soundnessConv↓Term x))))
  ⊢⊢is⊢~! (cast-refl x x₁ x₂ castΠΠ%!ₙ cast) =
    let Π=Π = SG.soundnessConv↓Term x
        _ , erF , _ = injectivityGen (univ Π=Π)
    in ⊥-elim (!≢% (PE.sym erF))
  ⊢⊢is⊢~! (cast-refl x x₁ x₂ castΠΠ!%ₙ cast) =
    let Π=Π = SG.soundnessConv↓Term x
        _ , erF , _ = injectivityGen (univ Π=Π)
    in ⊥-elim (!≢% erF)

  ⊢⊢is⊢~! (cast-refl' x x₁ x₂ (castₙ x₃ x₄ x₅) cast) = cast-refl' (inversion-ne-U x₄ (⊢⊢is⊢conv↓Term x)) (⊢⊢is⊢conv↓Term x₁) x₂
  ⊢⊢is⊢~! (cast-refl' x x₁ x₂ (castnℕₙ x₃) cast) = ⊥-elim (ℕ≢ne! x₃ (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-refl' x x₁ x₂ (castnΠₙ x₃) cast) = ⊥-elim (I.Π≢ne x₃ (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-refl' x x₁ x₂ (castℕₙ x₃) cast) =  ⊥-elim (ℕ≢ne! x₃ (univ (sym (SG.soundnessConv↓Term x))))
  ⊢⊢is⊢~! (cast-refl' x x₁ x₂ (castΠₙ x₃) cast) = ⊥-elim (I.Π≢ne x₃ (univ (sym (SG.soundnessConv↓Term x))))
  ⊢⊢is⊢~! (cast-refl' x x₁ x₂ (castℕℕₙ x₃) cast) = castℕ-refl' (inversion-ne-ℕ cast x₃ (⊢⊢is⊢conv↓Term x₁)) x₂
  ⊢⊢is⊢~! (cast-refl' x x₁ x₂ castℕΠₙ cast) = ⊥-elim (ℕ≢Π! (sym (univ (SG.soundnessConv↓Term x))))
  ⊢⊢is⊢~! (cast-refl' x x₁ x₂ castΠℕₙ cast) = ⊥-elim (ℕ≢Π! (univ (SG.soundnessConv↓Term x)))
  ⊢⊢is⊢~! (cast-refl' x x₁ x₂ castΠΠ%!ₙ cast) =
    let Π=Π = SG.soundnessConv↓Term x
        _ , erF , _ = injectivityGen (univ Π=Π)
    in ⊥-elim (!≢% erF)
  ⊢⊢is⊢~! (cast-refl' x x₁ x₂ castΠΠ!%ₙ cast) =
    let Π=Π = SG.soundnessConv↓Term x
        _ , erF , _ = injectivityGen (univ Π=Π)
    in ⊥-elim (!≢% (PE.sym erF))

  ⊢⊢is⊢~% (%~↑ ⊢⊢k ⊢⊢l) = %~↑ ⊢⊢k ⊢⊢l
  ⊢⊢is⊢~↓! ([~] A D whnfB k~l) = [~] A D whnfB (⊢⊢is⊢~! k~l)
  ⊢⊢is⊢conv↑ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) = [↑] A′ B′ D D′ whnfA′ whnfB′ (⊢⊢is⊢conv↓ A′<>B′)
  ⊢⊢is⊢conv↓ (U-refl x x₁) = U-refl x x₁
  ⊢⊢is⊢conv↓ (univ x) = univ (⊢⊢is⊢conv↓Term x)
  ⊢⊢is⊢conv↑Term ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) = [↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ (⊢⊢is⊢conv↓Term t<>u)
  ⊢⊢is⊢conv↓Term (U-refl x x₁) = U-refl x x₁
  ⊢⊢is⊢conv↓Term (ℕ-refl x) = ℕ-refl x
  ⊢⊢is⊢conv↓Term (Empty-refl x) = Empty-refl x
  ⊢⊢is⊢conv↓Term (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇) =
    let F=F = SG.soundnessConv↑Term x₆
        _ , F , _  = syntacticEqTerm F=F
    in Π-cong x x₁ x₂ x₃ x₄ x₅ (univ F) (⊢⊢is⊢conv↑Term x₆) (⊢⊢is⊢conv↑Term x₇)
  ⊢⊢is⊢conv↓Term (Id-cong x x₁ x₂) = Id-cong (⊢⊢is⊢conv↑Term x) (⊢⊢is⊢conv↑Term x₁) (⊢⊢is⊢conv↑Term x₂)
  ⊢⊢is⊢conv↓Term (ne x) = ne (⊢⊢is⊢~↓! x)
  ⊢⊢is⊢conv↓Term (ℕ-ins x) = ℕ-ins (⊢⊢is⊢~↓! x)
  ⊢⊢is⊢conv↓Term (ne-ins x x₁ x₂ x₃) = ne-ins x x₁ x₂ (⊢⊢is⊢~↓! x₃)
  ⊢⊢is⊢conv↓Term (zero-refl x) = zero-refl x
  ⊢⊢is⊢conv↓Term (suc-cong x) = suc-cong (⊢⊢is⊢conv↑Term x) 
  ⊢⊢is⊢conv↓Term (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) = η-eq x x₁ x₂ x₃ x₄ x₅ x₆ (⊢⊢is⊢conv↑Term x₇)
  ⊢⊢is⊢genconv↑ {l = [ ! , l ]} X = ⊢⊢is⊢conv↑Term X
  ⊢⊢is⊢genconv↑ {l = [ % , l ]} X = ⊢⊢is⊢~% X

