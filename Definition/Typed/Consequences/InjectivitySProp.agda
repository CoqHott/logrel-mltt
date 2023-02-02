{-# OPTIONS --safe #-}

module Definition.Typed.Consequences.InjectivitySProp where

open import Definition.Untyped hiding (wk)
import Definition.Untyped as U
open import Definition.Untyped.Properties

open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.Typed.EqRelInstance
open import Definition.Typed.Consequences.Syntactic
open import Definition.Conversion
-- open import Definition.Conversion.Decidable
open import Definition.Conversion.Soundness
open import Definition.Conversion.Stability
open import Definition.Conversion.EqRelInstance
open import Definition.Conversion.Universe
open import Definition.Conversion.Consequences.Completeness

open import Tools.Product
import Tools.PropositionalEquality as PE

injectivity-irr↓ : ∀ {Γ F G H E rF lF lH rH} →
              Γ ⊢ Π F ^ rF ° lF ▹ G ° ⁰ ° ⁰ ^ % [conv↓] Π H ^ rH ° lH ▹ E ° ⁰ ° ⁰ ^ % ^ [ % , ι ⁰ ]
            → Γ ⊢ F [conv↑] H ^ [ rF , ι lF ]
            × rF PE.≡ rH
            × lF PE.≡ lH
            × Γ ∙ F ^ [ rF , ι lF ] ⊢ G [conv↑] E ^ [ % , ι ⁰ ]
injectivity-irr↓ (univ (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈)) = univConv↑ x₇ , x₁ , x₂ , univConv↑ x₈

injectivity-irr↑ : ∀ {Γ F G H E rF lF lH rH} →
              Γ ⊢ Π F ^ rF ° lF ▹ G ° ⁰ ° ⁰ ^ % [conv↑] Π H ^ rH ° lH ▹ E ° ⁰ ° ⁰ ^ % ^ [ % , ι ⁰ ]
            → Γ ⊢ F [conv↑] H ^ [ rF , ι lF ]
            × rF PE.≡ rH
            × lF PE.≡ lH
            × Γ ∙ F ^ [ rF , ι lF ] ⊢ G [conv↑] E ^ [ % , ι ⁰ ]
injectivity-irr↑ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′)
  rewrite PE.sym (whnfRed* D Πₙ) | PE.sym (whnfRed* D′ Πₙ) = injectivity-irr↓ A′<>B′


injectivity-irr : ∀ {Γ F G H E rF lF lH rH} →
              Γ ⊢ Π F ^ rF ° lF ▹ G ° ⁰ ° ⁰ ^ % ≡ Π H ^ rH ° lH ▹ E ° ⁰ ° ⁰ ^ % ^ [ % , ι ⁰ ]
            → Γ ⊢ F ≡ H ^ [ rF , ι lF ]
            × rF PE.≡ rH
            × lF PE.≡ lH
            × Γ ∙ F ^ [ rF , ι lF ] ⊢ G ≡ E ^ [ % , ι ⁰ ]
injectivity-irr ⊢ΠFG≡ΠHE =
  let [ΠFG≡ΠHE] = completeEq ⊢ΠFG≡ΠHE
      [F] , er , el , [G] = injectivity-irr↑ [ΠFG≡ΠHE]
  in soundnessConv↑ [F] , er , el , soundnessConv↑ [G]  


-- Injectivity of Id

Idinjectivity↓ : ∀ {Γ F t u E t' u'} →
              Γ ⊢ Id F t u [conv↓] Id E t' u' ^ [ % , ι ⁰ ]
            → ∃ λ l →
              Γ ⊢ F [conv↑] E ^ [ ! , ι l ]
            × Γ ⊢ t [conv↑] t' ∷ F ^ ι l
            × Γ ⊢ u [conv↑] u' ∷ F ^ ι l
Idinjectivity↓ (univ (Id-cong x x₁ x₂)) = _ , univConv↑ x , x₁ , x₂

Idinjectivity↑ : ∀ {Γ F t u E t' u'} →
              Γ ⊢ Id F t u [conv↑] Id E t' u' ^ [ % , ι ⁰ ]
            → ∃ λ l →
              Γ ⊢ F [conv↑] E ^ [ ! , ι l ]
            × Γ ⊢ t [conv↑] t' ∷ F ^ ι l
            × Γ ⊢ u [conv↑] u' ∷ F ^ ι l
Idinjectivity↑ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′)
  rewrite PE.sym (whnfRed* D Idₙ) | PE.sym (whnfRed* D′ Idₙ) = Idinjectivity↓ A′<>B′

Idinjectivity : ∀ {Γ F t u E t' u'} →
              Γ ⊢ Id F t u ≡ Id E t' u' ^ [ % , ι ⁰ ]
            → ∃ λ l →
              Γ ⊢ F ≡ E ^ [ ! , ι l ]
            × Γ ⊢ t ≡ t' ∷ F ^ [ ! , ι l ]
            × Γ ⊢ u ≡ u' ∷ F ^ [ ! , ι l ]
Idinjectivity ⊢IdFG≡IdHE  =
  let [IdFG≡IdHE] = completeEq ⊢IdFG≡IdHE
      l , [F] , [t] , [u] = Idinjectivity↑ [IdFG≡IdHE]
  in l , soundnessConv↑ [F] , soundnessConv↑Term [t] , soundnessConv↑Term [u]
