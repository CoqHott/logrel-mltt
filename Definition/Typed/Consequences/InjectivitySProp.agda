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


-- Injectivity of ∃

∃injectivity↓ : ∀ {Γ F G H E} →
              Γ ⊢ ∃ F ▹ G [conv↓] ∃ H ▹ E ^ [ % , ι ⁰ ]
            → Γ ⊢ F [conv↑] H ^ [ % , ι ⁰ ]
            × Γ ∙ F ^ [ % , ι ⁰ ] ⊢ G [conv↑] E ^ [ % , ι ⁰ ]
∃injectivity↓ (univ (∃-cong x x₁ x₂)) = univConv↑ x₁ , univConv↑ x₂

∃injectivity↑ : ∀ {Γ F G H E} →
              Γ ⊢ ∃ F ▹ G [conv↑] ∃ H ▹ E ^ [ % , ι ⁰ ]
            → Γ ⊢ F [conv↑] H ^ [ % , ι ⁰ ]
            × Γ ∙ F ^ [ % , ι ⁰ ] ⊢ G [conv↑] E ^ [ % , ι ⁰ ]
∃injectivity↑ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′)
  rewrite PE.sym (whnfRed* D ∃ₙ) | PE.sym (whnfRed* D′ ∃ₙ) = ∃injectivity↓ A′<>B′


∃injectivity : ∀ {Γ F G H E} →
              Γ ⊢ ∃ F ▹ G ≡ ∃ H ▹ E ^ [ % , ι ⁰ ]
            → Γ ⊢ F ≡ H ^ [ % , ι ⁰ ]
            × Γ ∙ F ^ [ % , ι ⁰ ] ⊢ G ≡ E ^ [ % , ι ⁰ ]
∃injectivity ⊢∃FG≡∃HE  =
  let [∃FG≡∃HE] = completeEq ⊢∃FG≡∃HE
      [F] , [G] = ∃injectivity↑ [∃FG≡∃HE]
  in soundnessConv↑ [F] , soundnessConv↑ [G]  
