{-# OPTIONS --safe #-}

module Definition.Typed.Consequences.SucCong where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Congurence of the type of the successor case in natrec.
sucCong : ∀ {F G rF lF Γ} → Γ ∙ ℕ ^ [ ! , ι ⁰ ] ⊢ F ≡ G ^ [ rF , ι lF ]
        → Γ ⊢ Π ℕ ^ ! ° ⁰ ▹ (F ^ rF ° lF ▹▹ F [ suc (var 0) ]↑ ° lF ) ° lF
            ≡ Π ℕ ^ ! ° ⁰ ▹ (G ^ rF ° lF ▹▹ G [ suc (var 0) ]↑ ° lF ) ° lF ^ [ rF , ι lF ]
sucCong F≡G with wfEq F≡G
sucCong {lF = lF} F≡G | ⊢Γ ∙ ⊢ℕ =
  let ⊢F , _ = syntacticEq F≡G
  in  univ (Π-cong (⁰min lF) (≡is≤ PE.refl) ⊢ℕ (refl (un-univ ⊢ℕ))
             (Π-cong (≡is≤ PE.refl) (≡is≤ PE.refl) ⊢F (un-univ≡ F≡G)
                     (wkEqTerm (step id) (⊢Γ ∙ ⊢ℕ ∙ ⊢F)
                               (un-univ≡ (subst↑TypeEq F≡G
                                                       (refl (sucⱼ (var (⊢Γ ∙ ⊢ℕ) here))))))))
