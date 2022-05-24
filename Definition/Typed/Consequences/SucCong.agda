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
open import Tools.Empty using (⊥; ⊥-elim)


-- Congurence of the type of the successor case in natrec.
sucCong : ∀ {F G lF Γ} → Γ ∙ ℕ ^ [ ! , ι ⁰ ] ⊢ F ≡ G ^ [ ! , ι lF ]
        → Γ ⊢ Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° lF ▹▹ F [ suc (var 0) ]↑ ° lF ° lF ^ !) ° lF ° lF ^ !
            ≡ Π ℕ ^ ! ° ⁰ ▹ (G ^ ! ° lF ▹▹ G [ suc (var 0) ]↑ ° lF ° lF ^ !) ° lF ° lF ^ ! ^ [ ! , ι lF ]
sucCong F≡G with wfEq F≡G
sucCong {lF = lF} F≡G | ⊢Γ ∙ ⊢ℕ =
  let ⊢F , _ = syntacticEq F≡G
  in  univ (Π-cong (λ x → (⁰min lF) , (≡is≤ PE.refl)) (λ abs → ⊥-elim (!≢% abs)) ⊢ℕ (refl (un-univ ⊢ℕ))
             (Π-cong (λ x → (≡is≤ PE.refl) , (≡is≤ PE.refl)) (λ abs → ⊥-elim (!≢% abs)) ⊢F (un-univ≡ F≡G)
                     (wkEqTerm (step id) (⊢Γ ∙ ⊢ℕ ∙ ⊢F)
                               (un-univ≡ (subst↑TypeEq F≡G
                                                       (refl (sucⱼ (var (⊢Γ ∙ ⊢ℕ) here))))))))
