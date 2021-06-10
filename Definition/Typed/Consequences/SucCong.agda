{-# OPTIONS --without-K  #-}

module Definition.Typed.Consequences.SucCong where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution

open import Tools.Product


-- Congurence of the type of the successor case in natrec.
sucCong : ∀ {F G sF Γ} → Γ ∙ ℕ ⦂ 𝕥y ⊢ F ≡ G ⦂ sF
        → Γ ⊢ Π ℕ ⦂ 𝕥y ▹ (F ⦂ sF ▹▹ F [ suc (var 0) ]↑)
            ≡ Π ℕ ⦂ 𝕥y ▹ (G ⦂ sF ▹▹ G [ suc (var 0) ]↑) ⦂ sF
sucCong F≡G with wfEq F≡G
sucCong F≡G | ⊢Γ ∙ ⊢ℕ =
  let ⊢F , _ = syntacticEq F≡G
  in  Π-cong ⊢ℕ (refl ⊢ℕ)
             (Π-cong ⊢F F≡G
                     (wkEq (step id) (⊢Γ ∙ ⊢ℕ ∙ ⊢F)
                           (subst↑TypeEq F≡G
                                         (refl (sucⱼ (var (⊢Γ ∙ ⊢ℕ) here))))))
