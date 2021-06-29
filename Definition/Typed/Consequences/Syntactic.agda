{-# OPTIONS --safe #-}

module Definition.Typed.Consequences.Syntactic where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.EqRelInstance
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Escape
open import Definition.LogicalRelation.Fundamental
open import Definition.Typed.Consequences.Injectivity

open import Tools.Product


-- Syntactic validity of type equality.
syntacticEq : ∀ {A B rA Γ} → Γ ⊢ A ≡ B ^ rA → Γ ⊢ A ^ rA × Γ ⊢ B ^ rA
syntacticEq A≡B with fundamentalEq A≡B
syntacticEq A≡B | [Γ] , [A] , [B] , [A≡B] =
  escapeᵛ [Γ] [A] , escapeᵛ [Γ] [B]

-- Syntactic validity of terms.
syntacticTerm : ∀ {t A rA Γ} → Γ ⊢ t ∷ A ^ rA → Γ ⊢ A ^ rA
syntacticTerm t with fundamentalTerm t
syntacticTerm t | [Γ] , [A] , [t] = escapeᵛ [Γ] [A]

-- Syntactic validity of term equality.
syntacticEqTerm : ∀ {t u A rA Γ} → Γ ⊢ t ≡ u ∷ A ^ rA → Γ ⊢ A ^ rA × (Γ ⊢ t ∷ A ^ rA × Γ ⊢ u ∷ A ^ rA)
syntacticEqTerm t≡u with fundamentalTermEq t≡u
syntacticEqTerm t≡u | [Γ] , modelsTermEq [A] [t] [u] [t≡u] =
  escapeᵛ [Γ] [A] , escapeTermᵛ [Γ] [A] [t] , escapeTermᵛ [Γ] [A] [u]

-- Syntactic validity of type reductions.
syntacticRed : ∀ {A B rA Γ} → Γ ⊢ A ⇒* B ^ rA → Γ ⊢ A ^ rA × Γ ⊢ B ^ rA
syntacticRed D with fundamentalEq (subset* D)
syntacticRed D | [Γ] , [A] , [B] , [A≡B] =
  escapeᵛ [Γ] [A] , escapeᵛ [Γ] [B]

-- Syntactic validity of term reductions.
syntacticRedTerm : ∀ {t u A Γ} → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ A ^ ! × (Γ ⊢ t ∷ A ^ ! × Γ ⊢ u ∷ A ^ !)
syntacticRedTerm d with fundamentalTermEq (subset*Term d)
syntacticRedTerm d | [Γ] , modelsTermEq [A] [t] [u] [t≡u] =
  escapeᵛ [Γ] [A] , escapeTermᵛ [Γ] [A] [t] , escapeTermᵛ [Γ] [A] [u]

-- Syntactic validity of Π-types.
syntacticΠ : ∀ {Γ F G rF rG} → Γ ⊢ Π F ^ rF ▹ G ^ rG → Γ ⊢ F ^ rF × Γ ∙ F ^ rF ⊢ G ^ rG
syntacticΠ ΠFG with injectivity (refl ΠFG)
syntacticΠ ΠFG | F≡F , rF≡rF , G≡G = proj₁ (syntacticEq F≡F) , proj₁ (syntacticEq G≡G)
