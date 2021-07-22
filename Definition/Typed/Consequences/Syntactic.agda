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

-- the `with` syntax does not work 

-- Syntactic validity of type equality.
syntacticEq : ∀ {A B rA Γ} → Γ ⊢ A ≡ B ^ rA → Γ ⊢ A ^ rA × Γ ⊢ B ^ rA
syntacticEq {A} {B} {rA} {Γ} A≡B =
  let X = fundamentalEq A≡B
      [Γ] = proj₁ X
      [A] = proj₁ (proj₂ X)
      [B] = proj₁ (proj₂ (proj₂ X))
  in escapeᵛ [Γ] [A] , escapeᵛ [Γ] [B]


-- Syntactic validity of terms.
syntacticTerm : ∀ {t A rA Γ} → Γ ⊢ t ∷ A ^ rA → Γ ⊢ A ^ rA
syntacticTerm t =
  let X = fundamentalTerm t
      [Γ] = proj₁ X
      [A] = proj₁ (proj₂ X)
      [t] = proj₂ (proj₂ X)
   in  escapeᵛ [Γ] [A]

-- Syntactic validity of term equality.
syntacticEqTerm : ∀ {t u A rA Γ} → Γ ⊢ t ≡ u ∷ A ^ rA → Γ ⊢ A ^ rA × (Γ ⊢ t ∷ A ^ rA × Γ ⊢ u ∷ A ^ rA)
syntacticEqTerm t≡u with fundamentalTermEq t≡u
syntacticEqTerm t≡u | [Γ] , modelsTermEq [A] [t] [u] [t≡u] =
  escapeᵛ [Γ] [A] , escapeTermᵛ [Γ] [A] [t] , escapeTermᵛ [Γ] [A] [u]


-- Syntactic validity of type reductions.
syntacticRed : ∀ {A B rA Γ} → Γ ⊢ A ⇒* B ^ rA → Γ ⊢ A ^ rA × Γ ⊢ B ^ rA
syntacticRed D =
  let X = fundamentalEq (subset* D)
      [Γ] = proj₁ X
      [A] = proj₁ (proj₂ X)
      [B] = proj₁ (proj₂ (proj₂ X))
  in escapeᵛ [Γ] [A] , escapeᵛ [Γ] [B]


-- Syntactic validity of term reductions.
syntacticRedTerm : ∀ {t u A Γ l} → Γ ⊢ t ⇒* u ∷ A ^ l → Γ ⊢ A ^ [ ! , l ] × (Γ ⊢ t ∷ A ^ [ ! , l ] × Γ ⊢ u ∷ A ^ [ ! , l ])
syntacticRedTerm d with fundamentalTermEq (subset*Term d)
syntacticRedTerm d | [Γ] , modelsTermEq [A] [t] [u] [t≡u] =
  escapeᵛ [Γ] [A] , escapeTermᵛ [Γ] [A] [t] , escapeTermᵛ [Γ] [A] [u]


-- Syntactic validity of Π-types.
syntacticΠ : ∀ {Γ F G rF lF lG rΠ lΠ} → Γ ⊢ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ [ rΠ , ι lΠ ] → Γ ⊢ F ^ [ rF , ι lF ] × Γ ∙ F ^ [ rF , ι lF ] ⊢ G ^ [ rΠ , ι lG ]
syntacticΠ ΠFG with injectivity (refl ΠFG)
syntacticΠ ΠFG | F≡F , rF≡rF , lF≡lF , lG≡lG , G≡G = proj₁ (syntacticEq F≡F) , proj₁ (syntacticEq G≡G)

