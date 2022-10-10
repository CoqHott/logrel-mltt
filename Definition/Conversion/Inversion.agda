{-# OPTIONS --safe #-}

module Definition.Conversion.Inversion where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.Conversion
open import Definition.Conversion.Soundness
open import Definition.Conversion.Stability
open import Definition.Conversion.Conversion
open import Definition.Conversion.Whnf
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Reduction
open import Definition.Typed.Consequences.Injectivity
import Definition.Typed.Consequences.Inequality as WF
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution
open import Definition.Typed.Consequences.NeTypeEq
open import Definition.Typed.Consequences.SucCong
open import Definition.Typed.Consequences.RelevanceUnicity
open import Definition.Typed.Consequences.Equality
open import Definition.Typed.Consequences.Inversion

open import Tools.Nat
open import Tools.Product
open import Tools.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Tools.Empty
import Tools.PropositionalEquality as PE

[conv↓]ne : ∀ {Γ t u A l} → Neutral A → Γ ⊢ t [conv↓] u ∷ A ^ l → ∃ λ B → Γ ⊢ t ~ u ↓! B ^ l × Γ ⊢ A ≡ B ^ [ ! , l ]
[conv↓]ne neA (ne-ins x x₁ x₂ x₃) =
  let t~u = (ne-ins x x₁ x₂ x₃)
      _ , ⊢t , _ = syntacticEqTerm (soundnessConv↓Term t~u)
      _ , nft , _ = whnfConv↓Term t~u
      net = inversion-ne neA nft ⊢t
      _ , ⊢t' , _ = syntacticEqTerm (soundness~↓! x₃)
      _ , eq = neTypeEq net ⊢t ⊢t'
  in _ , x₃ , eq
