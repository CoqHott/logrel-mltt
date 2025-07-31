{-# OPTIONS  --safe #-}

module Definition.Typed.Validity where

open import Definition.Untyped as U hiding (wk;subst)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.RedSteps
open import Definition.Typed.Properties
open import Definition.Typed.Weakening 

open import Tools.Empty using (⊥; ⊥-elim)
open import Tools.Product
open import Tools.Sum hiding (id ; sym)
import Tools.PropositionalEquality as PE

import Data.Fin as Fin
import Data.Nat as Nat

validityCon :  ∀ {Γ A x r } → ⊢ Γ → x ∷ A ^ r ∈ Γ → Γ ⊢ A ^ r
validityCon (⊢Γ ∙ x) here = wk (step id) (⊢Γ ∙ x) x
validityCon (⊢Γ ∙ x) (there X) = wk (step id) (⊢Γ ∙ x) (validityCon ⊢Γ X)

validity : ∀ {Γ A t r} →
  Γ ⊢ t ∷ A ^ r → Γ ⊢ A ^ r
validity (univ 0<1 ⊢Γ) = Uⱼ ⊢Γ
validity (ℕⱼ ⊢Γ) = univ (univ 0<1 ⊢Γ)
validity (Emptyⱼ ⊢Γ) = univ (univ 0<1 ⊢Γ)
validity (Πⱼ_▹_▹_▹_ x x₁ X X₁) = univ-gen (wfTerm X)
validity (var x x₁) = validityCon x x₁
validity (lamⱼ <l <l' F t) = univ (Πⱼ <l ▹ <l' ▹ (un-univ F) ▹ (un-univ (validity t)))
validity (_▹_▹_▹_∘ⱼ_ {F = F} {G = G} r% ⊢F ⊢G g a) = {!!}
validity (fstⱼ X X₁ X₂ X₃ X₄) = {!!}
validity (sndⱼ X X₁ X₂ X₃ X₄) = {!!}
validity (zeroⱼ x) = {!!}
validity (sucⱼ X) = {!!}
validity (natrecⱼ x x₁ X X₁ X₂) = {!!}
validity (Emptyrecⱼ x X) = {!!}
validity (Idⱼ X X₁ X₂) = {!!}
validity (Idreflⱼ X) = {!!}
validity (transpⱼ x x₁ X X₁ X₂ X₃) = {!!}
validity (castⱼ X X₁ X₂ X₃) = {!!}
validity (conv X x) = {!!}
