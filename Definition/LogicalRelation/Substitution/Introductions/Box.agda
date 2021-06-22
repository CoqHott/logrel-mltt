{-# OPTIONS --without-K  --allow-unsolved-meta #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Box {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Introductions.Universe

open import Tools.Product


Boxᵛ : ∀ {Γ A sA l} ([Γ] : ⊩ᵛ Γ) ([A] : Γ ⊩ᵛ⟨ l ⟩ A ⦂ ‼ sA / [Γ]) → Γ ⊩ᵛ⟨ l ⟩ Box sA A ⦂ 𝕥y / [Γ]
Boxᵛ [Γ] [A] ⊢Δ [σ] = {!!}

Boxᵗᵛ : ∀ {Γ A sA l}
          ([Γ] : ⊩ᵛ Γ)
          ([A] : Γ ⊩ᵛ⟨ l ⟩ A ∷ Univ sA ⦂ 𝕥y / [Γ] / Uᵛ [Γ])
      → Γ ⊩ᵛ⟨ l ⟩ Box sA A ∷ Univ 𝕥y ⦂ 𝕥y / [Γ] / Uᵛ [Γ]
Boxᵗᵛ [Γ] [A] ⊢Δ [σ] = ?


boxᵛ : ∀ {Γ A s t l}
         ([Γ] : ⊩ᵛ Γ)
         ([A] : Γ ⊩ᵛ⟨ l ⟩ A ⦂ s / [Γ])
         ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ A ⦂ s / [Γ] / [A])
     → Γ ⊩ᵛ⟨ l ⟩ box s t ∷ Box s A ⦂ 𝕥y / [Γ] / Boxᵛ [Γ] [A]
boxᵛ [Γ] [A] [t] = ?


-- Box-congᵛ : ∀ {}
