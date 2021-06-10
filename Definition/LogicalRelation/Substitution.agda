{-# OPTIONS --without-K  #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution {{eqrel : EqRelSet}} where

open import Definition.Untyped
open import Definition.Typed
open import Definition.LogicalRelation

open import Tools.Product
open import Tools.Unit


-- The validity judgements:
-- We consider expressions that satisfy these judgments valid

mutual
  -- Validity of contexts
  data ⊩ᵛ_ : Con Term → Set where
    ε : ⊩ᵛ ε
    _∙_ : ∀ {Γ A sA l} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ l ⟩ A ⦂ sA / [Γ]
        → ⊩ᵛ Γ ∙ A ⦂ sA

  -- Validity of types
  _⊩ᵛ⟨_⟩_⦂_/_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → 𝕊 → ⊩ᵛ Γ → Set
  Γ ⊩ᵛ⟨ l ⟩ A ⦂ s / [Γ] = ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
                   → Σ (Δ ⊩⟨ l ⟩ subst σ A ⦂ s)
                       (λ [Aσ] → ∀ {σ′} ([σ′] : Δ ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ)
                               → ([σ≡σ′] : Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ])
                               → Δ ⊩⟨ l ⟩ subst σ A ≡ subst σ′ A ⦂ s / [Aσ])

  -- Logical relation for substitutions from a valid context
  _⊩ˢ_∷_/_/_ : (Δ : Con Term) (σ : Subst) (Γ : Con Term) ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ Δ)
             → Set
  Δ ⊩ˢ σ ∷ .ε        / ε  / ⊢Δ                = ⊤
  Δ ⊩ˢ σ ∷ .(Γ ∙ A ⦂ sA) / (_∙_ {Γ} {A} {sA} {l} [Γ] [A]) / ⊢Δ =
    Σ (Δ ⊩ˢ tail σ ∷ Γ / [Γ] / ⊢Δ) λ [tailσ] →
    (Δ ⊩⟨ l ⟩ head σ ∷ subst (tail σ) A ⦂ sA / proj₁ ([A] ⊢Δ [tailσ]))

  -- Logical relation for equality of substitutions from a valid context
  _⊩ˢ_≡_∷_/_/_/_ : (Δ : Con Term) (σ σ′ : Subst) (Γ : Con Term) ([Γ] : ⊩ᵛ Γ)
                    (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) → Set
  Δ ⊩ˢ σ ≡ σ′ ∷ .ε       / ε       / ⊢Δ              / [σ] = ⊤
  Δ ⊩ˢ σ ≡ σ′ ∷ .(Γ ∙ A ⦂ sA) / (_∙_ {Γ} {A} {sA} {l} [Γ] [A]) / ⊢Δ / [σ] =
    (Δ ⊩ˢ tail σ ≡ tail σ′ ∷ Γ / [Γ] / ⊢Δ / proj₁ [σ]) ×
    (Δ ⊩⟨ l ⟩ head σ ≡ head σ′ ∷ subst (tail σ) A ⦂ sA / proj₁ ([A] ⊢Δ (proj₁ [σ])))


-- Validity of terms
_⊩ᵛ⟨_⟩_∷_⦂_/_/_ : (Γ : Con Term) (l : TypeLevel) (t A : Term) (sA : 𝕊) ([Γ] : ⊩ᵛ Γ)
                 ([A] : Γ ⊩ᵛ⟨ l ⟩ A ⦂ sA / [Γ]) → Set
Γ ⊩ᵛ⟨ l ⟩ t ∷ A ⦂ sA / [Γ] / [A] =
  ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) →
  Σ (Δ ⊩⟨ l ⟩ subst σ t ∷ subst σ A ⦂ sA / proj₁ ([A] ⊢Δ [σ])) λ [tσ] →
  ∀ {σ′} → Δ ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ → Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ]
    → Δ ⊩⟨ l ⟩ subst σ t ≡ subst σ′ t ∷ subst σ A ⦂ sA / proj₁ ([A] ⊢Δ [σ])

-- Validity of type equality
_⊩ᵛ⟨_⟩_≡_⦂_/_/_ : (Γ : Con Term) (l : TypeLevel) (A B : Term) (sA : 𝕊) ([Γ] : ⊩ᵛ Γ)
                ([A] : Γ ⊩ᵛ⟨ l ⟩ A ⦂ sA / [Γ]) → Set
Γ ⊩ᵛ⟨ l ⟩ A ≡ B ⦂ sA / [Γ] / [A] =
  ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
  → Δ ⊩⟨ l ⟩ subst σ A ≡ subst σ B ⦂ sA / proj₁ ([A] ⊢Δ [σ])

-- Validity of term equality
_⊩ᵛ⟨_⟩_≡_∷_⦂_/_/_ : (Γ : Con Term) (l : TypeLevel) (t u A : Term) (sA : 𝕊) ([Γ] : ⊩ᵛ Γ)
                    ([A] : Γ ⊩ᵛ⟨ l ⟩ A ⦂ sA / [Γ]) → Set
Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A ⦂ sA / [Γ] / [A] =
  ∀ {Δ σ} → (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
          → Δ ⊩⟨ l ⟩ subst σ t ≡ subst σ u ∷ subst σ A ⦂ sA / proj₁ ([A] ⊢Δ [σ])

-- Valid term equality with validity of its type and terms
record [_⊩ᵛ⟨_⟩_≡_∷_⦂_/_] (Γ : Con Term) (l : TypeLevel)
                       (t u A : Term) (sA : 𝕊) ([Γ] : ⊩ᵛ Γ) : Set where
  constructor modelsTermEq
  field
    [A]   : Γ ⊩ᵛ⟨ l ⟩ A ⦂ sA / [Γ]
    [t]   : Γ ⊩ᵛ⟨ l ⟩ t ∷ A ⦂ sA / [Γ] / [A]
    [u]   : Γ ⊩ᵛ⟨ l ⟩ u ∷ A ⦂ sA / [Γ] / [A]
    [t≡u] : Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A ⦂ sA / [Γ] / [A]

-- Validity of reduction of terms
_⊩ᵛ_⇒_∷_⦂_/_ : (Γ : Con Term) (t u A : Term) (sA : 𝕊) ([Γ] : ⊩ᵛ Γ) → Set
Γ ⊩ᵛ t ⇒ u ∷ A ⦂ sA / [Γ] = ∀ {Δ σ} (⊢Δ : ⊢ Δ) ([σ] : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
                       → Δ ⊢ subst σ t ⇒ subst σ u ∷ subst σ A ⦂ sA
