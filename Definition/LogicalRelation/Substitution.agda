{-# OPTIONS --safe #-}

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
    _∙_ : ∀ {Γ A rA l} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ l ⟩ A ^ rA / [Γ]
        → ⊩ᵛ Γ ∙ A ^ rA

  -- Validity of types
  _⊩ᵛ⟨_⟩_^_/_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → TypeInfo → ⊩ᵛ Γ → Set
  Γ ⊩ᵛ⟨ l ⟩ A ^ r / [Γ] = ∀ {σ} (⊢Δ : ⊢ ε) ([σ] : ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
                   → Σ (ε ⊩⟨ l ⟩ subst σ A ^ r)
                       (λ [Aσ] → ∀ {σ′} ([σ′] : ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ)
                               → ([σ≡σ′] : ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ])
                               → ε ⊩⟨ l ⟩ subst σ A ≡ subst σ′ A ^ r / [Aσ])

  -- Logical relation for substitutions from a valid context
  ⊩ˢ_∷_/_/_ : (σ : Subst) (Γ : Con Term) ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ ε)
             → Set
  ⊩ˢ σ ∷ .ε        / ε  / ⊢Δ                = ⊤
  ⊩ˢ σ ∷ .(Γ ∙ A ^ rA) / (_∙_ {Γ} {A} {rA} {l} [Γ] [A]) / ⊢Δ =
    Σ (⊩ˢ tail σ ∷ Γ / [Γ] / ⊢Δ) λ [tailσ] →
    (ε ⊩⟨ l ⟩ head σ ∷ subst (tail σ) A ^ rA / proj₁ ([A] ⊢Δ [tailσ]))

  -- Logical relation for equality of substitutions from a valid context
  ⊩ˢ_≡_∷_/_/_/_ : (σ σ′ : Subst) (Γ : Con Term) ([Γ] : ⊩ᵛ Γ)
                    (⊢Δ : ⊢ ε) ([σ] : ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) → Set
  ⊩ˢ σ ≡ σ′ ∷ .ε       / ε       / ⊢Δ              / [σ] = ⊤
  ⊩ˢ σ ≡ σ′ ∷ .(Γ ∙ A ^ rA) / (_∙_ {Γ} {A} {rA} {l} [Γ] [A]) / ⊢Δ / [σ] =
    (⊩ˢ tail σ ≡ tail σ′ ∷ Γ / [Γ] / ⊢Δ / proj₁ [σ]) ×
    (ε ⊩⟨ l ⟩ head σ ≡ head σ′ ∷ subst (tail σ) A ^ rA / proj₁ ([A] ⊢Δ (proj₁ [σ])))


-- Validity of terms
_⊩ᵛ⟨_⟩_∷_^_/_/_ : (Γ : Con Term) (l : TypeLevel) (t A : Term) (rA : TypeInfo) ([Γ] : ⊩ᵛ Γ)
                 ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ rA / [Γ]) → Set
Γ ⊩ᵛ⟨ l ⟩ t ∷ A ^ rA / [Γ] / [A] =
  ∀ {σ} (⊢Δ : ⊢ ε) ([σ] : ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ) →
  Σ (ε ⊩⟨ l ⟩ subst σ t ∷ subst σ A ^ rA / proj₁ ([A] ⊢Δ [σ])) λ [tσ] →
  ∀ {σ′} → ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ → ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ]
    → ε ⊩⟨ l ⟩ subst σ t ≡ subst σ′ t ∷ subst σ A ^ rA / proj₁ ([A] ⊢Δ [σ])

-- Validity of type equality
_⊩ᵛ⟨_⟩_≡_^_/_/_ : (Γ : Con Term) (l : TypeLevel) (A B : Term) (rA : TypeInfo) ([Γ] : ⊩ᵛ Γ)
                ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ rA / [Γ]) → Set
Γ ⊩ᵛ⟨ l ⟩ A ≡ B ^ rA / [Γ] / [A] =
  ∀ {σ} (⊢Δ : ⊢ ε) ([σ] : ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
  → ε ⊩⟨ l ⟩ subst σ A ≡ subst σ B ^ rA / proj₁ ([A] ⊢Δ [σ])

-- Validity of term equality
_⊩ᵛ⟨_⟩_≡_∷_^_/_/_ : (Γ : Con Term) (l : TypeLevel) (t u A : Term) (rA : TypeInfo) ([Γ] : ⊩ᵛ Γ)
                    ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ rA / [Γ]) → Set
Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A ^ rA / [Γ] / [A] =
  ∀ {σ} → (⊢Δ : ⊢ ε) ([σ] : ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
          → ε ⊩⟨ l ⟩ subst σ t ≡ subst σ u ∷ subst σ A ^ rA / proj₁ ([A] ⊢Δ [σ])

-- Valid term equality with validity of its type and terms
record [_⊩ᵛ⟨_⟩_≡_∷_^_/_] (Γ : Con Term) (l : TypeLevel)
                       (t u A : Term) (rA : TypeInfo) ([Γ] : ⊩ᵛ Γ) : Set where
  constructor modelsTermEq
  field
    [A]   : Γ ⊩ᵛ⟨ l ⟩ A ^ rA / [Γ]
    [t]   : Γ ⊩ᵛ⟨ l ⟩ t ∷ A ^ rA / [Γ] / [A]
    [u]   : Γ ⊩ᵛ⟨ l ⟩ u ∷ A ^ rA / [Γ] / [A]
    [t≡u] : Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A ^ rA / [Γ] / [A]

-- Validity of reduction of terms
_⊩ᵛ_⇒_∷_^_/_ : (Γ : Con Term) (t u A : Term) (r : TypeLevel) ([Γ] : ⊩ᵛ Γ) → Set
Γ ⊩ᵛ t ⇒ u ∷ A ^ r / [Γ] = ∀ {σ} (⊢Δ : ⊢ ε) ([σ] : ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
                       → ε ⊢ subst σ t ⇒ subst σ u ∷ subst σ A ^ r
