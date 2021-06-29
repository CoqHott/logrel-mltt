{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Universe {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.MaybeEmbed

open import Tools.Product
open import Tools.Empty

import Definition.LogicalRelation.Weakening as wkLR
import Tools.PropositionalEquality as PE
import Data.Nat as Nat

-- Validity of the universe type.
U¹ᵛ : ∀ {Γ rU l} → (ι ¹ <∞ l) → ([Γ] : ⊩ᵛ Γ)
      → Γ ⊩ᵛ⟨ l ⟩ Univ rU ¹ ^ [ ! , ∞ ] / [Γ]
U¹ᵛ {Γ} {rU} ∞< [Γ] ⊢Δ [σ] =
  Ugen ⊢Δ , (λ [σ′] [σ≡σ′] → id (Uⱼ ⊢Δ))

U⁰ᵛ : ∀ {Γ rU l' l} → (⁰ ≤ l') → (ι l' <∞ l) → ([Γ] : ⊩ᵛ Γ)
      → Γ ⊩ᵛ⟨ l ⟩ Univ rU ⁰ ^ [ ! , ι ¹ ] / [Γ]
U⁰ᵛ {Γ} {rU} (<is≤ 0<1) ∞< [Γ] ⊢Δ [σ] = emb ∞< (Uᵣ (Uᵣ rU ⁰ emb< PE.refl [[ Ugenⱼ ⊢Δ , Ugenⱼ ⊢Δ , id (Ugenⱼ ⊢Δ) ]])) , (λ [σ′] [σ≡σ′] → id (Ugenⱼ ⊢Δ))
U⁰ᵛ {Γ} {rU} (≡is≤ PE.refl) l< [Γ] ⊢Δ [σ] = 
  Uᵣ (Uᵣ rU ⁰ l< PE.refl [[ Ugenⱼ ⊢Δ , Ugenⱼ ⊢Δ , id (Ugenⱼ ⊢Δ) ]])
  , (λ [σ′] [σ≡σ′] → id (Ugenⱼ ⊢Δ))

Uᵛgen : ∀ {Γ rU lU lU' l} → (lU ≤ lU') → (ι lU' <∞ l) → ([Γ] : ⊩ᵛ Γ)
     → Γ ⊩ᵛ⟨ l ⟩ Univ rU lU ^ [ ! , next lU ] / [Γ]
Uᵛgen {lU = ⁰} = U⁰ᵛ
Uᵛgen {lU = ¹} (≡is≤ PE.refl) = U¹ᵛ

Uᵛ : ∀ {Γ rU lU l} → (ι lU <∞ l) → ([Γ] : ⊩ᵛ Γ)
     → Γ ⊩ᵛ⟨ l ⟩ Univ rU lU ^ [ ! , next lU ] / [Γ]
Uᵛ = Uᵛgen (≡is≤ PE.refl)

Uᵗᵛ₁ :  ∀ {Γ rU} → (⊢Γ : ⊢ Γ) → Γ ⊩⟨ ∞ ⟩ Univ rU ⁰ ∷ Univ ! ¹ ^ [ ! , ∞ ] / Ugen ⊢Γ
Uᵗᵛ₁ {Γ} {rU} ⊢Γ = Uₜ (Univ rU ⁰) (idRedTerm:*: (univ 0<1 ⊢Γ)) Uₙ (≅-U⁰refl ⊢Γ)
                                  (λ σ ⊢Δ₁ → Uᵣ′ (Univ rU ⁰) (ι ¹) rU ⁰ emb< PE.refl (idRed:*: (Ugenⱼ ⊢Δ₁)))

Uᵗᵛ : ∀ {Γ rU} → ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ ∞ ⟩ Univ rU ⁰ ∷ Univ ! ¹ ^ [ ! , ∞ ] / [Γ] / Uᵛ ∞< [Γ]
Uᵗᵛ {Γ} {rU} [Γ] = λ ⊢Δ [σ] → Uᵗᵛ₁ ⊢Δ
                            , λ [σ′] [σ≡σ′] → Uₜ₌ (Uᵗᵛ₁ ⊢Δ) (Uᵗᵛ₁ ⊢Δ) (≅-U⁰refl ⊢Δ) λ [ρ] ⊢Δ → id (Ugenⱼ ⊢Δ)

-- Valid terms of type U are valid types.
univᵛ : ∀ {A Γ rU lU lU' l} ([Γ] : ⊩ᵛ Γ)
        (lU< : lU ≤ lU')
        ([U] : Γ ⊩ᵛ⟨ l ⟩ Univ rU lU ^ [ ! , next lU ] / [Γ])
      → Γ ⊩ᵛ⟨ l ⟩ A ∷ Univ rU lU ^ [ ! , next lU ] / [Γ] / [U]
      → Γ ⊩ᵛ⟨ ι lU' ⟩ A ^ [ rU , ι lU ] / [Γ]
univᵛ {lU = lU} {l = l} [Γ] lU< [U] [A] ⊢Δ [σ] =
  let [A]₁ = irrelevance-≤ lU< (univEq (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ]))) in
  [A]₁ , λ [σ′] [σ≡σ′] → univEqEq (proj₁ ([U] ⊢Δ [σ])) [A]₁
                                  ((proj₂ ([A] ⊢Δ [σ])) [σ′] [σ≡σ′])



-- Valid term equality of type U is valid type equality.
univEqᵛ : ∀ {A B Γ rU lU l l′} ([Γ] : ⊩ᵛ Γ)
          ([U] : Γ ⊩ᵛ⟨ l′ ⟩ Univ rU lU ^ [ ! , next lU ] / [Γ])
          ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ [ rU , ι lU ] / [Γ])
        → Γ ⊩ᵛ⟨ l′ ⟩ A ≡ B ∷ Univ rU lU ^ [ ! , next lU ] / [Γ] / [U]
        → Γ ⊩ᵛ⟨ l ⟩ A ≡ B ^ [ rU , ι lU ] / [Γ] / [A]
univEqᵛ {A} [Γ] [U] [A] [t≡u] ⊢Δ [σ] =
  univEqEq (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])) ([t≡u] ⊢Δ [σ])

univᵗᵛ : ∀ {Γ A t r l′}  ([Γ] : ⊩ᵛ Γ)
       → ([U] : Γ ⊩ᵛ⟨ ∞ ⟩ Univ r l′ ^ [ ! , next l′ ] / [Γ] )
       → ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ∷ Univ r l′ ^ [ ! , next l′ ] / [Γ] / [U])
       → Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ [ r , ι l′ ] / [Γ] / maybeEmbᵛ {A = A} [Γ] (univᵛ {A = A} [Γ] (≡is≤ PE.refl) [U] [A]) 
       → Γ ⊩ᵛ⟨ ι l′ ⟩ t ∷ A ^ [ r , ι l′ ] / [Γ] / univᵛ {A = A} [Γ] (≡is≤ PE.refl) [U] [A]
univᵗᵛ {Γ} {A} {t} {r} {⁰} [Γ] [U] [A] [t] ⊢Δ [σ] =
  univEqTerm (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ])) ,
  λ [σ′] [σ≡σ′] → univEqEqTerm (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ])) (proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]) 
univᵗᵛ {Γ} {A} {t} {r} {¹} [Γ] [U] [A] [t] ⊢Δ [σ] =
  univEqTerm (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ])) ,
  λ [σ′] [σ≡σ′] → univEqEqTerm (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ])) (proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′]) 


un-univᵛ : ∀ {A Γ r l} ([Γ] : ⊩ᵛ Γ)
        ([U] : Γ ⊩ᵛ⟨ next l ⟩ Univ r l ^ [ ! , next l ] / [Γ])
      → Γ ⊩ᵛ⟨ ι l ⟩ A ^ [ r , ι l ] / [Γ]
      → Γ ⊩ᵛ⟨ next l ⟩ A ∷ Univ r l ^ [ ! , next l ] / [Γ] / [U]
un-univᵛ {l = l} [Γ] [U] [A] = λ ⊢Δ [σ] →
  irrelevanceTerm (Ugen (wf (escape (proj₁ ([A] ⊢Δ [σ])))))  (proj₁ ([U] ⊢Δ [σ])) (un-univEq (proj₁ ([A] ⊢Δ [σ]))) ,
  λ [σ′] [σ≡σ′] → irrelevanceEqTerm (Ugen (wf (escape (proj₁ ([A] ⊢Δ [σ]))))) (proj₁ ([U] ⊢Δ [σ])) (un-univEqEq (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ′])) (proj₂ ([A] ⊢Δ [σ]) [σ′] [σ≡σ′])) 


un-univEqᵛ : ∀ {A B Γ r l} ([Γ] : ⊩ᵛ Γ)
        ([U] : Γ ⊩ᵛ⟨ next l ⟩ Univ r l ^ [ ! , next l ] / [Γ])
      → ([A] : Γ ⊩ᵛ⟨ ι l ⟩ A ^ [ r , ι l ] / [Γ])
      → ([B] : Γ ⊩ᵛ⟨ ι l ⟩ B ^ [ r , ι l ] / [Γ])
      → Γ ⊩ᵛ⟨ ι l ⟩ A ≡ B ^ [ r , ι l ] / [Γ] / [A]
      → Γ ⊩ᵛ⟨ next l ⟩ A ≡ B ∷ Univ r l ^ [ ! , next l ] / [Γ] / [U] 
un-univEqᵛ {l = l} [Γ] [U] [A] [B] [A≡B] = λ ⊢Δ [σ] → 
  irrelevanceEqTerm (Ugen (wf (escape (proj₁ ([A] ⊢Δ [σ])))))  (proj₁ ([U] ⊢Δ [σ])) (un-univEqEq (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([B] ⊢Δ [σ])) ([A≡B] ⊢Δ [σ]))
