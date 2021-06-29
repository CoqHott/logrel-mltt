{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Emptyrec {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties
open import Definition.Typed
import Definition.Typed.Weakening as T
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Application
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
import Definition.LogicalRelation.Substitution.Irrelevance as S
open import Definition.LogicalRelation.Substitution.Reflexivity
open import Definition.LogicalRelation.Substitution.Weakening
open import Definition.LogicalRelation.Substitution.Introductions.Empty
open import Definition.LogicalRelation.Substitution.Introductions.Pi
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst

open import Tools.Product
open import Tools.Unit
open import Tools.Empty
open import Tools.Nat

import Tools.PropositionalEquality as PE

-- Reducibility of natural recursion under a valid substitution.
EmptyrecTerm : ∀ {F rF lF lEmpty n Γ Δ σ l}
             ([Γ]  : ⊩ᵛ Γ)
             ([F]  : Γ ⊩ᵛ⟨ l ⟩ F ^ [ rF , lF ] / [Γ])
             (⊢Δ   : ⊢ Δ)
             ([σ]  : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
             ([σn] : Δ ⊩⟨ l ⟩ n ∷ Empty  ^ [ % , ι lEmpty ] / Emptyᵣ (idRed:*: (univ (Emptyⱼ ⊢Δ))))
           → Δ ⊩⟨ l ⟩ Emptyrec (subst σ F) n
               ∷ subst σ F ^ [ rF , lF ]
               / proj₁ ([F] ⊢Δ [σ])
EmptyrecTerm {F} {rF = !} {lF} {lEmpty} {n} {Γ} {Δ} {σ} {l} [Γ] [F] ⊢Δ [σ]
           (Emptyₜ (ne d)) =
  let [Empty] = Emptyᵛ {ll = lEmpty} {l = l} [Γ]
      [σEmpty] = proj₁ ([Empty] ⊢Δ [σ])
      [σF] = proj₁ ([F] ⊢Δ [σ])
      ⊢F = escape [σF]
      ⊢F≡F = escapeEq [σF] (reflEq [σF])
  in neuTerm [σF] (Emptyrecₙ) (Emptyrecⱼ ⊢F d)
                  (~-Emptyrec ⊢F≡F d d)
EmptyrecTerm {F} {rF = %} {lF} {lEmpty} {n} {Γ} {Δ} {σ} {l} [Γ] [F] ⊢Δ [σ]
           (Emptyₜ (ne d)) =
  let [Empty] = Emptyᵛ {ll = lEmpty} {l = l} [Γ]
      [σEmpty] = proj₁ ([Empty] ⊢Δ [σ])
      [σF] = proj₁ ([F] ⊢Δ [σ])
      ⊢F = escape [σF]
      ⊢F≡F = escapeEq [σF] (reflEq [σF])
  in logRelIrr [σF] (Emptyrecⱼ ⊢F d)


-- Reducibility of natural recursion congurence under a valid substitution equality.
Emptyrec-congTerm : ∀ {F F′ rF lF lEmpty n m Γ Δ σ σ′ l}
                  ([Γ]      : ⊩ᵛ Γ)
                  ([F]      : Γ ⊩ᵛ⟨ l ⟩ F ^ [ rF , lF ] / [Γ])
                  ([F′]     : Γ ⊩ᵛ⟨ l ⟩ F′ ^ [ rF , lF ] / [Γ])
                  ([F≡F′]   : Γ ⊩ᵛ⟨ l ⟩ F ≡ F′ ^ [ rF , lF ] / [Γ] / [F])
                  (⊢Δ       : ⊢ Δ)
                  ([σ]      : Δ ⊩ˢ σ  ∷ Γ / [Γ] / ⊢Δ)
                  ([σ′]     : Δ ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ)
                  ([σ≡σ′]   : Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ])
                  ([σn]     : Δ ⊩⟨ l ⟩ n ∷ Empty  ^ [ % , ι lEmpty ] / Emptyᵣ (idRed:*: (univ (Emptyⱼ ⊢Δ))))
                  ([σm]     : Δ ⊩⟨ l ⟩ m ∷ Empty  ^ [ % , ι lEmpty ] / Emptyᵣ (idRed:*: (univ (Emptyⱼ ⊢Δ))))
                → Δ ⊩⟨ l ⟩ Emptyrec (subst σ F) n
                    ≡ Emptyrec (subst σ′ F′) m
                    ∷ subst σ F ^ [ rF , lF ]
                    / proj₁ ([F] ⊢Δ [σ])
Emptyrec-congTerm {F} {F′} {rF = !} {lF} {lEmpty} {n} {m} {Γ} {Δ} {σ} {σ′} {l}
                [Γ] [F] [F′] [F≡F′]
                ⊢Δ [σ] [σ′] [σ≡σ′]
                (Emptyₜ (ne ⊢n′))
                (Emptyₜ (ne ⊢m′)) =
  let [Empty] = Emptyᵛ {ll = lEmpty} {l = l} [Γ]
      [σEmpty] = proj₁ ([Empty] ⊢Δ [σ])
      [σ′Empty] = proj₁ ([Empty] ⊢Δ [σ′])
      [σF] = proj₁ ([F] ⊢Δ [σ])
      [σ′F] = proj₁ ([F] ⊢Δ [σ′])
      [σ′F′] = proj₁ ([F′] ⊢Δ [σ′])
      ⊢F = escape [σF]
      ⊢F≡F = escapeEq [σF] (reflEq [σF])
      ⊢F′ = escape [σ′F′]
      ⊢F′≡F′ = escapeEq [σ′F′] (reflEq [σ′F′])
      ⊢σF≡σ′F = escapeEq [σF] (proj₂ ([F] ⊢Δ [σ]) [σ′] [σ≡σ′])
      ⊢σ′F≡σ′F′ = escapeEq [σ′F] ([F≡F′] ⊢Δ [σ′])
      ⊢F≡F′ = ≅-trans ⊢σF≡σ′F ⊢σ′F≡σ′F′
      [σF≡σ′F] = proj₂ ([F] ⊢Δ [σ]) [σ′] [σ≡σ′]
      [σ′F≡σ′F′] = [F≡F′] ⊢Δ [σ′]
      [σF≡σ′F′] = transEq [σF] [σ′F] [σ′F′] [σF≡σ′F] [σ′F≡σ′F′]
      EmptyrecN = neuTerm [σF] (Emptyrecₙ) (Emptyrecⱼ ⊢F ⊢n′)
                           (~-Emptyrec ⊢F≡F ⊢n′ ⊢n′)
      EmptyrecM = neuTerm [σ′F′] (Emptyrecₙ) (Emptyrecⱼ ⊢F′ ⊢m′)
                           (~-Emptyrec ⊢F′≡F′ ⊢m′ ⊢m′)
      EmptyrecN≡M =
          neuEqTerm [σF] Emptyrecₙ Emptyrecₙ
                     (Emptyrecⱼ ⊢F ⊢n′)
                     (conv (Emptyrecⱼ ⊢F′ ⊢m′)
                            (sym (≅-eq (escapeEq [σF]
                              (transEq [σF] [σ′F] [σ′F′] [σF≡σ′F] [σ′F≡σ′F′])))))
                     (~-Emptyrec ⊢F≡F′ ⊢n′ ⊢m′)
  in EmptyrecN≡M

Emptyrec-congTerm {F} {F′} {rF = %} {lF} {lEmpty} {n} {m} {Γ} {Δ} {σ} {σ′} {l}
                [Γ] [F] [F′] [F≡F′]
                ⊢Δ [σ] [σ′] [σ≡σ′]
                (Emptyₜ (ne ⊢n′))
                (Emptyₜ (ne ⊢m′)) =
  let [Empty] = Emptyᵛ {ll = lEmpty} {l = l} [Γ]
      [σEmpty] = proj₁ ([Empty] ⊢Δ [σ])
      [σ′Empty] = proj₁ ([Empty] ⊢Δ [σ′])
      [σF] = proj₁ ([F] ⊢Δ [σ])
      [σ′F] = proj₁ ([F] ⊢Δ [σ′])
      [σ′F′] = proj₁ ([F′] ⊢Δ [σ′])
      ⊢F = escape [σF]
      ⊢F≡F = escapeEq [σF] (reflEq [σF])
      ⊢F′ = escape [σ′F′]
      ⊢F′≡F′ = escapeEq [σ′F′] (reflEq [σ′F′])
      ⊢σF≡σ′F = escapeEq [σF] (proj₂ ([F] ⊢Δ [σ]) [σ′] [σ≡σ′])
      ⊢σ′F≡σ′F′ = escapeEq [σ′F] ([F≡F′] ⊢Δ [σ′])
      ⊢F≡F′ = ≅-trans ⊢σF≡σ′F ⊢σ′F≡σ′F′
      [σF≡σ′F] = proj₂ ([F] ⊢Δ [σ]) [σ′] [σ≡σ′]
      [σ′F≡σ′F′] = [F≡F′] ⊢Δ [σ′]
      [σF≡σ′F′] = transEq [σF] [σ′F] [σ′F′] [σF≡σ′F] [σ′F≡σ′F′]
  in logRelIrrEq [σF] (Emptyrecⱼ ⊢F ⊢n′) (conv (Emptyrecⱼ ⊢F′ ⊢m′)
                            (sym (≅-eq (escapeEq [σF]
                              (transEq [σF] [σ′F] [σ′F′] [σF≡σ′F] [σ′F≡σ′F′])))))



-- Validity of empty recursion.
Emptyrecᵛ : ∀ {F rF lF lEmpty  n Γ l} ([Γ] : ⊩ᵛ Γ)
          ([Empty]  : Γ ⊩ᵛ⟨ l ⟩ Empty ^ [ % , ι lEmpty ] / [Γ])
          ([F]  : Γ ⊩ᵛ⟨ l ⟩ F ^ [ rF , lF ] / [Γ])
        → ([n] : Γ ⊩ᵛ⟨ l ⟩ n ∷ Empty ^ [ % , ι lEmpty ] / [Γ] / [Empty])
        → Γ ⊩ᵛ⟨ l ⟩ Emptyrec F n ∷ F ^ [ rF , lF ] / [Γ] / [F]
Emptyrecᵛ {F} {rF} {lF} {lEmpty} {n} {l = l} [Γ] [Empty] [F] [n]
        {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [σn] = irrelevanceTerm {l′ = l} (proj₁ ([Empty] ⊢Δ [σ]))
                             (Emptyᵣ (idRed:*: (univ (Emptyⱼ ⊢Δ)))) (proj₁ ([n] ⊢Δ [σ]))
  in EmptyrecTerm {F = F} [Γ] [F] ⊢Δ [σ] [σn]
    , λ {σ'} [σ′] [σ≡σ′] →
      let [σ′n] = irrelevanceTerm {l′ = l} (proj₁ ([Empty] ⊢Δ [σ′]))
                                  (Emptyᵣ (idRed:*: (univ (Emptyⱼ ⊢Δ)))) (proj₁ ([n] ⊢Δ [σ′]))
          [σn≡σ′n] = irrelevanceEqTerm {l′ = l} (proj₁ ([Empty] ⊢Δ [σ]))
                                       (Emptyᵣ (idRed:*: (univ (Emptyⱼ ⊢Δ))))
                                       (proj₂ ([n] ⊢Δ [σ]) [σ′] [σ≡σ′])
          congTerm = Emptyrec-congTerm {F = F} {F′ = F} [Γ] [F] [F] (reflᵛ {F} {l = l} [Γ] [F])
                                       ⊢Δ [σ] [σ′] [σ≡σ′] [σn] [σ′n]
      in congTerm

-- Validity of natural recursion congurence.
Emptyrec-congᵛ : ∀ {F F′ rF lF lEmpty n n′ Γ l} ([Γ] : ⊩ᵛ Γ)
          ([Empty]  : Γ ⊩ᵛ⟨ l ⟩ Empty ^ [ % , ι lEmpty ] / [Γ])
          ([F]  : Γ ⊩ᵛ⟨ l ⟩ F ^ [ rF , lF ] / [Γ])
          ([F′]  : Γ ⊩ᵛ⟨ l ⟩ F′ ^ [ rF , lF ] / [Γ])
          ([F≡F′]  : Γ ⊩ᵛ⟨ l ⟩ F ≡ F′ ^ [ rF , lF ] / [Γ] / [F])
          ([n] : Γ ⊩ᵛ⟨ l ⟩ n ∷ Empty ^ [ % , ι lEmpty ] / [Γ] / [Empty])
          ([n′] : Γ ⊩ᵛ⟨ l ⟩ n′ ∷ Empty ^ [ % , ι lEmpty ] / [Γ] / [Empty])
        → Γ ⊩ᵛ⟨ l ⟩ Emptyrec F n ≡ Emptyrec F′ n′ ∷ F ^ [ rF , lF ] / [Γ] / [F]
Emptyrec-congᵛ {F} {F′} {rF} {lF} {lEmpty} {n} {n′} {l = l}
             [Γ] [Empty] [F] [F′] [F≡F′]
             [n] [n′] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [σn] = irrelevanceTerm {l′ = l} (proj₁ ([Empty] ⊢Δ [σ]))
                             (Emptyᵣ (idRed:*: (univ (Emptyⱼ ⊢Δ)))) (proj₁ ([n] ⊢Δ [σ]))
      [σn′] = irrelevanceTerm {l′ = l} (proj₁ ([Empty] ⊢Δ [σ]))
                             (Emptyᵣ (idRed:*: (univ (Emptyⱼ ⊢Δ)))) (proj₁ ([n′] ⊢Δ [σ]))
      congTerm = Emptyrec-congTerm {F} {F′} [Γ] [F] [F′] [F≡F′]
                                   ⊢Δ [σ] [σ] (reflSubst [Γ] ⊢Δ [σ]) [σn] [σn′] 
  in congTerm
