{-# OPTIONS --without-K  #-}

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


-- Natural recursion closure reduction (requires reducible terms and equality).
Emptyrec-subst* : ∀ {Γ C sC n n′ l}
              → Γ ⊢ C ⦂ sC
              → Γ ⊢ n ⇒* n′ ∷ Empty ⦂ 𝕥y
              → ([Empty] : Γ ⊩⟨ l ⟩ Empty ⦂ 𝕥y)
              → Γ ⊩⟨ l ⟩ n′ ∷ Empty ⦂ 𝕥y / [Empty]
              → Γ ⊢ Emptyrec C n ⇒* Emptyrec C n′ ∷ C ⦂ sC
Emptyrec-subst* C (id x) [Empty] [n′] = id (Emptyrecⱼ C x)
Emptyrec-subst* C (x ⇨ n⇒n′) [Empty] [n′] =
  let q , w = redSubst*Term n⇒n′ [Empty] [n′]
      a , s = redSubstTerm x [Empty] q
  in  Emptyrec-subst C x ⇨ conv* (Emptyrec-subst* C n⇒n′ [Empty] [n′]) (refl C)

-- Reducibility of natural recursion under a valid substitution.
EmptyrecTerm : ∀ {F sF n Γ Δ σ l}
             ([Γ]  : ⊩ᵛ Γ)
             ([F]  : Γ ⊩ᵛ⟨ l ⟩ F ⦂ sF / [Γ])
             (⊢Δ   : ⊢ Δ)
             ([σ]  : Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
             ([σn] : Δ ⊩⟨ l ⟩ n ∷ Empty  ⦂ 𝕥y / Emptyᵣ (idRed:*: (Emptyⱼ ⊢Δ)))
           → Δ ⊩⟨ l ⟩ Emptyrec (subst σ F) n
               ∷ subst σ F ⦂ sF
               / proj₁ ([F] ⊢Δ [σ])
EmptyrecTerm {F} {sF} {n} {Γ} {Δ} {σ} {l} [Γ] [F] ⊢Δ [σ]
           (Emptyₜ m d n≡n (ne (neNfₜ neM ⊢m m≡m))) =
  let [Empty] = Emptyᵛ {l = l} [Γ]
      [σEmpty] = proj₁ ([Empty] ⊢Δ [σ])
      [σm] = neuTerm [σEmpty] neM ⊢m m≡m
      [σF] = proj₁ ([F] ⊢Δ [σ])
      ⊢F = escape [σF]
      ⊢F≡F = escapeEq [σF] (reflEq [σF])
      EmptyrecM = neuTerm [σF] (Emptyrecₙ neM) (Emptyrecⱼ ⊢F ⊢m)
                        (~-Emptyrec ⊢F≡F m≡m)
      reduction = Emptyrec-subst* ⊢F (redₜ d) [σEmpty] [σm]
  in proj₁ (redSubst*Term reduction [σF] EmptyrecM)


-- Reducibility of natural recursion congurence under a valid substitution equality.
Emptyrec-congTerm : ∀ {F F′ sF n m Γ Δ σ σ′ l}
                  ([Γ]      : ⊩ᵛ Γ)
                  ([F]      : Γ ⊩ᵛ⟨ l ⟩ F ⦂ sF / [Γ])
                  ([F′]     : Γ ⊩ᵛ⟨ l ⟩ F′ ⦂ sF / [Γ])
                  ([F≡F′]   : Γ ⊩ᵛ⟨ l ⟩ F ≡ F′ ⦂ sF / [Γ] / [F])
                  (⊢Δ       : ⊢ Δ)
                  ([σ]      : Δ ⊩ˢ σ  ∷ Γ / [Γ] / ⊢Δ)
                  ([σ′]     : Δ ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ)
                  ([σ≡σ′]   : Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ])
                  ([σn]     : Δ ⊩⟨ l ⟩ n ∷ Empty  ⦂ 𝕥y / Emptyᵣ (idRed:*: (Emptyⱼ ⊢Δ)))
                  ([σm]     : Δ ⊩⟨ l ⟩ m ∷ Empty  ⦂ 𝕥y / Emptyᵣ (idRed:*: (Emptyⱼ ⊢Δ)))
                  ([σn≡σm]  : Δ ⊩⟨ l ⟩ n ≡ m ∷ Empty  ⦂ 𝕥y / Emptyᵣ (idRed:*: (Emptyⱼ ⊢Δ)))
                → Δ ⊩⟨ l ⟩ Emptyrec (subst σ F) n
                    ≡ Emptyrec (subst σ′ F′) m
                    ∷ subst σ F ⦂ sF
                    / proj₁ ([F] ⊢Δ [σ])
Emptyrec-congTerm {F} {F′} {sF} {n} {m} {Γ} {Δ} {σ} {σ′} {l}
                [Γ] [F] [F′] [F≡F′]
                ⊢Δ [σ] [σ′] [σ≡σ′]
                (Emptyₜ n′ d n≡n (ne (neNfₜ neN′ ⊢n′ n≡n₁)))
                (Emptyₜ m′ d′ m≡m (ne (neNfₜ neM′ ⊢m′ m≡m₁)))
                (Emptyₜ₌ n″ m″ d₁ d₁′ t≡u (ne (neNfₜ₌ x₂ x₃ prop₂))) =
  let n″≡n′ = whrDet*Term (redₜ d₁ , ne x₂) (redₜ d , ne neN′)
      m″≡m′ = whrDet*Term (redₜ d₁′ , ne x₃) (redₜ d′ , ne neM′)
      [Empty] = Emptyᵛ {l = l} [Γ]
      [σEmpty] = proj₁ ([Empty] ⊢Δ [σ])
      [σ′Empty] = proj₁ ([Empty] ⊢Δ [σ′])
      [σF] = proj₁ ([F] ⊢Δ [σ])
      [σ′F] = proj₁ ([F] ⊢Δ [σ′])
      [σ′F′] = proj₁ ([F′] ⊢Δ [σ′])
      [σn′] = neuTerm [σEmpty] neN′ ⊢n′ n≡n₁
      [σ′m′] = neuTerm [σ′Empty] neM′ ⊢m′ m≡m₁
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
      EmptyrecN = neuTerm [σF] (Emptyrecₙ neN′) (Emptyrecⱼ ⊢F ⊢n′)
                        (~-Emptyrec ⊢F≡F n≡n₁)
      EmptyrecM = neuTerm [σ′F′] (Emptyrecₙ neM′) (Emptyrecⱼ ⊢F′ ⊢m′)
                        (~-Emptyrec ⊢F′≡F′ m≡m₁)
      EmptyrecN≡M =
          (neuEqTerm [σF] (Emptyrecₙ neN′) (Emptyrecₙ neM′)
                     (Emptyrecⱼ ⊢F ⊢n′)
                     (conv (Emptyrecⱼ ⊢F′ ⊢m′)
                            (sym (≅-eq (escapeEq [σF]
                              (transEq [σF] [σ′F] [σ′F′] [σF≡σ′F] [σ′F≡σ′F′])))))
                     (~-Emptyrec ⊢F≡F′
                               (PE.subst₂ (λ x y → _ ⊢ x ~ y ∷ _ ⦂ 𝕥y)
                                          n″≡n′ m″≡m′ prop₂)))
      reduction₁ = Emptyrec-subst* ⊢F (redₜ d) [σEmpty] [σn′]
      reduction₂ = Emptyrec-subst* ⊢F′ (redₜ d′) [σ′Empty] [σ′m′]
      eq₁ = proj₂ (redSubst*Term reduction₁ [σF] EmptyrecN)
      eq₂ = proj₂ (redSubst*Term reduction₂ [σ′F′] EmptyrecM)
  in transEqTerm [σF] eq₁
                 (transEqTerm [σF] EmptyrecN≡M
                              (convEqTerm₂ [σF] [σ′F′] [σF≡σ′F′]
                                           (symEqTerm [σ′F′] eq₂)))



-- Validity of empty recursion.
Emptyrecᵛ : ∀ {F sF n Γ l} ([Γ] : ⊩ᵛ Γ)
          ([Empty]  : Γ ⊩ᵛ⟨ l ⟩ Empty ⦂ 𝕥y / [Γ])
          ([F]  : Γ ⊩ᵛ⟨ l ⟩ F ⦂ sF / [Γ])
        → ([n] : Γ ⊩ᵛ⟨ l ⟩ n ∷ Empty ⦂ 𝕥y / [Γ] / [Empty])
        → Γ ⊩ᵛ⟨ l ⟩ Emptyrec F n ∷ F ⦂ sF / [Γ] / [F]
Emptyrecᵛ {F} {sF} {n} {l = l} [Γ] [Empty] [F] [n]
        {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [σn] = irrelevanceTerm {l′ = l} (proj₁ ([Empty] ⊢Δ [σ]))
                             (Emptyᵣ (idRed:*: (Emptyⱼ ⊢Δ))) (proj₁ ([n] ⊢Δ [σ]))
  in EmptyrecTerm {F = F} [Γ] [F] ⊢Δ [σ] [σn]
    , λ {σ'} [σ′] [σ≡σ′] →
      let [σ′n] = irrelevanceTerm {l′ = l} (proj₁ ([Empty] ⊢Δ [σ′]))
                                  (Emptyᵣ (idRed:*: (Emptyⱼ ⊢Δ))) (proj₁ ([n] ⊢Δ [σ′]))
          [σn≡σ′n] = irrelevanceEqTerm {l′ = l} (proj₁ ([Empty] ⊢Δ [σ]))
                                       (Emptyᵣ (idRed:*: (Emptyⱼ ⊢Δ)))
                                       (proj₂ ([n] ⊢Δ [σ]) [σ′] [σ≡σ′])
          congTerm = Emptyrec-congTerm {F = F} {F′ = F} [Γ] [F] [F] (reflᵛ {F} {l = l} [Γ] [F])
                                       ⊢Δ [σ] [σ′] [σ≡σ′] [σn] [σ′n] [σn≡σ′n]
      in congTerm

-- Validity of natural recursion congurence.
Emptyrec-congᵛ : ∀ {F F′ sF n n′ Γ l} ([Γ] : ⊩ᵛ Γ)
          ([Empty]  : Γ ⊩ᵛ⟨ l ⟩ Empty ⦂ 𝕥y / [Γ])
          ([F]  : Γ ⊩ᵛ⟨ l ⟩ F ⦂ sF / [Γ])
          ([F′]  : Γ ⊩ᵛ⟨ l ⟩ F′ ⦂ sF / [Γ])
          ([F≡F′]  : Γ ⊩ᵛ⟨ l ⟩ F ≡ F′ ⦂ sF / [Γ] / [F])
          ([n] : Γ ⊩ᵛ⟨ l ⟩ n ∷ Empty ⦂ 𝕥y / [Γ] / [Empty])
          ([n′] : Γ ⊩ᵛ⟨ l ⟩ n′ ∷ Empty ⦂ 𝕥y / [Γ] / [Empty])
          ([n≡n′] : Γ ⊩ᵛ⟨ l ⟩ n ≡ n′ ∷ Empty ⦂ 𝕥y / [Γ] / [Empty])
        → Γ ⊩ᵛ⟨ l ⟩ Emptyrec F n ≡ Emptyrec F′ n′ ∷ F ⦂ sF / [Γ] / [F]
Emptyrec-congᵛ {F} {F′} {sF} {n} {n′} {l = l}
             [Γ] [Empty] [F] [F′] [F≡F′]
             [n] [n′] [n≡n′] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [σn] = irrelevanceTerm {l′ = l} (proj₁ ([Empty] ⊢Δ [σ]))
                             (Emptyᵣ (idRed:*: (Emptyⱼ ⊢Δ))) (proj₁ ([n] ⊢Δ [σ]))
      [σn′] = irrelevanceTerm {l′ = l} (proj₁ ([Empty] ⊢Δ [σ]))
                             (Emptyᵣ (idRed:*: (Emptyⱼ ⊢Δ))) (proj₁ ([n′] ⊢Δ [σ]))
      [σn≡σn′] = irrelevanceEqTerm {l′ = l} (proj₁ ([Empty] ⊢Δ [σ]))
                                   (Emptyᵣ (idRed:*: (Emptyⱼ ⊢Δ))) ([n≡n′] ⊢Δ [σ])
      congTerm = Emptyrec-congTerm {F} {F′} [Γ] [F] [F′] [F≡F′]
                                   ⊢Δ [σ] [σ] (reflSubst [Γ] ⊢Δ [σ]) [σn] [σn′] [σn≡σn′]
  in congTerm
