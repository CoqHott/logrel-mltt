{-# OPTIONS --allow-unsolved-metas #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.IdUniv {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
import Definition.Typed.Weakening as Twk
open import Definition.Typed.EqualityRelation
open import Definition.Typed.RedSteps
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Application
open import Definition.LogicalRelation.Substitution
import Definition.LogicalRelation.Weakening as Lwk
open import Definition.LogicalRelation.Substitution.Properties
import Definition.LogicalRelation.Substitution.Irrelevance as S
open import Definition.LogicalRelation.Substitution.Reflexivity
open import Definition.LogicalRelation.Substitution.Weakening
-- open import Definition.LogicalRelation.Substitution.Introductions.Nat
open import Definition.LogicalRelation.Substitution.Introductions.Empty
open import Definition.LogicalRelation.Substitution.Introductions.Pi
open import Definition.LogicalRelation.Substitution.Introductions.Idlemmas
open import Definition.LogicalRelation.Substitution.MaybeEmbed
-- open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Definition.LogicalRelation.Substitution.Introductions.Universe

open import Tools.Product
open import Tools.Empty
import Tools.Unit as TU
import Tools.PropositionalEquality as PE
import Data.Nat as Nat


[Id]SProp : ∀ {t u Γ}
         (⊢Γ : ⊢ Γ)
         ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ^ [ % , ι ⁰ ])
         ([u] : Γ ⊩⟨ ι ⁰ ⟩ u ^ [ % , ι ⁰ ])
         → Γ ⊩⟨ ι ¹ ⟩ Id (SProp ⁰) t u ^ [ % , ι ¹ ]
[Id]SProp {t} {u} {Γ} ⊢Γ [t] [u] =
  let
    ⊢t = escape [t]
    ⊢u = escape [u]
    ⊢wkt = Twk.wk (Twk.step Twk.id) (⊢Γ ∙ ⊢u) ⊢t
    ⊢wku = Twk.wk (Twk.step Twk.id) (⊢Γ ∙ ⊢t) ⊢u
    [wkt] = λ {ρ} {Δ} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Lwk.wk [ρ] ⊢Δ [t]
    [wku] = λ {ρ} {Δ} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Lwk.wk [ρ] ⊢Δ [u]

    [t▹u] : Γ ⊩⟨ ι ⁰ ⟩ t ^ % ° ⁰ ▹▹ u ° ⁰ ^ [ % , ι ¹ ]
    [t▹u] = Πᵣ′ % ⁰ ⁰ (<is≤ 0<1) (<is≤ 0<1) t (wk1 u)
      (idRed:*: (univ (Πⱼ <is≤ 0<1 ▹ <is≤ 0<1 ▹ un-univ ⊢t ▹ un-univ ⊢wku))) ⊢t ⊢wku
      (≅-univ (≅ₜ-Π-cong ⊢t (≅-un-univ (escapeEqRefl [t])) (≅-un-univ (≅-wk (Twk.step Twk.id) (⊢Γ ∙ ⊢t) (escapeEqRefl [u])))))
      [wkt] ([nondep] [u] [wkt]) ([nondepext] [u] [wkt])
    [u▹t] : Γ ⊩⟨ ι ⁰ ⟩ u ^ % ° ⁰ ▹▹ t ° ⁰ ^ [ % , ι ¹ ]
    [u▹t] = Πᵣ′ % ⁰ ⁰ (<is≤ 0<1) (<is≤ 0<1) u (wk1 t)
      (idRed:*: (univ (Πⱼ <is≤ 0<1 ▹ <is≤ 0<1 ▹ un-univ ⊢u ▹ un-univ ⊢wkt))) ⊢u ⊢wkt
      (≅-univ (≅ₜ-Π-cong ⊢u (≅-un-univ (escapeEqRefl [u])) (≅-un-univ (≅-wk (Twk.step Twk.id) (⊢Γ ∙ ⊢u) (escapeEqRefl [t])))))
      [wku] ([nondep] [t] [wku]) ([nondepext] [t] [wku])
    [wkt▹u] = λ {ρ} {Δ} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Lwk.wk [ρ] ⊢Δ (emb emb< [t▹u])
    ⊢t▹u = escape [t▹u]
    ⊢u▹t = Twk.wk (Twk.step Twk.id) (⊢Γ ∙ ⊢t▹u) (escape [u▹t])

    ⊢Id = univ (Idⱼ (univ 0<1 ⊢Γ) (un-univ ⊢t) (un-univ ⊢u))
    ⊢Eq = univ (∃ⱼ un-univ ⊢t▹u ▹ un-univ ⊢u▹t)
  in ∃ᵣ′ (t ^ % ° ⁰ ▹▹ u ° ⁰) (wk1 (u ^ % ° ⁰ ▹▹ t ° ⁰))
    [[ ⊢Id , ⊢Eq , univ (Id-SProp (un-univ ⊢t) (un-univ ⊢u)) ⇨ id ⊢Eq ]] ⊢t▹u ⊢u▹t
    (≅-univ (≅ₜ-∃-cong ⊢t▹u (≅-un-univ (escapeEqRefl [t▹u])) (≅-un-univ (≅-wk (Twk.step Twk.id) (⊢Γ ∙ ⊢t▹u) (escapeEqRefl [u▹t])))))
    [wkt▹u] ([nondep] (emb emb< [u▹t]) [wkt▹u]) ([nondepext] (emb emb< [u▹t]) [wkt▹u])


[IdExt]SProp : ∀ {t t′ u u′ Γ}
         (⊢Γ : ⊢ Γ)
         ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ^ [ % , ι ⁰ ])
         ([t′] : Γ ⊩⟨ ι ⁰ ⟩ t′ ^ [ % , ι ⁰ ])
         ([t≡t′] : Γ ⊩⟨ ι ⁰ ⟩ t ≡ t′ ^ [ % , ι ⁰ ] / [t])
         ([u] : Γ ⊩⟨ ι ⁰ ⟩ u ^ [ % , ι ⁰ ])
         ([u′] : Γ ⊩⟨ ι ⁰ ⟩ u′ ^ [ % , ι ⁰ ])
         ([u≡u′] : Γ ⊩⟨ ι ⁰ ⟩ u ≡ u′ ^ [ % , ι ⁰ ] / [u])
         → Γ ⊩⟨ ι ¹ ⟩ Id (SProp ⁰) t u ≡ Id (SProp ⁰) t′ u′ ^ [ % , ι ¹ ] / [Id]SProp ⊢Γ [t] [u]
[IdExt]SProp {t} {t′} {u} {u′} {Γ} ⊢Γ [t] [t′] [t≡t′] [u] [u′] [u≡u′] =
  let ⊢t = escape [t]
      ⊢t′ = escape [t′]
      ⊢u = escape [u]
      ⊢u′ = escape [u′]
      ⊢t≡t′ = ≅-un-univ (escapeEq [t] [t≡t′])
      ⊢u≡u′ = ≅-un-univ (escapeEq [u] [u≡u′])
      
      ⊢wkt = Twk.wk (Twk.step Twk.id) (⊢Γ ∙ ⊢u) ⊢t
      ⊢wku = Twk.wk (Twk.step Twk.id) (⊢Γ ∙ ⊢t) ⊢u
      [wkt] = λ {ρ} {Δ} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Lwk.wk [ρ] ⊢Δ [t]
      [wku] = λ {ρ} {Δ} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Lwk.wk [ρ] ⊢Δ [u]

      ⊢wkt′ = Twk.wk (Twk.step Twk.id) (⊢Γ ∙ ⊢u′) ⊢t′
      ⊢wku′ = Twk.wk (Twk.step Twk.id) (⊢Γ ∙ ⊢t′) ⊢u′
      [wkt′] = λ {ρ} {Δ} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Lwk.wk [ρ] ⊢Δ [t′]
      [wku′] = λ {ρ} {Δ} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Lwk.wk [ρ] ⊢Δ [u′]

      [t▹u] : Γ ⊩⟨ ι ⁰ ⟩ t ^ % ° ⁰ ▹▹ u ° ⁰ ^ [ % , ι ¹ ]
      [t▹u] = Πᵣ′ % ⁰ ⁰ (<is≤ 0<1) (<is≤ 0<1) t (wk1 u)
        (idRed:*: (univ (Πⱼ <is≤ 0<1 ▹ <is≤ 0<1 ▹ un-univ ⊢t ▹ un-univ ⊢wku))) ⊢t ⊢wku
        (≅-univ (≅ₜ-Π-cong ⊢t (≅-un-univ (escapeEqRefl [t])) (≅-un-univ (≅-wk (Twk.step Twk.id) (⊢Γ ∙ ⊢t) (escapeEqRefl [u])))))
        [wkt] ([nondep] [u] [wkt]) ([nondepext] [u] [wkt])
      [u▹t] : Γ ⊩⟨ ι ⁰ ⟩ u ^ % ° ⁰ ▹▹ t ° ⁰ ^ [ % , ι ¹ ]
      [u▹t] = Πᵣ′ % ⁰ ⁰ (<is≤ 0<1) (<is≤ 0<1) u (wk1 t)
        (idRed:*: (univ (Πⱼ <is≤ 0<1 ▹ <is≤ 0<1 ▹ un-univ ⊢u ▹ un-univ ⊢wkt))) ⊢u ⊢wkt
        (≅-univ (≅ₜ-Π-cong ⊢u (≅-un-univ (escapeEqRefl [u])) (≅-un-univ (≅-wk (Twk.step Twk.id) (⊢Γ ∙ ⊢u) (escapeEqRefl [t])))))
        [wku] ([nondep] [t] [wku]) ([nondepext] [t] [wku])


      [t▹u′] : Γ ⊩⟨ ι ⁰ ⟩ t′ ^ % ° ⁰ ▹▹ u′ ° ⁰ ^ [ % , ι ¹ ]
      [t▹u′] = Πᵣ′ % ⁰ ⁰ (<is≤ 0<1) (<is≤ 0<1) t′ (wk1 u′)
        (idRed:*: (univ (Πⱼ <is≤ 0<1 ▹ <is≤ 0<1 ▹ un-univ ⊢t′ ▹ un-univ ⊢wku′))) ⊢t′ ⊢wku′
        (≅-univ (≅ₜ-Π-cong ⊢t′ (≅-un-univ (escapeEqRefl [t′])) (≅-un-univ (≅-wk (Twk.step Twk.id) (⊢Γ ∙ ⊢t′) (escapeEqRefl [u′])))))
        [wkt′] ([nondep] [u′] [wkt′]) ([nondepext] [u′] [wkt′])
      [u▹t′] : Γ ⊩⟨ ι ⁰ ⟩ u′ ^ % ° ⁰ ▹▹ t′ ° ⁰ ^ [ % , ι ¹ ]
      [u▹t′] = Πᵣ′ % ⁰ ⁰ (<is≤ 0<1) (<is≤ 0<1) u′ (wk1 t′)
        (idRed:*: (univ (Πⱼ <is≤ 0<1 ▹ <is≤ 0<1 ▹ un-univ ⊢u′ ▹ un-univ ⊢wkt′)))
        ⊢u′ ⊢wkt′
        (≅-univ (≅ₜ-Π-cong ⊢u′ (≅-un-univ (escapeEqRefl [u′])) (≅-un-univ (≅-wk (Twk.step Twk.id) (⊢Γ ∙ ⊢u′) (escapeEqRefl [t′])))))
        [wku′] ([nondep] [t′] [wku′]) ([nondepext] [t′] [wku′])

      [t▹u≡t▹u′] : Γ ⊩⟨ ι ⁰ ⟩ t ^ % ° ⁰ ▹▹ u ° ⁰ ≡ t′ ^ % ° ⁰ ▹▹ u′ ° ⁰ ^ [ % , ι ¹ ] / [t▹u]
      [t▹u≡t▹u′] = Π₌ t′ (wk1 u′) (id (univ (Πⱼ <is≤ 0<1 ▹ <is≤ 0<1 ▹ un-univ ⊢t′ ▹ un-univ ⊢wku′)))
                      (≅-univ (≅ₜ-Π-cong ⊢t ⊢t≡t′ (≅ₜ-wk (Twk.step Twk.id) (⊢Γ ∙ ⊢t) ⊢u≡u′)))
                      (λ {ρ} {Δ} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Lwk.wkEq [ρ] ⊢Δ (emb emb< [t]) [t≡t′])
                      ([nondepext'] [u] [u′] [u≡u′] [wkt] [wkt′])

      [u▹t≡u▹t′] : Γ ⊩⟨ ι ⁰ ⟩ u ^ % ° ⁰ ▹▹ t ° ⁰ ≡ u′ ^ % ° ⁰ ▹▹ t′ ° ⁰ ^ [ % , ι ¹ ] / [u▹t]
      [u▹t≡u▹t′] = Π₌ u′ (wk1 t′) (id (univ (Πⱼ <is≤ 0<1 ▹ <is≤ 0<1 ▹ un-univ ⊢u′ ▹ un-univ ⊢wkt′)))
                      (≅-univ (≅ₜ-Π-cong ⊢u ⊢u≡u′ (≅ₜ-wk (Twk.step Twk.id) (⊢Γ ∙ ⊢u) ⊢t≡t′)))
                      (λ {ρ} {Δ} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Lwk.wkEq [ρ] ⊢Δ (emb emb< [u]) [u≡u′])
                      ([nondepext'] [t] [t′] [t≡t′] [wku] [wku′])

      ⊢t▹u = escape [t▹u]

  in ∃₌ {l′ = ι ¹} (t′ ^ % ° ⁰ ▹▹ u′ ° ⁰) (wk1 (u′ ^ % ° ⁰ ▹▹ t′ ° ⁰))
        (univ (Id-SProp (un-univ ⊢t′) (un-univ ⊢u′)) ⇨ id (univ (××ⱼ (▹▹ⱼ <is≤ 0<1 ▹ <is≤ 0<1 ▹ un-univ ⊢t′ ▹ un-univ ⊢u′) ▹
                                                                     (▹▹ⱼ <is≤ 0<1 ▹ <is≤ 0<1 ▹ un-univ ⊢u′ ▹ un-univ ⊢t′))))
        (≅-univ (≅ₜ-∃-cong ⊢t▹u
                           (≅ₜ-Π-cong ⊢t ⊢t≡t′ (≅ₜ-wk (Twk.step Twk.id) (⊢Γ ∙ ⊢t) ⊢u≡u′))
                           (≅ₜ-Π-cong (Twk.wk (Twk.step Twk.id) (⊢Γ ∙ ⊢t▹u) ⊢u)
                                      (≅ₜ-wk (Twk.step Twk.id) (⊢Γ ∙ ⊢t▹u) ⊢u≡u′)
                                      (≅ₜ-wk (Twk.lift (Twk.step Twk.id)) ((⊢Γ ∙ ⊢t▹u) ∙
                                                       (Twk.wk (Twk.step Twk.id) (⊢Γ ∙ ⊢t▹u) ⊢u))
                                             (≅ₜ-wk (Twk.step Twk.id) (⊢Γ ∙ ⊢u) ⊢t≡t′)) )))
        (λ {ρ} {Δ} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Lwk.wkEq [ρ] ⊢Δ [t▹u] [t▹u≡t▹u′])
        ([nondepext'] (emb emb< [u▹t]) (emb emb< [u▹t′]) [u▹t≡u▹t′]
                      (λ {ρ} {Δ} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Lwk.wk [ρ] ⊢Δ (emb emb< [t▹u]))
                      (λ {ρ} {Δ} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Lwk.wk [ρ] ⊢Δ (emb emb< [t▹u′])))

[Id]U : ∀ {A B Γ}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ ! , ι ⁰ ])
         ([B] : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ ! , ι ⁰ ])
         → Γ ⊩⟨ ι ¹ ⟩ Id (U ⁰) A B ^ [ % , ι ¹ ]
[IdExtShape]U : ∀ {A A′ B B′ Γ}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ ! , ι ⁰ ])
         ([A′] : Γ ⊩⟨ ι ⁰ ⟩ A′ ^ [ ! , ι ⁰ ])
         (ShapeA : ShapeView Γ (ι ⁰) (ι ⁰) A A′ [ ! , ι ⁰ ] [ ! , ι ⁰ ] [A] [A′])
         ([A≡A′] : Γ ⊩⟨ ι ⁰ ⟩ A ≡ A′ ^ [ ! , ι ⁰ ] / [A])
         ([B] : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ ! , ι ⁰ ])
         ([B′] : Γ ⊩⟨ ι ⁰ ⟩ B′ ^ [ ! , ι ⁰ ])
         (ShapeB : ShapeView Γ (ι ⁰) (ι ⁰) B B′ [ ! , ι ⁰ ] [ ! , ι ⁰ ] [B] [B′])
         ([B≡B′] : Γ ⊩⟨ ι ⁰ ⟩ B ≡ B′ ^ [ ! , ι ⁰ ] / [B])
         → Γ ⊩⟨ ι ¹ ⟩ Id (U ⁰) A B ≡ Id (U ⁰) A′ B′ ^ [ % , ι ¹ ] / [Id]U ⊢Γ [A] [B]
[IdExt]U : ∀ {A A′ B B′ Γ}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ ! , ι ⁰ ])
         ([A′] : Γ ⊩⟨ ι ⁰ ⟩ A′ ^ [ ! , ι ⁰ ])
         ([A≡A′] : Γ ⊩⟨ ι ⁰ ⟩ A ≡ A′ ^ [ ! , ι ⁰ ] / [A])
         ([B] : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ ! , ι ⁰ ])
         ([B′] : Γ ⊩⟨ ι ⁰ ⟩ B′ ^ [ ! , ι ⁰ ])
         ([B≡B′] : Γ ⊩⟨ ι ⁰ ⟩ B ≡ B′ ^ [ ! , ι ⁰ ] / [B])
         → Γ ⊩⟨ ι ¹ ⟩ Id (U ⁰) A B ≡ Id (U ⁰) A′ B′ ^ [ % , ι ¹ ] / [Id]U ⊢Γ [A] [B]


[Id]U {A} {B} ⊢Γ (ne′ K D neK K≡K) [B] =
  let ⊢B = escape [B]
      B≡B = escapeEqRefl [B]
  in ne (ne (Id (U ⁰) K B) (univ:⇒*: (IdURed*Term (un-univ:⇒*: D) (un-univ ⊢B))) (IdUₙ neK) (~-IdU ⊢Γ K≡K (≅-un-univ B≡B)))

[Id]U ⊢Γ (ℕᵣ [[ ⊢A , ⊢K , D ]]) (ℕᵣ [[ ⊢B , ⊢L , D₁ ]]) =
  let
    ⊢tA = (subset* D)
  in proj₁ (redSubst* (trans⇒* (univ⇒* (IdURed*Term′ (un-univ ⊢A) (un-univ ⊢K) (un-univ⇒* D) (un-univ ⊢B)))
                        (trans⇒* (univ⇒* (IdUℕRed*Term′ (un-univ ⊢B) (un-univ ⊢L) (un-univ⇒* D₁))) (univ (Id-U-ℕℕ ⊢Γ) ⇨ id (univ (Unitⱼ ⊢Γ))))) (UnitType ⊢Γ))

[Id]U ⊢Γ (ℕᵣ D) (ne′ K D₁ neK K≡K) =
  let [B] = ne′ K D₁ neK K≡K
      ⊢B = escape {l = ι ¹} [B]
  in ne′ (Id (U ⁰) ℕ K) (univ:⇒*: (transTerm:⇒:* (IdURed*Term (un-univ:⇒*: D) (un-univ ⊢B) ) (IdUℕRed*Term (un-univ:⇒*: D₁))))
         (IdUℕₙ neK) (~-IdUℕ ⊢Γ K≡K)
  
[Id]U ⊢Γ (ℕᵣ [[ ⊢A , ⊢ℕ , D ]]) (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  let [B] = Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G D′ ⊢F ⊢G A≡A [F] [G] G-ext
      ⊢B = escape [B]
  in proj₁ (redSubst* (trans⇒* (univ⇒* (IdURed*Term′ (un-univ ⊢A) (un-univ ⊢ℕ) (un-univ⇒* D) (un-univ ⊢B)))
                        (trans⇒* (univ⇒* (IdUℕRed*Term′ (un-univ ⊢B) (Πⱼ ≡is≤ PE.refl ▹ ≡is≤ PE.refl ▹ (un-univ ⊢F) ▹ (un-univ ⊢G)) (un-univ⇒* (red D′))))
                                 (univ (Id-U-ℕΠ (un-univ ⊢F) (un-univ ⊢G)) ⇨ id (univ (Emptyⱼ ⊢Γ))))) (EmptyType ⊢Γ))

[Id]U ⊢Γ (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢Π , D ]] ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ [[ ⊢B , ⊢ℕ , D' ]]) =
  proj₁ (redSubst* (trans⇒* (univ⇒* (IdURed*Term′ (un-univ ⊢A) (un-univ ⊢Π) (un-univ⇒* D) (un-univ ⊢B)))
                        (trans⇒* (univ⇒* (IdUΠRed*Term′ (un-univ ⊢F) (un-univ ⊢G) (un-univ ⊢B) (un-univ ⊢ℕ) (un-univ⇒* D')))
                                 (univ (Id-U-Πℕ (un-univ ⊢F) (un-univ ⊢G)) ⇨ id (univ (Emptyⱼ ⊢Γ))))) (EmptyType ⊢Γ))

[Id]U ⊢Γ (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne′ K D₁ neK K≡K) =
  let [B] = ne′ K D₁ neK K≡K
      ⊢B = escape {l = ι ¹} [B]
      -- [F]' = PE.subst (λ X → _  ⊩⟨ _ ⟩ X ^ [ _ , _ ]) (wk-id F) ([F] Twk.id ⊢Γ)
      -- ⊢F≅F = ≅-un-univ (escapeEqRefl [F]')
      -- [G]' = PE.subst (λ X → _  ⊩⟨ _ ⟩ X ^ [ _ , _ ]) (wkSingleSubstId G) ([G] {a = var 0} (Twk.step Twk.id) (⊢Γ ∙ ⊢F) {!!})
      -- ⊢G≅G = ≅-un-univ (escapeEqRefl [G]')
  in ne′ (Id (U ⁰) (Π F ^ rF ° lF ▹ G ° lG) K)
         (univ:⇒*: (transTerm:⇒:* (IdURed*Term (un-univ:⇒*: D) (un-univ ⊢B) ) (IdUΠRed*Term (un-univ ⊢F) (un-univ ⊢G) (un-univ:⇒*: D₁))))
         (IdUΠₙ neK) (~-IdUΠ (≅-un-univ A≡A) K≡K)
         
[Id]U {A} {B} {Γ} ⊢Γ (Πᵣ′ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢ΠFG , D ]] ⊢F ⊢G A≡A [F] [G] G-ext)
  (Πᵣ′ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢B , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ B≡B [F₁] [G₁] G₁-ext) =
  ∃ᵣ′ (Id (U ⁰) F F₁) (IdGG₁ (step id) (var 0))
    [[ (univ (Idⱼ (univ 0<1 ⊢Γ) (un-univ ⊢A) (un-univ ⊢B))) , ⊢∃ , D∃ ]]
    ⊢IdFF₁ ⊢IdGG₁ ∃≡∃ [IdFF₁]
    (λ {ρ} {Δ} {a} [ρ] ⊢Δ [a] → PE.subst (λ X → Δ ⊩⟨ ι ¹ ⟩ X ^ [ % , ι ¹ ]) (PE.sym (wksubst-IdTel ρ a)) ([IdGG₁] [ρ] ⊢Δ [a]))
    (λ {ρ} {Δ} {a} {b} [ρ] ⊢Δ [a] [b] [a≡b] → irrelevanceEq″ (PE.sym (wksubst-IdTel ρ a)) (PE.sym (wksubst-IdTel ρ b)) PE.refl PE.refl
      ([IdGG₁] [ρ] ⊢Δ [a]) (PE.subst (λ X → Δ ⊩⟨ ι ¹ ⟩ X ^ [ % , ι ¹ ]) (PE.sym (wksubst-IdTel ρ a)) ([IdGG₁] [ρ] ⊢Δ [a]))
      ([IdGG₁-ext] [ρ] ⊢Δ [a] [b] [a≡b]))
  where
    open IdTypeU-lemmas ⊢Γ ⊢A ⊢ΠFG D ⊢F ⊢G A≡A [F] [G] G-ext ⊢B ⊢ΠF₁G₁ D₁ ⊢F₁ ⊢G₁ B≡B [F₁] [G₁] G₁-ext
      (λ [ρ] ⊢Δ → [Id]U ⊢Δ ([F] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ))
      (λ [ρ] ⊢Δ [x] [y] → [Id]U ⊢Δ ([G] [ρ] ⊢Δ [x]) ([G₁] [ρ] ⊢Δ [y]))
      (λ [ρ] ⊢Δ [x] [x′] [x≡x′] [y] [y′] [y≡y′] →
        [IdExt]U ⊢Δ ([G] [ρ] ⊢Δ [x]) ([G] [ρ] ⊢Δ [x′]) (G-ext [ρ] ⊢Δ [x] [x′] [x≡x′]) ([G₁] [ρ] ⊢Δ [y]) ([G₁] [ρ] ⊢Δ [y′]) (G₁-ext [ρ] ⊢Δ [y] [y′] [y≡y′]))

[Id]U {A} {B} {Γ} ⊢Γ (Πᵣ′ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢ΠFG , D ]] ⊢F ⊢G A≡A [F] [G] G-ext)
  (Πᵣ′ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢B , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ B≡B [F₁] [G₁] G₁-ext) =
  ∃ᵣ′ (Id (SProp ⁰) F F₁) (IdGG₁ (step id) (var 0))
    [[ (univ (Idⱼ (univ 0<1 ⊢Γ) (un-univ ⊢A) (un-univ ⊢B))) , ⊢∃ , D∃ ]]
    ⊢IdFF₁ ⊢IdGG₁ ∃≡∃ [IdFF₁]
    (λ {ρ} {Δ} {a} [ρ] ⊢Δ [a] → PE.subst (λ X → Δ ⊩⟨ ι ¹ ⟩ X ^ [ % , ι ¹ ]) (PE.sym (wksubst-IdTel ρ a)) ([IdGG₁] [ρ] ⊢Δ [a]))
    (λ {ρ} {Δ} {a} {b} [ρ] ⊢Δ [a] [b] [a≡b] → irrelevanceEq″ (PE.sym (wksubst-IdTel ρ a)) (PE.sym (wksubst-IdTel ρ b)) PE.refl PE.refl
      ([IdGG₁] [ρ] ⊢Δ [a]) (PE.subst (λ X → Δ ⊩⟨ ι ¹ ⟩ X ^ [ % , ι ¹ ]) (PE.sym (wksubst-IdTel ρ a)) ([IdGG₁] [ρ] ⊢Δ [a]))
      ([IdGG₁-ext] [ρ] ⊢Δ [a] [b] [a≡b]))
  where
    open IdTypeU-lemmas ⊢Γ ⊢A ⊢ΠFG D ⊢F ⊢G A≡A [F] [G] G-ext ⊢B ⊢ΠF₁G₁ D₁ ⊢F₁ ⊢G₁ B≡B [F₁] [G₁] G₁-ext
      (λ [ρ] ⊢Δ → [Id]SProp ⊢Δ ([F] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ))
      (λ [ρ] ⊢Δ [x] [y] → [Id]U ⊢Δ ([G] [ρ] ⊢Δ [x]) ([G₁] [ρ] ⊢Δ [y]))
      (λ [ρ] ⊢Δ [x] [x′] [x≡x′] [y] [y′] [y≡y′] →
        [IdExt]U ⊢Δ ([G] [ρ] ⊢Δ [x]) ([G] [ρ] ⊢Δ [x′]) (G-ext [ρ] ⊢Δ [x] [x′] [x≡x′]) ([G₁] [ρ] ⊢Δ [y]) ([G₁] [ρ] ⊢Δ [y′]) (G₁-ext [ρ] ⊢Δ [y] [y′] [y≡y′]))

[Id]U ⊢Γ (Πᵣ′ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢ΠFG , D ]] ⊢F ⊢G A≡A [F] [G] G-ext)
         (Πᵣ′ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢B , ⊢ΠF₁G₁ , D' ]] ⊢F₁ ⊢G₁ B≡B [F₁] [G₁] G₁-ext) =
    proj₁ (redSubst* (trans⇒* (univ⇒* (IdURed*Term′ (un-univ ⊢A) (un-univ ⊢ΠFG) (un-univ⇒* D) (un-univ ⊢B)))
                        (trans⇒* (univ⇒* (IdUΠRed*Term′ (un-univ ⊢F) (un-univ ⊢G) (un-univ ⊢B) (un-univ ⊢ΠF₁G₁) (un-univ⇒* D')))
                                 (univ (Id-U-ΠΠ!% !≢% (un-univ ⊢F) (un-univ ⊢G) (un-univ ⊢F₁) (un-univ ⊢G₁)) ⇨ id (univ (Emptyⱼ ⊢Γ))))) (EmptyType ⊢Γ))

[Id]U ⊢Γ (Πᵣ′ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢ΠFG , D ]] ⊢F ⊢G A≡A [F] [G] G-ext)
  (Πᵣ′ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢B , ⊢ΠF₁G₁ , D' ]] ⊢F₁ ⊢G₁ B≡B [F₁] [G₁] G₁-ext) =
    proj₁ (redSubst* (trans⇒* (univ⇒* (IdURed*Term′ (un-univ ⊢A) (un-univ ⊢ΠFG) (un-univ⇒* D) (un-univ ⊢B)))
                       (trans⇒* (univ⇒* (IdUΠRed*Term′ (un-univ ⊢F) (un-univ ⊢G) (un-univ ⊢B) (un-univ ⊢ΠF₁G₁) (un-univ⇒* D')))
                                 (univ (Id-U-ΠΠ!% (λ e → !≢% (PE.sym e)) (un-univ ⊢F) (un-univ ⊢G) (un-univ ⊢F₁) (un-univ ⊢G₁)) ⇨ id (univ (Emptyⱼ ⊢Γ))))) (EmptyType ⊢Γ))


[IdExtShape]U ⊢Γ _ _ (ℕᵥ ℕA [[ ⊢A , ⊢K , D ]]) [A≡A′] _ _ (ℕᵥ NB [[ ⊢B , ⊢L , D₁ ]]) [B≡B′] =
  Π₌ Empty Empty
    (trans⇒* (univ⇒* (IdURed*Term′ (un-univ ⊢A) (un-univ ⊢K) (un-univ⇒* D) (un-univ ⊢B)))
                        (trans⇒* (univ⇒* (IdUℕRed*Term′ (un-univ ⊢B) (un-univ ⊢L) (un-univ⇒* D₁))) (univ (Id-U-ℕℕ ⊢Γ) ⇨ id (univ (Unitⱼ ⊢Γ)))))
                        (≅-univ (Unit≡Unit ⊢Γ))
    (λ [ρ] ⊢Δ → id (univ (Emptyⱼ ⊢Δ)))
    λ [ρ] ⊢Δ [a] → id (univ (Emptyⱼ ⊢Δ))
    
[IdExtShape]U ⊢Γ _ _ (ℕᵥ ℕA D) [A≡A′] _ _ (ne neB neB') (ne₌ M D′ neM K≡M) =
  let [[ ⊢B , _ ,  _ ]] = D′
  in ne₌ (Id (U ⁰) ℕ M) (univ:⇒*: (transTerm:⇒:* (IdURed*Term (un-univ:⇒*: D) (un-univ ⊢B) ) (IdUℕRed*Term (un-univ:⇒*: D′))))
         (IdUℕₙ neM) (~-IdUℕ ⊢Γ K≡M)
         
[IdExtShape]U ⊢Γ _ _ (ℕᵥ [[ ⊢A , ⊢ℕ , D ]] [[ ⊢A' , ⊢ℕ' , D' ]]) [A≡A′] _ _
                     (Πᵥ (Πᵣ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G D′ ⊢F ⊢G A≡A [F] [G] G-ext)
                         (Πᵣ rF' lF' lG' (≡is≤ PE.refl) (≡is≤ PE.refl) F' G' D′' ⊢F' ⊢G' A≡A' [F]' [G]' G-ext')) [B≡B′] =
  let [B]' = Πᵣ′ rF' lF' lG' (≡is≤ PE.refl) (≡is≤ PE.refl) F' G' D′' ⊢F' ⊢G' A≡A' [F]' [G]' G-ext'
      ⊢B' = escape [B]'
  in trans⇒* (univ⇒* (IdURed*Term′ (un-univ ⊢A') (un-univ ⊢ℕ') (un-univ⇒* D') (un-univ ⊢B')))
                        (trans⇒* (univ⇒* (IdUℕRed*Term′ (un-univ ⊢B') (Πⱼ ≡is≤ PE.refl ▹ ≡is≤ PE.refl ▹ (un-univ ⊢F') ▹ (un-univ ⊢G')) (un-univ⇒* (red D′'))))
                                 (univ (Id-U-ℕΠ (un-univ ⊢F') (un-univ ⊢G')) ⇨ id (univ (Emptyⱼ ⊢Γ))))
  
[IdExtShape]U {A} {A′} {B} {B′} ⊢Γ _ _ (ne neA neA') (ne₌ M D neM K≡M) [B] [B'] [ShapeB] [B≡B′] =
  let ⊢B' = escape [B']
      B≡B' = escapeEq [B] [B≡B′]
  in ne₌ (Id (U ⁰) M B′) (univ:⇒*: (IdURed*Term (un-univ:⇒*: D) (un-univ ⊢B')))
         (IdUₙ neM) (~-IdU ⊢Γ K≡M (≅-un-univ B≡B'))
  
[IdExtShape]U ⊢Γ _ _ (Πᵥ (Πᵣ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G D′ ⊢F ⊢G A≡A [F] [G] G-ext)
                         (Πᵣ rF' lF' lG' (≡is≤ PE.refl) (≡is≤ PE.refl) F' G' [[ ⊢A' , ⊢Π' , DΠ' ]] ⊢F' ⊢G' A≡A' [F]' [G]' G-ext')) [A≡A′] _ _
                     (ℕᵥ [[ ⊢A , ⊢ℕ , D ]] [[ ⊢B' , ⊢ℕ' , D' ]]) [B≡B′] =
   trans⇒* (univ⇒* (IdURed*Term′ (un-univ ⊢A') (un-univ ⊢Π') (un-univ⇒* DΠ') (un-univ ⊢B')))
                        (trans⇒* (univ⇒* (IdUΠRed*Term′ (un-univ ⊢F') (un-univ ⊢G') (un-univ ⊢B') (un-univ ⊢ℕ') (un-univ⇒* D')))
                                 (univ (Id-U-Πℕ (un-univ ⊢F') (un-univ ⊢G')) ⇨ id (univ (Emptyⱼ ⊢Γ))))

[IdExtShape]U ⊢Γ _ _ (Πᵥ (Πᵣ rF' .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F' G' De' ⊢F' ⊢G' A≡A' [F]' [G]' G-ext')
                         (Πᵣ rF .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Π₌ F′ G′ D′₁ A≡B [F≡F′] [G≡G′])
                 _ _ (ne neA neB) (ne₌ M D′ neM K≡M) =
  let [[ ⊢B , _ ,  _ ]] = D′
      Π≡Π = whrDet* (red D , Whnf.Πₙ) (D′₁ , Whnf.Πₙ)
      F≡F' , rF≡rF' , _ , G≡G' , _  = Π-PE-injectivity Π≡Π
  in ne₌ (Id (U ⁰) (Π F ^ rF ° ⁰ ▹ G ° ⁰) M)
         (univ:⇒*: (transTerm:⇒:* (IdURed*Term (un-univ:⇒*: D) (un-univ ⊢B) ) (IdUΠRed*Term (un-univ ⊢F) (un-univ ⊢G) (un-univ:⇒*: D′))))
         (IdUΠₙ neM) (PE.subst (λ X → _  ⊢ Id (U ⁰) (Π F' ^ rF' ° ⁰ ▹ G' ° ⁰) _ ~ Id (U ⁰) (Π F ^ X ° ⁰ ▹ G ° ⁰) M ∷ SProp _ ^ _) (PE.sym rF≡rF')
                               (~-IdUΠ (≅-un-univ
                                 (PE.subst (λ X → _ ⊢ Π F' ^ rF' ° ⁰ ▹ G' ° ⁰ ≅  Π F ^ rF' ° ⁰ ▹ X ° ⁰ ^ _ ) (PE.sym G≡G')
                                   (PE.subst (λ X → _ ⊢ Π F' ^ rF' ° ⁰ ▹ G' ° ⁰ ≅  Π X ^ rF' ° ⁰ ▹ G′ ° ⁰ ^ _ ) (PE.sym F≡F') A≡B))) K≡M)) 

[IdExtShape]U ⊢Γ _ _ (Πᵥ (Πᵣ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)
                         (Πᵣ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₂ G₂ [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]] ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext))
                      (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
                 _ _ (Πᵥ _ _) (Π₌ F′₁ G′₁ D′₁ A≡B₁ [F≡F′]₁ [G≡G′]₁) =
  let ΠFG′≡ΠFG′₁ = whrDet* (D₂ , Πₙ) (D′ , Πₙ)
      F′≡F′₁ , rF≡rF′ , _ , G′≡G′₁ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₁
  in ⊥-elim (!≢% rF≡rF′)

[IdExtShape]U ⊢Γ _ _ (Πᵥ (Πᵣ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)
                         (Πᵣ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₂ G₂ [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]] ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext))
                      (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
                 _ _ (Πᵥ _ _) (Π₌ F′₁ G′₁ D′₁ A≡B₁ [F≡F′]₁ [G≡G′]₁) =
  let ΠFG′≡ΠFG′₁ = whrDet* (D₂ , Πₙ) (D′ , Πₙ)
      F′≡F′₁ , rF≡rF′ , _ , G′≡G′₁ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₁
  in ⊥-elim (!≢% (PE.sym rF≡rF′))

[IdExtShape]U ⊢Γ _ _ (Πᵥ _ _)
                      (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
                 _ _ (Πᵥ (Πᵣ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)
                         (Πᵣ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₂ G₂ [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]] ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext)) (Π₌ F′₁ G′₁ D′₁ A≡B₁ [F≡F′]₁ [G≡G′]₁) =
  let ΠFG′≡ΠFG′₁ = whrDet* (D₂ , Πₙ) (D′₁ , Πₙ)
      F′≡F′₁ , rF≡rF′ , _ , G′≡G′₁ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₁
  in ⊥-elim (!≢% rF≡rF′)

[IdExtShape]U ⊢Γ _ _ (Πᵥ _ _)
                      (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
                 _ _ (Πᵥ (Πᵣ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)
                         (Πᵣ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₂ G₂ [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]] ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext)) (Π₌ F′₁ G′₁ D′₁ A≡B₁ [F≡F′]₁ [G≡G′]₁) =
  let ΠFG′≡ΠFG′₁ = whrDet* (D₂ , Πₙ) (D′₁ , Πₙ)
      F′≡F′₁ , rF≡rF′ , _ , G′≡G′₁ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₁
  in ⊥-elim (!≢% (PE.sym rF≡rF′))

[IdExtShape]U ⊢Γ _ _ (Πᵥ (Πᵣ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)
                         (Πᵣ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₂ G₂ [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]] ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext))
                      (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
                 _ _ (Πᵥ (Πᵣ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₃ G₃ [[ ⊢A₃ , ⊢ΠF₃G₃ , D₃ ]] ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext)
                         (Πᵣ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₄ G₄ [[ ⊢A₄ , ⊢ΠF₄G₄ , D₄ ]] ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext)) (Π₌ F′₁ G′₁ D′₁ A≡B₁ [F≡F′]₁ [G≡G′]₁) =
  trans⇒* (univ⇒* (IdURed*Term′ (un-univ ⊢A₂) (un-univ ⊢ΠF₂G₂) (un-univ⇒* D₂) (un-univ ⊢A₄)))
                        (trans⇒* (univ⇒* (IdUΠRed*Term′ (un-univ ⊢F₂) (un-univ ⊢G₂) (un-univ ⊢A₄) (un-univ ⊢ΠF₄G₄) (un-univ⇒* D₄)))
                                 (univ (Id-U-ΠΠ!% !≢% (un-univ ⊢F₂) (un-univ ⊢G₂) (un-univ ⊢F₄) (un-univ ⊢G₄)) ⇨ id (univ (Emptyⱼ ⊢Γ))))

[IdExtShape]U ⊢Γ _ _ (Πᵥ (Πᵣ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)
                         (Πᵣ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₂ G₂ [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]] ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext))
                      (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
                 _ _ (Πᵥ (Πᵣ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₃ G₃ [[ ⊢A₃ , ⊢ΠF₃G₃ , D₃ ]] ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext)
                         (Πᵣ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₄ G₄ [[ ⊢A₄ , ⊢ΠF₄G₄ , D₄ ]] ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext)) (Π₌ F′₁ G′₁ D′₁ A≡B₁ [F≡F′]₁ [G≡G′]₁) =
  trans⇒* (univ⇒* (IdURed*Term′ (un-univ ⊢A₂) (un-univ ⊢ΠF₂G₂) (un-univ⇒* D₂) (un-univ ⊢A₄)))
                        (trans⇒* (univ⇒* (IdUΠRed*Term′ (un-univ ⊢F₂) (un-univ ⊢G₂) (un-univ ⊢A₄) (un-univ ⊢ΠF₄G₄) (un-univ⇒* D₄)))
                                 (univ (Id-U-ΠΠ!% (λ e → !≢% (PE.sym e)) (un-univ ⊢F₂) (un-univ ⊢G₂) (un-univ ⊢F₄) (un-univ ⊢G₄)) ⇨ id (univ (Emptyⱼ ⊢Γ))))


[IdExtShape]U {A₁} {A₂} {A₃} {A₄} {Γ}  ⊢Γ _ _
                   (Πᵥ (Πᵣ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)
                   (Πᵣ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₂ G₂ [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]] ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext))
                   (Π₌ F₂′ G₂′ D₂′ A₁≡A₂′ [F₁≡F₂′] [G₁≡G₂′])
               _ _ (Πᵥ (Πᵣ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₃ G₃ [[ ⊢A₃ , ⊢ΠF₃G₃ , D₃ ]] ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext)
                   (Πᵣ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₄ G₄ [[ ⊢A₄ , ⊢ΠF₄G₄ , D₄ ]] ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext))
                   (Π₌ F₄′ G₄′ D₄′ A₃≡A₄′ [F₃≡F₄′] [G₃≡G₄′]) =
    ∃₌ (Id (U ⁰) F₂ F₄) (E₂.IdGG₁ (step id) (var 0))
    E₂.D∃ ∃₁≡∃₂
    [IdFF₁≡IdFF₂]
    (λ {ρ} {Δ} {e} [ρ] ⊢Δ [e] → irrelevanceEq″ (PE.sym (E₁.wksubst-IdTel ρ e)) (PE.sym (E₂.wksubst-IdTel ρ e)) PE.refl PE.refl
      (E₁.[IdGG₁] [ρ] ⊢Δ [e]) (PE.subst (λ X → Δ ⊩⟨ ι ¹ ⟩ X ^ [ % , ι ¹ ]) (PE.sym (E₁.wksubst-IdTel ρ e)) (E₁.[IdGG₁] [ρ] ⊢Δ [e]))
      ([IdGG₁≡IdGG₂] [ρ] ⊢Δ [e]))
  where
    Π≡Π = whrDet* (D₂ , Whnf.Πₙ) (D₂′ , Whnf.Πₙ)
    F₂≡F₂′ = let x , _ , _ , _ , _ = Π-PE-injectivity Π≡Π in x
    G₂≡G₂′ = let _ , _ , _ , x , _ = Π-PE-injectivity Π≡Π in x
    Π≡Π′ = whrDet* (D₄ , Whnf.Πₙ) (D₄′ , Whnf.Πₙ)
    F₄≡F₄′ = let x , _ , _ , _ , _ = Π-PE-injectivity Π≡Π′ in x
    G₄≡G₄′ = let _ , _ , _ , x , _ = Π-PE-injectivity Π≡Π′ in x

    A₁≡A₂ = PE.subst₂ (λ X Y → Γ ⊢ Π F₁ ^ ! ° ⁰ ▹ G₁ ° ⁰ ≅ Π X ^ ! ° ⁰ ▹ Y ° ⁰ ^ [ ! , ι ⁰ ]) (PE.sym F₂≡F₂′) (PE.sym G₂≡G₂′) A₁≡A₂′
    A₃≡A₄ = PE.subst₂ (λ X Y → Γ ⊢ Π F₃ ^ ! ° ⁰ ▹ G₃ ° ⁰ ≅ Π X ^ ! ° ⁰ ▹ Y ° ⁰ ^ [ ! , ι ⁰ ]) (PE.sym F₄≡F₄′) (PE.sym G₄≡G₄′) A₃≡A₄′
    [F₁≡F₂] = PE.subst (λ X → ∀ {ρ Δ} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Δ ⊩⟨ ι ⁰ ⟩ wk ρ F₁ ≡ wk ρ X ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
                       (PE.sym F₂≡F₂′) [F₁≡F₂′]
    [F₃≡F₄] = PE.subst (λ X → ∀ {ρ Δ} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Δ ⊩⟨ ι ⁰ ⟩ wk ρ F₃ ≡ wk ρ X ^ [ ! , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
                       (PE.sym F₄≡F₄′) [F₃≡F₄′]
    [G₁≡G₂] = PE.subst (λ X → ∀ {ρ Δ a} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
                              → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F₁ ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
                              → Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₁ [ a ] ≡ wk (lift ρ) X [ a ] ^ [ ! , ι ⁰ ] / [G₁] [ρ] ⊢Δ [a])
                       (PE.sym G₂≡G₂′) [G₁≡G₂′]
    [G₃≡G₄] = PE.subst (λ X → ∀ {ρ Δ a} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
                              → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F₃ ^ [ ! , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
                              → Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₃ [ a ] ≡ wk (lift ρ) X [ a ] ^ [ ! , ι ⁰ ] / [G₃] [ρ] ⊢Δ [a])
                       (PE.sym G₄≡G₄′) [G₃≡G₄′]

    open IdTypeU-lemmas-2 ⊢Γ ⊢A₁ ⊢ΠF₁G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext
      ⊢A₂ ⊢ΠF₂G₂ D₂ ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext
      ⊢A₃ ⊢ΠF₃G₃ D₃ ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext
      ⊢A₄ ⊢ΠF₄G₄ D₄ ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext
      A₁≡A₂ A₃≡A₄ [F₁≡F₂] [F₃≡F₄] [G₁≡G₂] [G₃≡G₄]
      (λ [ρ] ⊢Δ → [Id]U ⊢Δ ([F₁] [ρ] ⊢Δ) ([F₃] [ρ] ⊢Δ))
      (λ [ρ] ⊢Δ [x] [y] → [Id]U ⊢Δ ([G₁] [ρ] ⊢Δ [x]) ([G₃] [ρ] ⊢Δ [y]))
      (λ [ρ] ⊢Δ → [Id]U ⊢Δ ([F₂] [ρ] ⊢Δ) ([F₄] [ρ] ⊢Δ))
      (λ [ρ] ⊢Δ [x] [y] → [Id]U ⊢Δ ([G₂] [ρ] ⊢Δ [x]) ([G₄] [ρ] ⊢Δ [y]))
      (λ [ρ] ⊢Δ [x] [x′] [x≡x′] [y] [y′] [y≡y′] →
        [IdExt]U ⊢Δ ([G₁] [ρ] ⊢Δ [x]) ([G₁] [ρ] ⊢Δ [x′]) (G₁-ext [ρ] ⊢Δ [x] [x′] [x≡x′]) ([G₃] [ρ] ⊢Δ [y]) ([G₃] [ρ] ⊢Δ [y′]) (G₃-ext [ρ] ⊢Δ [y] [y′] [y≡y′]))
      (λ [ρ] ⊢Δ [x] [x′] [x≡x′] [y] [y′] [y≡y′] →
        [IdExt]U ⊢Δ ([G₂] [ρ] ⊢Δ [x]) ([G₂] [ρ] ⊢Δ [x′]) (G₂-ext [ρ] ⊢Δ [x] [x′] [x≡x′]) ([G₄] [ρ] ⊢Δ [y]) ([G₄] [ρ] ⊢Δ [y′]) (G₄-ext [ρ] ⊢Δ [y] [y′] [y≡y′]))
      (λ [ρ] ⊢Δ → [IdExt]U ⊢Δ ([F₁] [ρ] ⊢Δ) ([F₂] [ρ] ⊢Δ) ([F₁≡F₂] [ρ] ⊢Δ) ([F₃] [ρ] ⊢Δ) ([F₄] [ρ] ⊢Δ) ([F₃≡F₄] [ρ] ⊢Δ))
      (λ [ρ] ⊢Δ [x₁] [x₂] [G₁x₁≡G₂x₂] [x₃] [x₄] [G₃x₃≡G₄x₄] → [IdExt]U ⊢Δ ([G₁] [ρ] ⊢Δ [x₁]) ([G₂] [ρ] ⊢Δ [x₂]) [G₁x₁≡G₂x₂] ([G₃] [ρ] ⊢Δ [x₃]) ([G₄] [ρ] ⊢Δ [x₄]) [G₃x₃≡G₄x₄])

[IdExtShape]U {A₁} {A₂} {A₃} {A₄} {Γ}  ⊢Γ _ _
                   (Πᵥ (Πᵣ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)
                   (Πᵣ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₂ G₂ [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]] ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext))
                   (Π₌ F₂′ G₂′ D₂′ A₁≡A₂′ [F₁≡F₂′] [G₁≡G₂′])
               _ _ (Πᵥ (Πᵣ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₃ G₃ [[ ⊢A₃ , ⊢ΠF₃G₃ , D₃ ]] ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext)
                   (Πᵣ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₄ G₄ [[ ⊢A₄ , ⊢ΠF₄G₄ , D₄ ]] ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext))
                   (Π₌ F₄′ G₄′ D₄′ A₃≡A₄′ [F₃≡F₄′] [G₃≡G₄′]) =
    ∃₌ (Id (SProp ⁰) F₂ F₄) (E₂.IdGG₁ (step id) (var 0))
    E₂.D∃ ∃₁≡∃₂
    [IdFF₁≡IdFF₂]
    (λ {ρ} {Δ} {e} [ρ] ⊢Δ [e] → irrelevanceEq″ (PE.sym (E₁.wksubst-IdTel ρ e)) (PE.sym (E₂.wksubst-IdTel ρ e)) PE.refl PE.refl
      (E₁.[IdGG₁] [ρ] ⊢Δ [e]) (PE.subst (λ X → Δ ⊩⟨ ι ¹ ⟩ X ^ [ % , ι ¹ ]) (PE.sym (E₁.wksubst-IdTel ρ e)) (E₁.[IdGG₁] [ρ] ⊢Δ [e]))
      ([IdGG₁≡IdGG₂] [ρ] ⊢Δ [e]))
  where
    Π≡Π = whrDet* (D₂ , Whnf.Πₙ) (D₂′ , Whnf.Πₙ)
    F₂≡F₂′ = let x , _ , _ , _ , _ = Π-PE-injectivity Π≡Π in x
    G₂≡G₂′ = let _ , _ , _ , x , _ = Π-PE-injectivity Π≡Π in x
    Π≡Π′ = whrDet* (D₄ , Whnf.Πₙ) (D₄′ , Whnf.Πₙ)
    F₄≡F₄′ = let x , _ , _ , _ , _ = Π-PE-injectivity Π≡Π′ in x
    G₄≡G₄′ = let _ , _ , _ , x , _ = Π-PE-injectivity Π≡Π′ in x

    A₁≡A₂ = PE.subst₂ (λ X Y → Γ ⊢ Π F₁ ^ % ° ⁰ ▹ G₁ ° ⁰ ≅ Π X ^ % ° ⁰ ▹ Y ° ⁰ ^ [ ! , ι ⁰ ]) (PE.sym F₂≡F₂′) (PE.sym G₂≡G₂′) A₁≡A₂′
    A₃≡A₄ = PE.subst₂ (λ X Y → Γ ⊢ Π F₃ ^ % ° ⁰ ▹ G₃ ° ⁰ ≅ Π X ^ % ° ⁰ ▹ Y ° ⁰ ^ [ ! , ι ⁰ ]) (PE.sym F₄≡F₄′) (PE.sym G₄≡G₄′) A₃≡A₄′
    [F₁≡F₂] = PE.subst (λ X → ∀ {ρ Δ} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Δ ⊩⟨ ι ⁰ ⟩ wk ρ F₁ ≡ wk ρ X ^ [ % , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
                       (PE.sym F₂≡F₂′) [F₁≡F₂′]
    [F₃≡F₄] = PE.subst (λ X → ∀ {ρ Δ} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Δ ⊩⟨ ι ⁰ ⟩ wk ρ F₃ ≡ wk ρ X ^ [ % , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
                       (PE.sym F₄≡F₄′) [F₃≡F₄′]
    [G₁≡G₂] = PE.subst (λ X → ∀ {ρ Δ a} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
                              → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F₁ ^ [ % , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
                              → Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₁ [ a ] ≡ wk (lift ρ) X [ a ] ^ [ ! , ι ⁰ ] / [G₁] [ρ] ⊢Δ [a])
                       (PE.sym G₂≡G₂′) [G₁≡G₂′]
    [G₃≡G₄] = PE.subst (λ X → ∀ {ρ Δ a} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
                              → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F₃ ^ [ % , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
                              → Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₃ [ a ] ≡ wk (lift ρ) X [ a ] ^ [ ! , ι ⁰ ] / [G₃] [ρ] ⊢Δ [a])
                       (PE.sym G₄≡G₄′) [G₃≡G₄′]

    open IdTypeU-lemmas-2 ⊢Γ ⊢A₁ ⊢ΠF₁G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext
      ⊢A₂ ⊢ΠF₂G₂ D₂ ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext
      ⊢A₃ ⊢ΠF₃G₃ D₃ ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext
      ⊢A₄ ⊢ΠF₄G₄ D₄ ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext
      A₁≡A₂ A₃≡A₄ [F₁≡F₂] [F₃≡F₄] [G₁≡G₂] [G₃≡G₄]
      (λ [ρ] ⊢Δ → [Id]SProp ⊢Δ ([F₁] [ρ] ⊢Δ) ([F₃] [ρ] ⊢Δ))
      (λ [ρ] ⊢Δ [x] [y] → [Id]U ⊢Δ ([G₁] [ρ] ⊢Δ [x]) ([G₃] [ρ] ⊢Δ [y]))
      (λ [ρ] ⊢Δ → [Id]SProp ⊢Δ ([F₂] [ρ] ⊢Δ) ([F₄] [ρ] ⊢Δ))
      (λ [ρ] ⊢Δ [x] [y] → [Id]U ⊢Δ ([G₂] [ρ] ⊢Δ [x]) ([G₄] [ρ] ⊢Δ [y]))
      (λ [ρ] ⊢Δ [x] [x′] [x≡x′] [y] [y′] [y≡y′] →
        [IdExt]U ⊢Δ ([G₁] [ρ] ⊢Δ [x]) ([G₁] [ρ] ⊢Δ [x′]) (G₁-ext [ρ] ⊢Δ [x] [x′] [x≡x′]) ([G₃] [ρ] ⊢Δ [y]) ([G₃] [ρ] ⊢Δ [y′]) (G₃-ext [ρ] ⊢Δ [y] [y′] [y≡y′]))
      (λ [ρ] ⊢Δ [x] [x′] [x≡x′] [y] [y′] [y≡y′] →
        [IdExt]U ⊢Δ ([G₂] [ρ] ⊢Δ [x]) ([G₂] [ρ] ⊢Δ [x′]) (G₂-ext [ρ] ⊢Δ [x] [x′] [x≡x′]) ([G₄] [ρ] ⊢Δ [y]) ([G₄] [ρ] ⊢Δ [y′]) (G₄-ext [ρ] ⊢Δ [y] [y′] [y≡y′]))
      (λ [ρ] ⊢Δ → [IdExt]SProp ⊢Δ ([F₁] [ρ] ⊢Δ) ([F₂] [ρ] ⊢Δ) ([F₁≡F₂] [ρ] ⊢Δ) ([F₃] [ρ] ⊢Δ) ([F₄] [ρ] ⊢Δ) ([F₃≡F₄] [ρ] ⊢Δ))
      (λ [ρ] ⊢Δ [x₁] [x₂] [G₁x₁≡G₂x₂] [x₃] [x₄] [G₃x₃≡G₄x₄] → [IdExt]U ⊢Δ ([G₁] [ρ] ⊢Δ [x₁]) ([G₂] [ρ] ⊢Δ [x₂]) [G₁x₁≡G₂x₂] ([G₃] [ρ] ⊢Δ [x₃]) ([G₄] [ρ] ⊢Δ [x₄]) [G₃x₃≡G₄x₄])


[IdExt]U ⊢Γ [A] [A′] [A≡A′] [B] [B′] [B≡B′] = [IdExtShape]U ⊢Γ [A] [A′] (goodCases [A] [A′] [A≡A′]) [A≡A′] [B] [B′] (goodCases [B] [B′] [B≡B′]) [B≡B′]

Ugen' : ∀ {Γ rU l} → (⊢Γ : ⊢ Γ) →  ((next l) LogRel.⊩¹U logRelRec (next l) ^ Γ) (Univ rU l) (next l)
Ugen' {Γ} {rU} {⁰} ⊢Γ = Uᵣ rU ⁰ emb< PE.refl ((idRed:*: (Ugenⱼ ⊢Γ)))
Ugen' {Γ} {rU} {¹} ⊢Γ = Uᵣ rU ¹ ∞< PE.refl (idRed:*: (Uⱼ ⊢Γ))


[Id]UGen : ∀ {A t u Γ l}
         (⊢Γ : ⊢ Γ)
         ([A] : (l LogRel.⊩¹U logRelRec l ^ Γ) A (ι ¹))
         ([t] : Γ ⊩⟨ l ⟩ t ∷ A ^ [ ! , ι ¹ ] / Uᵣ [A])
         ([u] : Γ ⊩⟨ l ⟩ u ∷ A ^ [ ! , ι ¹ ] / Uᵣ [A])
       → Γ ⊩⟨ l ⟩ Id A t u ^ [ % , ι ¹ ]
[Id]UGen {A} {t} {u} {Γ} {ι .¹} ⊢Γ (Uᵣ ! ⁰ emb< PE.refl [[ ⊢A , ⊢B , D ]]) (Uₜ K d typeK K≡K [t]) (Uₜ M d₁ typeM M≡M [u]) =
  let
    [t0] : Γ ⊩⟨ ι ⁰ ⟩ t ^ [ ! , ι ⁰ ]
    [t0] = PE.subst (λ X → Γ ⊩⟨ ι ⁰ ⟩ X ^ [ ! , ι ⁰ ]) (wk-id t) ([t] Twk.id ⊢Γ)
    [u0] = PE.subst (λ X → Γ ⊩⟨ ι ⁰ ⟩ X ^ [ ! , ι ⁰ ]) (wk-id u) ([u] Twk.id ⊢Γ)
    ⊢tA = conv (un-univ (escape [t0])) (sym (subset* D))
    ⊢uA = conv (un-univ (escape [u0])) (sym (subset* D))
  in proj₁ (redSubst* (IdRed* ⊢tA ⊢uA D) ([Id]U ⊢Γ [t0] [u0]))

[Id]UGen {A} {t} {u} {Γ} {ι .¹} ⊢Γ (Uᵣ % ⁰ emb< PE.refl [[ ⊢A , ⊢B , D ]]) (Uₜ K d typeK K≡K [t]) (Uₜ M d₁ typeM M≡M [u]) =
  let
    [t0] : Γ ⊩⟨ ι ⁰ ⟩ t ^ [ % , ι ⁰ ]
    [t0] = PE.subst (λ X → Γ ⊩⟨ ι ⁰ ⟩ X ^ [ % , ι ⁰ ]) (wk-id t) ([t] Twk.id ⊢Γ)
    [u0] = PE.subst (λ X → Γ ⊩⟨ ι ⁰ ⟩ X ^ [ % , ι ⁰ ]) (wk-id u) ([u] Twk.id ⊢Γ)
    ⊢tA = conv (un-univ (escape [t0])) (sym (subset* D))
    ⊢uA = conv (un-univ (escape [u0])) (sym (subset* D))
  in proj₁ (redSubst* (IdRed* ⊢tA ⊢uA D) ([Id]SProp ⊢Γ [t0] [u0]))


[IdExt]UGen : ∀ {A B t v u w Γ l l'}
         (⊢Γ : ⊢ Γ)
         ([A] : (l LogRel.⊩¹U logRelRec l ^ Γ) A (ι ¹))
         ([B] : (l' LogRel.⊩¹U logRelRec l' ^ Γ) B (ι ¹))
         ([A≡B] : Γ ⊩⟨ l ⟩ A ≡ B ^ [ ! , ι ¹ ] / Uᵣ [A])
         ([t] : Γ ⊩⟨ l ⟩ t ∷ A ^ [ ! , ι ¹ ] / Uᵣ [A])
         ([v] : Γ ⊩⟨ l' ⟩ v ∷ B ^ [ ! , ι ¹ ] / Uᵣ [B])
         ([t≡v] : Γ ⊩⟨ l ⟩ t ≡ v ∷ A ^ [ ! , ι ¹ ] / Uᵣ [A])
         ([u] : Γ ⊩⟨ l ⟩ u ∷ A ^ [ ! , ι ¹ ] / Uᵣ [A])
         ([w] : Γ ⊩⟨ l' ⟩ w ∷ B ^ [ ! , ι ¹ ] / Uᵣ [B])
         ([u≡w] : Γ ⊩⟨ l ⟩ u ≡ w ∷ A ^ [ ! , ι ¹ ] / Uᵣ [A])
       → Γ ⊩⟨ l ⟩ Id A t u ≡ Id B v w ^ [ % , ι ¹ ] / [Id]UGen ⊢Γ [A] [t] [u]
[IdExt]UGen {A} {B} {t} {v} {u} {w} {Γ} {.(ι ¹)} {.(ι ¹)} ⊢Γ (Uᵣ ! ⁰ emb< PE.refl d) (Uᵣ r₁ ⁰ emb< PE.refl d₁) [A≡B] [t] [v] [t≡v] [u] [w] [u≡w] =
  let U≡U = whrDet* (red d₁ , Uₙ) ([A≡B] , Uₙ)
      r≡r , _ = Univ-PE-injectivity U≡U
      [UA] = Uᵣ ! ⁰ emb< PE.refl d
      [UB] = Uᵣ r₁ ⁰ emb< PE.refl d₁
      [U] = Ugen' ⊢Γ
      [U]' = Ugen' ⊢Γ
      [UA]' , [UAeq] = redSubst* (red d) (Uᵣ [U])
      [UB]' , [UBeq] = redSubst* (PE.subst (λ X → Γ ⊢ _ ⇒* Univ X _ ^ _) r≡r (red d₁)) (Uᵣ [U]')
      [t]′ = convTerm₁ {t = t} [UA]' (Uᵣ [U]) [UAeq] (irrelevanceTerm (Uᵣ [UA]) [UA]' [t])
      [t^] = univEq (Uᵣ [U]) [t]′
      [v]′ = convTerm₁ {t = v} [UB]' (Uᵣ [U]) [UBeq] (irrelevanceTerm (Uᵣ [UB]) [UB]' [v])
      [v^] = univEq (Uᵣ [U]) [v]′
      [t≡v]′ = convEqTerm₁ {t = t} {u = v} [UA]' (Uᵣ [U]) [UAeq] (irrelevanceEqTerm (Uᵣ [UA]) [UA]' [t≡v])
      [t≡v^] = univEqEq (Uᵣ [U]) [t^] [t≡v]′
      [u]′ = convTerm₁ {t = u} [UA]' (Uᵣ [U]) [UAeq] (irrelevanceTerm (Uᵣ [UA]) [UA]' [u])
      [u^] = univEq (Uᵣ [U]) [u]′
      [w]′ = convTerm₁ {t = w} [UB]' (Uᵣ [U]) [UBeq] (irrelevanceTerm (Uᵣ [UB]) [UB]'  [w])
      [w^] = univEq (Uᵣ [U]) [w]′
      [u≡w]′ = convEqTerm₁ {t = u} {u = w} [UA]' (Uᵣ [U]) [UAeq] (irrelevanceEqTerm (Uᵣ [UA]) [UA]' [u≡w])
      [u≡w^] = univEqEq (Uᵣ [U]) [u^] [u≡w]′
      X = irrelevanceEq {A = Id (U ⁰) t u} {B = Id (U ⁰) v w} ([Id]U ⊢Γ [t^] [u^]) ([Id]UGen ⊢Γ [U] [t]′ [u]′) ([IdExt]U ⊢Γ [t^] [v^] [t≡v^] [u^] [w^] [u≡w^])
      [IdA] , [IdA≡U] = redSubst* (IdRed* (escapeTerm (Uᵣ [UA]) [t]) (escapeTerm (Uᵣ [UA]) [u]) (red d)) ([Id]UGen ⊢Γ [U] [t]′ [u]′)
      [IdB] , [IdB≡U] = redSubst* (IdRed* (escapeTerm (Uᵣ [UB]) [v]) (escapeTerm (Uᵣ [UB]) [w]) (PE.subst (λ X → Γ ⊢ _ ⇒* Univ X _ ^ _) r≡r (red d₁))) ([Id]UGen ⊢Γ [U] [v]′ [w]′)
      [IdA≡U]′ = irrelevanceEq {A = Id A t u} {B = Id (U ⁰) t u} [IdA] ([Id]UGen ⊢Γ [UA] [t] [u]) [IdA≡U]
      [IdB≡U]′ = irrelevanceEq {A = Id B v w} {B = Id (U ⁰) v w} [IdB] ([Id]UGen ⊢Γ [UB] [v] [w]) [IdB≡U]
  in transEq {A = Id A t u} {B = Id (U _) t u} {C = Id B v w}  ([Id]UGen ⊢Γ [UA] [t] [u]) ([Id]UGen ⊢Γ [U] [t]′ [u]′) ([Id]UGen ⊢Γ [UB] [v] [w])
                  [IdA≡U]′ 
                  (transEq {A = Id (U _) t u} {B = Id (U _) v w} {C = Id B v w} ([Id]UGen ⊢Γ [U] [t]′ [u]′) ([Id]UGen ⊢Γ [U] [v]′ [w]′) ([Id]UGen ⊢Γ [UB] [v] [w])
                                   X (symEq {A = Id B v w} {B = Id (U _) v w} ([Id]UGen ⊢Γ [UB] [v] [w]) ([Id]UGen ⊢Γ [U] [v]′ [w]′) [IdB≡U]′)) 

[IdExt]UGen {A} {B} {t} {v} {u} {w} {Γ} {.(ι ¹)} {.(ι ¹)} ⊢Γ (Uᵣ % ⁰ emb< PE.refl d) (Uᵣ r₁ ⁰ emb< PE.refl d₁) [A≡B] [t] [v] [t≡v] [u] [w] [u≡w] =
  let U≡U = whrDet* (red d₁ , Uₙ) ([A≡B] , Uₙ)
      r≡r , _ = Univ-PE-injectivity U≡U
      [UA] = Uᵣ % ⁰ emb< PE.refl d
      [UB] = Uᵣ r₁ ⁰ emb< PE.refl d₁
      [U] = Ugen' ⊢Γ
      [U]' = Ugen' ⊢Γ
      [UA]' , [UAeq] = redSubst* (red d) (Uᵣ [U])
      [UB]' , [UBeq] = redSubst* (PE.subst (λ X → Γ ⊢ _ ⇒* Univ X _ ^ _) r≡r (red d₁)) (Uᵣ [U]')
      [t]′ = convTerm₁ {t = t} [UA]' (Uᵣ [U]) [UAeq] (irrelevanceTerm (Uᵣ [UA]) [UA]' [t])
      [t^] = univEq (Uᵣ [U]) [t]′
      [v]′ = convTerm₁ {t = v} [UB]' (Uᵣ [U]) [UBeq] (irrelevanceTerm (Uᵣ [UB]) [UB]' [v])
      [v^] = univEq (Uᵣ [U]) [v]′
      [t≡v]′ = convEqTerm₁ {t = t} {u = v} [UA]' (Uᵣ [U]) [UAeq] (irrelevanceEqTerm (Uᵣ [UA]) [UA]' [t≡v])
      [t≡v^] = univEqEq (Uᵣ [U]) [t^] [t≡v]′
      [u]′ = convTerm₁ {t = u} [UA]' (Uᵣ [U]) [UAeq] (irrelevanceTerm (Uᵣ [UA]) [UA]' [u])
      [u^] = univEq (Uᵣ [U]) [u]′
      [w]′ = convTerm₁ {t = w} [UB]' (Uᵣ [U]) [UBeq] (irrelevanceTerm (Uᵣ [UB]) [UB]'  [w])
      [w^] = univEq (Uᵣ [U]) [w]′
      [u≡w]′ = convEqTerm₁ {t = u} {u = w} [UA]' (Uᵣ [U]) [UAeq] (irrelevanceEqTerm (Uᵣ [UA]) [UA]' [u≡w])
      [u≡w^] = univEqEq (Uᵣ [U]) [u^] [u≡w]′
      X = irrelevanceEq {A = Id (SProp ⁰) t u} {B = Id (SProp ⁰) v w} ([Id]SProp ⊢Γ [t^] [u^]) ([Id]UGen ⊢Γ [U] [t]′ [u]′) ([IdExt]SProp ⊢Γ [t^] [v^] [t≡v^] [u^] [w^] [u≡w^])
      [IdA] , [IdA≡U] = redSubst* (IdRed* (escapeTerm (Uᵣ [UA]) [t]) (escapeTerm (Uᵣ [UA]) [u]) (red d)) ([Id]UGen ⊢Γ [U] [t]′ [u]′)
      [IdB] , [IdB≡U] = redSubst* (IdRed* (escapeTerm (Uᵣ [UB]) [v]) (escapeTerm (Uᵣ [UB]) [w]) (PE.subst (λ X → Γ ⊢ _ ⇒* Univ X _ ^ _) r≡r (red d₁))) ([Id]UGen ⊢Γ [U] [v]′ [w]′)
      [IdA≡U]′ = irrelevanceEq {A = Id A t u} {B = Id (SProp ⁰) t u} [IdA] ([Id]UGen ⊢Γ [UA] [t] [u]) [IdA≡U]
      [IdB≡U]′ = irrelevanceEq {A = Id B v w} {B = Id (SProp ⁰) v w} [IdB] ([Id]UGen ⊢Γ [UB] [v] [w]) [IdB≡U]
  in transEq {A = Id A t u} {B = Id (SProp _) t u} {C = Id B v w}  ([Id]UGen ⊢Γ [UA] [t] [u]) ([Id]UGen ⊢Γ [U] [t]′ [u]′) ([Id]UGen ⊢Γ [UB] [v] [w])
                  [IdA≡U]′ 
                  (transEq {A = Id (SProp _) t u} {B = Id (SProp _) v w} {C = Id B v w} ([Id]UGen ⊢Γ [U] [t]′ [u]′) ([Id]UGen ⊢Γ [U] [v]′ [w]′) ([Id]UGen ⊢Γ [UB] [v] [w])
                                   X (symEq {A = Id B v w} {B = Id (SProp _) v w} ([Id]UGen ⊢Γ [UB] [v] [w]) ([Id]UGen ⊢Γ [U] [v]′ [w]′) [IdB≡U]′)) 
