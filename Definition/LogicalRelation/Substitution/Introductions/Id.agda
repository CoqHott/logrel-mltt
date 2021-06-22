{-# OPTIONS --allow-unsolved-metas #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Id {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
import Definition.Typed.Weakening as Twk
open import Definition.Typed.EqualityRelation
open import Definition.Typed.RedSteps
open import Definition.LogicalRelation
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

IdTypeSProp : ∀ {t u Γ}
         (⊢Γ : ⊢ Γ)
         ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ^ [ % , ι ⁰ ])
         ([u] : Γ ⊩⟨ ι ⁰ ⟩ u ^ [ % , ι ⁰ ])
         → Γ ⊩⟨ ι ¹ ⟩ Id (SProp ⁰) t u ^ [ % , ι ¹ ]
IdTypeSProp {t} {u} {Γ} ⊢Γ [t] [u] =
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

IdTypeU : ∀ {A B Γ}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ ! , ι ⁰ ])
         ([B] : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ ! , ι ⁰ ])
         → Γ ⊩⟨ ι ¹ ⟩ Id (U ⁰) A B ^ [ % , ι ¹ ]
IdTypeUExt : ∀ {A A′ B B′ Γ}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ ! , ι ⁰ ])
         ([A′] : Γ ⊩⟨ ι ⁰ ⟩ A′ ^ [ ! , ι ⁰ ])
         ([A≡A′] : Γ ⊩⟨ ι ⁰ ⟩ A ≡ A′ ^ [ ! , ι ⁰ ] / [A])
         ([B] : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ ! , ι ⁰ ])
         ([B′] : Γ ⊩⟨ ι ⁰ ⟩ B′ ^ [ ! , ι ⁰ ])
         ([B≡B′] : Γ ⊩⟨ ι ⁰ ⟩ B ≡ B′ ^ [ ! , ι ⁰ ] / [B])
         → Γ ⊩⟨ ι ¹ ⟩ Id (U ⁰) A B ≡ Id (U ⁰) A′ B′ ^ [ % , ι ¹ ] / IdTypeU ⊢Γ [A] [B]
IdTypeU ⊢Γ (ne x) [B] = {!!}
IdTypeU ⊢Γ (ℕᵣ x) (ℕᵣ x₁) = {!!}
IdTypeU ⊢Γ (ℕᵣ x) (ne x₁) = {!!}
IdTypeU ⊢Γ (ℕᵣ x) (Πᵣ x₁) = {!!}
IdTypeU ⊢Γ (Πᵣ x) (ℕᵣ x₁) = {!!}
IdTypeU ⊢Γ (Πᵣ x) (ne x₁) = {!!}
IdTypeU {A} {B} {Γ} ⊢Γ (Πᵣ′ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢ΠFG , D ]] ⊢F ⊢G A≡A [F] [G] G-ext)
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
      (λ [ρ] ⊢Δ → IdTypeU ⊢Δ ([F] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ))
      (λ [ρ] ⊢Δ [x] [y] → IdTypeU ⊢Δ ([G] [ρ] ⊢Δ [x]) ([G₁] [ρ] ⊢Δ [y]))
      (λ [ρ] ⊢Δ [x] [x′] [x≡x′] [y] [y′] [y≡y′] →
        IdTypeUExt ⊢Δ ([G] [ρ] ⊢Δ [x]) ([G] [ρ] ⊢Δ [x′]) (G-ext [ρ] ⊢Δ [x] [x′] [x≡x′]) ([G₁] [ρ] ⊢Δ [y]) ([G₁] [ρ] ⊢Δ [y′]) (G₁-ext [ρ] ⊢Δ [y] [y′] [y≡y′]))

IdTypeU ⊢Γ (Πᵣ′ rF .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢ΠFG , D ]] ⊢F ⊢G A≡A [F] [G] G-ext)
  (Πᵣ′ rF₁ .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢B , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ B≡B [F₁] [G₁] G₁-ext) = {!!}

IdTypeUExt {A₁} {A₂} {A₃} {A₄} {Γ} ⊢Γ (Πᵣ′ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)
  (Πᵣ′ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₂ G₂ [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]] ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext)
  (Π₌ F₂′ G₂′ D₂′ A₁≡A₂′ [F₁≡F₂′] [G₁≡G₂′])
  (Πᵣ′ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₃ G₃ [[ ⊢A₃ , ⊢ΠF₃G₃ , D₃ ]] ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext)
  (Πᵣ′ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₄ G₄ [[ ⊢A₄ , ⊢ΠF₄G₄ , D₄ ]] ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext)
  (Π₌ F₄′ G₄′ D₄′ A₃≡A₄′ [F₃≡F₄′] [G₃≡G₄′]) =
    ∃₌ (Id (U ⁰) F₂ F₄) (E₂.IdGG₁ (step id) (var 0))
    E₂.D∃ ∃₁≡∃₂
    [IdFF₁≡IdFF₂]
    (λ {ρ} {Δ} {e} [ρ] ⊢Δ [e] → irrelevanceEq″ (PE.sym (E₁.wksubst-IdTel ρ e)) (PE.sym (E₂.wksubst-IdTel ρ e)) PE.refl PE.refl
      (E₁.[IdGG₁] [ρ] ⊢Δ [e]) (PE.subst (λ X → Δ ⊩⟨ ι ¹ ⟩ X ^ [ % , ι ¹ ]) (PE.sym (E₁.wksubst-IdTel ρ e)) (E₁.[IdGG₁] [ρ] ⊢Δ [e]))
      ([IdGG₁≡IdGG₂] [ρ] ⊢Δ [e]))
  where
    module E₁ = IdTypeU-lemmas ⊢Γ ⊢A₁ ⊢ΠF₁G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext ⊢A₃ ⊢ΠF₃G₃ D₃ ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext
      (λ [ρ] ⊢Δ → IdTypeU ⊢Δ ([F₁] [ρ] ⊢Δ) ([F₃] [ρ] ⊢Δ))
      (λ [ρ] ⊢Δ [x] [y] → IdTypeU ⊢Δ ([G₁] [ρ] ⊢Δ [x]) ([G₃] [ρ] ⊢Δ [y]))
      (λ [ρ] ⊢Δ [x] [x′] [x≡x′] [y] [y′] [y≡y′] →
        IdTypeUExt ⊢Δ ([G₁] [ρ] ⊢Δ [x]) ([G₁] [ρ] ⊢Δ [x′]) (G₁-ext [ρ] ⊢Δ [x] [x′] [x≡x′]) ([G₃] [ρ] ⊢Δ [y]) ([G₃] [ρ] ⊢Δ [y′]) (G₃-ext [ρ] ⊢Δ [y] [y′] [y≡y′]))
    module E₂ = IdTypeU-lemmas ⊢Γ ⊢A₂ ⊢ΠF₂G₂ D₂ ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext ⊢A₄ ⊢ΠF₄G₄ D₄ ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext
      (λ [ρ] ⊢Δ → IdTypeU ⊢Δ ([F₂] [ρ] ⊢Δ) ([F₄] [ρ] ⊢Δ))
      (λ [ρ] ⊢Δ [x] [y] → IdTypeU ⊢Δ ([G₂] [ρ] ⊢Δ [x]) ([G₄] [ρ] ⊢Δ [y]))
      (λ [ρ] ⊢Δ [x] [x′] [x≡x′] [y] [y′] [y≡y′] →
        IdTypeUExt ⊢Δ ([G₂] [ρ] ⊢Δ [x]) ([G₂] [ρ] ⊢Δ [x′]) (G₂-ext [ρ] ⊢Δ [x] [x′] [x≡x′]) ([G₄] [ρ] ⊢Δ [y]) ([G₄] [ρ] ⊢Δ [y′]) (G₄-ext [ρ] ⊢Δ [y] [y′] [y≡y′]))

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

    [IdFF₁≡IdFF₂] : ∀ {ρ Δ} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ)
      → Δ ⊩⟨ ι ¹ ⟩ wk ρ (Id (U ⁰) F₁ F₃) ≡ wk ρ (Id (U ⁰) F₂ F₄) ^ [ % , ι ¹ ] / E₁.[IdFF₁] [ρ] ⊢Δ
    [IdFF₁≡IdFF₂] = (λ [ρ] ⊢Δ → irrelevanceEq (IdTypeU ⊢Δ ([F₁] [ρ] ⊢Δ) ([F₃] [ρ] ⊢Δ)) (E₁.[IdFF₁] [ρ] ⊢Δ)
      (IdTypeUExt ⊢Δ ([F₁] [ρ] ⊢Δ) ([F₂] [ρ] ⊢Δ) ([F₁≡F₂] [ρ] ⊢Δ) ([F₃] [ρ] ⊢Δ) ([F₄] [ρ] ⊢Δ) ([F₃≡F₄] [ρ] ⊢Δ)))

    abstract
      [Ideq] : ∀ {ρ Δ e} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ)
        → ([e] : Δ ⊩⟨ ι ¹ ⟩ e ∷ wk ρ (Id (U ⁰) F₁ F₃) ^ [ % , ι ¹ ] / E₁.[IdFF₁] [ρ] ⊢Δ)
        → ∀ {ρ₁ Δ₁ a} → ([ρ₁] : ρ₁ Twk.∷ Δ₁ ⊆ Δ) → (⊢Δ₁ : ⊢ Δ₁)
        → ([a] : Δ₁ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ₁ (wk ρ F₃) ^ [ ! , ι ⁰ ] / (Lwk.wk [ρ₁] ⊢Δ₁ ([F₃] [ρ] ⊢Δ)))
        → Δ₁ ⊩⟨ ι ¹ ⟩ wk (lift ρ₁) (Id (U ⁰) (wk (lift (step ρ)) G₁ [ E₁.b (step ρ) (wk1 e) (var 0) ]) (wk (lift ρ) G₃)) [ a ]
             ≡ wk (lift ρ₁) (Id (U ⁰) (wk (lift (step ρ)) G₂ [ E₂.b (step ρ) (wk1 e) (var 0) ]) (wk (lift ρ) G₄)) [ a ] ^ [ % , ι ¹ ]
             / E₁.[Id] [ρ] ⊢Δ [e] [ρ₁] ⊢Δ₁ [a]
      [Ideq] {ρ} {Δ} {e} [ρ] ⊢Δ [e] {ρ₁} {Δ₁} {a} [ρ₁] ⊢Δ₁ [a] =
        let
          ρ′ = ρ₁ • ρ
          [ρ′] : ρ′ Twk.∷ Δ₁ ⊆ Γ
          [ρ′] = [ρ₁] Twk.•ₜ [ρ]
          [a₃] : Δ₁ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ′ F₃ ^ [ ! , ι ⁰ ] / [F₃] [ρ′] ⊢Δ₁
          [a₃] = irrelevanceTerm′ (wk-comp ρ₁ ρ F₃) PE.refl PE.refl (Lwk.wk [ρ₁] ⊢Δ₁ ([F₃] [ρ] ⊢Δ)) ([F₃] [ρ′] ⊢Δ₁) [a]
          [a₄] = convTerm₁ ([F₃] [ρ′] ⊢Δ₁) ([F₄] [ρ′] ⊢Δ₁) ([F₃≡F₄] [ρ′] ⊢Δ₁) [a₃]
          [a₃≡a₄] = reflEqTerm ([F₃] [ρ′] ⊢Δ₁) [a₃]
          ⊢e′ = PE.subst (λ X → Δ₁ ⊢ wk ρ₁ e ∷ X ^ [ % , ι ¹ ]) (wk-comp ρ₁ ρ _) (Twk.wkTerm [ρ₁] ⊢Δ₁ (escapeTerm (E₁.[IdFF₁] [ρ] ⊢Δ) [e]))
          ⊢e₁ = Idsymⱼ (univ 0<1 ⊢Δ₁) (un-univ (escape ([F₁] [ρ′] ⊢Δ₁))) (un-univ (escape ([F₃] [ρ′] ⊢Δ₁))) ⊢e′
          ⊢e″ = conv ⊢e′ (≅-eq (escapeEq (E₁.[IdFF₁] [ρ′] ⊢Δ₁) ([IdFF₁≡IdFF₂] [ρ′] ⊢Δ₁)))
          ⊢e₂ = Idsymⱼ (univ 0<1 ⊢Δ₁) (un-univ (escape ([F₂] [ρ′] ⊢Δ₁))) (un-univ (escape ([F₄] [ρ′] ⊢Δ₁))) ⊢e″
          [b₁] = [cast] ⊢Δ₁ ([F₃] [ρ′] ⊢Δ₁) ([F₁] [ρ′] ⊢Δ₁) [a₃] ⊢e₁
          [b₂] = [cast] ⊢Δ₁ ([F₄] [ρ′] ⊢Δ₁) ([F₂] [ρ′] ⊢Δ₁) [a₄] ⊢e₂
          [b₁≡b₂] = [castext] ⊢Δ₁ ([F₃] [ρ′] ⊢Δ₁) ([F₄] [ρ′] ⊢Δ₁) ([F₃≡F₄] [ρ′] ⊢Δ₁)
            ([F₁] [ρ′] ⊢Δ₁) ([F₂] [ρ′] ⊢Δ₁) ([F₁≡F₂] [ρ′] ⊢Δ₁)
            [a₃] [a₄] [a₃≡a₄] ⊢e₁ ⊢e₂
          [b₁:F₂] = convTerm₁ ([F₁] [ρ′] ⊢Δ₁) ([F₂] [ρ′] ⊢Δ₁) ([F₁≡F₂] [ρ′] ⊢Δ₁) [b₁]
          [b₁≡b₂:F₂] = convEqTerm₁ ([F₁] [ρ′] ⊢Δ₁) ([F₂] [ρ′] ⊢Δ₁) ([F₁≡F₂] [ρ′] ⊢Δ₁) [b₁≡b₂]
          [G₁b₁≡G₂b₂] = transEq ([G₁] [ρ′] ⊢Δ₁ [b₁]) ([G₂] [ρ′] ⊢Δ₁ [b₁:F₂]) ([G₂] [ρ′] ⊢Δ₁ [b₂])
            ([G₁≡G₂] [ρ′] ⊢Δ₁ [b₁]) (G₂-ext [ρ′] ⊢Δ₁ [b₁:F₂] [b₂] [b₁≡b₂:F₂])
          [a₃≡a₄:F₄] = convEqTerm₁ ([F₃] [ρ′] ⊢Δ₁) ([F₄] [ρ′] ⊢Δ₁) ([F₃≡F₄] [ρ′] ⊢Δ₁) [a₃≡a₄]
          [G₃a₃≡G₄a₄] = transEq ([G₃] [ρ′] ⊢Δ₁ [a₃]) ([G₄] [ρ′] ⊢Δ₁ [a₄]) ([G₄] [ρ′] ⊢Δ₁ [a₄])
            ([G₃≡G₄] [ρ′] ⊢Δ₁ [a₃]) (G₄-ext [ρ′] ⊢Δ₁ [a₄] [a₄] [a₃≡a₄:F₄])
          x₁ = IdTypeU ⊢Δ₁ ([G₁] [ρ′] ⊢Δ₁ [b₁]) ([G₃] [ρ′] ⊢Δ₁ [a₃])
          x = IdTypeUExt ⊢Δ₁ ([G₁] [ρ′] ⊢Δ₁ [b₁]) ([G₂] [ρ′] ⊢Δ₁ [b₂]) [G₁b₁≡G₂b₂]
            ([G₃] [ρ′] ⊢Δ₁ [a₃]) ([G₄] [ρ′] ⊢Δ₁ [a₄]) [G₃a₃≡G₄a₄]
        in irrelevanceEq″ (PE.sym (E₁.IdTel₂-prettify ρ₁ ρ e a)) (PE.sym (E₂.IdTel₂-prettify ρ₁ ρ e a)) PE.refl PE.refl x₁ (E₁.[Id] [ρ] ⊢Δ [e] [ρ₁] ⊢Δ₁ [a]) x

    abstract
      [IdGG₁≡IdGG₂] : ∀ {ρ Δ e} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ)
          → ([e] : Δ ⊩⟨ ι ¹ ⟩ e ∷ wk ρ (Id (U ⁰) F₁ F₃) ^ [ % , ι ¹ ] / E₁.[IdFF₁] [ρ] ⊢Δ)
          → Δ ⊩⟨ ι ¹ ⟩ E₁.IdGG₁ ρ e ≡ E₂.IdGG₁ ρ e ^ [ % , ι ¹ ] / E₁.[IdGG₁] [ρ] ⊢Δ [e]
      [IdGG₁≡IdGG₂] {ρ} {Δ} {e} [ρ] ⊢Δ [e] = let
          [e]′ = convTerm₁ (E₁.[IdFF₁] [ρ] ⊢Δ) (E₂.[IdFF₁] [ρ] ⊢Δ) ([IdFF₁≡IdFF₂] [ρ] ⊢Δ) [e]
          ⊢wkF₃ = escape ([F₃] [ρ] ⊢Δ)
          ⊢wkF₄ = escape ([F₄] [ρ] ⊢Δ)
          [0:F₃] : Δ ∙ wk ρ F₃ ^ [ ! , ι ⁰ ] ⊩⟨ ι ⁰ ⟩ var 0 ∷ wk1 (wk ρ F₃) ^ [ ! , ι ⁰ ] / (Lwk.wk (Twk.step Twk.id) (⊢Δ ∙ ⊢wkF₃) ([F₃] [ρ] ⊢Δ))
          [0:F₃] = let ⊢0 = (var (⊢Δ ∙ ⊢wkF₃) here) in
            neuTerm (Lwk.wk (Twk.step Twk.id) (⊢Δ ∙ ⊢wkF₃) ([F₃] [ρ] ⊢Δ)) (var 0) ⊢0 (~-var ⊢0)
          [0:F₄] = let ⊢0 = (var (⊢Δ ∙ ⊢wkF₄) here) in
            neuTerm (Lwk.wk (Twk.step Twk.id) (⊢Δ ∙ ⊢wkF₄) ([F₄] [ρ] ⊢Δ)) (var 0) ⊢0 (~-var ⊢0)
          x = E₁.[Id] [ρ] ⊢Δ [e] (Twk.step Twk.id) (⊢Δ ∙ ⊢wkF₃) [0:F₃]
          x₁ = [Ideq] [ρ] ⊢Δ [e] (Twk.step Twk.id) (⊢Δ ∙ ⊢wkF₃) [0:F₃]
          ⊢x₁ = PE.subst₂ (λ X Y → Δ ∙ wk ρ F₃ ^ [ ! , ι ⁰ ] ⊢ X ≅ Y ^ [ % , ι ¹ ]) (wkSingleSubstId _) (wkSingleSubstId _) (escapeEq x x₁)
          x₂ = E₂.[Id] [ρ] ⊢Δ [e]′ (Twk.step Twk.id) (⊢Δ ∙ ⊢wkF₄) [0:F₄]
          ⊢x₂ = PE.subst (λ X → Δ ∙ wk ρ F₄ ^ [ ! , ι ⁰ ] ⊢ X ^ [ % , ι ¹ ]) (wkSingleSubstId _) (escape x₂)
        in Π₌ (wk ρ F₄) (Id (U ⁰) (wk (lift (step ρ)) G₂ [ E₂.b (step ρ) (wk1 e) (var 0) ]) (wk (lift ρ) G₄))
          (id (univ (Πⱼ <is≤ 0<1 ▹ ≡is≤ PE.refl ▹ un-univ ⊢wkF₄ ▹ un-univ ⊢x₂)))
          (≅-univ (≅ₜ-Π-cong ⊢wkF₃ (≅-un-univ (escapeEq ([F₃] [ρ] ⊢Δ) ([F₃≡F₄] [ρ] ⊢Δ))) (≅-un-univ ⊢x₁)))
          (λ [ρ₁] ⊢Δ₁ → Lwk.wkEq [ρ₁] ⊢Δ₁ ([F₃] [ρ] ⊢Δ) ([F₃≡F₄] [ρ] ⊢Δ))
          (λ [ρ₁] ⊢Δ₁ [a] → [Ideq] [ρ] ⊢Δ [e] [ρ₁] ⊢Δ₁ [a])

    ∃₁≡∃₂ : Γ ⊢ ∃ Id (U ⁰) F₁ F₃ ▹ E₁.IdGG₁ (step id) (var 0) ≅ ∃ Id (U ⁰) F₂ F₄ ▹ E₂.IdGG₁ (step id) (var 0) ^ [ % , ι ¹ ]
    ∃₁≡∃₂ = (≅-univ (≅ₜ-∃-cong
      E₁.⊢IdFF₁
      (≅-un-univ {!!})
      (≅-un-univ {!!})))

IdTypeUExt [A₁] [A₂] [A₁≡A₂] [A₃] [A₄] [A₃≡A₄] = {!!}

{-

IdType : ∀ {A t u Γ l lA}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ l ⟩ A ^ [ ! , ι lA ])
         ([t] : Γ ⊩⟨ l ⟩ t ∷ A ^ [ ! , ι lA ] / [A])
         ([u] : Γ ⊩⟨ l ⟩ u ∷ A ^ [ ! , ι lA ] / [A])
       → Γ ⊩⟨ l ⟩ Id A t u ^ [ % , ι lA ]
IdTypeExt : ∀ {A B t u v w Γ l lA}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ l ⟩ A ^ [ ! , ι lA ])
         ([B] : Γ ⊩⟨ l ⟩ B ^ [ ! , ι lA ])
         ([A≡B] : Γ ⊩⟨ l ⟩ A ≡ B ^ [ ! , ι lA ] / [A])
         ([t] : Γ ⊩⟨ l ⟩ t ∷ A ^ [ ! , ι lA ] / [A])
         ([v] : Γ ⊩⟨ l ⟩ v ∷ B ^ [ ! , ι lA ] / [B])
         ([t≡v] : Γ ⊩⟨ l ⟩ t ≡ v ∷ A ^ [ ! , ι lA ] / [A])
         ([u] : Γ ⊩⟨ l ⟩ u ∷ A ^ [ ! , ι lA ] / [A])
         ([w] : Γ ⊩⟨ l ⟩ w ∷ B ^ [ ! , ι lA ] / [B])
         ([u≡w] : Γ ⊩⟨ l ⟩ u ≡ w ∷ A ^ [ ! , ι lA ] / [A])
       → Γ ⊩⟨ l ⟩ Id A t u ≡ Id B v w ^ [ % , ι lA ] / IdType ⊢Γ [A] [t] [u]
IdType ⊢Γ (Uᵣ (Uᵣ r ¹ l< () d)) [t] [u]
IdType {A} {t} {u} {Γ} {ι .¹} {.¹} ⊢Γ (Uᵣ (Uᵣ ! ⁰ emb< PE.refl [[ ⊢A , ⊢B , D ]])) (Uₜ K d typeK K≡K [t]) (Uₜ M d₁ typeM M≡M [u]) =
  let
    [t0] : Γ ⊩⟨ ι ⁰ ⟩ t ^ [ ! , ι ⁰ ]
    [t0] = PE.subst (λ X → Γ ⊩⟨ ι ⁰ ⟩ X ^ [ ! , ι ⁰ ]) (wk-id t) ([t] Twk.id ⊢Γ)
    [u0] = PE.subst (λ X → Γ ⊩⟨ ι ⁰ ⟩ X ^ [ ! , ι ⁰ ]) (wk-id u) ([u] Twk.id ⊢Γ)
    ⊢tA = conv (un-univ (escape [t0])) (sym (subset* D))
    ⊢uA = conv (un-univ (escape [u0])) (sym (subset* D))
  in proj₁ (redSubst* (IdRed* ⊢tA ⊢uA D) (IdTypeU ⊢Γ [t0] [u0]))

IdType {A} {t} {u} {Γ} {ι .¹} {.¹} ⊢Γ (Uᵣ (Uᵣ % ⁰ emb< PE.refl [[ ⊢A , ⊢B , D ]])) (Uₜ K d typeK K≡K [t]) (Uₜ M d₁ typeM M≡M [u]) =
  let
    [t0] : Γ ⊩⟨ ι ⁰ ⟩ t ^ [ % , ι ⁰ ]
    [t0] = PE.subst (λ X → Γ ⊩⟨ ι ⁰ ⟩ X ^ [ % , ι ⁰ ]) (wk-id t) ([t] Twk.id ⊢Γ)
    [u0] = PE.subst (λ X → Γ ⊩⟨ ι ⁰ ⟩ X ^ [ % , ι ⁰ ]) (wk-id u) ([u] Twk.id ⊢Γ)
    ⊢tA = conv (un-univ (escape [t0])) (sym (subset* D))
    ⊢uA = conv (un-univ (escape [u0])) (sym (subset* D))
  in proj₁ (redSubst* (IdRed* ⊢tA ⊢uA D) (IdTypeSProp ⊢Γ [t0] [u0]))

IdType ⊢Γ (ℕᵣ x) [t] [u] = {!!}

IdType {A} {t} {u} {Γ} {l} {lA} ⊢Γ (ne′ K [[ ⊢A , ⊢B , D ]] neK K≡K) [t] [u] =
  let
    [A] = ne′ K [[ ⊢A , ⊢B , D ]] neK K≡K
    ⊢tA = escapeTerm {l = l} [A] [t]
    ⊢uA = escapeTerm {l = l} [A] [u]
    [K] = neu {l = l} neK ⊢B K≡K
    [A]′ , [A≡K] = redSubst* D [K]
    [t:K] = convTerm₁ [A]′ [K] [A≡K] (irrelevanceTerm [A] [A]′ [t])
    [u:K] = convTerm₁ [A]′ [K] [A≡K] (irrelevanceTerm [A] [A]′ [u])
    t≡t = escapeTermEq [K] (reflEqTerm [K] [t:K])
    u≡u = escapeTermEq [K] (reflEqTerm [K] [u:K])
    [Id] : Γ ⊩⟨ l ⟩ Id A t u ^ [ % , ι lA ]
    [Id] = ne′ (Id K t u) (redSProp (IdRed*Term ⊢tA ⊢uA [[ ⊢A , ⊢B , D ]])) (Idₙ neK) (~-Id K≡K t≡t u≡u)
  in [Id]

IdType {A} {t} {u} {Γ} {l} {lA} ⊢Γ (Πᵣ′ rF lF lG lF≤ lG≤ F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext)
  (f , [[ ⊢t , ⊢f , Df ]] , funf , f≡f , [fext] , [f]) (g , [[ ⊢u , ⊢g , Dg ]] , fung , g≡g , [gext] , [g]) =
  let
    ⊢tA = conv ⊢t (sym (subset* D))
    ⊢uA = conv ⊢u (sym (subset* D))

    [F0] : Γ ⊩⟨ l ⟩ F ^ [ rF , ι lF ]
    [F0] = PE.subst (λ X → Γ ⊩⟨ l ⟩ X ^ [ rF , ι lF ]) (wk-id F) ([F] Twk.id ⊢Γ)

    ⊢idG : Γ ∙ F ^ [ rF , ι lF ] ⊢ Id G (wk1 t ∘ var 0) (wk1 u ∘ var 0) ^ [ % , ι lG ]
    ⊢idG = let
        ⊢t∘0 = PE.subst (λ X → _ ⊢ wk1 t ∘ var 0 ∷ X ^ [ ! , ι lG ]) (wkSingleSubstId G)
          (Twk.wkTerm (Twk.step Twk.id) (⊢Γ ∙ ⊢F) ⊢t ∘ⱼ var (⊢Γ ∙ ⊢F) here)
        ⊢u∘0 = PE.subst (λ X → _ ⊢ wk1 u ∘ var 0 ∷ X ^ [ ! , ι lG ]) (wkSingleSubstId G)
          (Twk.wkTerm (Twk.step Twk.id) (⊢Γ ∙ ⊢F) ⊢u ∘ⱼ var (⊢Γ ∙ ⊢F) here)
      in univ (Idⱼ (un-univ ⊢G) ⊢t∘0 ⊢u∘0)

    ⊢funext : Γ ⊢ Π F ^ rF ° lF ▹ (Id G ((wk1 t) ∘ (var 0)) ((wk1 u) ∘ (var 0))) ° lG ^ [ % , ι lA ]
    ⊢funext = univ (Πⱼ lF≤ ▹ lG≤ ▹ un-univ ⊢F ▹ un-univ ⊢idG)

    Did : Γ ⊢ Id A t u ⇒* Π F ^ rF ° lF ▹ (Id G ((wk1 t) ∘ (var 0)) ((wk1 u) ∘ (var 0))) ° lG ^ [ % , ι lA ]
    Did =  IdRed* ⊢tA ⊢uA D ⇨* (univ (Id-Π lF≤ lG≤ (un-univ ⊢F) (un-univ ⊢G) ⊢t ⊢u) ⇨ id ⊢funext)

    [idG] : ∀ {ρ Δ a}
          → ([ρ] : Twk._∷_⊆_ ρ Δ Γ) → (⊢Δ : ⊢ Δ)
          → (Δ ⊩⟨ l ⟩ a ∷ wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ)
          → Δ ⊩⟨ l ⟩ wk (lift ρ) (Id G (wk1 t ∘ var 0) (wk1 u ∘ var 0)) [ a ] ^ [ % , ι lG ]
    [idG] {ρ} {Δ} {a} [ρ] ⊢Δ [a] =
      let
        [t∘a] : Δ ⊩⟨ l ⟩ wk ρ t ∘ a ∷ wk (lift ρ) G [ a ] ^ [ ! , ι lG ] / [G] [ρ] ⊢Δ [a]
        [t∘a] = proj₁ (redSubst*Term
          (appRed* (escapeTerm ([F] [ρ] ⊢Δ) [a]) (Twk.wkRed*Term [ρ] ⊢Δ Df))
          ([G] [ρ] ⊢Δ [a]) ([f] [ρ] ⊢Δ [a]))
        [u∘a] : Δ ⊩⟨ l ⟩ wk ρ u ∘ a ∷ wk (lift ρ) G [ a ] ^ [ ! , ι lG ] / [G] [ρ] ⊢Δ [a]
        [u∘a] = proj₁ (redSubst*Term
          (appRed* (escapeTerm ([F] [ρ] ⊢Δ) [a]) (Twk.wkRed*Term [ρ] ⊢Δ Dg))
          ([G] [ρ] ⊢Δ [a]) ([g] [ρ] ⊢Δ [a]))
        [Id] : Δ ⊩⟨ l ⟩ (Id (wk (lift ρ) G [ a ]) (wk ρ t ∘ a) (wk ρ u ∘ a)) ^ [ % , ι lG ]
        [Id] = IdType ⊢Δ ([G] [ρ] ⊢Δ [a]) [t∘a] [u∘a]
      in PE.subst₂ (λ X Y → Δ ⊩⟨ l ⟩ (Id _ (X ∘ a) (Y ∘ a)) ^ [ % , ι lG ]) (PE.sym (irrelevant-subst′ ρ t a)) (PE.sym (irrelevant-subst′ ρ u a)) [Id]

    [idG0] : Γ ∙ F ^ [ rF , ι lF ] ⊩⟨ l ⟩ (Id G (wk1 t ∘ var 0) (wk1 u ∘ var 0)) ^ [ % , ι lG ]
    [idG0] = PE.subst₃ (λ X Y Z → _ ⊩⟨ l ⟩ (Id X (Y ∘ var 0) (Z ∘ var 0)) ^ _)
      (wkSingleSubstId G) (wkSingleSubstId (wk1 t)) (wkSingleSubstId (wk1 u))
      ([idG] {step id} {Γ ∙ F ^ [ rF , ι lF ]} {var 0} (Twk.step Twk.id)
       (⊢Γ ∙ ⊢F) (neuTerm ([F] (Twk.step Twk.id) (⊢Γ ∙ ⊢F)) (var 0)
         (var (⊢Γ ∙ ⊢F) here) (~-var (var (⊢Γ ∙ ⊢F) here))))

    [idGext] : ∀ {ρ Δ a b}
          → ([ρ] : Twk._∷_⊆_ ρ Δ Γ)
          → (⊢Δ : ⊢ Δ)
          → ([a] : Δ ⊩⟨ l ⟩ a ∷ wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ)
          → ([b] : Δ ⊩⟨ l ⟩ b ∷ wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ)
          → ([a≡b] : Δ ⊩⟨ l ⟩ a ≡ b ∷ wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ)
          → Δ ⊩⟨ l ⟩ wk (lift ρ) (Id G (wk1 t ∘ var 0) (wk1 u ∘ var 0)) [ a ] ≡ wk (lift ρ) (Id G (wk1 t ∘ var 0) (wk1 u ∘ var 0)) [ b ] ^ [ % , ι lG ] / [idG] [ρ] ⊢Δ [a]
    [idGext] {ρ} {Δ} {a} {b} [ρ] ⊢Δ [a] [b] [a≡b] =
      let
        [Ga] = [G] [ρ] ⊢Δ [a]
        [Gb] = [G] [ρ] ⊢Δ [b]
        [t∘a] , [ta≡fa] = redSubst*Term
          (appRed* (escapeTerm ([F] [ρ] ⊢Δ) [a]) (Twk.wkRed*Term [ρ] ⊢Δ Df))
          [Ga] ([f] [ρ] ⊢Δ [a])
        [u∘a] , [ua≡ga] = redSubst*Term
          (appRed* (escapeTerm ([F] [ρ] ⊢Δ) [a]) (Twk.wkRed*Term [ρ] ⊢Δ Dg))
          [Ga] ([g] [ρ] ⊢Δ [a])
        [Ga≡Gb] : Δ ⊩⟨ l ⟩ wk (lift ρ) G [ a ] ≡ wk (lift ρ) G [ b ] ^ [ ! , ι lG ] / [Ga]
        [Ga≡Gb] = G-ext [ρ] ⊢Δ [a] [b] [a≡b]
        [t∘b:Gb] , [tb≡fb:Gb] = redSubst*Term
          (appRed* (escapeTerm ([F] [ρ] ⊢Δ) [b]) (Twk.wkRed*Term [ρ] ⊢Δ Df))
          [Gb] ([f] [ρ] ⊢Δ [b])
        [t∘b] : Δ ⊩⟨ l ⟩ wk ρ t ∘ b ∷ wk (lift ρ) G [ a ] ^ [ ! , ι lG ] / [Ga]
        [t∘b] = convTerm₂ [Ga] [Gb] [Ga≡Gb] [t∘b:Gb]
        [u∘b:Gb] , [ub≡gb:Gb] = redSubst*Term
          (appRed* (escapeTerm ([F] [ρ] ⊢Δ) [b]) (Twk.wkRed*Term [ρ] ⊢Δ Dg))
          [Gb] ([g] [ρ] ⊢Δ [b])
        [u∘b] : Δ ⊩⟨ l ⟩ wk ρ u ∘ b ∷ wk (lift ρ) G [ a ] ^ [ ! , ι lG ] / [Ga]
        [u∘b] = convTerm₂ [Ga] [Gb] [Ga≡Gb] [u∘b:Gb]
        [ta≡tb] : Δ ⊩⟨ l ⟩ wk ρ t ∘ a ≡ wk ρ t ∘ b ∷ wk (lift ρ) G [ a ] ^ [ ! , ι lG ] / [Ga]
        [ta≡tb] = transEqTerm [Ga] (transEqTerm [Ga] [ta≡fa] ([fext] [ρ] ⊢Δ [a] [b] [a≡b])) (symEqTerm [Ga] (convEqTerm₂ [Ga] [Gb] [Ga≡Gb] [tb≡fb:Gb]))
        [ua≡ub] : Δ ⊩⟨ l ⟩ wk ρ u ∘ a ≡ wk ρ u ∘ b ∷ wk (lift ρ) G [ a ] ^ [ ! , ι lG ] / [Ga]
        [ua≡ub] = transEqTerm [Ga] (transEqTerm [Ga] [ua≡ga] ([gext] [ρ] ⊢Δ [a] [b] [a≡b])) (symEqTerm [Ga] (convEqTerm₂ [Ga] [Gb] [Ga≡Gb] [ub≡gb:Gb]))
        [IdExt] : Δ ⊩⟨ l ⟩ (Id (wk (lift ρ) G [ a ]) (wk ρ t ∘ a) (wk ρ u ∘ a)) ≡ (Id (wk (lift ρ) G [ b ]) (wk ρ t ∘ b) (wk ρ u ∘ b)) ^ [ % , ι lG ] / IdType ⊢Δ [Ga] [t∘a] [u∘a]
        [IdExt] = IdTypeExt ⊢Δ [Ga] [Gb] [Ga≡Gb] [t∘a] [t∘b:Gb] [ta≡tb] [u∘a] [u∘b:Gb] [ua≡ub]
      in irrelevanceEq″
        (PE.cong₂ (λ X Y → Id _ (X ∘ a) (Y ∘ a)) (PE.sym (irrelevant-subst′ ρ t a)) (PE.sym (irrelevant-subst′ ρ u a)))
        (PE.cong₂ (λ X Y → Id _ (X ∘ b) (Y ∘ b)) (PE.sym (irrelevant-subst′ ρ t b)) (PE.sym (irrelevant-subst′ ρ u b)))
        PE.refl PE.refl
        (IdType ⊢Δ [Ga] [t∘a] [u∘a]) ([idG] [ρ] ⊢Δ [a]) [IdExt]
  in Πᵣ (Πᵣ rF lF lG lF≤ lG≤ F (Id G ((wk1 t) ∘ (var 0)) ((wk1 u) ∘ (var 0)))
      [[ univ (Idⱼ (un-univ ⊢A) ⊢tA ⊢uA) , ⊢funext , Did ]]
      ⊢F ⊢idG
      (≅-univ (≅ₜ-Π-cong ⊢F (≅-un-univ (escapeEqRefl [F0]))
        (≅-un-univ (escapeEqRefl [idG0]))))
      [F] [idG] [idGext])

IdType ⊢Γ (emb {l′ = ι ⁰} emb< [A]) [t] [u] = emb emb< (IdType ⊢Γ [A] [t] [u])
IdType ⊢Γ (emb {l′ = ι ¹} ∞< [A]) [t] [u] = emb ∞< (IdType ⊢Γ [A] [t] [u])

IdTypeExt ⊢Γ [A] [B] [t] [v] [t≡v] [u] [w] [u≡w] = {!!}

-- IdTypeExt {A} {A′} {t} {t′} {u} {u′} {Γ} ⊢Γ (ℕᵣ [[ ⊢A , ⊢B , D ]]) [A′] [A≡A′] [t] [t′] [t≡t′] [u] [u′] [u≡u′] = {!!}

-- IdTypeExt {A} {A′} {t} {t′} {u} {u′} {Γ} ⊢Γ (ne′ K [[ ⊢A , ⊢B , D ]] neK K≡K) [A′] (ne₌ M [[ ⊢A′ , ⊢B′ ,  D′ ]] neM K≡M) [t] [t′] [t≡t′] [u] [u′] [u≡u′] =
--   let
--     [A] = (ne′ K [[ ⊢A , ⊢B , D ]] neK K≡K)
--     ⊢t′A′ = escapeTerm {l = ι ⁰} [A′] [t′]
--     ⊢u′A′ = escapeTerm {l = ι ⁰} [A′] [u′]
--     A≡K = subset* D
--     t≡t′ = ≅-conv (escapeTermEq {l = ι ⁰} [A] [t≡t′]) A≡K
--     u≡u′ = ≅-conv (escapeTermEq {l = ι ⁰} [A] [u≡u′]) A≡K
--   in
--   ne₌ (Id M t′ u′) (redSProp (IdRed*Term ⊢t′A′ ⊢u′A′ [[ ⊢A′ , ⊢B′ , D′ ]]))
--     (Idₙ neM) (~-Id K≡M t≡t′ u≡u′)

-- IdTypeExt {A} {A′} {t} {t′} {u} {u′} {Γ} ⊢Γ
--   (Πᵣ′ rF .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D ⊢F ⊢G A≡A [F] [G] G-ext)
--   (Πᵣ′ rF′ .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢A′ , ⊢B′ , D′ ]] ⊢F′ ⊢G′ A′≡A′ [F′] [G′] G′-ext)
--   (Π₌ F′₀ G′₀ D′₀ A≡B [F≡F′₀] [G≡G′₀])
--   [t] [t′] (f₀ , f′₀ , [[ ⊢t , ⊢f₀ , Df₀ ]] , [[ ⊢t′ , ⊢f′₀ , Df′₀ ]] , funf₀ , funf′₀ , f₀≡f′₀ , [t]′ , [t′]′ , [f₀≡f′₀])
--   [u] [u′] (g₀ , g′₀ , [[ ⊢u , ⊢g₀ , Dg₀ ]] , [[ ⊢u′ , ⊢g′₀ , Dg′₀ ]] , fung₀ , fung′₀ , g₀≡g′₀ , [u]′ , [u′]′ , [g₀≡g′₀]) = {!!}
--   -- let
--   --   Π≡Π = whrDet* (D′ , Whnf.Πₙ) (D′₀ , Whnf.Πₙ)
--   --   F′≡F′₀ , rF′≡rF , lF′≡lF , G′≡G′₀ , lG′≡lG = Π-PE-injectivity Π≡Π
--   --   [F≡F′] = PE.subst (λ X → ∀ {ρ} {Δ} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ) → Δ ⊩⟨ ι ⁰ ⟩ wk ρ F ≡ wk ρ X ^ [ rF , _ ] / [F] [ρ] ⊢Δ) (PE.sym F′≡F′₀) [F≡F′₀]
--   --   [G≡G′] = PE.subst (λ X → ∀ {ρ} {Δ} {a} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ) → ([a] : _) → Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G [ a ] ≡ wk (lift ρ) X [ a ] ^ [ _ , _ ] / [G] [ρ] ⊢Δ [a]) (PE.sym G′≡G′₀) [G≡G′₀]

--   --   f , [[ ⊢t , _ , Df ]] , funf , _ , _ , [f] = [t]
--   --   f₀≡f = whrDet*Term (Df₀ , functionWhnf funf₀) (Df , functionWhnf funf)
--   --   f′ , [[ ⊢t′ , _ , Df′ ]] , funf′ , _ , _ , [f′] = [t′]
--   --   f′₀≡f′ = whrDet*Term (Df′₀ , functionWhnf funf′₀) (Df′ , functionWhnf funf′)
--   --   g , [[ ⊢u , _ , Dg ]] , fung , _ , _ , [g] = [u]
--   --   g₀≡g = whrDet*Term (Dg₀ , functionWhnf fung₀) (Dg , functionWhnf fung)
--   --   g′ , [[ ⊢u′ , _ , Dg′ ]] , fung′ , _ , _ , [g′] = [u′]
--   --   g′₀≡g′ = whrDet*Term (Dg′₀ , functionWhnf fung′₀) (Dg′ , functionWhnf fung′)

--   --   [text] = λ {ρ} {Δ} {a} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
--   --         ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F ^ [ rF , ι ⁰ ] / [F] [ρ] ⊢Δ) → redSubst*Term
--   --         (appRed* (escapeTerm ([F] [ρ] ⊢Δ) [a]) (Twk.wkRed*Term [ρ] ⊢Δ Df))
--   --         ([G] [ρ] ⊢Δ [a]) ([f] [ρ] ⊢Δ [a])
--   --   [t′ext] = λ {ρ} {Δ} {a} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
--   --         ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F′ ^ [ rF′ , ι ⁰ ] / [F′] [ρ] ⊢Δ) → redSubst*Term
--   --         (appRed* (escapeTerm ([F′] [ρ] ⊢Δ) [a]) (Twk.wkRed*Term [ρ] ⊢Δ Df′))
--   --         ([G′] [ρ] ⊢Δ [a]) ([f′] [ρ] ⊢Δ [a])
--   --   [uext] = λ {ρ} {Δ} {a} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
--   --         ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F ^ [ rF , ι ⁰ ] / [F] [ρ] ⊢Δ) → redSubst*Term
--   --         (appRed* (escapeTerm ([F] [ρ] ⊢Δ) [a]) (Twk.wkRed*Term [ρ] ⊢Δ Dg))
--   --         ([G] [ρ] ⊢Δ [a]) ([g] [ρ] ⊢Δ [a])
--   --   [u′ext] = λ {ρ} {Δ} {a} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
--   --         ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F′ ^ [ rF′ , ι ⁰ ] / [F′] [ρ] ⊢Δ) → redSubst*Term
--   --         (appRed* (escapeTerm ([F′] [ρ] ⊢Δ) [a]) (Twk.wkRed*Term [ρ] ⊢Δ Dg′))
--   --         ([G′] [ρ] ⊢Δ [a]) ([g′] [ρ] ⊢Δ [a])

--   --   [idG] = λ {ρ} {Δ} {a} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F ^ [ rF , ι ⁰ ] / [F] [ρ] ⊢Δ) →
--   --     PE.subst₂ (λ X Y → Δ ⊩⟨ ι ⁰ ⟩ Id (subst (sgSubst a) (wk (lift ρ) G)) (X ∘ a) (Y ∘ a) ^ [ % , ι ⁰ ])
--   --       (PE.sym (irrelevant-subst′ ρ t a)) (PE.sym (irrelevant-subst′ ρ u a))
--   --       (IdType ⊢Δ ([G] [ρ] ⊢Δ [a]) (proj₁ ([text] [ρ] ⊢Δ [a])) (proj₁ ([uext] [ρ] ⊢Δ [a])))
--   --   [idG≡idG′] : ∀ {ρ Δ a}
--   --         → ([ρ] : Twk._∷_⊆_ ρ Δ Γ)
--   --         → (⊢Δ : ⊢ Δ)
--   --         → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F ^ [ rF , ι ⁰ ] / [F] [ρ] ⊢Δ)
--   --         → Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) (Id G (wk1 t ∘ var 0) (wk1 u ∘ var 0)) [ a ] ≡ wk (lift ρ) (Id G′ (wk1 t′ ∘ var 0) (wk1 u′ ∘ var 0)) [ a ] ^ [ % , ι ⁰ ] / [idG] [ρ] ⊢Δ [a]
--   --   [idG≡idG′] {ρ} {Δ} {a} [ρ] ⊢Δ [a] =
--   --     let
--   --       [aF′] = convTerm₁′ (PE.sym rF′≡rF) PE.refl ([F] [ρ] ⊢Δ) ([F′] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ) [a]
--   --       [Ga] = [G] [ρ] ⊢Δ [a]
--   --       [G′a] = [G′] [ρ] ⊢Δ [aF′]
--   --       [Ga≡G′a] : Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G [ a ] ≡ wk (lift ρ) G′ [ a ] ^ [ ! , ι ⁰ ] / [Ga]
--   --       [Ga≡G′a] = [G≡G′] [ρ] ⊢Δ [a]
--   --       [t∘a] , [ta≡fa] = [text] [ρ] ⊢Δ [a]
--   --       [t′∘a] , [t′a≡f′a] = [t′ext] [ρ] ⊢Δ [aF′]
--   --       [fa≡f′a] = PE.subst₂ (λ X Y → Δ ⊩⟨ ι ⁰ ⟩ wk ρ X ∘ a ≡ wk ρ Y ∘ a ∷ wk (lift ρ) G [ a ] ^ [ ! , ι ⁰ ] / [Ga]) f₀≡f f′₀≡f′ ([f₀≡f′₀] [ρ] ⊢Δ [a])
--   --       [ta≡t′a] : Δ ⊩⟨ ι ⁰ ⟩ wk ρ t ∘ a ≡ wk ρ t′ ∘ a ∷ wk (lift ρ) G [ a ] ^ [ ! , ι ⁰ ] / [Ga]
--   --       [ta≡t′a] = transEqTerm [Ga] (transEqTerm [Ga] [ta≡fa] [fa≡f′a]) (symEqTerm [Ga] (convEqTerm₂ [Ga] [G′a] [Ga≡G′a] [t′a≡f′a]))
--   --       [u∘a] , [ua≡ga] = [uext] [ρ] ⊢Δ [a]
--   --       [u′∘a] , [u′a≡g′a] = [u′ext] [ρ] ⊢Δ [aF′]
--   --       [ga≡g′a] = PE.subst₂ (λ X Y → Δ ⊩⟨ ι ⁰ ⟩ wk ρ X ∘ a ≡ wk ρ Y ∘ a ∷ wk (lift ρ) G [ a ] ^ [ ! , ι ⁰ ] / [Ga]) g₀≡g g′₀≡g′ ([g₀≡g′₀] [ρ] ⊢Δ [a])
--   --       [ua≡u′a] : Δ ⊩⟨ ι ⁰ ⟩ wk ρ u ∘ a ≡ wk ρ u′ ∘ a ∷ wk (lift ρ) G [ a ] ^ [ ! , ι ⁰ ] / [Ga]
--   --       [ua≡u′a] = transEqTerm [Ga] (transEqTerm [Ga] [ua≡ga] [ga≡g′a]) (symEqTerm [Ga] (convEqTerm₂ [Ga] [G′a] [Ga≡G′a] [u′a≡g′a]))
--   --       [idG≡idG′]′ : Δ ⊩⟨ ι ⁰ ⟩ Id (wk (lift ρ) G [ a ]) (wk ρ t ∘ a) (wk ρ u ∘ a) ≡ Id (wk (lift ρ) G′ [ a ]) (wk ρ t′ ∘ a) (wk ρ u′ ∘ a) ^ [ % , ι ⁰ ] / IdType ⊢Δ [Ga] [t∘a] [u∘a]
--   --       [idG≡idG′]′ = IdTypeExt ⊢Δ [Ga] [G′a] [Ga≡G′a] [t∘a] [t′∘a] [ta≡t′a] [u∘a] [u′∘a] [ua≡u′a]
--   --     in irrelevanceEq″ (PE.cong₂ (λ X Y → Id (wk (lift ρ) G [ a ]) (X ∘ a) (Y ∘ a)) (PE.sym (irrelevant-subst′ ρ t a)) (PE.sym (irrelevant-subst′ ρ u a)))
--   --       (PE.cong₂ (λ X Y → Id (wk (lift ρ) G′ [ a ]) (X ∘ a) (Y ∘ a)) (PE.sym (irrelevant-subst′ ρ t′ a)) (PE.sym (irrelevant-subst′ ρ u′ a)))
--   --       PE.refl PE.refl
--   --       (IdType ⊢Δ [Ga] [t∘a] [u∘a]) ([idG] [ρ] ⊢Δ [a]) [idG≡idG′]′

--   --   [var0] = neuTerm ([F] (Twk.step Twk.id) (⊢Γ ∙ ⊢F)) (var 0) (var (⊢Γ ∙ ⊢F) here) (~-var (var (⊢Γ ∙ ⊢F) here))
--   --   ⊢idG≡idG′₀ : Γ ∙ F ^ [ rF , ι ⁰ ] ⊢ (Id G (wk1 t ∘ var 0) (wk1 u ∘ var 0)) ≅ (Id G′ (wk1 t′ ∘ var 0) (wk1 u′ ∘ var 0)) ^ [ % , ι ⁰ ]
--   --   ⊢idG≡idG′₀ = PE.subst₃ (λ X Y Z → _ ⊢ (Id X (Y ∘ var 0) (Z ∘ var 0)) ≅ _ ^ _)
--   --     (wkSingleSubstId G) (wkSingleSubstId (wk1 t)) (wkSingleSubstId (wk1 u))
--   --     (PE.subst₃ (λ X Y Z → _ ⊢ _ ≅ (Id X (Y ∘ var 0) (Z ∘ var 0)) ^ _)
--   --       (wkSingleSubstId G′) (wkSingleSubstId (wk1 t′)) (wkSingleSubstId (wk1 u′))
--   --       (escapeEq ([idG] (Twk.step Twk.id) (⊢Γ ∙ ⊢F) [var0]) ([idG≡idG′] {step id} {Γ ∙ F ^ [ rF , ι ⁰ ]} {var 0} (Twk.step Twk.id) (⊢Γ ∙ ⊢F) [var0])))

--   --   ⊢F≡F′ = PE.subst₂ (λ X Y → _ ⊢ X ≅ Y ^ _) (wk-id F) (PE.trans (wk-id F′₀) (PE.sym F′≡F′₀))
--   --     (escapeEq ([F] Twk.id ⊢Γ) ([F≡F′₀] Twk.id ⊢Γ))

--   --   [A′] = (Πᵣ′ rF′ ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢A′ , ⊢B′ , D′ ]] ⊢F′ ⊢G′ A′≡A′ [F′] [G′] G′-ext)
--   --   ⊢t′A′ = escapeTerm {l = ι ⁰} [A′] [t′]
--   --   ⊢u′A′ = escapeTerm {l = ι ⁰} [A′] [u′]
--   --   ⊢t′∘a = PE.subst (λ X → _ ⊢ wk1 t′ ∘ var 0 ∷ X ^ [ ! , ι ⁰ ]) (wkSingleSubstId G′)
--   --     (Twk.wkTerm (Twk.step Twk.id) (⊢Γ ∙ ⊢F′) ⊢t′ ∘ⱼ var (⊢Γ ∙ ⊢F′) here)
--   --   ⊢u′∘a = PE.subst (λ X → _ ⊢ wk1 u′ ∘ var 0 ∷ X ^ [ ! , ι ⁰ ]) (wkSingleSubstId G′)
--   --     (Twk.wkTerm (Twk.step Twk.id) (⊢Γ ∙ ⊢F′) ⊢u′ ∘ⱼ var (⊢Γ ∙ ⊢F′) here)
--   --   ⊢funext′ : Γ ⊢ Π F′ ^ rF′ ° ⁰ ▹ Id G′ (wk1 t′ ∘ var 0) (wk1 u′ ∘ var 0) ° ⁰ ^ [ % , ι ⁰ ]
--   --   ⊢funext′ = univ (Πⱼ ≡is≤ PE.refl ▹ ≡is≤ PE.refl ▹ un-univ ⊢F′ ▹ Idⱼ (un-univ ⊢G′) ⊢t′∘a ⊢u′∘a)
--   --   Did : Γ ⊢ Id A′ t′ u′ ⇒* Π F′ ^ rF′ ° ⁰ ▹ (Id G′ ((wk1 t′) ∘ (var 0)) ((wk1 u′) ∘ (var 0))) ° ⁰ ^ [ % , ι ⁰ ]
--   --   Did = IdRed* ⊢t′A′ ⊢u′A′ D′ ⇨* ((univ (Id-Π (≡is≤ PE.refl) (≡is≤ PE.refl) (un-univ ⊢F′) (un-univ ⊢G′) ⊢t′ ⊢u′)) ⇨ id ⊢funext′)
--   -- in
--   -- Π₌ F′ (Id G′ ((wk1 t′) ∘ (var 0)) ((wk1 u′) ∘ (var 0)))
--   --   (PE.subst (λ X → Γ ⊢ Id A′ t′ u′ ⇒* Π F′ ^ X ° ⁰ ▹ _ ° ⁰ ^ [ % , ι ⁰ ]) rF′≡rF Did)
--   --   (≅-univ (≅ₜ-Π-cong ⊢F (≅-un-univ ⊢F≡F′) (≅-un-univ ⊢idG≡idG′₀))) [F≡F′] [idG≡idG′]

-- IdTypeExt ⊢Γ (Πᵣ′ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
--   (ℕᵣ [[ ⊢A′ , ⊢B′ , D′ ]])
--   (Π₌ F′′ G′′ D′′ A≡B [F≡F′] [G≡G′]) [t] [t′] [t≡t′] [u] [u′] [u≡u′] =
--   ⊥-elim (ℕ≢Π (whrDet* (D′ , ℕₙ) (D′′ , Πₙ)))

-- IdTypeExt ⊢Γ (Πᵣ′ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
--   (ne′ M [[ ⊢A′ , ⊢B′ , D′ ]] neM M≡M)
--   (Π₌ F′′ G′′ D′′ A≡B [F≡F′] [G≡G′]) [t] [t′] [t≡t′] [u] [u′] [u≡u′] =
--   ⊥-elim (Π≢ne neM (whrDet* (D′′ , Πₙ) (D′ , ne neM)))

-- IdTerm : ∀ {A t u Γ l}
--          (⊢Γ : ⊢ Γ)
--          ([A] : Γ ⊩⟨ l ⟩ A ^ !)
--          ([t] : Γ ⊩⟨ l ⟩ t ∷ A ^ ! / [A])
--          ([u] : Γ ⊩⟨ l ⟩ u ∷ A ^ ! / [A])
--        → Γ ⊩⟨ ¹ ⟩ Id A t u ∷ SProp ^ ! / Uᵣ′ _ ⁰ 0<1 ⊢Γ
-- IdTerm {A} {t} {u} {Γ} {l} ⊢Γ [A] [t] [u] with escapeTerm {l = l} [A] [t] | escapeTerm {l = l} [A] [u]
-- IdTerm ⊢Γ (Uᵣ (Uᵣ l′ l< ⊢Γ₁)) [t] [u] | ⊢tA | ⊢uA = {!!}
-- IdTerm {A} {t} {u} {Γ} {l} ⊢Γ (ℕᵣ [ ⊢A , ⊢B , D ]) [t] [u] | ⊢tA | ⊢uA =
--   proj₁ (redSubst*Term (IdRed*Term′ ⊢tA ⊢uA D) (Uᵣ′ _ ⁰ 0<1 ⊢Γ) (aux [t] [u]))
--   where
--     [A] = (ℕᵣ ([ ⊢A , ⊢B , D ]))
--     [ℕ] : Γ ⊩⟨ l ⟩ ℕ ^ !
--     [ℕ] = ℕᵣ (idRed:*: (ℕⱼ ⊢Γ))
--     A≡ℕ = redSubst* D [ℕ]

--     aux : ∀ {t u} ([t]′ : Γ ⊩⟨ l ⟩ t ∷ ℕ ^ ! / [ℕ]) ([u]′ : Γ ⊩⟨ l ⟩ u ∷ ℕ ^ ! / [ℕ]) →
--         Γ ⊩⟨ ¹ ⟩ Id ℕ t u ∷ SProp ^ ! / Uᵣ′ _ ⁰ 0<1 ⊢Γ
--     aux (ℕₜ .(suc m) [ ⊢tℕ , ⊢smℕ , dt ] sm≡sm (sucᵣ {m} [m]))
--         (ℕₜ .(suc n) [ ⊢uℕ , ⊢snℕ , du ] sn≡sn (sucᵣ {n} [n])) =
--       let [Idmn] = aux [m] [n]
--           ⊢mℕ = escapeTerm [ℕ] [m]
--           ⊢nℕ = escapeTerm [ℕ] [n]
--           nfId = (IdℕRed*Term′ ⊢tℕ ⊢smℕ dt ⊢uℕ ⇨∷* IdℕSRed*Term′ ⊢mℕ ⊢uℕ ⊢snℕ du)
--             ⇨∷* (Id-ℕ-SS ⊢mℕ ⊢nℕ ⇨ id (Idⱼ (ℕⱼ ⊢Γ) ⊢mℕ ⊢nℕ))
--       in proj₁ (redSubst*Term nfId (Uᵣ′ _ ⁰ 0<1 ⊢Γ) [Idmn])
--     aux (ℕₜ .(suc m) [ ⊢tℕ , ⊢smℕ , dt ] sm≡sm (sucᵣ {m} [m]))
--         (ℕₜ .zero [ ⊢uℕ , ⊢0ℕ , du ] 0≡0 zeroᵣ) =
--       let ⊢mℕ = escapeTerm [ℕ] [m]
--           nfId = (IdℕRed*Term′ ⊢tℕ ⊢smℕ dt ⊢uℕ)
--             ⇨∷* (IdℕSRed*Term′ ⊢mℕ ⊢uℕ ⊢0ℕ du ⇨∷* (Id-ℕ-S0 ⊢mℕ ⇨ id (Emptyⱼ ⊢Γ)))
--           nfId′ = [ Idⱼ (ℕⱼ ⊢Γ) ⊢tℕ ⊢uℕ , Emptyⱼ ⊢Γ , nfId ]
--           [Empty] = Emptyᵣ (idRed:*: (Emptyⱼ ⊢Γ))
--           [Empty]′ = proj₁ (redSubst* (redSProp′ nfId) [Empty])
--       in Uₜ Empty nfId′ Emptyₙ (≅ₜ-Emptyrefl ⊢Γ) [Empty]′
--     aux (ℕₜ .(suc m) [ ⊢tℕ , ⊢smℕ , dt ] sm≡sm (sucᵣ {m} [m]))
--         (ℕₜ k [ ⊢uℕ , ⊢kℕ , du ] k≡k′ (ne (neNfₜ neK ⊢k k≡k))) =
--       let ⊢mℕ = escapeTerm [ℕ] [m]
--           nfId = (IdℕRed*Term′ ⊢tℕ ⊢smℕ dt ⊢uℕ) ⇨∷* IdℕSRed*Term′ ⊢mℕ ⊢uℕ ⊢kℕ du
--           nfId′ = [ Idⱼ (ℕⱼ ⊢Γ) ⊢tℕ ⊢uℕ , Idⱼ (ℕⱼ ⊢Γ) ⊢smℕ ⊢kℕ , nfId ]
--           m≡m = escapeTermEq [ℕ] (reflEqTerm [ℕ] [m])
--       in Uₜ (Id ℕ (suc m) k) nfId′ (ne (IdℕSₙ neK)) (~-to-≅ₜ (~-IdℕS ⊢Γ m≡m k≡k))
--         (ne′ (Id ℕ (suc m) k) (redSProp nfId′) (IdℕSₙ neK) (~-IdℕS ⊢Γ m≡m k≡k))
--     aux (ℕₜ .zero [ ⊢tℕ , ⊢0ℕ , dt ] 0≡0 zeroᵣ)
--         (ℕₜ .(suc _) [ ⊢uℕ , ⊢sucℕ , du ] suc≡suc (sucᵣ (ℕₜ n [ ⊢u′ , ⊢nℕ , du′ ] n≡n prop))) =
--       let nfId = (IdℕRed*Term′ ⊢tℕ ⊢0ℕ dt ⊢uℕ)
--             ⇨∷* (Idℕ0Red*Term′ ⊢uℕ ⊢sucℕ du ⇨∷* (Id-ℕ-0S ⊢u′ ⇨ id (Emptyⱼ ⊢Γ)))
--           nfId′ = [ Idⱼ (ℕⱼ ⊢Γ) ⊢tℕ ⊢uℕ , Emptyⱼ ⊢Γ , nfId ]
--           [Empty] = Emptyᵣ (idRed:*: (Emptyⱼ ⊢Γ))
--           [Empty]′ = proj₁ (redSubst* (redSProp′ nfId) [Empty])
--       in Uₜ Empty nfId′ Emptyₙ (≅ₜ-Emptyrefl ⊢Γ) [Empty]′
--     aux (ℕₜ .zero [ ⊢tℕ , ⊢0ℕ , dt ] 0≡0 zeroᵣ)
--         (ℕₜ .zero [ ⊢uℕ , ⊢0ℕ′ , du ] 0≡0′ zeroᵣ) =
--       let nfId = (IdℕRed*Term′ ⊢tℕ ⊢0ℕ dt ⊢uℕ)
--             ⇨∷* (Idℕ0Red*Term′ ⊢uℕ ⊢0ℕ du ⇨∷* (Id-ℕ-00 ⊢Γ ⇨ id (Unitⱼ ⊢Γ)))
--           nfId′ = [ Idⱼ (ℕⱼ ⊢Γ) ⊢tℕ ⊢uℕ , Unitⱼ ⊢Γ , nfId ]
--           [Unit] = proj₁ (redSubst* (redSProp′ nfId) (UnitType ⊢Γ))
--       in Uₜ Unit nfId′ typeUnit (Unit≡Unit ⊢Γ) [Unit]
--     aux (ℕₜ .zero [ ⊢tℕ , ⊢0ℕ , dt ] 0≡0 zeroᵣ)
--         (ℕₜ k [ ⊢uℕ , ⊢kℕ , du ] k≡k′ (ne (neNfₜ neK ⊢k k≡k))) =
--       let nfId = (IdℕRed*Term′ ⊢tℕ ⊢0ℕ dt ⊢uℕ) ⇨∷* Idℕ0Red*Term′ ⊢uℕ ⊢kℕ du
--           nfId′ = [ Idⱼ (ℕⱼ ⊢Γ) ⊢tℕ ⊢uℕ , Idⱼ (ℕⱼ ⊢Γ) (zeroⱼ ⊢Γ) ⊢kℕ , nfId ]
--       in Uₜ (Id ℕ zero k) nfId′ (ne (Idℕ0ₙ neK)) (~-to-≅ₜ (~-Idℕ0 ⊢Γ k≡k))
--         (ne′ (Id ℕ zero k) (redSProp nfId′) (Idℕ0ₙ neK) (~-Idℕ0 ⊢Γ k≡k))
--     aux {t} {u} (ℕₜ k [ ⊢t , ⊢k , d ] n≡n (ne (neNfₜ neK ⊢k′ k≡k))) [u] =
--       let nfId = [ Idⱼ (ℕⱼ ⊢Γ) ⊢t (escapeTerm [ℕ] [u]) , Idⱼ (ℕⱼ ⊢Γ) ⊢k (escapeTerm [ℕ] [u])
--                  , IdℕRed*Term′ ⊢t ⊢k d (escapeTerm [ℕ] [u]) ]
--           [u]′ = convTerm₁ (proj₁ A≡ℕ) [ℕ] (proj₂ A≡ℕ)
--             (irrelevanceTerm {l = l} [A] (proj₁ A≡ℕ) [u])
--           u≡u = escapeTermEq [ℕ] (reflEqTerm [ℕ] [u]′)
--       in Uₜ (Id ℕ k u) nfId (ne (Idℕₙ neK)) (~-to-≅ₜ (~-Idℕ ⊢Γ k≡k u≡u))
--         (ne′ (Id ℕ k u) (redSProp nfId) (Idℕₙ neK) (~-Idℕ ⊢Γ k≡k u≡u))

-- IdTerm {A} {t} {u} {Γ} {l} ⊢Γ (ne′ K D neK K≡K) [t] [u] | ⊢tA | ⊢uA =
--   let [A] = ne′ K D neK K≡K
--       [K] = neu {l = l} neK (_⊢_:⇒*:_^_.⊢B D) K≡K
--       A≡K = redSubst* (_⊢_:⇒*:_^_.D D) [K]
--       [t]′ = convTerm₁ (proj₁ A≡K) [K] (proj₂ A≡K)
--         (irrelevanceTerm  {l = l} [A] (proj₁ A≡K) [t])
--       [u]′ = convTerm₁ (proj₁ A≡K) [K] (proj₂ A≡K)
--         (irrelevanceTerm {l = l} [A] (proj₁ A≡K) [u])
--       t≡t = escapeTermEq [K] (reflEqTerm [K] [t]′)
--       u≡u = escapeTermEq [K] (reflEqTerm [K] [u]′)
--   in Uₜ (Id K t u)
--     (IdRed*Term ⊢tA ⊢uA D)
--     (ne (Idₙ neK))
--     (~-to-≅ₜ (~-Id K≡K t≡t u≡u))
--     (ne′ (Id K t u) (redSProp (IdRed*Term ⊢tA ⊢uA D)) (Idₙ neK) (~-Id K≡K t≡t u≡u))
-- IdTerm ⊢Γ (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) [t] [u] | ⊢tA | ⊢uA = {!!}
-- IdTerm {A} {t} {u} {Γ} {⁰} ⊢Γ (emb {l′ = l′} () [A]) [t] [u] | ⊢tA | ⊢uA
-- IdTerm {A} {t} {u} {Γ} {¹} ⊢Γ (emb {l′ = .⁰} 0<1 [A]) [t] [u] | ⊢tA | ⊢uA =
--   IdTerm ⊢Γ [A] [t] [u]

Idᵛ : ∀ {A t u Γ l}
       ([Γ] : ⊩ᵛ Γ)
       ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ ! , ι l ] / [Γ])
       ([t] : Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ [ ! , ι l ] / [Γ] / [A])
       ([u] : Γ ⊩ᵛ⟨ ∞ ⟩ u ∷ A ^ [ ! , ι l ] / [Γ] / [A])
     → Γ ⊩ᵛ⟨ ∞ ⟩ Id A t u ^ [ % , ι l ] / [Γ]
Idᵛ [Γ] [A] [t] [u] ⊢Δ [σ] = {!!}
  -- (IdTerm ⊢Δ (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ])) (proj₁ ([u] ⊢Δ [σ])))
  -- , {!!}

Idᵗᵛ : ∀ {A t u Γ l}
       ([Γ] : ⊩ᵛ Γ)
       ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ ! , ι l ] / [Γ])
       ([t] : Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ [ ! , ι l ] / [Γ] / [A])
       ([u] : Γ ⊩ᵛ⟨ ∞ ⟩ u ∷ A ^ [ ! , ι l ] / [Γ] / [A])
     → Γ ⊩ᵛ⟨ ∞ ⟩ Id A t u ∷ SProp l ^ [ ! , next l ] / [Γ] / maybeEmbᵛ {A = SProp _} [Γ] (Uᵛ (proj₂ (levelBounded l)) [Γ])
Idᵗᵛ [Γ] [A] [t] [u] ⊢Δ [σ] = {!!}
  -- (IdTerm ⊢Δ (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ])) (proj₁ ([u] ⊢Δ [σ])))
  -- , {!!}

-}
