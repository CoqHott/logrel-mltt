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
[IdExt]SProp {t} {t′} {u} {u′} ⊢Γ [t] [t′] [t≡t′] [u] [u′] [u≡u′] =
  ∃₌ (t′ ^ % ° ⁰ ▹▹ u′ ° ⁰) (wk1 (u′ ^ % ° ⁰ ▹▹ t′ ° ⁰))
    {!univ (Id-SProp (un-univ ⊢t) (un-univ ⊢u)) ⇨ id ?!} {!!} {!!} {!!}

[Id]U : ∀ {A B Γ}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ ! , ι ⁰ ])
         ([B] : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ ! , ι ⁰ ])
         → Γ ⊩⟨ ι ¹ ⟩ Id (U ⁰) A B ^ [ % , ι ¹ ]
[IdExt]U : ∀ {A A′ B B′ Γ}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ ! , ι ⁰ ])
         ([A′] : Γ ⊩⟨ ι ⁰ ⟩ A′ ^ [ ! , ι ⁰ ])
         ([A≡A′] : Γ ⊩⟨ ι ⁰ ⟩ A ≡ A′ ^ [ ! , ι ⁰ ] / [A])
         ([B] : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ ! , ι ⁰ ])
         ([B′] : Γ ⊩⟨ ι ⁰ ⟩ B′ ^ [ ! , ι ⁰ ])
         ([B≡B′] : Γ ⊩⟨ ι ⁰ ⟩ B ≡ B′ ^ [ ! , ι ⁰ ] / [B])
         → Γ ⊩⟨ ι ¹ ⟩ Id (U ⁰) A B ≡ Id (U ⁰) A′ B′ ^ [ % , ι ¹ ] / [Id]U ⊢Γ [A] [B]
[Id]U ⊢Γ (ne x) [B] = {!!}
[Id]U ⊢Γ (ℕᵣ x) (ℕᵣ x₁) = {!!}
[Id]U ⊢Γ (ℕᵣ x) (ne x₁) = {!!}
[Id]U ⊢Γ (ℕᵣ x) (Πᵣ x₁) = {!!}
[Id]U ⊢Γ (Πᵣ x) (ℕᵣ x₁) = {!!}
[Id]U ⊢Γ (Πᵣ x) (ne x₁) = {!!}
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

[Id]U ⊢Γ (Πᵣ′ rF .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢ΠFG , D ]] ⊢F ⊢G A≡A [F] [G] G-ext)
  (Πᵣ′ rF₁ .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢B , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ B≡B [F₁] [G₁] G₁-ext) = {!!}

[IdExt]U {A₁} {A₂} {A₃} {A₄} {Γ} ⊢Γ (Πᵣ′ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)
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

[IdExt]U {A₁} {A₂} {A₃} {A₄} {Γ} ⊢Γ (Πᵣ′ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)
  (Πᵣ′ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₂ G₂ [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]] ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext)
  (Π₌ F₂′ G₂′ D₂′ A₁≡A₂′ [F₁≡F₂′] [G₁≡G₂′])
  (Πᵣ′ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₃ G₃ [[ ⊢A₃ , ⊢ΠF₃G₃ , D₃ ]] ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext)
  (Πᵣ′ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₄ G₄ [[ ⊢A₄ , ⊢ΠF₄G₄ , D₄ ]] ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext)
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

[IdExt]U ⊢Γ [A₁] [A₂] [A₁≡A₂] [A₃] [A₄] [A₃≡A₄] = {!!}
