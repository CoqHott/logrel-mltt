{-# OPTIONS --allow-unsolved-metas #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Cast {{eqrel : EqRelSet}} where
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
-- open import Definition.LogicalRelation.Substitution.Introductions.Pi
-- open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Definition.LogicalRelation.Substitution.Introductions.Universe
open import Definition.LogicalRelation.Substitution.MaybeEmbed

open import Tools.Product
open import Tools.Empty
import Tools.Unit as TU
import Tools.PropositionalEquality as PE
import Data.Nat as Nat


escapeEqReflTerm : ∀ {l Γ A t r}
            → ([A] : Γ ⊩⟨ l ⟩ A ^ r)
            → ([t] : Γ ⊩⟨ l ⟩ t ∷ A ^ r / [A])
            → Γ ⊢ t ≅ t ∷ A ^ r
escapeEqReflTerm [A] [t] = escapeTermEq [A] (reflEqTerm [A] [t])

redSubst*EqTerm : ∀ {A B t t′ u u′ l ll Γ}
                → Γ ⊢ t ⇒* t′ ∷ A ^ ll
                → Γ ⊢ u ⇒* u′ ∷ B ^ ll
                → ([A] : Γ ⊩⟨ l ⟩ A ^ [ ! , ll ])
                → ([B] : Γ ⊩⟨ l ⟩ B ^ [ ! , ll ])
                → Γ ⊩⟨ l ⟩ A ≡ B ^ [ ! , ll ] / [A]
                → Γ ⊩⟨ l ⟩ t′ ∷ A ^ [ ! , ll ] / [A]
                → Γ ⊩⟨ l ⟩ u′ ∷ B ^ [ ! , ll ] / [B]
                → Γ ⊩⟨ l ⟩ t′ ≡ u′ ∷ A ^ [ ! , ll ] / [A]
                → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ [ ! , ll ] / [A]
redSubst*EqTerm D D′ [A] [B] [A≡B] [t′] [u′] [t′≡u′] =
  let
    [t≡t′] = proj₂ (redSubst*Term D [A] [t′])
    [u≡u′:B] = proj₂ (redSubst*Term D′ [B] [u′])
    [u≡u′] = convEqTerm₂ [A] [B] [A≡B] [u≡u′:B]
  in transEqTerm [A] [t≡t′] (transEqTerm [A] [t′≡u′] (symEqTerm [A] [u≡u′]))

[cast] : ∀ {A B Γ}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ ! , ι ⁰ ])
         ([B] : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ ! , ι ⁰ ])
       → (∀ {t e} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ ! , ι ⁰ ] / [A]) → (⊢e : Γ ⊢ e ∷ Id (U ⁰) A B ^ [ % , ι ¹ ]) → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ∷ B ^ [ ! , ι ⁰ ] / [B])
       × (∀ {t e} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ B ^ [ ! , ι ⁰ ] / [B]) → (⊢e : Γ ⊢ e ∷ Id (U ⁰) B A ^ [ % , ι ¹ ]) → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ B A e t ∷ A ^ [ ! , ι ⁰ ] / [A])
[castext] : ∀ {A A′ B B′ Γ}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ ! , ι ⁰ ])
         ([A′] : Γ ⊩⟨ ι ⁰ ⟩ A′ ^ [ ! , ι ⁰ ])
         ([A≡A′] : Γ ⊩⟨ ι ⁰ ⟩ A ≡ A′ ^ [ ! , ι ⁰ ] / [A])
         ([B] : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ ! , ι ⁰ ])
         ([B′] : Γ ⊩⟨ ι ⁰ ⟩ B′ ^ [ ! , ι ⁰ ])
         ([B≡B′] : Γ ⊩⟨ ι ⁰ ⟩ B ≡ B′ ^ [ ! , ι ⁰ ] / [B])
       → (∀ {t t′ e e′} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ ! , ι ⁰ ] / [A])
                        → ([t′] : Γ ⊩⟨ ι ⁰ ⟩ t′ ∷ A′ ^ [ ! , ι ⁰ ] / [A′])
                        → ([t≡t′] : Γ ⊩⟨ ι ⁰ ⟩ t ≡ t′ ∷ A ^ [ ! , ι ⁰ ] / [A])
                        → (⊢e : Γ ⊢ e ∷ Id (U ⁰) A B ^ [ % , ι ¹ ])
                        → (⊢e′ : Γ ⊢ e′ ∷ Id (U ⁰) A′ B′ ^ [ % , ι ¹ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ≡ cast ⁰ A′ B′ e′ t′ ∷ B ^ [ ! , ι ⁰ ] / [B])
       × (∀ {t t′ e e′} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ B ^ [ ! , ι ⁰ ] / [B])
                        → ([t′] : Γ ⊩⟨ ι ⁰ ⟩ t′ ∷ B′ ^ [ ! , ι ⁰ ] / [B′])
                        → ([t≡t′] : Γ ⊩⟨ ι ⁰ ⟩ t ≡ t′ ∷ B ^ [ ! , ι ⁰ ] / [B])
                        → (⊢e : Γ ⊢ e ∷ Id (U ⁰) B A ^ [ % , ι ¹ ])
                        → (⊢e′ : Γ ⊢ e′ ∷ Id (U ⁰) B′ A′ ^ [ % , ι ¹ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ B A e t ≡ cast ⁰ B′ A′ e′ t′ ∷ A ^ [ ! , ι ⁰ ] / [A])
[cast] ⊢Γ (ℕᵣ x) (ℕᵣ x₁) = {!!}
[cast] ⊢Γ (ℕᵣ x) (ne x₁) = {!!}
[cast] ⊢Γ (ℕᵣ x) (Πᵣ x₁) = {!!}
[cast] ⊢Γ (ne x) (ℕᵣ x₁) = {!!}
[cast] ⊢Γ (ne x) (ne x₁) = {!!}
[cast] ⊢Γ (ne x) (Πᵣ x₁) = {!!}
[cast] ⊢Γ (Πᵣ x) (ℕᵣ x₁) = {!!}
[cast] ⊢Γ (Πᵣ x) (ne x₁) = {!!}
[cast] {A} {B} {Γ} ⊢Γ (Πᵣ′ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢ΠFG , D ]] ⊢F ⊢G A≡A [F] [G] G-ext)
  (Πᵣ′ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢B , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext) =
  ( [castΠΠ] ⊢A ⊢ΠFG D ⊢F ⊢G A≡A [F] [G] G-ext ⊢B ⊢ΠF₁G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext
             (λ [ρ] ⊢Δ → proj₂ ([cast] ⊢Δ ([F] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ)))
             (λ [ρ] ⊢Δ [x] [y] → proj₁ ([cast] ⊢Δ ([G] [ρ] ⊢Δ [x]) ([G₁] [ρ] ⊢Δ [y])))
             [b₁]
  , [castΠΠ] ⊢B ⊢ΠF₁G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext ⊢A ⊢ΠFG D ⊢F ⊢G A≡A [F] [G] G-ext
             (λ [ρ] ⊢Δ → proj₁ ([cast] ⊢Δ ([F] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ)))
             (λ [ρ] ⊢Δ [y] [x] → proj₁ ([cast] ⊢Δ ([G₁] [ρ] ⊢Δ [y]) ([G] [ρ] ⊢Δ [x])))
             [b₂])
  where
    -- Somehow Agda will hang if [b₁] and [b₂] are factored in [castΠΠ]
    -- So I have to define them outside
    -- ????
    b₁ = λ ρ e x → cast ⁰ (wk ρ F₁) (wk ρ F) (Idsym (U ⁰) (wk ρ F) (wk ρ F₁) e) x
    [b₁] : ∀ {ρ Δ e x} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
        → (Δ ⊢ e ∷ Id (U ⁰) (wk ρ F) (wk ρ F₁) ^ [ % , ι ¹ ])
        → (Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F₁ ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
        → Δ ⊩⟨ ι ⁰ ⟩ b₁ ρ e x ∷ wk ρ F ^ [ ! , ι ⁰ ] / [F] [ρ] ⊢Δ
    [b₁] [ρ] ⊢Δ ⊢e [x] =
      let
        ⊢e′ = Idsymⱼ (univ 0<1 ⊢Δ) (un-univ (escape ([F] [ρ] ⊢Δ)))
          (un-univ (escape ([F₁] [ρ] ⊢Δ))) ⊢e
      in proj₂ ([cast] ⊢Δ ([F] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ)) [x] ⊢e′

    b₂ = λ ρ e x → cast ⁰ (wk ρ F) (wk ρ F₁) (Idsym (U ⁰) (wk ρ F₁) (wk ρ F) e) x
    [b₂] : ∀ {ρ Δ e x} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
        → (Δ ⊢ e ∷ Id (U ⁰) (wk ρ F₁) (wk ρ F) ^ [ % , ι ¹ ])
        → (Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F ^ [ ! , ι ⁰ ] / [F] [ρ] ⊢Δ)
        → Δ ⊩⟨ ι ⁰ ⟩ b₂ ρ e x ∷ wk ρ F₁ ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ
    [b₂] [ρ] ⊢Δ ⊢e [x] =
      let
        ⊢e′ = Idsymⱼ (univ 0<1 ⊢Δ) (un-univ (escape ([F₁] [ρ] ⊢Δ)))
          (un-univ (escape ([F] [ρ] ⊢Δ))) ⊢e
      in proj₁ ([cast] ⊢Δ ([F] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ)) [x] ⊢e′

    [castΠΠ] : ∀ {t e A B F G F₁ G₁}
      (⊢A : Γ ⊢ A ^ [ ! , ι ⁰ ])
      (⊢ΠFG : Γ ⊢ Π F ^ ! ° ⁰ ▹ G ° ⁰ ^ [ ! , ι ⁰ ])
      (D : Γ ⊢ A ⇒* Π F ^ ! ° ⁰ ▹ G ° ⁰ ^ [ ! , ι ⁰ ])
      (⊢F : Γ ⊢ F ^ [ ! , ι ⁰ ])
      (⊢G : (Γ ∙ F ^ [ ! , ι ⁰ ]) ⊢ G ^ [ ! , ι ⁰ ])
      (A≡A : Γ ⊢ (Π F ^ ! ° ⁰ ▹ G ° ⁰) ≅ (Π F ^ ! ° ⁰ ▹ G ° ⁰) ^ [ ! , ι ⁰ ])
      ([F] : ∀ {ρ} {Δ} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Δ ⊩⟨ ι ⁰ ⟩ wk ρ F ^ [ ! , ι ⁰ ])
      ([G] : ∀ {ρ} {Δ} {a} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
         ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷  wk ρ F ^ [ ! , ι ⁰ ] / ([F] [ρ] ⊢Δ))
         → (Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G [ a ] ^ [ ! , ι ⁰ ]))
      (G-ext : ∀ {ρ} {Δ} {a} {b} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
         ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷  wk ρ F ^ [ ! , ι ⁰ ] / ([F] [ρ] ⊢Δ))
         ([b] : Δ ⊩⟨ ι ⁰ ⟩ b ∷  wk ρ F ^ [ ! , ι ⁰ ] / ([F] [ρ] ⊢Δ))
         ([a≡b] : Δ ⊩⟨ ι ⁰ ⟩ a ≡ b ∷ wk ρ F ^ [ ! , ι ⁰ ] / ([F] [ρ] ⊢Δ))
         → (Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G [ a ] ≡ wk (lift ρ) G [ b ] ^ [ ! , ι ⁰ ] / ([G] [ρ] ⊢Δ [a])))
      (⊢B     : Γ ⊢ B ^ [ ! , ι ⁰ ])
      (⊢ΠF₁G₁ : Γ ⊢ Π F₁ ^ ! ° ⁰ ▹ G₁ ° ⁰ ^ [ ! , ι ⁰ ])
      (D₁     : Γ ⊢ B ⇒* Π F₁ ^ ! ° ⁰ ▹ G₁ ° ⁰ ^ [ ! , ι ⁰ ])
      (⊢F₁    : Γ ⊢ F₁ ^ [ ! , ι ⁰ ])
      (⊢G₁    : (Γ ∙ F₁ ^ [ ! , ι ⁰ ]) ⊢ G₁ ^ [ ! , ι ⁰ ])
      (A₁≡A₁  : Γ ⊢ (Π F₁ ^ ! ° ⁰ ▹ G₁ ° ⁰) ≅ (Π F₁ ^ ! ° ⁰ ▹ G₁ ° ⁰) ^ [ ! , ι ⁰ ])
      ([F₁] : ∀ {ρ} {Δ} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Δ ⊩⟨ ι ⁰ ⟩ wk ρ F₁ ^ [ ! , ι ⁰ ])
      ([G₁] : ∀ {ρ} {Δ} {a} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
         ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷  wk ρ F₁ ^ [ ! , ι ⁰ ] / ([F₁] [ρ] ⊢Δ))
         → (Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₁ [ a ] ^ [ ! , ι ⁰ ]))
      (G₁-ext : ∀ {ρ} {Δ} {a} {b} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
         ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷  wk ρ F₁ ^ [ ! , ι ⁰ ] / ([F₁] [ρ] ⊢Δ))
         ([b] : Δ ⊩⟨ ι ⁰ ⟩ b ∷  wk ρ F₁ ^ [ ! , ι ⁰ ] / ([F₁] [ρ] ⊢Δ))
         ([a≡b] : Δ ⊩⟨ ι ⁰ ⟩ a ≡ b ∷ wk ρ F₁ ^ [ ! , ι ⁰ ] / ([F₁] [ρ] ⊢Δ))
         → (Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₁ [ a ] ≡ wk (lift ρ) G₁ [ b ] ^ [ ! , ι ⁰ ] / ([G₁] [ρ] ⊢Δ [a])))
      (recursor₁ : ∀ {ρ Δ x e}
         ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
         ([x] : Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F₁ ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ) (⊢e : Δ ⊢ e ∷ Id (U ⁰) (wk ρ F₁) (wk ρ F) ^ [ % , ι ¹ ])
         → Δ ⊩⟨ ι ⁰ ⟩ cast ⁰ (wk ρ F₁) (wk ρ F) e x ∷ wk ρ F ^ [ ! , ι ⁰ ] / [F] [ρ] ⊢Δ)
      (recursor₂ : ∀ {ρ Δ x y t e}
         ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
         ([x] : Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F ^ [ ! , ι ⁰ ] / [F] [ρ] ⊢Δ)
         ([y] : Δ ⊩⟨ ι ⁰ ⟩ y ∷ wk ρ F₁ ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
         ([t] : Δ ⊩⟨ ι ⁰ ⟩ t ∷ wk (lift ρ) G [ x ] ^ [ ! , ι ⁰ ] / [G] [ρ] ⊢Δ [x])
         (⊢e : Δ ⊢ e ∷ Id (U ⁰) (wk (lift ρ) G [ x ]) (wk (lift ρ) G₁ [ y ]) ^ [ % , ι ¹ ])
         → Δ ⊩⟨ ι ⁰ ⟩ cast ⁰ (wk (lift ρ) G [ x ]) (wk (lift ρ) G₁ [ y ]) e t ∷ wk (lift ρ) G₁ [ y ] ^ [ ! , ι ⁰ ] / [G₁] [ρ] ⊢Δ [y])
      ([b] : ∀ {ρ Δ e x}
         ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
         (⊢e : Δ ⊢ e ∷ Id (U ⁰) (wk ρ F) (wk ρ F₁) ^ [ % , ι ¹ ])
         ([x] : Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F₁ ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
         → Δ ⊩⟨ ι ⁰ ⟩ cast ⁰ (wk ρ F₁) (wk ρ F) (Idsym (U ⁰) (wk ρ F) (wk ρ F₁) e) x ∷ wk ρ F ^ [ ! , ι ⁰ ] / [F] [ρ] ⊢Δ)
      ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ ! , ι ⁰ ] / (Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢ΠFG , D ]] ⊢F ⊢G A≡A [F] [G] G-ext))
      (⊢e : Γ ⊢ e ∷ Id (U ⁰) A B ^ [ % , ι ¹ ])
      → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ∷ B ^ [ ! , ι ⁰ ] / (Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢B , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)
    [castΠΠ] {t} {e} {A} {B} {F} {G} {F₁} {G₁}
      ⊢A ⊢ΠFG D ⊢F ⊢G A≡A [F] [G] G-ext ⊢B ⊢ΠF₁G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext recursor₁ recursor₂ [b]
      (f , [[ ⊢t , ⊢f , Df ]] , funf , f≡f , [fext] , [f]) ⊢e = {!!}
      -- let
      --   b = λ ρ e x → cast ⁰ (wk ρ F₁) (wk ρ F) (Idsym (U ⁰) (wk ρ F) (wk ρ F₁) e) x

      --   [bext] : ∀ {ρ Δ e e′ x y} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
      --       → (Δ ⊢ e ∷ Id (U ⁰) (wk ρ F) (wk ρ F₁) ^ [ % , ι ¹ ])
      --       → (Δ ⊢ e′ ∷ Id (U ⁰) (wk ρ F) (wk ρ F₁) ^ [ % , ι ¹ ])
      --       → (Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F₁ ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
      --       → (Δ ⊩⟨ ι ⁰ ⟩ y ∷ wk ρ F₁ ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
      --       → (Δ ⊩⟨ ι ⁰ ⟩ x ≡ y ∷ wk ρ F₁ ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
      --       → Δ ⊩⟨ ι ⁰ ⟩ b ρ e x ≡ b ρ e′ y ∷ wk ρ F ^ [ ! , ι ⁰ ] / [F] [ρ] ⊢Δ
      --   [bext] [ρ] ⊢Δ ⊢e ⊢e′ [x] [y] [x≡y] =
      --     let
      --       ⊢syme = Idsymⱼ (univ 0<1 ⊢Δ) (un-univ (escape ([F] [ρ] ⊢Δ)))
      --         (un-univ (escape ([F₁] [ρ] ⊢Δ))) ⊢e
      --       ⊢syme′ = Idsymⱼ (univ 0<1 ⊢Δ) (un-univ (escape ([F] [ρ] ⊢Δ)))
      --         (un-univ (escape ([F₁] [ρ] ⊢Δ))) ⊢e′
      --     in proj₁ ([castext] ⊢Δ ([F₁] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ) (reflEq ([F₁] [ρ] ⊢Δ))
      --       ([F] [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) (reflEq ([F] [ρ] ⊢Δ)))
      --       [x] [y] [x≡y] ⊢syme ⊢syme′

      --   ⊢IdFF₁ = univ (Idⱼ (univ 0<1 ⊢Γ) (un-univ ⊢F) (un-univ ⊢F₁))
      --   Δ₀ = Γ ∙ Id (U ⁰) F F₁ ^ [ % , ι ¹ ] ∙ wk1 F₁ ^ [ ! , ι ⁰ ]
      --   ρ₀ = (step (step id))

      --   ⊢IdG₁G : Γ ∙ Id (U ⁰) F F₁ ^ [ % , ι ¹ ] ⊢ Π (wk1 F₁) ^ ! ° ⁰ ▹ Id (U ⁰) ((wk1d G) [ b ρ₀ (var 1) (var 0) ]↑) (wk1d G₁) ° ¹ ^ [ % , ι ¹ ]
      --   ⊢IdG₁G =
      --     let
      --       ⊢Δ₀ : ⊢ Δ₀
      --       ⊢Δ₀ = ⊢Γ ∙ ⊢IdFF₁ ∙ univ (Twk.wkTerm (Twk.step Twk.id) (⊢Γ ∙ ⊢IdFF₁) (un-univ ⊢F₁))
      --       [ρ₀] : ρ₀ Twk.∷ Δ₀ ⊆ Γ
      --       [ρ₀] = Twk.step (Twk.step Twk.id)
      --       [0] : Δ₀ ⊩⟨ ι ⁰ ⟩ var 0 ∷ wk ρ₀ F₁ ^ [ ! , ι ⁰ ] / [F₁] [ρ₀] ⊢Δ₀
      --       [0] = let x = (var ⊢Δ₀ (PE.subst (λ X → 0 ∷ X ^ [ ! , ι ⁰ ] ∈ Δ₀) (wk1-wk (step id) F₁) here)) in
      --         neuTerm ([F₁] [ρ₀] ⊢Δ₀) (var 0) x (~-var x)
      --       ⊢1 : Δ₀ ⊢ (var 1) ∷ Id (U ⁰) (wk ρ₀ F) (wk ρ₀ F₁) ^ [ % , ι ¹ ]
      --       ⊢1 = var ⊢Δ₀ (PE.subst₂ (λ X Y → 1 ∷ Id (U ⁰) X Y ^ [ % , ι ¹ ] ∈ Δ₀)
      --         (wk1-wk (step id) F) (wk1-wk (step id) F₁) (there here))
      --       ⊢G₀ : Δ₀ ⊢ wk (lift ρ₀) G [ b ρ₀ (var 1) (var 0) ] ^ [ ! , ι ⁰ ]
      --       ⊢G₀ = escape ([G] [ρ₀] ⊢Δ₀ ([b] [ρ₀] ⊢Δ₀ ⊢1 [0]))
      --       ⊢G₀′ = PE.subst (λ X → Δ₀ ⊢ X ^ [ ! , ι ⁰ ]) (PE.sym (cast-subst-lemma2 G (b ρ₀ (var 1) (var 0)))) ⊢G₀
      --       x₀ : Δ₀ ⊢ Id (U ⁰) ((wk1d G) [ b ρ₀ (var 1) (var 0) ]↑) (wk1d G₁) ∷ SProp ¹ ^ [ ! , ∞ ]
      --       x₀ = Idⱼ (univ 0<1 ⊢Δ₀) (un-univ ⊢G₀′)
      --           (un-univ (Twk.wk (Twk.lift (Twk.step Twk.id)) ⊢Δ₀ ⊢G₁))
      --       x₁ = Πⱼ <is≤ 0<1 ▹ ≡is≤ PE.refl ▹ Twk.wkTerm (Twk.step Twk.id) (⊢Γ ∙ ⊢IdFF₁) (un-univ ⊢F₁) ▹ x₀
      --     in univ x₁

      --   ⊢e′ : Γ ⊢ e ∷ ∃ (Id (U ⁰) F F₁) ▹ (Π (wk1 F₁) ^ ! ° ⁰ ▹ Id (U ⁰) ((wk1d G) [ b ρ₀ (var 1) (var 0) ]↑) (wk1d G₁) ° ¹) ^ [ % , ι ¹ ]
      --   ⊢e′ =
      --     let
      --       b₀ = cast ⁰ (wk1 (wk1 F₁)) (wk1 (wk1 F)) (Idsym (U ⁰) (wk1 (wk1 F)) (wk1 (wk1 F₁)) (var 1)) (var 0)
      --       b≡b₀ : b ρ₀ (var 1) (var 0) PE.≡ b₀
      --       b≡b₀ = PE.cong₂ (λ X Y → cast ⁰ Y X (Idsym (U ⁰) X Y (var 1)) (var 0))
      --         (PE.sym (wk1-wk (step id) F)) (PE.sym (wk1-wk (step id) F₁))
      --       x₀ = conv ⊢e (univ (Id-cong (refl (univ 0<1 ⊢Γ)) (un-univ≡ (subset* D)) (un-univ≡ (subset* D₁))))
      --       x₁ = conv x₀ (univ (Id-U-ΠΠ (un-univ ⊢F) (un-univ ⊢G) (un-univ ⊢F₁) (un-univ ⊢G₁)))
      --       x₂ = PE.subst (λ X → Γ ⊢ e ∷ ∃ (Id (U ⁰) F F₁) ▹ (Π (wk1 F₁) ^ ! ° ⁰ ▹ Id (U ⁰) ((wk1d G) [ X ]↑) (wk1d G₁) ° ¹) ^ [ % , ι ¹ ]) (PE.sym b≡b₀) x₁
      --     in x₂

      --   ⊢fste : Γ ⊢ fst e ∷ Id (U ⁰) F F₁ ^ [ % , ι ¹ ]
      --   ⊢fste = fstⱼ (un-univ ⊢IdFF₁) (un-univ ⊢IdG₁G) ⊢e′

      --   ⊢snde : Γ ⊢ snd e ∷ Π F₁ ^ ! ° ⁰ ▹ Id (U ⁰) (wk1d G [ b (step id) (fst (wk1 e)) (var 0) ]) G₁ ° ¹ ^ [ % , ι ¹ ]
      --   ⊢snde =
      --     let
      --       x₀ = sndⱼ (un-univ ⊢IdFF₁) (un-univ ⊢IdG₁G) ⊢e′
      --       x₁ = PE.subst₂ (λ X Y → Γ ⊢ snd e ∷ (Π X ^ ! ° ⁰ ▹ subst _ (Id (U ⁰) Y (wk1d G₁)) ° ¹) ^ [ % , ι ¹ ])
      --           (wk1-singleSubst F₁ (fst e)) (cast-subst-lemma2 G (b ρ₀ (var 1) (var 0))) x₀
      --       x₂ = PE.subst₂ (λ X Y → Γ ⊢ snd e ∷ Π F₁ ^ ! ° ⁰ ▹ Id (U ⁰) X Y ° ¹ ^ [ % , ι ¹ ])
      --         (singleSubstLift (wk (lift ρ₀) G) (b ρ₀ (var 1) (var 0))) (wk1d-singleSubst G₁ (fst e)) x₁
      --       σ = liftSubst (sgSubst (fst e))
      --       b≡b : subst σ (b ρ₀ (var 1) (var 0)) PE.≡ b (step id) (fst (wk1 e)) (var 0)
      --       b≡b = PE.trans (PE.cong (λ X → cast ⁰ (subst σ (wk ρ₀ F₁)) (subst σ (wk ρ₀ F)) X (var 0)) (subst-Idsym σ (U ⁰) (wk ρ₀ F) (wk ρ₀ F₁) (var 1)))
      --         (PE.cong₂ (λ X Y → cast ⁰ Y X (Idsym (U ⁰) X Y (fst (wk1 e))) (var 0)) (cast-subst-lemma5 F (fst e)) (cast-subst-lemma5 F₁ (fst e)))
      --       x₃ = PE.subst₂ (λ X Y → Γ ⊢ snd e ∷ Π F₁ ^ ! ° ⁰ ▹ Id (U ⁰) (X [ Y ]) G₁ ° ¹ ^ [ % , ι ¹ ])
      --         (cast-subst-lemma3 G (fst e)) b≡b x₂
      --    in x₃

      --   ⊢snde′ : ∀ {ρ Δ x} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
      --       → (⊢x : Δ ⊢ x ∷ wk ρ F₁ ^ [ ! , ι ⁰ ])
      --       → Δ ⊢ snd (wk ρ e) ∘ x ∷ Id (U ⁰) (wk (lift ρ) G [ b ρ (fst (wk ρ e)) x ])
      --         (wk (lift ρ) G₁ [ x ]) ^ [ % , ι ¹ ]
      --   ⊢snde′ {ρ} {Δ} {x} [ρ] ⊢Δ ⊢x =
      --     let
      --       -- I should probably make some generic lemma about pushing weakening and subst in b
      --       y₀ = PE.trans (PE.cong (λ X → X [ x ]) (wk-Idsym (lift ρ) (U ⁰) (wk1 F) (wk1 F₁) (fst (wk1 e))))
      --         (PE.trans (subst-Idsym (sgSubst x) (U ⁰) (wk (lift ρ) (wk1 F)) (wk (lift ρ) (wk1 F₁)) (fst (wk (lift ρ) (wk1 e))))
      --         (PE.cong₃ (λ X Y Z → Idsym (U ⁰) X Y (fst Z)) (irrelevant-subst′ ρ F x) (irrelevant-subst′ ρ F₁ x) (irrelevant-subst′ ρ e x)))
      --       y₁ : wk (lift ρ) (b (step id) (fst (wk1 e)) (var 0)) [ x ] PE.≡ b ρ (fst (wk ρ e)) x
      --       y₁ = PE.cong₃ (λ X Y Z → cast ⁰ X Y Z x) (irrelevant-subst′ ρ F₁ x) (irrelevant-subst′ ρ F x) y₀
      --       x₀ = Δ ⊢ (wk ρ (snd e)) ∘ x ∷ Id (U ⁰) (wk (lift ρ) (wk1d G [ b (step id) (fst (wk1 e)) (var 0) ]) [ x ]) (wk (lift ρ) G₁ [ x ]) ^ [ % , ι ¹ ]
      --       x₀ = Twk.wkTerm [ρ] ⊢Δ ⊢snde ∘ⱼ ⊢x
      --       x₁ = PE.cong₂ (λ X Y → X [ Y ]) (cast-subst-lemma4 ρ x G) y₁
      --       x₂ = PE.trans (singleSubstLift (wk (lift (lift ρ)) (wk1d G))
      --         (wk (lift ρ) (b (step id) (fst (wk1 e)) (var 0)))) x₁
      --       x₃ = PE.trans (PE.cong (λ X → X [ x ]) (wk-β {a = b (step id) (fst (wk1 e)) (var 0)} (wk1d G))) x₂
      --       x₄ = PE.subst (λ X → Δ ⊢ snd (wk ρ e) ∘ x ∷ Id (U ⁰) X (wk (lift ρ) G₁ [ x ]) ^ [ % , ι ¹ ]) x₃ x₀
      --     in x₄

      --   g = λ ρ x → cast ⁰ (wk (lift ρ) G [ b ρ (fst (wk ρ e)) x ]) (wk (lift ρ) G₁ [ x ])
      --     ((snd (wk ρ e)) ∘ x) ((wk ρ t) ∘ (b ρ (fst (wk ρ e)) x))

      --   [g] : ∀ {ρ Δ x} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
      --       → ([x] : Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F₁ ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
      --       → Δ ⊩⟨ ι ⁰ ⟩ g ρ x ∷ wk (lift ρ) G₁ [ x ] ^ [ ! , ι ⁰ ] / [G₁] [ρ] ⊢Δ [x]
      --   [g] {ρ} {Δ} {x} [ρ] ⊢Δ [x] =
      --     let
      --       [b] = [b] [ρ] ⊢Δ (Twk.wkTerm [ρ] ⊢Δ ⊢fste) [x]
      --       [t] = proj₁ (redSubst*Term (appRed* (escapeTerm ([F] [ρ] ⊢Δ) [b]) (Twk.wkRed*Term [ρ] ⊢Δ Df))
      --         ([G] [ρ] ⊢Δ [b]) ([f] [ρ] ⊢Δ [b]))
      --       x = recursor₂ [ρ] ⊢Δ [b] [x] [t] (⊢snde′ [ρ] ⊢Δ (escapeTerm ([F₁] [ρ] ⊢Δ) [x]))
      --     in x

      --   [gext] : ∀ {ρ Δ x y} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
      --       → ([x] : Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F₁ ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
      --       → ([y] : Δ ⊩⟨ ι ⁰ ⟩ y ∷ wk ρ F₁ ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
      --       → ([x≡y] : Δ ⊩⟨ ι ⁰ ⟩ x ≡ y ∷ wk ρ F₁ ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
      --       → Δ ⊩⟨ ι ⁰ ⟩ g ρ x ≡ g ρ y ∷ wk (lift ρ) G₁ [ x ] ^ [ ! , ι ⁰ ] / [G₁] [ρ] ⊢Δ [x]
      --   [gext] {ρ} {Δ} {x} {y} [ρ] ⊢Δ [x] [y] [x≡y] = let
      --     [b₁] = [b] [ρ] ⊢Δ (Twk.wkTerm [ρ] ⊢Δ ⊢fste) [x]
      --     [b₂] = [b] [ρ] ⊢Δ (Twk.wkTerm [ρ] ⊢Δ ⊢fste) [y]
      --     [b₁≡b₂] = [bext] [ρ] ⊢Δ (Twk.wkTerm [ρ] ⊢Δ ⊢fste) (Twk.wkTerm [ρ] ⊢Δ ⊢fste) [x] [y] [x≡y]
      --     D₁ = (appRed* (escapeTerm ([F] [ρ] ⊢Δ) [b₁]) (Twk.wkRed*Term [ρ] ⊢Δ Df))
      --     D₂ = (appRed* (escapeTerm ([F] [ρ] ⊢Δ) [b₂]) (Twk.wkRed*Term [ρ] ⊢Δ Df))
      --     [t₁] = proj₁ (redSubst*Term D₁ ([G] [ρ] ⊢Δ [b₁]) ([f] [ρ] ⊢Δ [b₁]))
      --     [t₂] = proj₁ (redSubst*Term D₂ ([G] [ρ] ⊢Δ [b₂]) ([f] [ρ] ⊢Δ [b₂]))
      --     [t₁≡t₂] = redSubst*EqTerm D₁ D₂ ([G] [ρ] ⊢Δ [b₁]) ([G] [ρ] ⊢Δ [b₂]) (G-ext [ρ] ⊢Δ [b₁] [b₂] [b₁≡b₂])
      --       ([f] [ρ] ⊢Δ [b₁]) ([f] [ρ] ⊢Δ [b₂]) ([fext] [ρ] ⊢Δ [b₁] [b₂] [b₁≡b₂])
      --     in proj₁ ([castext] ⊢Δ ([G] [ρ] ⊢Δ [b₁]) ([G] [ρ] ⊢Δ [b₂]) (G-ext [ρ] ⊢Δ [b₁] [b₂] [b₁≡b₂])
      --       ([G₁] [ρ] ⊢Δ [x]) ([G₁] [ρ] ⊢Δ [y]) (G₁-ext [ρ] ⊢Δ [x] [y] [x≡y]))
      --       [t₁] [t₂] [t₁≡t₂]
      --       (⊢snde′ [ρ] ⊢Δ (escapeTerm ([F₁] [ρ] ⊢Δ) [x])) (⊢snde′ [ρ] ⊢Δ (escapeTerm ([F₁] [ρ] ⊢Δ) [y]))

      --   Δ₁ = Γ ∙ F₁ ^ [ ! , ι ⁰ ]
      --   ⊢Δ₁ : ⊢ Δ₁
      --   ⊢Δ₁ = ⊢Γ ∙ ⊢F₁
      --   ρ₁ = (step id)
      --   [ρ₁] : ρ₁ Twk.∷ Δ₁ ⊆ Γ
      --   [ρ₁] = Twk.step Twk.id
      --   [0] : Δ₁ ⊩⟨ ι ⁰ ⟩ var 0 ∷ wk ρ₁ F₁ ^ [ ! , ι ⁰ ] / [F₁] [ρ₁] ⊢Δ₁
      --   [0] = neuTerm ([F₁] [ρ₁] ⊢Δ₁) (var 0) (var ⊢Δ₁ here) (~-var (var ⊢Δ₁ here))

      --   ⊢g0 = PE.subst (λ X → Δ₁ ⊢ g (step id) (var 0) ∷ X ^ [ ! , ι ⁰ ]) (wkSingleSubstId G₁) (escapeTerm ([G₁] [ρ₁] ⊢Δ₁ [0]) ([g] [ρ₁] ⊢Δ₁ [0]))
      --   ⊢λg : Γ ⊢ lam F₁ ▹ g (step id) (var 0) ∷ Π F₁ ^ ! ° ⁰ ▹ G₁ ° ⁰ ^ [ ! , ι ⁰ ]
      --   ⊢λg = lamⱼ (≡is≤ PE.refl) (≡is≤ PE.refl) ⊢F₁ ⊢g0

      --   D : Γ ⊢ cast ⁰ A B e t :⇒*: (lam F₁ ▹ g (step id) (var 0)) ∷ Π F₁ ^ ! ° ⁰ ▹ G₁ ° ⁰ ^ ι ⁰
      --   D = let
      --       g0 = lam F₁ ▹ cast ⁰ (G [ b (step id) (fst (wk1 e)) (var 0) ]↑) G₁
      --         ((snd (wk1 e)) ∘ (var 0)) ((wk1 t) ∘ (b (step id) (fst (wk1 e)) (var 0)))
      --       g≡g : g0 PE.≡ lam F₁ ▹ g (step id) (var 0)
      --       g≡g = PE.cong₂ (λ X Y → lam F₁ ▹ cast ⁰ X Y ((snd (wk1 e)) ∘ (var 0)) ((wk1 t) ∘ (b (step id) (fst (wk1 e)) (var 0))))
      --         (wk1d[]-[]↑ G (b (step id) (fst (wk1 e)) (var 0))) (PE.sym (wkSingleSubstId G₁))
      --       ⊢e′ = conv ⊢e (univ (Id-cong (refl (univ 0<1 ⊢Γ))
      --         (un-univ≡ (subset* D)) (refl (un-univ ⊢B))))
      --       ⊢e″ = conv ⊢e (univ (Id-cong (refl (univ 0<1 ⊢Γ))
      --         (un-univ≡ (subset* D)) (un-univ≡ (subset* D₁))))
      --     in [[ conv (castⱼ (un-univ ⊢A) (un-univ ⊢B) ⊢e (conv ⊢t (sym (subset* D)))) (subset* D₁)
      --     , ⊢λg
      --     , (conv* (CastRed*Term′ ⊢B ⊢e (conv ⊢t (sym (subset* D))) D
      --         ⇨∷* castΠRed* ⊢F ⊢G ⊢e′ ⊢t D₁) (subset* D₁))
      --       ⇨∷* (PE.subst (λ X → Γ ⊢ cast ⁰ (Π F ^ ! ° ⁰ ▹ G ° ⁰) (Π F₁ ^ ! ° ⁰ ▹ G₁ ° ⁰) e t ⇒ X ∷ Π F₁ ^ ! ° ⁰ ▹ G₁ ° ⁰ ^ ι ⁰) g≡g
      --         (cast-Π (un-univ ⊢F) (un-univ ⊢G) (un-univ ⊢F₁) (un-univ ⊢G₁) ⊢e″ ⊢t) ⇨ (id ⊢λg)) ]]

      --   g≡g : Γ ⊢ (lam F₁ ▹ g (step id) (var 0)) ≅ (lam F₁ ▹ g (step id) (var 0)) ∷ Π F₁ ^ ! ° ⁰ ▹ G₁ ° ⁰ ^ [ ! , ι ⁰ ]
      --   g≡g = let
      --     ⊢F₁′ = Twk.wk (Twk.step Twk.id) ⊢Δ₁ ⊢F₁
      --     ⊢g0 = escapeTerm ([G₁] [ρ₁] ⊢Δ₁ [0]) ([g] [ρ₁] ⊢Δ₁ [0])
      --     ⊢g0′ = (PE.subst (λ X → Δ₁ ⊢ g (step id) (var 0) ∷ X ^ [ ! , ι ⁰ ]) (wkSingleSubstId G₁) ⊢g0)
      --     ⊢g0″ = Twk.wkTerm (Twk.lift (Twk.step Twk.id)) (⊢Δ₁ ∙ ⊢F₁′) ⊢g0′
      --     D : Δ₁ ⊢ (lam (wk1 F₁) ▹ wk1d (g (step id) (var 0))) ∘ (var 0) ⇒* g (step id) (var 0) ∷ wk1d G₁ [ var 0 ] ^ ι ⁰
      --     D = PE.subst (λ X → Δ₁ ⊢ (lam (wk1 F₁) ▹ wk1d (g (step id) (var 0))) ∘ (var 0) ⇒ X ∷ wk1d G₁ [ var 0 ] ^ ι ⁰) (wkSingleSubstId (g (step id) (var 0)))
      --       (β-red ⊢F₁′ ⊢g0″ (var ⊢Δ₁ here))
      --       ⇨ id ⊢g0
      --     [g0] : Δ₁ ⊩⟨ ι ⁰ ⟩ (lam (wk1 F₁) ▹ wk1d (g (step id) (var 0))) ∘ (var 0) ∷ wk1d G₁ [ var 0 ] ^ [ ! , ι ⁰ ] / [G₁] [ρ₁] ⊢Δ₁ [0]
      --     [g0] = proj₁ (redSubst*Term D ([G₁] [ρ₁] ⊢Δ₁ [0]) ([g] [ρ₁] ⊢Δ₁ [0]))
      --     x₀ = escapeEqReflTerm ([G₁] [ρ₁] ⊢Δ₁ [0]) [g0]
      --     x₁ = PE.subst (λ X → Δ₁ ⊢ (lam (wk1 F₁) ▹ wk1d (g (step id) (var 0))) ∘ (var 0) ≅ (lam (wk1 F₁) ▹ wk1d (g (step id) (var 0))) ∘ (var 0) ∷ X ^ [ ! , ι ⁰ ]) (wkSingleSubstId G₁) x₀
      --     in ≅-η-eq ⊢F₁ ⊢λg ⊢λg lamₙ lamₙ x₁

      --   g∘a≡ga : ∀ {ρ Δ a}
      --     → ([ρ] : ρ Twk.∷ Δ ⊆ Γ)
      --     → (⊢Δ : ⊢ Δ)
      --     → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F₁ ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
      --     → Δ ⊢ wk ρ (lam F₁ ▹ g (step id) (var 0)) ∘ a ⇒* g ρ a ∷ wk (lift ρ) G₁ [ a ] ^ ι ⁰
      --   g∘a≡ga {ρ} {Δ} {a} [ρ] ⊢Δ [a] = let
      --     ⊢F₁′ = (Twk.wk [ρ] ⊢Δ ⊢F₁)
      --     -- this lemma is already in ⊢snde′. maybe refactor?
      --     x₀ : wk (lift ρ) (b (step id) (fst (wk1 e)) (var 0)) [ a ] PE.≡ b ρ (fst (wk ρ e)) a
      --     x₀ = PE.trans
      --       (PE.cong (λ X → cast ⁰ (wk (lift ρ) (wk1 F₁) [ a ]) (wk (lift ρ) (wk1 F) [ a ]) X a)
      --         (PE.trans (PE.cong (λ X → X [ a ]) (wk-Idsym (lift ρ) (U ⁰) (wk1 F) (wk1 F₁) (fst (wk1 e))))
      --           (subst-Idsym (sgSubst a) (U ⁰) (wk (lift ρ) (wk1 F)) (wk (lift ρ) (wk1 F₁)) (fst (wk (lift ρ) (wk1 e))))))
      --       (PE.cong₃ (λ X Y Z → cast ⁰ Y X (Idsym (U ⁰) X Y (fst Z)) a) (irrelevant-subst′ ρ F a) (irrelevant-subst′ ρ F₁ a) (irrelevant-subst′ ρ e a))
      --     x₁ : wk (lift ρ) (g (step id) (var 0)) [ a ] PE.≡ g ρ a
      --     x₁ = PE.cong₄ (λ X Y Z T → cast ⁰ X Y Z T)
      --       (PE.trans (cast-subst-lemma6 ρ G _ a) (PE.cong (λ X → wk (lift ρ) G [ X ]) x₀))
      --       (PE.cong (λ X → wk (lift ρ) X [ a ]) (wkSingleSubstId G₁))
      --       (PE.cong (λ X → snd X ∘ a) (irrelevant-subst′ ρ e a))
      --       (PE.cong₂ (λ X Y → X ∘ Y) (irrelevant-subst′ ρ t a) x₀)
      --     x₂ : Δ ∙ (wk ρ F₁) ^ [ ! , ι ⁰ ] ⊢  wk (lift ρ) (g (step id) (var 0)) ∷ wk (lift ρ) G₁ ^ [ ! , ι ⁰ ]
      --     x₂ = Twk.wkTerm (Twk.lift [ρ]) (⊢Δ ∙ ⊢F₁′) ⊢g0
      --     in PE.subst (λ X → Δ ⊢ wk ρ (lam F₁ ▹ g (step id) (var 0)) ∘ a ⇒ X ∷ wk (lift ρ) G₁ [ a ] ^ ι ⁰) x₁
      --       (β-red ⊢F₁′ x₂ (escapeTerm ([F₁] [ρ] ⊢Δ) [a]))
      --       ⇨ id (escapeTerm ([G₁] [ρ] ⊢Δ [a]) ([g] [ρ] ⊢Δ [a]))

      -- in ((lam F₁ ▹ g (step id) (var 0)) , D , lamₙ , g≡g
      --   , (λ [ρ] ⊢Δ [a] [a′] [a≡a′] → redSubst*EqTerm (g∘a≡ga [ρ] ⊢Δ [a]) (g∘a≡ga [ρ] ⊢Δ [a′])
      --        ([G₁] [ρ] ⊢Δ [a]) ([G₁] [ρ] ⊢Δ [a′]) (G₁-ext [ρ] ⊢Δ [a] [a′] [a≡a′])
      --        ([g] [ρ] ⊢Δ [a]) ([g] [ρ] ⊢Δ [a′]) ([gext] [ρ] ⊢Δ [a] [a′] [a≡a′]))
      --   , (λ [ρ] ⊢Δ [a] → proj₁ (redSubst*Term (g∘a≡ga [ρ] ⊢Δ [a]) ([G₁] [ρ] ⊢Δ [a]) ([g] [ρ] ⊢Δ [a]))))


[cast] ⊢Γ (Πᵣ′ rF .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D ⊢F ⊢G A≡A [F] [G] G-ext)
  (Πᵣ′ rF₁ lF₁ lG₁ lF₁≤⁰ lG₁≤⁰ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) = {!!}
[castext] {A₁} {A₂} {A₃} {A₄} {Γ} ⊢Γ
  (Πᵣ′ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)
  (Πᵣ′ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₂ G₂ [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]] ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext)
  (Π₌ F₂′ G₂′ D₂′ A₁≡A₂′ [F₁≡F₂′] [G₁≡G₂′])
  (Πᵣ′ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₃ G₃ [[ ⊢A₃ , ⊢ΠF₃G₃ , D₃ ]] ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext)
  (Πᵣ′ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₄ G₄ [[ ⊢A₄ , ⊢ΠF₄G₄ , D₄ ]] ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext)
  (Π₌ F₄′ G₄′ D₄′ A₃≡A₄′ [F₃≡F₄′] [G₃≡G₄′]) =
      ([castext]₁ , {!!})
   where
      [A₁] = (Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)
      [A₂] = (Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₂ G₂ [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]] ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext)
      [A₁≡A₂] = (Π₌ F₂′ G₂′ D₂′ A₁≡A₂′ [F₁≡F₂′] [G₁≡G₂′])
      [A₃] = (Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₃ G₃ [[ ⊢A₃ , ⊢ΠF₃G₃ , D₃ ]] ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext)
      [A₄] = (Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₄ G₄ [[ ⊢A₄ , ⊢ΠF₄G₄ , D₄ ]] ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext)
      [A₃≡A₄] = (Π₌ F₄′ G₄′ D₄′ A₃≡A₄′ [F₃≡F₄′] [G₃≡G₄′])

      b₁ = λ ρ e x → cast ⁰ (wk ρ F₃) (wk ρ F₁) (Idsym (U ⁰) (wk ρ F₁) (wk ρ F₃) e) x

      [b₁] : ∀ {ρ Δ e x} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          → (Δ ⊢ e ∷ Id (U ⁰) (wk ρ F₁) (wk ρ F₃) ^ [ % , ι ¹ ])
          → (Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F₃ ^ [ ! , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
          → Δ ⊩⟨ ι ⁰ ⟩ b₁ ρ e x ∷ wk ρ F₁ ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ
      [b₁] [ρ] ⊢Δ ⊢e [x] =
        let
          ⊢e′ = Idsymⱼ (univ 0<1 ⊢Δ) (un-univ (escape ([F₁] [ρ] ⊢Δ)))
            (un-univ (escape ([F₃] [ρ] ⊢Δ))) ⊢e
        in proj₂ ([cast] ⊢Δ ([F₁] [ρ] ⊢Δ) ([F₃] [ρ] ⊢Δ)) [x] ⊢e′

      b₂ = λ ρ e x → cast ⁰ (wk ρ F₄) (wk ρ F₂) (Idsym (U ⁰) (wk ρ F₂) (wk ρ F₄) e) x

      [b₁≡b₂] : ∀ {ρ Δ e₁₃ e₂₄ x₃ x₄} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          → (Δ ⊢ e₁₃ ∷ Id (U ⁰) (wk ρ F₁) (wk ρ F₃) ^ [ % , ι ¹ ])
          → (Δ ⊢ e₂₄ ∷ Id (U ⁰) (wk ρ F₂) (wk ρ F₄) ^ [ % , ι ¹ ])
          → (Δ ⊩⟨ ι ⁰ ⟩ x₃ ∷ wk ρ F₃ ^ [ ! , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
          → (Δ ⊩⟨ ι ⁰ ⟩ x₄ ∷ wk ρ F₄ ^ [ ! , ι ⁰ ] / [F₄] [ρ] ⊢Δ)
          → (Δ ⊩⟨ ι ⁰ ⟩ x₃ ≡ x₄ ∷ wk ρ F₃ ^ [ ! , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
          → Δ ⊩⟨ ι ⁰ ⟩ b₁ ρ e₁₃ x₃ ≡ b₂ ρ e₂₄ x₄ ∷ wk ρ F₁ ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ
      [b₁≡b₂] [ρ] ⊢Δ ⊢e₁₃ ⊢e₂₄ [x₃] [x₄] [x₃≡x₄] = {!!}
        -- let
        --   ⊢e′ = Idsymⱼ (univ 0<1 ⊢Δ) (un-univ (escape ([F₁] [ρ] ⊢Δ)))
        --     (un-univ (escape ([F₃] [ρ] ⊢Δ))) ⊢e
        -- in proj₂ ([cast] ⊢Δ ([F₁] [ρ] ⊢Δ) ([F₃] [ρ] ⊢Δ)) [x] ⊢e′

      [castext]₁ : (∀ {t₁ t₂ e₁₃ e₂₄} → ([t₁] : Γ ⊩⟨ ι ⁰ ⟩ t₁ ∷ A₁ ^ [ ! , ι ⁰ ] / [A₁])
                        → ([t₁] : Γ ⊩⟨ ι ⁰ ⟩ t₂ ∷ A₂ ^ [ ! , ι ⁰ ] / [A₂])
                        → ([t₁≡t₂] : Γ ⊩⟨ ι ⁰ ⟩ t₁ ≡ t₂ ∷ A₁ ^ [ ! , ι ⁰ ] / [A₁])
                        → (⊢e₁₃ : Γ ⊢ e₁₃ ∷ Id (U ⁰) A₁ A₃ ^ [ % , ι ¹ ])
                        → (⊢e₂₄ : Γ ⊢ e₂₄ ∷ Id (U ⁰) A₂ A₄ ^ [ % , ι ¹ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A₁ A₃ e₁₃ t₁ ≡ cast ⁰ A₂ A₄ e₂₄ t₂ ∷ A₃ ^ [ ! , ι ⁰ ] / [A₃])
      [castext]₁ {t₁} {t₂} {e₁₃} {e₂₄} [t₁] [t₂] [t₁≡t₂] ⊢e₁₃ ⊢e₂₄ =
        let
          g₁ = λ ρ x → cast ⁰ (wk (lift ρ) G₁ [ b₁ ρ (fst (wk ρ e₁₃)) x ]) (wk (lift ρ) G₃ [ x ])
            ((snd (wk ρ e₁₃)) ∘ x) ((wk ρ t₁) ∘ (b₁ ρ (fst (wk ρ e₁₃)) x))

          g₂ = λ ρ x → cast ⁰ (wk (lift ρ) G₂ [ b₂ ρ (fst (wk ρ e₂₄)) x ]) (wk (lift ρ) G₄ [ x ])
            ((snd (wk ρ e₂₄)) ∘ x) ((wk ρ t₂) ∘ (b₂ ρ (fst (wk ρ e₂₄)) x))
        in ( {!!} -- lam F₂ ▹ g₁ (step id) (var 0)
          , {!!} -- lam F₄ ▹ g₃ (step id) (var 0)
          , {!!}
          , {!!}
          , {!!}
          , {!!}
          , {!!}
          , {!!}
          , {!!}
          , {!!} )

      [castext]₂ : (∀ {t₃ t₄ e₃₁ e₄₂} → ([t₃] : Γ ⊩⟨ ι ⁰ ⟩ t₃ ∷ A₃ ^ [ ! , ι ⁰ ] / [A₃])
                        → ([t₄] : Γ ⊩⟨ ι ⁰ ⟩ t₄ ∷ A₄ ^ [ ! , ι ⁰ ] / [A₄])
                        → ([t₃≡t₄] : Γ ⊩⟨ ι ⁰ ⟩ t₃ ≡ t₄ ∷ A₃ ^ [ ! , ι ⁰ ] / [A₃])
                        → (⊢e₃₁ : Γ ⊢ e₃₁ ∷ Id (U ⁰) A₃ A₁ ^ [ % , ι ¹ ])
                        → (⊢e₄₂ : Γ ⊢ e₄₂ ∷ Id (U ⁰) A₄ A₂ ^ [ % , ι ¹ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A₃ A₁ e₃₁ t₃ ≡ cast ⁰ A₄ A₂ e₄₂ t₄ ∷ A₁ ^ [ ! , ι ⁰ ] / [A₁])
      [castext]₂ = {!!}

      -- [castext]₂ : {!!}
      -- [castext]₂ = {!!}
    -- ( lam F₂ ▹ g₁ (step id) (var 0)
    --   , lam F₄ ▹ g₃ (step id) (var 0)
    --   , {!!}
    --   , {!!}
    --   , {!!}
    --   , {!!}
    --   , {!!}
    --   , {!!}
    --   , {!!}
    --   , {!!} )
[castext] {A} {C} {B} {D} {Γ} ⊢Γ [A] [C] [A≡C] [B] [D] [B≡D] = {!!}



cast∞ : ∀ {A B r t e Γ}
         (⊢Γ : ⊢ Γ)
         ([U] : Γ ⊩⟨ ∞ ⟩ Univ r ⁰ ^ [ ! , ι ¹ ])
         ([AU] : Γ ⊩⟨ ∞ ⟩ A ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [U])
         ([BU] : Γ ⊩⟨ ∞ ⟩ B ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [U])
         ([A] : Γ ⊩⟨ ∞ ⟩ A ^ [ r , ι ⁰ ])
         ([B] : Γ ⊩⟨ ∞ ⟩ B ^ [ r , ι ⁰ ])
         ([t] : Γ ⊩⟨ ∞ ⟩ t ∷ A ^ [ r , ι ⁰ ] / [A])
         ([Id] : Γ ⊩⟨ ∞ ⟩ Id (Univ r ⁰) A B ^ [ % , ι ¹ ]) →
         ([e] : Γ ⊩⟨ ∞ ⟩ e ∷ Id (Univ r ⁰) A B ^ [ % , ι ¹ ] / [Id] ) →
         Γ ⊩⟨ ∞ ⟩ cast ⁰ A B e t ∷ B ^ [ r , ι ⁰ ] / [B]
cast∞ {A} {B} {r} {t} {e} {Γ} ⊢Γ [U] [AU] [BU] [A] [B] [t] [Id] [e] =
  let
    [A]′ : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ r , ι ⁰ ]
    [A]′ = univEq [U] [AU]
    [B]′ : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ r , ι ⁰ ]
    [B]′ = univEq [U] [BU]
    [t]′ : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ r , ι ⁰ ] / [A]′
    [t]′ = irrelevanceTerm [A] (emb ∞< (emb emb< [A]′)) [t]
    ⊢e : Γ ⊢ e ∷ Id (Univ r ⁰) A B ^ [ % , ι ¹ ]
    ⊢e = escapeTerm [Id] [e]
    x : Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ∷ B ^ [ r , ι ⁰ ] / [B]′
    x = ? -- proj₁ ([cast] ⊢Γ [A]′ [B]′) [t]′ ⊢e
  in irrelevanceTerm (emb ∞< (emb emb< [B]′)) [B] x
  

castᵗᵛ : ∀ {A B r t e Γ}
         ([Γ] : ⊩ᵛ Γ)
         ([U] : Γ ⊩ᵛ⟨ ∞ ⟩ Univ r ⁰ ^ [ ! , ι ¹ ] / [Γ])
         ([AU] : Γ ⊩ᵛ⟨ ∞ ⟩ A ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [Γ] / [U])
         ([BU] : Γ ⊩ᵛ⟨ ∞ ⟩ B ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [Γ] / [U])
         ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ r , ι ⁰ ] / [Γ])
         ([B] : Γ ⊩ᵛ⟨ ∞ ⟩ B ^ [ r , ι ⁰ ] / [Γ])
         ([t] : Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ [ r , ι ⁰ ] / [Γ] / [A])
         ([Id] : Γ ⊩ᵛ⟨ ∞ ⟩ Id (Univ r ⁰) A B ^ [ % , ι ¹ ] / [Γ]) →
         ([e] : Γ ⊩ᵛ⟨ ∞ ⟩ e ∷ Id (Univ r ⁰) A B ^ [ % , ι ¹ ] / [Γ] / [Id] ) →
         Γ ⊩ᵛ⟨ ∞ ⟩ cast ⁰ A B e t ∷ B ^ [ r , ι ⁰ ] / [Γ] / [B]
castᵗᵛ {A} {B} {t} {e} {Γ} [Γ] [U] [AU] [BU] [A] [B] [t] [Id] [e] ⊢Δ [σ] =
  cast∞ ⊢Δ (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([AU] ⊢Δ [σ])) (proj₁ ([BU] ⊢Δ [σ]))
    (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([B] ⊢Δ [σ]))
    (proj₁ ([t] ⊢Δ [σ])) (proj₁ ([Id] ⊢Δ [σ])) (proj₁ ([e] ⊢Δ [σ]))
  , {!!}

cast-congᵗᵛ : ∀ {A A' B B' t t' e e' Γ}
         ([Γ] : ⊩ᵛ Γ) →
         ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ ! , ι ⁰ ] / [Γ])
         ([A'] : Γ ⊩ᵛ⟨ ∞ ⟩ A' ^ [ ! , ι ⁰ ] / [Γ])
         ([A≡A']ₜ : Γ ⊩ᵛ⟨ ∞ ⟩ A ≡ A' ^ [ ! , ι ⁰ ] / [Γ] / [A])
         ([B] : Γ ⊩ᵛ⟨ ∞ ⟩ B ^ [ ! , ι ⁰ ] / [Γ])
         ([B'] : Γ ⊩ᵛ⟨ ∞ ⟩ B' ^ [ ! , ι ⁰ ] / [Γ])
         ([B≡B']ₜ : Γ ⊩ᵛ⟨ ∞ ⟩ B ≡ B' ^ [ ! , ι ⁰ ] / [Γ] / [B] )
         ([t] : Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ [ ! , ι ⁰ ] / [Γ] / [A])
         ([t≡t']ₜ : Γ ⊩ᵛ⟨ ∞ ⟩ t ≡ t' ∷ A ^ [ ! , ι ⁰ ] / [Γ] / [A] )
         ([Id] : Γ ⊩ᵛ⟨ ∞ ⟩ Id (U ⁰) A B ^ [ % , ι ¹ ] / [Γ])
         ([e] : Γ ⊩ᵛ⟨ ∞ ⟩ e ∷ Id (U ⁰) A B ^ [ % , ι ¹ ] / [Γ] / [Id] )
         ([Id'] : Γ ⊩ᵛ⟨ ∞ ⟩ Id (U ⁰) A' B' ^ [ % , ι ¹ ] / [Γ])
         ([e'] : Γ ⊩ᵛ⟨ ∞ ⟩ e' ∷ Id (U ⁰) A' B' ^ [ % , ι ¹ ] / [Γ] / [Id'] ) →
         Γ ⊩ᵛ⟨ ∞ ⟩ cast ⁰ A B e t ≡ cast ⁰ A' B' e' t' ∷ B ^ [ ! , ι ⁰ ] / [Γ] / [B]
cast-congᵗᵛ = {!!}

