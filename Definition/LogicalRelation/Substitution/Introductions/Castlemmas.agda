{-# OPTIONS --allow-unsolved-metas #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Castlemmas {{eqrel : EqRelSet}} where
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


module cast-ΠΠ-lemmas
       {Γ rF F F₁}
       (⊢Γ : ⊢ Γ)
       (⊢F : Γ ⊢ F ^ [ rF , ι ⁰ ])
       ([F] : ∀ {ρ} {Δ} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Δ ⊩⟨ ι ⁰ ⟩ wk ρ F ^ [ rF , ι ⁰ ])
       (⊢F₁    : Γ ⊢ F₁ ^ [ rF , ι ⁰ ])
       ([F₁] : ∀ {ρ} {Δ} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Δ ⊩⟨ ι ⁰ ⟩ wk ρ F₁ ^ [ rF , ι ⁰ ])
       (recursor : ∀ {x e ρ Δ}
         ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
         ([x] : Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
         (⊢e : Δ ⊢ e ∷ Id (Univ rF ⁰) (wk ρ F₁) (wk ρ F) ^ [ % , ι ¹ ])
         → Δ ⊩⟨ ι ⁰ ⟩ cast ⁰ (wk ρ F₁) (wk ρ F) e x ∷ wk ρ F ^ [ rF , ι ⁰ ] / [F] [ρ] ⊢Δ)
       (extrecursor : ∀ {ρ Δ x y e e′}
         → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
         → ([x] : Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
         → ([y] : Δ ⊩⟨ ι ⁰ ⟩ y ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
         → ([x≡y] : Δ ⊩⟨ ι ⁰ ⟩ x ≡ y ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
         → (⊢e : Δ ⊢ e ∷ Id (Univ rF ⁰) (wk ρ F₁) (wk ρ F) ^ [ % , ι ¹ ])
         → (⊢e′ : Δ ⊢ e′ ∷ Id (Univ rF ⁰) (wk ρ F₁) (wk ρ F) ^ [ % , ι ¹ ])
         → Δ ⊩⟨ ι ⁰ ⟩ cast ⁰ (wk ρ F₁) (wk ρ F) e x ≡ cast ⁰ (wk ρ F₁) (wk ρ F) e′ y ∷ wk ρ F ^ [ rF , ι ⁰ ] / [F] [ρ] ⊢Δ)
  where
    b = λ ρ e x → cast ⁰ (wk ρ F₁) (wk ρ F) (Idsym (Univ rF ⁰) (wk ρ F) (wk ρ F₁) e) x

    [b] : ∀ {ρ Δ e x} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
        → (Δ ⊢ e ∷ Id (Univ rF ⁰) (wk ρ F) (wk ρ F₁) ^ [ % , ι ¹ ])
        → (Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
        → Δ ⊩⟨ ι ⁰ ⟩ b ρ e x ∷ wk ρ F ^ [ rF , ι ⁰ ] / [F] [ρ] ⊢Δ
    [b] [ρ] ⊢Δ ⊢e [x] =
      let
        ⊢e′ = Idsymⱼ (univ 0<1 ⊢Δ) (un-univ (escape ([F] [ρ] ⊢Δ)))
                     (un-univ (escape ([F₁] [ρ] ⊢Δ))) ⊢e
      in recursor [ρ] ⊢Δ [x] ⊢e′

    [bext] : ∀ {ρ Δ e e′ x y} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
        → (Δ ⊢ e ∷ Id (Univ rF ⁰) (wk ρ F) (wk ρ F₁) ^ [ % , ι ¹ ])
        → (Δ ⊢ e′ ∷ Id (Univ rF ⁰) (wk ρ F) (wk ρ F₁) ^ [ % , ι ¹ ])
        → (Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
        → (Δ ⊩⟨ ι ⁰ ⟩ y ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
        → (Δ ⊩⟨ ι ⁰ ⟩ x ≡ y ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
        → Δ ⊩⟨ ι ⁰ ⟩ b ρ e x ≡ b ρ e′ y ∷ wk ρ F ^ [ rF , ι ⁰ ] / [F] [ρ] ⊢Δ
    [bext] [ρ] ⊢Δ ⊢e ⊢e′ [x] [y] [x≡y] =
      let
        ⊢syme = Idsymⱼ (univ 0<1 ⊢Δ) (un-univ (escape ([F] [ρ] ⊢Δ)))
          (un-univ (escape ([F₁] [ρ] ⊢Δ))) ⊢e
        ⊢syme′ = Idsymⱼ (univ 0<1 ⊢Δ) (un-univ (escape ([F] [ρ] ⊢Δ)))
          (un-univ (escape ([F₁] [ρ] ⊢Δ))) ⊢e′
      in extrecursor [ρ] ⊢Δ [x] [y] [x≡y] ⊢syme ⊢syme′

module cast-ΠΠ-lemmas-2
       {t e f Γ A B F rF G F₁ G₁}
       (⊢Γ : ⊢ Γ)
       (⊢A : Γ ⊢ A ^ [ ! , ι ⁰ ])
       (⊢ΠFG : Γ ⊢ Π F ^ rF ° ⁰ ▹ G ° ⁰ ^ [ ! , ι ⁰ ])
       (D : Γ ⊢ A ⇒* Π F ^ rF ° ⁰ ▹ G ° ⁰ ^ [ ! , ι ⁰ ])
       (⊢F : Γ ⊢ F ^ [ rF , ι ⁰ ])
       (⊢G : (Γ ∙ F ^ [ rF , ι ⁰ ]) ⊢ G ^ [ ! , ι ⁰ ])
       (A≡A : Γ ⊢ (Π F ^ rF ° ⁰ ▹ G ° ⁰) ≅ (Π F ^ rF ° ⁰ ▹ G ° ⁰) ^ [ ! , ι ⁰ ])
       ([F] : ∀ {ρ} {Δ} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Δ ⊩⟨ ι ⁰ ⟩ wk ρ F ^ [ rF , ι ⁰ ])
       ([G] : ∀ {ρ} {Δ} {a} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷  wk ρ F ^ [ rF , ι ⁰ ] / ([F] [ρ] ⊢Δ))
          → (Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G [ a ] ^ [ ! , ι ⁰ ]))
       (G-ext : ∀ {ρ} {Δ} {a} {b} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷  wk ρ F ^ [ rF , ι ⁰ ] / ([F] [ρ] ⊢Δ))
          ([b] : Δ ⊩⟨ ι ⁰ ⟩ b ∷  wk ρ F ^ [ rF , ι ⁰ ] / ([F] [ρ] ⊢Δ))
          ([a≡b] : Δ ⊩⟨ ι ⁰ ⟩ a ≡ b ∷ wk ρ F ^ [ rF , ι ⁰ ] / ([F] [ρ] ⊢Δ))
          → (Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G [ a ] ≡ wk (lift ρ) G [ b ] ^ [ ! , ι ⁰ ] / ([G] [ρ] ⊢Δ [a])))
       (⊢B     : Γ ⊢ B ^ [ ! , ι ⁰ ])
       (⊢ΠF₁G₁ : Γ ⊢ Π F₁ ^ rF ° ⁰ ▹ G₁ ° ⁰ ^ [ ! , ι ⁰ ])
       (D₁     : Γ ⊢ B ⇒* Π F₁ ^ rF ° ⁰ ▹ G₁ ° ⁰ ^ [ ! , ι ⁰ ])
       (⊢F₁    : Γ ⊢ F₁ ^ [ rF , ι ⁰ ])
       (⊢G₁    : (Γ ∙ F₁ ^ [ rF , ι ⁰ ]) ⊢ G₁ ^ [ ! , ι ⁰ ])
       (A₁≡A₁  : Γ ⊢ (Π F₁ ^ rF ° ⁰ ▹ G₁ ° ⁰) ≅ (Π F₁ ^ rF ° ⁰ ▹ G₁ ° ⁰) ^ [ ! , ι ⁰ ])
       ([F₁] : ∀ {ρ} {Δ} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Δ ⊩⟨ ι ⁰ ⟩ wk ρ F₁ ^ [ rF , ι ⁰ ])
       ([G₁] : ∀ {ρ} {Δ} {a} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷  wk ρ F₁ ^ [ rF , ι ⁰ ] / ([F₁] [ρ] ⊢Δ))
          → (Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₁ [ a ] ^ [ ! , ι ⁰ ]))
       (G₁-ext : ∀ {ρ} {Δ} {a} {b} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷  wk ρ F₁ ^ [ rF , ι ⁰ ] / ([F₁] [ρ] ⊢Δ))
          ([b] : Δ ⊩⟨ ι ⁰ ⟩ b ∷  wk ρ F₁ ^ [ rF , ι ⁰ ] / ([F₁] [ρ] ⊢Δ))
          ([a≡b] : Δ ⊩⟨ ι ⁰ ⟩ a ≡ b ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / ([F₁] [ρ] ⊢Δ))
          → (Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₁ [ a ] ≡ wk (lift ρ) G₁ [ b ] ^ [ ! , ι ⁰ ] / ([G₁] [ρ] ⊢Δ [a])))
       (⊢e : Γ ⊢ e ∷ Id (U ⁰) A B ^ [ % , ι ¹ ])
       (recursor : ∀ {ρ Δ x y t e}
          ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([x] : Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F ^ [ rF , ι ⁰ ] / [F] [ρ] ⊢Δ)
          ([y] : Δ ⊩⟨ ι ⁰ ⟩ y ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
          ([t] : Δ ⊩⟨ ι ⁰ ⟩ t ∷ wk (lift ρ) G [ x ] ^ [ ! , ι ⁰ ] / [G] [ρ] ⊢Δ [x])
          (⊢e : Δ ⊢ e ∷ Id (U ⁰) (wk (lift ρ) G [ x ]) (wk (lift ρ) G₁ [ y ]) ^ [ % , ι ¹ ])
          → Δ ⊩⟨ ι ⁰ ⟩ cast ⁰ (wk (lift ρ) G [ x ]) (wk (lift ρ) G₁ [ y ]) e t ∷ wk (lift ρ) G₁ [ y ] ^ [ ! , ι ⁰ ] / [G₁] [ρ] ⊢Δ [y])
       (extrecursor : ∀ {ρ Δ x x′ y y′ t t′ e e′}
         → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
         → ([x] : Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F ^ [ rF , ι ⁰ ] / [F] [ρ] ⊢Δ)
         → ([x′] : Δ ⊩⟨ ι ⁰ ⟩ x′ ∷ wk ρ F ^ [ rF , ι ⁰ ] / [F] [ρ] ⊢Δ)
         → ([x≡x′] : Δ ⊩⟨ ι ⁰ ⟩ x ≡ x′ ∷ wk ρ F ^ [ rF , ι ⁰ ] / [F] [ρ] ⊢Δ)
         → ([y] : Δ ⊩⟨ ι ⁰ ⟩ y ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
         → ([y′] : Δ ⊩⟨ ι ⁰ ⟩ y′ ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
         → ([y≡y′] : Δ ⊩⟨ ι ⁰ ⟩ y ≡ y′ ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
         → ([t] : Δ ⊩⟨ ι ⁰ ⟩ t ∷ wk (lift ρ) G [ x ] ^ [ ! , ι ⁰ ] / [G] [ρ] ⊢Δ [x])
         → ([t′] : Δ ⊩⟨ ι ⁰ ⟩ t′ ∷ wk (lift ρ) G [ x′ ] ^ [ ! , ι ⁰ ] / [G] [ρ] ⊢Δ [x′])
         → ([t≡t′] : Δ ⊩⟨ ι ⁰ ⟩ t ≡ t′ ∷ wk (lift ρ) G [ x ] ^ [ ! , ι ⁰ ] / [G] [ρ] ⊢Δ [x])
         → (⊢e : Δ ⊢ e ∷ Id (U ⁰) (wk (lift ρ) G [ x ]) (wk (lift ρ) G₁ [ y ]) ^ [ % , ι ¹ ])
         → (⊢e′ : Δ ⊢ e′ ∷ Id (U ⁰) (wk (lift ρ) G [ x′ ]) (wk (lift ρ) G₁ [ y′ ]) ^ [ % , ι ¹ ])
         → Δ ⊩⟨ ι ⁰ ⟩ cast ⁰ (wk (lift ρ) G [ x ]) (wk (lift ρ) G₁ [ y ]) e t ≡ cast ⁰ (wk (lift ρ) G [ x′ ]) (wk (lift ρ) G₁ [ y′ ]) e′ t′ ∷ wk (lift ρ) G₁ [ y ] ^ [ ! , ι ⁰ ] / [G₁] [ρ] ⊢Δ [y])
       (⊢t : Γ ⊢ t ∷ Π F ^ rF ° ⁰ ▹ G ° ⁰ ^ [ ! , ι ⁰ ])
       (Df : Γ ⊢ t ⇒* f ∷ Π F ^ rF ° ⁰ ▹ G ° ⁰ ^ ι ⁰)
       ([fext] : ∀ {ρ Δ a b} →
                ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
                ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F ^ [ rF , ι ⁰ ] / [F] [ρ] ⊢Δ)
                ([b] : Δ ⊩⟨ ι ⁰ ⟩ b ∷ wk ρ F ^ [ rF , ι ⁰ ] / [F] [ρ] ⊢Δ)
                ([a≡b] : Δ ⊩⟨ ι ⁰ ⟩ a ≡ b ∷ wk ρ F ^ [ rF , ι ⁰ ] / [F] [ρ] ⊢Δ)
              → Δ ⊩⟨ ι ⁰ ⟩ wk ρ f ∘ a ≡ wk ρ f ∘ b ∷ wk (lift ρ) G [ a ] ^ [ ! , ι ⁰ ] / [G] [ρ] ⊢Δ [a])
       ([f] : ∀ {ρ Δ a}
              → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
              → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F ^ [ rF , ι ⁰ ] / [F] [ρ] ⊢Δ)
              → Δ ⊩⟨ ι ⁰ ⟩ wk ρ f ∘ a ∷ wk (lift ρ) G [ a ] ^ [ ! , ι ⁰ ] / [G] [ρ] ⊢Δ [a])
       ([b] : ∀ {ρ Δ e x}
                ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
                (⊢e : Δ ⊢ e ∷ Id (Univ rF ⁰) (wk ρ F) (wk ρ F₁) ^ [ % , ι ¹ ])
                ([x] : Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
                → Δ ⊩⟨ ι ⁰ ⟩ cast ⁰ (wk ρ F₁) (wk ρ F) (Idsym (Univ rF ⁰) (wk ρ F) (wk ρ F₁) e) x ∷ wk ρ F ^ [ rF , ι ⁰ ] / [F] [ρ] ⊢Δ)
       ([bext] : ∀ {ρ Δ e e′ x y} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
           → (Δ ⊢ e ∷ Id (Univ rF ⁰) (wk ρ F) (wk ρ F₁) ^ [ % , ι ¹ ])
           → (Δ ⊢ e′ ∷ Id (Univ rF ⁰) (wk ρ F) (wk ρ F₁) ^ [ % , ι ¹ ])
           → (Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
           → (Δ ⊩⟨ ι ⁰ ⟩ y ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
           → (Δ ⊩⟨ ι ⁰ ⟩ x ≡ y ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
           → Δ ⊩⟨ ι ⁰ ⟩ cast ⁰ (wk ρ F₁) (wk ρ F) (Idsym (Univ rF ⁰) (wk ρ F) (wk ρ F₁) e) x
             ≡ cast ⁰ (wk ρ F₁) (wk ρ F) (Idsym (Univ rF ⁰) (wk ρ F) (wk ρ F₁) e′) y ∷ wk ρ F ^ [ rF , ι ⁰ ] / [F] [ρ] ⊢Δ)
  where
    b = λ ρ e x → cast ⁰ (wk ρ F₁) (wk ρ F) (Idsym (Univ rF ⁰) (wk ρ F) (wk ρ F₁) e) x

    ⊢IdFF₁ : Γ ⊢ Id (Univ rF ⁰) F F₁ ^ [ % , ι ¹ ]
    ⊢IdFF₁ = univ (Idⱼ (univ 0<1 ⊢Γ) (un-univ ⊢F) (un-univ ⊢F₁))

    Δ₀ = Γ ∙ Id (Univ rF ⁰) F F₁ ^ [ % , ι ¹ ] ∙ wk1 F₁ ^ [ rF , ι ⁰ ]
    ρ₀ = (step (step id))

    ⊢IdG₁G : Γ ∙ Id (Univ rF ⁰) F F₁ ^ [ % , ι ¹ ] ⊢ Π (wk1 F₁) ^ rF ° ⁰ ▹ Id (U ⁰) ((wk1d G) [ b ρ₀ (var 1) (var 0) ]↑) (wk1d G₁) ° ¹ ^ [ % , ι ¹ ]
    ⊢IdG₁G =
      let
        ⊢Δ₀ : ⊢ Δ₀
        ⊢Δ₀ = ⊢Γ ∙ ⊢IdFF₁ ∙ univ (Twk.wkTerm (Twk.step Twk.id) (⊢Γ ∙ ⊢IdFF₁) (un-univ ⊢F₁))
        [ρ₀] : ρ₀ Twk.∷ Δ₀ ⊆ Γ
        [ρ₀] = Twk.step (Twk.step Twk.id)
        [0] : Δ₀ ⊩⟨ ι ⁰ ⟩ var 0 ∷ wk ρ₀ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ₀] ⊢Δ₀
        [0] = let x = (var ⊢Δ₀ (PE.subst (λ X → 0 ∷ X ^ [ rF , ι ⁰ ] ∈ Δ₀) (wk1-wk (step id) F₁) here)) in
          neuTerm ([F₁] [ρ₀] ⊢Δ₀) (var 0) x (~-var x)
        ⊢1 : Δ₀ ⊢ (var 1) ∷ Id (Univ rF ⁰) (wk ρ₀ F) (wk ρ₀ F₁) ^ [ % , ι ¹ ]
        ⊢1 = var ⊢Δ₀ (PE.subst₂ (λ X Y → 1 ∷ Id (Univ rF ⁰) X Y ^ [ % , ι ¹ ] ∈ Δ₀)
          (wk1-wk (step id) F) (wk1-wk (step id) F₁) (there here))
        ⊢G₀ : Δ₀ ⊢ wk (lift ρ₀) G [ b ρ₀ (var 1) (var 0) ] ^ [ ! , ι ⁰ ]
        ⊢G₀ = escape ([G] [ρ₀] ⊢Δ₀ ([b] [ρ₀] ⊢Δ₀ ⊢1 [0]))
        ⊢G₀′ = PE.subst (λ X → Δ₀ ⊢ X ^ [ ! , ι ⁰ ]) (PE.sym (cast-subst-lemma2 G (b ρ₀ (var 1) (var 0)))) ⊢G₀
        x₀ : Δ₀ ⊢ Id (U ⁰) ((wk1d G) [ b ρ₀ (var 1) (var 0) ]↑) (wk1d G₁) ∷ SProp ¹ ^ [ ! , ∞ ]
        x₀ = Idⱼ (univ 0<1 ⊢Δ₀) (un-univ ⊢G₀′)
            (un-univ (Twk.wk (Twk.lift (Twk.step Twk.id)) ⊢Δ₀ ⊢G₁))
        x₁ = Πⱼ <is≤ 0<1 ▹ ≡is≤ PE.refl ▹ Twk.wkTerm (Twk.step Twk.id) (⊢Γ ∙ ⊢IdFF₁) (un-univ ⊢F₁) ▹ x₀
      in univ x₁

    ⊢e′ : Γ ⊢ e ∷ ∃ (Id (Univ rF ⁰) F F₁) ▹ (Π (wk1 F₁) ^ rF ° ⁰ ▹ Id (U ⁰) ((wk1d G) [ b ρ₀ (var 1) (var 0) ]↑) (wk1d G₁) ° ¹) ^ [ % , ι ¹ ]
    ⊢e′ =
      let
        b₀ = cast ⁰ (wk1 (wk1 F₁)) (wk1 (wk1 F)) (Idsym (Univ rF ⁰) (wk1 (wk1 F)) (wk1 (wk1 F₁)) (var 1)) (var 0)
        b≡b₀ : b ρ₀ (var 1) (var 0) PE.≡ b₀
        b≡b₀ = PE.cong₂ (λ X Y → cast ⁰ Y X (Idsym (Univ rF ⁰) X Y (var 1)) (var 0))
          (PE.sym (wk1-wk (step id) F)) (PE.sym (wk1-wk (step id) F₁))
        x₀ = conv ⊢e (univ (Id-cong (refl (univ 0<1 ⊢Γ)) (un-univ≡ (subset* D)) (un-univ≡ (subset* D₁))))
        x₁ = conv x₀ (univ (Id-U-ΠΠ (un-univ ⊢F) (un-univ ⊢G) (un-univ ⊢F₁) (un-univ ⊢G₁)))
        x₂ = PE.subst (λ X → Γ ⊢ e ∷ ∃ (Id (Univ rF ⁰) F F₁) ▹ (Π (wk1 F₁) ^ rF ° ⁰ ▹ Id (U ⁰) ((wk1d G) [ X ]↑) (wk1d G₁) ° ¹) ^ [ % , ι ¹ ]) (PE.sym b≡b₀) x₁
      in x₂

    ⊢fste : Γ ⊢ fst e ∷ Id (Univ rF ⁰) F F₁ ^ [ % , ι ¹ ]
    ⊢fste = fstⱼ (un-univ ⊢IdFF₁) (un-univ ⊢IdG₁G) ⊢e′

    ⊢snde : Γ ⊢ snd e ∷ Π F₁ ^ rF ° ⁰ ▹ Id (U ⁰) (wk1d G [ b (step id) (fst (wk1 e)) (var 0) ]) G₁ ° ¹ ^ [ % , ι ¹ ]
    ⊢snde =
      let
        x₀ = sndⱼ (un-univ ⊢IdFF₁) (un-univ ⊢IdG₁G) ⊢e′
        x₁ = PE.subst₂ (λ X Y → Γ ⊢ snd e ∷ (Π X ^ rF ° ⁰ ▹ subst _ (Id (U ⁰) Y (wk1d G₁)) ° ¹) ^ [ % , ι ¹ ])
            (wk1-singleSubst F₁ (fst e)) (cast-subst-lemma2 G (b ρ₀ (var 1) (var 0))) x₀
        x₂ = PE.subst₂ (λ X Y → Γ ⊢ snd e ∷ Π F₁ ^ rF ° ⁰ ▹ Id (U ⁰) X Y ° ¹ ^ [ % , ι ¹ ])
          (singleSubstLift (wk (lift ρ₀) G) (b ρ₀ (var 1) (var 0))) (wk1d-singleSubst G₁ (fst e)) x₁
        σ = liftSubst (sgSubst (fst e))
        b≡b : subst σ (b ρ₀ (var 1) (var 0)) PE.≡ b (step id) (fst (wk1 e)) (var 0)
        b≡b = PE.trans (PE.cong (λ X → cast ⁰ (subst σ (wk ρ₀ F₁)) (subst σ (wk ρ₀ F)) X (var 0)) (subst-Idsym σ (Univ rF ⁰) (wk ρ₀ F) (wk ρ₀ F₁) (var 1)))
          (PE.cong₂ (λ X Y → cast ⁰ Y X (Idsym (Univ rF ⁰) X Y (fst (wk1 e))) (var 0)) (cast-subst-lemma5 F (fst e)) (cast-subst-lemma5 F₁ (fst e)))
        x₃ = PE.subst₂ (λ X Y → Γ ⊢ snd e ∷ Π F₁ ^ rF ° ⁰ ▹ Id (U ⁰) (X [ Y ]) G₁ ° ¹ ^ [ % , ι ¹ ])
          (cast-subst-lemma3 G (fst e)) b≡b x₂
     in x₃

    ⊢snde′ : ∀ {ρ Δ x} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
        → (⊢x : Δ ⊢ x ∷ wk ρ F₁ ^ [ rF , ι ⁰ ])
        → Δ ⊢ snd (wk ρ e) ∘ x ∷ Id (U ⁰) (wk (lift ρ) G [ b ρ (fst (wk ρ e)) x ])
          (wk (lift ρ) G₁ [ x ]) ^ [ % , ι ¹ ]
    ⊢snde′ {ρ} {Δ} {x} [ρ] ⊢Δ ⊢x =
      let
        -- I should probably make some generic lemma about pushing weakening and subst in b
        y₀ = PE.trans (PE.cong (λ X → X [ x ]) (wk-Idsym (lift ρ) (Univ rF ⁰) (wk1 F) (wk1 F₁) (fst (wk1 e))))
          (PE.trans (subst-Idsym (sgSubst x) (Univ rF ⁰) (wk (lift ρ) (wk1 F)) (wk (lift ρ) (wk1 F₁)) (fst (wk (lift ρ) (wk1 e))))
          (PE.cong₃ (λ X Y Z → Idsym (Univ rF ⁰) X Y (fst Z)) (irrelevant-subst′ ρ F x) (irrelevant-subst′ ρ F₁ x) (irrelevant-subst′ ρ e x)))
        y₁ : wk (lift ρ) (b (step id) (fst (wk1 e)) (var 0)) [ x ] PE.≡ b ρ (fst (wk ρ e)) x
        y₁ = PE.cong₃ (λ X Y Z → cast ⁰ X Y Z x) (irrelevant-subst′ ρ F₁ x) (irrelevant-subst′ ρ F x) y₀
        x₀ = Δ ⊢ (wk ρ (snd e)) ∘ x ∷ Id (U ⁰) (wk (lift ρ) (wk1d G [ b (step id) (fst (wk1 e)) (var 0) ]) [ x ]) (wk (lift ρ) G₁ [ x ]) ^ [ % , ι ¹ ]
        x₀ = Twk.wkTerm [ρ] ⊢Δ ⊢snde ∘ⱼ ⊢x
        x₁ = PE.cong₂ (λ X Y → X [ Y ]) (cast-subst-lemma4 ρ x G) y₁
        x₂ = PE.trans (singleSubstLift (wk (lift (lift ρ)) (wk1d G))
          (wk (lift ρ) (b (step id) (fst (wk1 e)) (var 0)))) x₁
        x₃ = PE.trans (PE.cong (λ X → X [ x ]) (wk-β {a = b (step id) (fst (wk1 e)) (var 0)} (wk1d G))) x₂
        x₄ = PE.subst (λ X → Δ ⊢ snd (wk ρ e) ∘ x ∷ Id (U ⁰) X (wk (lift ρ) G₁ [ x ]) ^ [ % , ι ¹ ]) x₃ x₀
      in x₄

    g = λ ρ x → cast ⁰ (wk (lift ρ) G [ b ρ (fst (wk ρ e)) x ]) (wk (lift ρ) G₁ [ x ])
      ((snd (wk ρ e)) ∘ x) ((wk ρ t) ∘ (b ρ (fst (wk ρ e)) x))

    [g] : ∀ {ρ Δ x} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
        → ([x] : Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
        → Δ ⊩⟨ ι ⁰ ⟩ g ρ x ∷ wk (lift ρ) G₁ [ x ] ^ [ ! , ι ⁰ ] / [G₁] [ρ] ⊢Δ [x]
    [g] {ρ} {Δ} {x} [ρ] ⊢Δ [x] =
      let
        [b]′ = [b] [ρ] ⊢Δ (Twk.wkTerm [ρ] ⊢Δ ⊢fste) [x]
        [t] = proj₁ (redSubst*Term (appRed* (escapeTerm ([F] [ρ] ⊢Δ) [b]′) (Twk.wkRed*Term [ρ] ⊢Δ Df))
          ([G] [ρ] ⊢Δ [b]′) ([f] [ρ] ⊢Δ [b]′))
        x = recursor [ρ] ⊢Δ [b]′ [x] [t] (⊢snde′ [ρ] ⊢Δ (escapeTerm ([F₁] [ρ] ⊢Δ) [x]))
      in x

    [gext] : ∀ {ρ Δ x y} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
        → ([x] : Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
        → ([y] : Δ ⊩⟨ ι ⁰ ⟩ y ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
        → ([x≡y] : Δ ⊩⟨ ι ⁰ ⟩ x ≡ y ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
        → Δ ⊩⟨ ι ⁰ ⟩ g ρ x ≡ g ρ y ∷ wk (lift ρ) G₁ [ x ] ^ [ ! , ι ⁰ ] / [G₁] [ρ] ⊢Δ [x]
    [gext] {ρ} {Δ} {x} {y} [ρ] ⊢Δ [x] [y] [x≡y] =
      let
        [b₁] = [b] [ρ] ⊢Δ (Twk.wkTerm [ρ] ⊢Δ ⊢fste) [x]
        [b₂] = [b] [ρ] ⊢Δ (Twk.wkTerm [ρ] ⊢Δ ⊢fste) [y]
        [b₁≡b₂] = [bext] [ρ] ⊢Δ (Twk.wkTerm [ρ] ⊢Δ ⊢fste) (Twk.wkTerm [ρ] ⊢Δ ⊢fste) [x] [y] [x≡y]
        D₁ = (appRed* (escapeTerm ([F] [ρ] ⊢Δ) [b₁]) (Twk.wkRed*Term [ρ] ⊢Δ Df))
        D₂ = (appRed* (escapeTerm ([F] [ρ] ⊢Δ) [b₂]) (Twk.wkRed*Term [ρ] ⊢Δ Df))
        [t₁] = proj₁ (redSubst*Term D₁ ([G] [ρ] ⊢Δ [b₁]) ([f] [ρ] ⊢Δ [b₁]))
        [t₂] = proj₁ (redSubst*Term D₂ ([G] [ρ] ⊢Δ [b₂]) ([f] [ρ] ⊢Δ [b₂]))
        [t₁≡t₂] = redSubst*EqTerm D₁ D₂ ([G] [ρ] ⊢Δ [b₁]) ([G] [ρ] ⊢Δ [b₂]) (G-ext [ρ] ⊢Δ [b₁] [b₂] [b₁≡b₂])
          ([f] [ρ] ⊢Δ [b₁]) ([f] [ρ] ⊢Δ [b₂]) ([fext] [ρ] ⊢Δ [b₁] [b₂] [b₁≡b₂])
      in extrecursor [ρ] ⊢Δ [b₁] [b₂] [b₁≡b₂] [x] [y] [x≡y] [t₁] [t₂] [t₁≡t₂] (⊢snde′ [ρ] ⊢Δ (escapeTerm ([F₁] [ρ] ⊢Δ) [x])) (⊢snde′ [ρ] ⊢Δ (escapeTerm ([F₁] [ρ] ⊢Δ) [y]))

    Δ₁ = Γ ∙ F₁ ^ [ rF , ι ⁰ ]
    ⊢Δ₁ : ⊢ Δ₁
    ⊢Δ₁ = ⊢Γ ∙ ⊢F₁
    ρ₁ = (step id)
    [ρ₁] : ρ₁ Twk.∷ Δ₁ ⊆ Γ
    [ρ₁] = Twk.step Twk.id
    [0] : Δ₁ ⊩⟨ ι ⁰ ⟩ var 0 ∷ wk ρ₁ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ₁] ⊢Δ₁
    [0] = neuTerm ([F₁] [ρ₁] ⊢Δ₁) (var 0) (var ⊢Δ₁ here) (~-var (var ⊢Δ₁ here))

    ⊢g0 = PE.subst (λ X → Δ₁ ⊢ g (step id) (var 0) ∷ X ^ [ ! , ι ⁰ ]) (wkSingleSubstId G₁) (escapeTerm ([G₁] [ρ₁] ⊢Δ₁ [0]) ([g] [ρ₁] ⊢Δ₁ [0]))
    ⊢λg : Γ ⊢ lam F₁ ▹ g (step id) (var 0) ∷ Π F₁ ^ rF ° ⁰ ▹ G₁ ° ⁰ ^ [ ! , ι ⁰ ]
    ⊢λg = lamⱼ (≡is≤ PE.refl) (≡is≤ PE.refl) ⊢F₁ ⊢g0

    Dg : Γ ⊢ cast ⁰ A B e t :⇒*: (lam F₁ ▹ g (step id) (var 0)) ∷ Π F₁ ^ rF ° ⁰ ▹ G₁ ° ⁰ ^ ι ⁰
    Dg =
      let
        g0 = lam F₁ ▹ cast ⁰ (G [ b (step id) (fst (wk1 e)) (var 0) ]↑) G₁
          ((snd (wk1 e)) ∘ (var 0)) ((wk1 t) ∘ (b (step id) (fst (wk1 e)) (var 0)))
        g≡g : g0 PE.≡ lam F₁ ▹ g (step id) (var 0)
        g≡g = PE.cong₂ (λ X Y → lam F₁ ▹ cast ⁰ X Y ((snd (wk1 e)) ∘ (var 0)) ((wk1 t) ∘ (b (step id) (fst (wk1 e)) (var 0))))
          (wk1d[]-[]↑ G (b (step id) (fst (wk1 e)) (var 0))) (PE.sym (wkSingleSubstId G₁))
        ⊢e′ = conv ⊢e (univ (Id-cong (refl (univ 0<1 ⊢Γ))
          (un-univ≡ (subset* D)) (refl (un-univ ⊢B))))
        ⊢e″ = conv ⊢e (univ (Id-cong (refl (univ 0<1 ⊢Γ))
          (un-univ≡ (subset* D)) (un-univ≡ (subset* D₁))))
      in [[ conv (castⱼ (un-univ ⊢A) (un-univ ⊢B) ⊢e (conv ⊢t (sym (subset* D)))) (subset* D₁)
         , ⊢λg
         , (conv* (CastRed*Term′ ⊢B ⊢e (conv ⊢t (sym (subset* D))) D
           ⇨∷* castΠRed* ⊢F ⊢G ⊢e′ ⊢t D₁) (subset* D₁))
           ⇨∷* (PE.subst (λ X → Γ ⊢ cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰) (Π F₁ ^ rF ° ⁰ ▹ G₁ ° ⁰) e t ⇒ X ∷ Π F₁ ^ rF ° ⁰ ▹ G₁ ° ⁰ ^ ι ⁰) g≡g
           (cast-Π (un-univ ⊢F) (un-univ ⊢G) (un-univ ⊢F₁) (un-univ ⊢G₁) ⊢e″ ⊢t) ⇨ (id ⊢λg)) ]]

    g≡g : Γ ⊢ (lam F₁ ▹ g (step id) (var 0)) ≅ (lam F₁ ▹ g (step id) (var 0)) ∷ Π F₁ ^ rF ° ⁰ ▹ G₁ ° ⁰ ^ [ ! , ι ⁰ ]
    g≡g =
      let
        ⊢F₁′ = Twk.wk (Twk.step Twk.id) ⊢Δ₁ ⊢F₁
        ⊢g0 = escapeTerm ([G₁] [ρ₁] ⊢Δ₁ [0]) ([g] [ρ₁] ⊢Δ₁ [0])
        ⊢g0′ = (PE.subst (λ X → Δ₁ ⊢ g (step id) (var 0) ∷ X ^ [ ! , ι ⁰ ]) (wkSingleSubstId G₁) ⊢g0)
        ⊢g0″ = Twk.wkTerm (Twk.lift (Twk.step Twk.id)) (⊢Δ₁ ∙ ⊢F₁′) ⊢g0′
        D : Δ₁ ⊢ (lam (wk1 F₁) ▹ wk1d (g (step id) (var 0))) ∘ (var 0) ⇒* g (step id) (var 0) ∷ wk1d G₁ [ var 0 ] ^ ι ⁰
        D = PE.subst (λ X → Δ₁ ⊢ (lam (wk1 F₁) ▹ wk1d (g (step id) (var 0))) ∘ (var 0) ⇒ X ∷ wk1d G₁ [ var 0 ] ^ ι ⁰) (wkSingleSubstId (g (step id) (var 0)))
          (β-red ⊢F₁′ ⊢g0″ (var ⊢Δ₁ here))
          ⇨ id ⊢g0
        [g0] : Δ₁ ⊩⟨ ι ⁰ ⟩ (lam (wk1 F₁) ▹ wk1d (g (step id) (var 0))) ∘ (var 0) ∷ wk1d G₁ [ var 0 ] ^ [ ! , ι ⁰ ] / [G₁] [ρ₁] ⊢Δ₁ [0]
        [g0] = proj₁ (redSubst*Term D ([G₁] [ρ₁] ⊢Δ₁ [0]) ([g] [ρ₁] ⊢Δ₁ [0]))
        x₀ = escapeEqReflTerm ([G₁] [ρ₁] ⊢Δ₁ [0]) [g0]
        x₁ = PE.subst (λ X → Δ₁ ⊢ (lam (wk1 F₁) ▹ wk1d (g (step id) (var 0))) ∘ (var 0) ≅ (lam (wk1 F₁) ▹ wk1d (g (step id) (var 0))) ∘ (var 0) ∷ X ^ [ ! , ι ⁰ ]) (wkSingleSubstId G₁) x₀
      in ≅-η-eq ⊢F₁ ⊢λg ⊢λg lamₙ lamₙ x₁

    g∘a≡ga : ∀ {ρ Δ a}
      → ([ρ] : ρ Twk.∷ Δ ⊆ Γ)
      → (⊢Δ : ⊢ Δ)
      → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
      → Δ ⊢ wk ρ (lam F₁ ▹ g (step id) (var 0)) ∘ a ⇒* g ρ a ∷ wk (lift ρ) G₁ [ a ] ^ ι ⁰
    g∘a≡ga {ρ} {Δ} {a} [ρ] ⊢Δ [a] =
      let
        ⊢F₁′ = (Twk.wk [ρ] ⊢Δ ⊢F₁)
        -- this lemma is already in ⊢snde′. maybe refactor?
        x₀ : wk (lift ρ) (b (step id) (fst (wk1 e)) (var 0)) [ a ] PE.≡ b ρ (fst (wk ρ e)) a
        x₀ = PE.trans
          (PE.cong (λ X → cast ⁰ (wk (lift ρ) (wk1 F₁) [ a ]) (wk (lift ρ) (wk1 F) [ a ]) X a)
            (PE.trans (PE.cong (λ X → X [ a ]) (wk-Idsym (lift ρ) (Univ rF ⁰) (wk1 F) (wk1 F₁) (fst (wk1 e))))
              (subst-Idsym (sgSubst a) (Univ rF ⁰) (wk (lift ρ) (wk1 F)) (wk (lift ρ) (wk1 F₁)) (fst (wk (lift ρ) (wk1 e))))))
          (PE.cong₃ (λ X Y Z → cast ⁰ Y X (Idsym (Univ rF ⁰) X Y (fst Z)) a) (irrelevant-subst′ ρ F a) (irrelevant-subst′ ρ F₁ a) (irrelevant-subst′ ρ e a))
        x₁ : wk (lift ρ) (g (step id) (var 0)) [ a ] PE.≡ g ρ a
        x₁ = PE.cong₄ (λ X Y Z T → cast ⁰ X Y Z T)
          (PE.trans (cast-subst-lemma6 ρ G _ a) (PE.cong (λ X → wk (lift ρ) G [ X ]) x₀))
          (PE.cong (λ X → wk (lift ρ) X [ a ]) (wkSingleSubstId G₁))
          (PE.cong (λ X → snd X ∘ a) (irrelevant-subst′ ρ e a))
          (PE.cong₂ (λ X Y → X ∘ Y) (irrelevant-subst′ ρ t a) x₀)
        x₂ : Δ ∙ (wk ρ F₁) ^ [ rF , ι ⁰ ] ⊢  wk (lift ρ) (g (step id) (var 0)) ∷ wk (lift ρ) G₁ ^ [ ! , ι ⁰ ]
        x₂ = Twk.wkTerm (Twk.lift [ρ]) (⊢Δ ∙ ⊢F₁′) ⊢g0
      in PE.subst (λ X → Δ ⊢ wk ρ (lam F₁ ▹ g (step id) (var 0)) ∘ a ⇒ X ∷ wk (lift ρ) G₁ [ a ] ^ ι ⁰) x₁
        (β-red ⊢F₁′ x₂ (escapeTerm ([F₁] [ρ] ⊢Δ) [a]))
        ⇨ id (escapeTerm ([G₁] [ρ] ⊢Δ [a]) ([g] [ρ] ⊢Δ [a]))

    [castΠΠ] : Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ∷ B ^ [ ! , ι ⁰ ] / (Πᵣ′ rF ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢B , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)
    [castΠΠ] = ((lam F₁ ▹ g (step id) (var 0)) , Dg , lamₙ , g≡g
        , (λ [ρ] ⊢Δ [a] [a′] [a≡a′] → redSubst*EqTerm (g∘a≡ga [ρ] ⊢Δ [a]) (g∘a≡ga [ρ] ⊢Δ [a′])
             ([G₁] [ρ] ⊢Δ [a]) ([G₁] [ρ] ⊢Δ [a′]) (G₁-ext [ρ] ⊢Δ [a] [a′] [a≡a′])
             ([g] [ρ] ⊢Δ [a]) ([g] [ρ] ⊢Δ [a′]) ([gext] [ρ] ⊢Δ [a] [a′] [a≡a′]))
        , (λ [ρ] ⊢Δ [a] → proj₁ (redSubst*Term (g∘a≡ga [ρ] ⊢Δ [a]) ([G₁] [ρ] ⊢Δ [a]) ([g] [ρ] ⊢Δ [a]))))


module cast-ΠΠ-lemmas-3
       {Γ A₁ A₂ A₃ A₄ F₁ F₂ F₃ F₄ rF G₁ G₂ G₃ G₄ e₁₃ e₂₄ t₁ f₁ t₂ f₂}
       (⊢Γ : ⊢ Γ)

       (⊢A₁ : Γ ⊢ A₁ ^ [ ! , ι ⁰ ])
       (⊢ΠF₁G₁ : Γ ⊢ Π F₁ ^ rF ° ⁰ ▹ G₁ ° ⁰ ^ [ ! , ι ⁰ ])
       (D₁     : Γ ⊢ A₁ ⇒* Π F₁ ^ rF ° ⁰ ▹ G₁ ° ⁰ ^ [ ! , ι ⁰ ])
       (⊢F₁    : Γ ⊢ F₁ ^ [ rF , ι ⁰ ])
       (⊢G₁    : (Γ ∙ F₁ ^ [ rF , ι ⁰ ]) ⊢ G₁ ^ [ ! , ι ⁰ ])
       (A₁≡A₁  : Γ ⊢ (Π F₁ ^ rF ° ⁰ ▹ G₁ ° ⁰) ≅ (Π F₁ ^ rF ° ⁰ ▹ G₁ ° ⁰) ^ [ ! , ι ⁰ ])
       ([F₁] : ∀ {ρ} {Δ} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Δ ⊩⟨ ι ⁰ ⟩ wk ρ F₁ ^ [ rF , ι ⁰ ])
       ([G₁] : ∀ {ρ} {Δ} {a} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷  wk ρ F₁ ^ [ rF , ι ⁰ ] / ([F₁] [ρ] ⊢Δ))
          → (Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₁ [ a ] ^ [ ! , ι ⁰ ]))
       (G₁-ext : ∀ {ρ} {Δ} {a} {b} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷  wk ρ F₁ ^ [ rF , ι ⁰ ] / ([F₁] [ρ] ⊢Δ))
          ([b] : Δ ⊩⟨ ι ⁰ ⟩ b ∷  wk ρ F₁ ^ [ rF , ι ⁰ ] / ([F₁] [ρ] ⊢Δ))
          ([a≡b] : Δ ⊩⟨ ι ⁰ ⟩ a ≡ b ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / ([F₁] [ρ] ⊢Δ))
          → (Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₁ [ a ] ≡ wk (lift ρ) G₁ [ b ] ^ [ ! , ι ⁰ ] / ([G₁] [ρ] ⊢Δ [a])))

       (⊢A₂ : Γ ⊢ A₂ ^ [ ! , ι ⁰ ])
       (⊢ΠF₂G₂ : Γ ⊢ Π F₂ ^ rF ° ⁰ ▹ G₂ ° ⁰ ^ [ ! , ι ⁰ ])
       (D₂     : Γ ⊢ A₂ ⇒* Π F₂ ^ rF ° ⁰ ▹ G₂ ° ⁰ ^ [ ! , ι ⁰ ])
       (⊢F₂    : Γ ⊢ F₂ ^ [ rF , ι ⁰ ])
       (⊢G₂    : (Γ ∙ F₂ ^ [ rF , ι ⁰ ]) ⊢ G₂ ^ [ ! , ι ⁰ ])
       (A₂≡A₂  : Γ ⊢ (Π F₂ ^ rF ° ⁰ ▹ G₂ ° ⁰) ≅ (Π F₂ ^ rF ° ⁰ ▹ G₂ ° ⁰) ^ [ ! , ι ⁰ ])
       ([F₂] : ∀ {ρ} {Δ} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Δ ⊩⟨ ι ⁰ ⟩ wk ρ F₂ ^ [ rF , ι ⁰ ])
       ([G₂] : ∀ {ρ} {Δ} {a} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷  wk ρ F₂ ^ [ rF , ι ⁰ ] / ([F₂] [ρ] ⊢Δ))
          → (Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₂ [ a ] ^ [ ! , ι ⁰ ]))
       (G₂-ext : ∀ {ρ} {Δ} {a} {b} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷  wk ρ F₂ ^ [ rF , ι ⁰ ] / ([F₂] [ρ] ⊢Δ))
          ([b] : Δ ⊩⟨ ι ⁰ ⟩ b ∷  wk ρ F₂ ^ [ rF , ι ⁰ ] / ([F₂] [ρ] ⊢Δ))
          ([a≡b] : Δ ⊩⟨ ι ⁰ ⟩ a ≡ b ∷ wk ρ F₂ ^ [ rF , ι ⁰ ] / ([F₂] [ρ] ⊢Δ))
          → (Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₂ [ a ] ≡ wk (lift ρ) G₂ [ b ] ^ [ ! , ι ⁰ ] / ([G₂] [ρ] ⊢Δ [a])))

       (⊢A₃ : Γ ⊢ A₃ ^ [ ! , ι ⁰ ])
       (⊢ΠF₃G₃ : Γ ⊢ Π F₃ ^ rF ° ⁰ ▹ G₃ ° ⁰ ^ [ ! , ι ⁰ ])
       (D₃     : Γ ⊢ A₃ ⇒* Π F₃ ^ rF ° ⁰ ▹ G₃ ° ⁰ ^ [ ! , ι ⁰ ])
       (⊢F₃    : Γ ⊢ F₃ ^ [ rF , ι ⁰ ])
       (⊢G₃    : (Γ ∙ F₃ ^ [ rF , ι ⁰ ]) ⊢ G₃ ^ [ ! , ι ⁰ ])
       (A₃≡A₃  : Γ ⊢ (Π F₃ ^ rF ° ⁰ ▹ G₃ ° ⁰) ≅ (Π F₃ ^ rF ° ⁰ ▹ G₃ ° ⁰) ^ [ ! , ι ⁰ ])
       ([F₃] : ∀ {ρ} {Δ} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Δ ⊩⟨ ι ⁰ ⟩ wk ρ F₃ ^ [ rF , ι ⁰ ])
       ([G₃] : ∀ {ρ} {Δ} {a} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷  wk ρ F₃ ^ [ rF , ι ⁰ ] / ([F₃] [ρ] ⊢Δ))
          → (Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₃ [ a ] ^ [ ! , ι ⁰ ]))
       (G₃-ext : ∀ {ρ} {Δ} {a} {b} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷  wk ρ F₃ ^ [ rF , ι ⁰ ] / ([F₃] [ρ] ⊢Δ))
          ([b] : Δ ⊩⟨ ι ⁰ ⟩ b ∷  wk ρ F₃ ^ [ rF , ι ⁰ ] / ([F₃] [ρ] ⊢Δ))
          ([a≡b] : Δ ⊩⟨ ι ⁰ ⟩ a ≡ b ∷ wk ρ F₃ ^ [ rF , ι ⁰ ] / ([F₃] [ρ] ⊢Δ))
          → (Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₃ [ a ] ≡ wk (lift ρ) G₃ [ b ] ^ [ ! , ι ⁰ ] / ([G₃] [ρ] ⊢Δ [a])))

       (⊢A₄ : Γ ⊢ A₄ ^ [ ! , ι ⁰ ])
       (⊢ΠF₄G₄ : Γ ⊢ Π F₄ ^ rF ° ⁰ ▹ G₄ ° ⁰ ^ [ ! , ι ⁰ ])
       (D₄     : Γ ⊢ A₄ ⇒* Π F₄ ^ rF ° ⁰ ▹ G₄ ° ⁰ ^ [ ! , ι ⁰ ])
       (⊢F₄    : Γ ⊢ F₄ ^ [ rF , ι ⁰ ])
       (⊢G₄    : (Γ ∙ F₄ ^ [ rF , ι ⁰ ]) ⊢ G₄ ^ [ ! , ι ⁰ ])
       (A₄≡A₄  : Γ ⊢ (Π F₄ ^ rF ° ⁰ ▹ G₄ ° ⁰) ≅ (Π F₄ ^ rF ° ⁰ ▹ G₄ ° ⁰) ^ [ ! , ι ⁰ ])
       ([F₄] : ∀ {ρ} {Δ} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Δ ⊩⟨ ι ⁰ ⟩ wk ρ F₄ ^ [ rF , ι ⁰ ])
       ([G₄] : ∀ {ρ} {Δ} {a} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷  wk ρ F₄ ^ [ rF , ι ⁰ ] / ([F₄] [ρ] ⊢Δ))
          → (Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₄ [ a ] ^ [ ! , ι ⁰ ]))
       (G₄-ext : ∀ {ρ} {Δ} {a} {b} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷  wk ρ F₄ ^ [ rF , ι ⁰ ] / ([F₄] [ρ] ⊢Δ))
          ([b] : Δ ⊩⟨ ι ⁰ ⟩ b ∷  wk ρ F₄ ^ [ rF , ι ⁰ ] / ([F₄] [ρ] ⊢Δ))
          ([a≡b] : Δ ⊩⟨ ι ⁰ ⟩ a ≡ b ∷ wk ρ F₄ ^ [ rF , ι ⁰ ] / ([F₄] [ρ] ⊢Δ))
          → (Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₄ [ a ] ≡ wk (lift ρ) G₄ [ b ] ^ [ ! , ι ⁰ ] / ([G₄] [ρ] ⊢Δ [a])))

       (A₁≡A₂ : Γ ⊢ Π F₁ ^ rF ° ⁰ ▹ G₁ ° ⁰ ≅ Π F₂ ^ rF ° ⁰ ▹ G₂ ° ⁰ ^ [ ! , ι ⁰ ])
       (A₃≡A₄ : Γ ⊢ Π F₃ ^ rF ° ⁰ ▹ G₃ ° ⁰ ≅ Π F₄ ^ rF ° ⁰ ▹ G₄ ° ⁰ ^ [ ! , ι ⁰ ])
       ([F₁≡F₂] : ∀ {ρ Δ} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Δ ⊩⟨ ι ⁰ ⟩ wk ρ F₁ ≡ wk ρ F₂ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
       ([F₃≡F₄] : ∀ {ρ Δ} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Δ ⊩⟨ ι ⁰ ⟩ wk ρ F₃ ≡ wk ρ F₄ ^ [ rF , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
       ([G₁≡G₂] : ∀ {ρ Δ a} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
                  → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
                  → Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₁ [ a ] ≡ wk (lift ρ) G₂ [ a ] ^ [ ! , ι ⁰ ] / [G₁] [ρ] ⊢Δ [a])
       ([G₃≡G₄] : ∀ {ρ Δ a} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
                  → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F₃ ^ [ rF , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
                  → Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₃ [ a ] ≡ wk (lift ρ) G₄ [ a ] ^ [ ! , ι ⁰ ] / [G₃] [ρ] ⊢Δ [a])

       (⊢e₁₃ : Γ ⊢ e₁₃ ∷ Id (U ⁰) A₁ A₃ ^ [ % , ι ¹ ])
       (⊢e₂₄ : Γ ⊢ e₂₄ ∷ Id (U ⁰) A₂ A₄ ^ [ % , ι ¹ ])

       (⊢t₁ : Γ ⊢ t₁ ∷ Π F₁ ^ rF ° ⁰ ▹ G₁ ° ⁰ ^ [ ! , ι ⁰ ])
       (Df₁ : Γ ⊢ t₁ ⇒* f₁ ∷ Π F₁ ^ rF ° ⁰ ▹ G₁ ° ⁰ ^ ι ⁰)
       ([f₁ext] : ∀ {ρ Δ a b} →
                ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
                ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
                ([b] : Δ ⊩⟨ ι ⁰ ⟩ b ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
                ([a≡b] : Δ ⊩⟨ ι ⁰ ⟩ a ≡ b ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
              → Δ ⊩⟨ ι ⁰ ⟩ wk ρ f₁ ∘ a ≡ wk ρ f₁ ∘ b ∷ wk (lift ρ) G₁ [ a ] ^ [ ! , ι ⁰ ] / [G₁] [ρ] ⊢Δ [a])
       ([f₁] : ∀ {ρ Δ a}
              → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
              → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
              → Δ ⊩⟨ ι ⁰ ⟩ wk ρ f₁ ∘ a ∷ wk (lift ρ) G₁ [ a ] ^ [ ! , ι ⁰ ] / [G₁] [ρ] ⊢Δ [a])

       (⊢t₂ : Γ ⊢ t₂ ∷ Π F₂ ^ rF ° ⁰ ▹ G₂ ° ⁰ ^ [ ! , ι ⁰ ])
       (Df₂ : Γ ⊢ t₂ ⇒* f₂ ∷ Π F₂ ^ rF ° ⁰ ▹ G₂ ° ⁰ ^ ι ⁰)
       ([f₂ext] : ∀ {ρ Δ a b} →
                ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
                ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F₂ ^ [ rF , ι ⁰ ] / [F₂] [ρ] ⊢Δ)
                ([b] : Δ ⊩⟨ ι ⁰ ⟩ b ∷ wk ρ F₂ ^ [ rF , ι ⁰ ] / [F₂] [ρ] ⊢Δ)
                ([a≡b] : Δ ⊩⟨ ι ⁰ ⟩ a ≡ b ∷ wk ρ F₂ ^ [ rF , ι ⁰ ] / [F₂] [ρ] ⊢Δ)
              → Δ ⊩⟨ ι ⁰ ⟩ wk ρ f₂ ∘ a ≡ wk ρ f₂ ∘ b ∷ wk (lift ρ) G₂ [ a ] ^ [ ! , ι ⁰ ] / [G₂] [ρ] ⊢Δ [a])
       ([f₂] : ∀ {ρ Δ a}
              → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
              → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F₂ ^ [ rF , ι ⁰ ] / [F₂] [ρ] ⊢Δ)
              → Δ ⊩⟨ ι ⁰ ⟩ wk ρ f₂ ∘ a ∷ wk (lift ρ) G₂ [ a ] ^ [ ! , ι ⁰ ] / [G₂] [ρ] ⊢Δ [a])

       ([f₁≡f₂] : ∀ {ρ Δ a} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
          → Δ ⊩⟨ ι ⁰ ⟩ wk ρ f₁ ∘ a ≡ wk ρ f₂ ∘ a ∷ wk (lift ρ) G₁ [ a ] ^ [ ! , ι ⁰ ] / [G₁] [ρ] ⊢Δ [a])

       (recursor₁ : ∀ {ρ Δ x y t e}
          ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([x] : Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
          ([y] : Δ ⊩⟨ ι ⁰ ⟩ y ∷ wk ρ F₃ ^ [ rF , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
          ([t] : Δ ⊩⟨ ι ⁰ ⟩ t ∷ wk (lift ρ) G₁ [ x ] ^ [ ! , ι ⁰ ] / [G₁] [ρ] ⊢Δ [x])
          (⊢e : Δ ⊢ e ∷ Id (U ⁰) (wk (lift ρ) G₁ [ x ]) (wk (lift ρ) G₃ [ y ]) ^ [ % , ι ¹ ])
          → Δ ⊩⟨ ι ⁰ ⟩ cast ⁰ (wk (lift ρ) G₁ [ x ]) (wk (lift ρ) G₃ [ y ]) e t ∷ wk (lift ρ) G₃ [ y ] ^ [ ! , ι ⁰ ] / [G₃] [ρ] ⊢Δ [y])
       (recursor₂ : ∀ {ρ Δ x y t e}
          ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([x] : Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F₂ ^ [ rF , ι ⁰ ] / [F₂] [ρ] ⊢Δ)
          ([y] : Δ ⊩⟨ ι ⁰ ⟩ y ∷ wk ρ F₄ ^ [ rF , ι ⁰ ] / [F₄] [ρ] ⊢Δ)
          ([t] : Δ ⊩⟨ ι ⁰ ⟩ t ∷ wk (lift ρ) G₂ [ x ] ^ [ ! , ι ⁰ ] / [G₂] [ρ] ⊢Δ [x])
          (⊢e : Δ ⊢ e ∷ Id (U ⁰) (wk (lift ρ) G₂ [ x ]) (wk (lift ρ) G₄ [ y ]) ^ [ % , ι ¹ ])
          → Δ ⊩⟨ ι ⁰ ⟩ cast ⁰ (wk (lift ρ) G₂ [ x ]) (wk (lift ρ) G₄ [ y ]) e t ∷ wk (lift ρ) G₄ [ y ] ^ [ ! , ι ⁰ ] / [G₄] [ρ] ⊢Δ [y])
       (extrecursor₁ : ∀ {ρ Δ x x′ y y′ t t′ e e′}
         → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
         → ([x] : Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
         → ([x′] : Δ ⊩⟨ ι ⁰ ⟩ x′ ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
         → ([x≡x′] : Δ ⊩⟨ ι ⁰ ⟩ x ≡ x′ ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
         → ([y] : Δ ⊩⟨ ι ⁰ ⟩ y ∷ wk ρ F₃ ^ [ rF , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
         → ([y′] : Δ ⊩⟨ ι ⁰ ⟩ y′ ∷ wk ρ F₃ ^ [ rF , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
         → ([y≡y′] : Δ ⊩⟨ ι ⁰ ⟩ y ≡ y′ ∷ wk ρ F₃ ^ [ rF , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
         → ([t] : Δ ⊩⟨ ι ⁰ ⟩ t ∷ wk (lift ρ) G₁ [ x ] ^ [ ! , ι ⁰ ] / [G₁] [ρ] ⊢Δ [x])
         → ([t′] : Δ ⊩⟨ ι ⁰ ⟩ t′ ∷ wk (lift ρ) G₁ [ x′ ] ^ [ ! , ι ⁰ ] / [G₁] [ρ] ⊢Δ [x′])
         → ([t≡t′] : Δ ⊩⟨ ι ⁰ ⟩ t ≡ t′ ∷ wk (lift ρ) G₁ [ x ] ^ [ ! , ι ⁰ ] / [G₁] [ρ] ⊢Δ [x])
         → (⊢e : Δ ⊢ e ∷ Id (U ⁰) (wk (lift ρ) G₁ [ x ]) (wk (lift ρ) G₃ [ y ]) ^ [ % , ι ¹ ])
         → (⊢e′ : Δ ⊢ e′ ∷ Id (U ⁰) (wk (lift ρ) G₁ [ x′ ]) (wk (lift ρ) G₃ [ y′ ]) ^ [ % , ι ¹ ])
         → Δ ⊩⟨ ι ⁰ ⟩ cast ⁰ (wk (lift ρ) G₁ [ x ]) (wk (lift ρ) G₃ [ y ]) e t ≡ cast ⁰ (wk (lift ρ) G₁ [ x′ ]) (wk (lift ρ) G₃ [ y′ ]) e′ t′ ∷ wk (lift ρ) G₃ [ y ] ^ [ ! , ι ⁰ ] / [G₃] [ρ] ⊢Δ [y])
       (extrecursor₂ : ∀ {ρ Δ x x′ y y′ t t′ e e′}
         → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
         → ([x] : Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F₂ ^ [ rF , ι ⁰ ] / [F₂] [ρ] ⊢Δ)
         → ([x′] : Δ ⊩⟨ ι ⁰ ⟩ x′ ∷ wk ρ F₂ ^ [ rF , ι ⁰ ] / [F₂] [ρ] ⊢Δ)
         → ([x≡x′] : Δ ⊩⟨ ι ⁰ ⟩ x ≡ x′ ∷ wk ρ F₂ ^ [ rF , ι ⁰ ] / [F₂] [ρ] ⊢Δ)
         → ([y] : Δ ⊩⟨ ι ⁰ ⟩ y ∷ wk ρ F₄ ^ [ rF , ι ⁰ ] / [F₄] [ρ] ⊢Δ)
         → ([y′] : Δ ⊩⟨ ι ⁰ ⟩ y′ ∷ wk ρ F₄ ^ [ rF , ι ⁰ ] / [F₄] [ρ] ⊢Δ)
         → ([y≡y′] : Δ ⊩⟨ ι ⁰ ⟩ y ≡ y′ ∷ wk ρ F₄ ^ [ rF , ι ⁰ ] / [F₄] [ρ] ⊢Δ)
         → ([t] : Δ ⊩⟨ ι ⁰ ⟩ t ∷ wk (lift ρ) G₂ [ x ] ^ [ ! , ι ⁰ ] / [G₂] [ρ] ⊢Δ [x])
         → ([t′] : Δ ⊩⟨ ι ⁰ ⟩ t′ ∷ wk (lift ρ) G₂ [ x′ ] ^ [ ! , ι ⁰ ] / [G₂] [ρ] ⊢Δ [x′])
         → ([t≡t′] : Δ ⊩⟨ ι ⁰ ⟩ t ≡ t′ ∷ wk (lift ρ) G₂ [ x ] ^ [ ! , ι ⁰ ] / [G₂] [ρ] ⊢Δ [x])
         → (⊢e : Δ ⊢ e ∷ Id (U ⁰) (wk (lift ρ) G₂ [ x ]) (wk (lift ρ) G₄ [ y ]) ^ [ % , ι ¹ ])
         → (⊢e′ : Δ ⊢ e′ ∷ Id (U ⁰) (wk (lift ρ) G₂ [ x′ ]) (wk (lift ρ) G₄ [ y′ ]) ^ [ % , ι ¹ ])
         → Δ ⊩⟨ ι ⁰ ⟩ cast ⁰ (wk (lift ρ) G₂ [ x ]) (wk (lift ρ) G₄ [ y ]) e t ≡ cast ⁰ (wk (lift ρ) G₂ [ x′ ]) (wk (lift ρ) G₄ [ y′ ]) e′ t′ ∷ wk (lift ρ) G₄ [ y ] ^ [ ! , ι ⁰ ] / [G₄] [ρ] ⊢Δ [y])
       (eqrecursor : ∀ {ρ Δ x₁ x₂ x₃ x₄ t₁ t₂ e₁₃ e₂₄}
         → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
         → ([x₁] : Δ ⊩⟨ ι ⁰ ⟩ x₁ ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
         → ([x₂] : Δ ⊩⟨ ι ⁰ ⟩ x₂ ∷ wk ρ F₂ ^ [ rF , ι ⁰ ] / [F₂] [ρ] ⊢Δ)
         → ([G₁x₁≡G₂x₂] : Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₁ [ x₁ ] ≡ wk (lift ρ) G₂ [ x₂ ] ^ [ ! , ι ⁰ ] / [G₁] [ρ] ⊢Δ [x₁])
         → ([x₃] : Δ ⊩⟨ ι ⁰ ⟩ x₃ ∷ wk ρ F₃ ^ [ rF , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
         → ([x₄] : Δ ⊩⟨ ι ⁰ ⟩ x₄ ∷ wk ρ F₄ ^ [ rF , ι ⁰ ] / [F₄] [ρ] ⊢Δ)
         → ([G₃x₃≡G₄x₄] : Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₃ [ x₃ ] ≡ wk (lift ρ) G₄ [ x₄ ] ^ [ ! , ι ⁰ ] / [G₃] [ρ] ⊢Δ [x₃])
         → ([t₁] : Δ ⊩⟨ ι ⁰ ⟩ t₁ ∷ wk (lift ρ) G₁ [ x₁ ] ^ [ ! , ι ⁰ ] / [G₁] [ρ] ⊢Δ [x₁])
         → ([t₂] : Δ ⊩⟨ ι ⁰ ⟩ t₂ ∷ wk (lift ρ) G₂ [ x₂ ] ^ [ ! , ι ⁰ ] / [G₂] [ρ] ⊢Δ [x₂])
         → ([t₁≡t₂] : Δ ⊩⟨ ι ⁰ ⟩ t₁ ≡ t₂ ∷ wk (lift ρ) G₁ [ x₁ ] ^ [ ! , ι ⁰ ] / [G₁] [ρ] ⊢Δ [x₁])
         → (⊢e₁₃ : Δ ⊢ e₁₃ ∷ Id (U ⁰) (wk (lift ρ) G₁ [ x₁ ]) (wk (lift ρ) G₃ [ x₃ ]) ^ [ % , ι ¹ ])
         → (⊢e₂₄ : Δ ⊢ e₂₄ ∷ Id (U ⁰) (wk (lift ρ) G₂ [ x₂ ]) (wk (lift ρ) G₄ [ x₄ ]) ^ [ % , ι ¹ ])
         → Δ ⊩⟨ ι ⁰ ⟩ cast ⁰ (wk (lift ρ) G₁ [ x₁ ]) (wk (lift ρ) G₃ [ x₃ ]) e₁₃ t₁ ≡ cast ⁰ (wk (lift ρ) G₂ [ x₂ ]) (wk (lift ρ) G₄ [ x₄ ]) e₂₄ t₂ ∷ wk (lift ρ) G₃ [ x₃ ] ^ [ ! , ι ⁰ ] / [G₃] [ρ] ⊢Δ [x₃])

       ([b₁] : ∀ {ρ Δ e x}
                ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
                (⊢e : Δ ⊢ e ∷ Id (Univ rF ⁰) (wk ρ F₁) (wk ρ F₃) ^ [ % , ι ¹ ])
                ([x] : Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F₃ ^ [ rF , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
                → Δ ⊩⟨ ι ⁰ ⟩ cast ⁰ (wk ρ F₃) (wk ρ F₁) (Idsym (Univ rF ⁰) (wk ρ F₁) (wk ρ F₃) e) x ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
       ([bext₁] : ∀ {ρ Δ e e′ x y} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
           → (Δ ⊢ e ∷ Id (Univ rF ⁰) (wk ρ F₁) (wk ρ F₃) ^ [ % , ι ¹ ])
           → (Δ ⊢ e′ ∷ Id (Univ rF ⁰) (wk ρ F₁) (wk ρ F₃) ^ [ % , ι ¹ ])
           → (Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F₃ ^ [ rF , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
           → (Δ ⊩⟨ ι ⁰ ⟩ y ∷ wk ρ F₃ ^ [ rF , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
           → (Δ ⊩⟨ ι ⁰ ⟩ x ≡ y ∷ wk ρ F₃ ^ [ rF , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
           → Δ ⊩⟨ ι ⁰ ⟩ cast ⁰ (wk ρ F₃) (wk ρ F₁) (Idsym (Univ rF ⁰) (wk ρ F₁) (wk ρ F₃) e) x
             ≡ cast ⁰ (wk ρ F₃) (wk ρ F₁) (Idsym (Univ rF ⁰) (wk ρ F₁) (wk ρ F₃) e′) y ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
       ([b₂] : ∀ {ρ Δ e x}
                ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
                (⊢e : Δ ⊢ e ∷ Id (Univ rF ⁰) (wk ρ F₂) (wk ρ F₄) ^ [ % , ι ¹ ])
                ([x] : Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F₄ ^ [ rF , ι ⁰ ] / [F₄] [ρ] ⊢Δ)
                → Δ ⊩⟨ ι ⁰ ⟩ cast ⁰ (wk ρ F₄) (wk ρ F₂) (Idsym (Univ rF ⁰) (wk ρ F₂) (wk ρ F₄) e) x ∷ wk ρ F₂ ^ [ rF , ι ⁰ ] / [F₂] [ρ] ⊢Δ)
       ([bext₂] : ∀ {ρ Δ e e′ x y} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
           → (Δ ⊢ e ∷ Id (Univ rF ⁰) (wk ρ F₂) (wk ρ F₄) ^ [ % , ι ¹ ])
           → (Δ ⊢ e′ ∷ Id (Univ rF ⁰) (wk ρ F₂) (wk ρ F₄) ^ [ % , ι ¹ ])
           → (Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F₄ ^ [ rF , ι ⁰ ] / [F₄] [ρ] ⊢Δ)
           → (Δ ⊩⟨ ι ⁰ ⟩ y ∷ wk ρ F₄ ^ [ rF , ι ⁰ ] / [F₄] [ρ] ⊢Δ)
           → (Δ ⊩⟨ ι ⁰ ⟩ x ≡ y ∷ wk ρ F₄ ^ [ rF , ι ⁰ ] / [F₄] [ρ] ⊢Δ)
           → Δ ⊩⟨ ι ⁰ ⟩ cast ⁰ (wk ρ F₄) (wk ρ F₂) (Idsym (Univ rF ⁰) (wk ρ F₂) (wk ρ F₄) e) x
             ≡ cast ⁰ (wk ρ F₄) (wk ρ F₂) (Idsym (Univ rF ⁰) (wk ρ F₂) (wk ρ F₄) e′) y ∷ wk ρ F₂ ^ [ rF , ι ⁰ ] / [F₂] [ρ] ⊢Δ)
       ([b₁≡b₂] : ∀ {ρ Δ e₁₃ e₂₄ x₃ x₄} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
            → (Δ ⊢ e₁₃ ∷ Id (Univ rF ⁰) (wk ρ F₁) (wk ρ F₃) ^ [ % , ι ¹ ])
            → (Δ ⊢ e₂₄ ∷ Id (Univ rF ⁰) (wk ρ F₂) (wk ρ F₄) ^ [ % , ι ¹ ])
            → (Δ ⊩⟨ ι ⁰ ⟩ x₃ ∷ wk ρ F₃ ^ [ rF , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
            → (Δ ⊩⟨ ι ⁰ ⟩ x₄ ∷ wk ρ F₄ ^ [ rF , ι ⁰ ] / [F₄] [ρ] ⊢Δ)
            → (Δ ⊩⟨ ι ⁰ ⟩ x₃ ≡ x₄ ∷ wk ρ F₃ ^ [ rF , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
            → Δ ⊩⟨ ι ⁰ ⟩ cast ⁰ (wk ρ F₃) (wk ρ F₁) (Idsym (Univ rF ⁰) (wk ρ F₁) (wk ρ F₃) e₁₃) x₃
              ≡ cast ⁰ (wk ρ F₄) (wk ρ F₂) (Idsym (Univ rF ⁰) (wk ρ F₂) (wk ρ F₄) e₂₄) x₄ ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)

  where
    module g₁ = cast-ΠΠ-lemmas-2 ⊢Γ ⊢A₁ ⊢ΠF₁G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext ⊢A₃ ⊢ΠF₃G₃ D₃ ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext ⊢e₁₃
                          recursor₁ extrecursor₁ ⊢t₁ Df₁ [f₁ext] [f₁] [b₁] [bext₁]
    module g₂ = cast-ΠΠ-lemmas-2 ⊢Γ ⊢A₂ ⊢ΠF₂G₂ D₂ ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext ⊢A₄ ⊢ΠF₄G₄ D₄ ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext ⊢e₂₄
                          recursor₂ extrecursor₂ ⊢t₂ Df₂ [f₂ext] [f₂] [b₂] [bext₂]

    [g₁≡g₂] : ∀ {ρ Δ x₃ x₄} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
        → ([x₃] : Δ ⊩⟨ ι ⁰ ⟩ x₃ ∷ wk ρ F₃ ^ [ rF , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
        → ([x₄] : Δ ⊩⟨ ι ⁰ ⟩ x₄ ∷ wk ρ F₄ ^ [ rF , ι ⁰ ] / [F₄] [ρ] ⊢Δ)
        → ([x₃≡x₄] : Δ ⊩⟨ ι ⁰ ⟩ x₃ ≡ x₄ ∷ wk ρ F₃ ^ [ rF , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
        → Δ ⊩⟨ ι ⁰ ⟩ g₁.g ρ x₃ ≡ g₂.g ρ x₄ ∷ wk (lift ρ) G₃ [ x₃ ] ^ [ ! , ι ⁰ ] / [G₃] [ρ] ⊢Δ [x₃]
    [g₁≡g₂] {ρ} {Δ} {x₃} {x₄} [ρ] ⊢Δ [x₃] [x₄] [x₃≡x₄] =
      let
        [b₁] = [b₁] [ρ] ⊢Δ (Twk.wkTerm [ρ] ⊢Δ g₁.⊢fste) [x₃]
        [b₂] = [b₂] [ρ] ⊢Δ (Twk.wkTerm [ρ] ⊢Δ g₂.⊢fste) [x₄]
        [b₁≡b₂]′ = [b₁≡b₂] [ρ] ⊢Δ (Twk.wkTerm [ρ] ⊢Δ g₁.⊢fste) (Twk.wkTerm [ρ] ⊢Δ g₂.⊢fste) [x₃] [x₄] [x₃≡x₄]
        [b₁:F₂] = convTerm₁ ([F₁] [ρ] ⊢Δ) ([F₂] [ρ] ⊢Δ) ([F₁≡F₂] [ρ] ⊢Δ) [b₁]
        [b₁≡b₂:F₂] = convEqTerm₁ ([F₁] [ρ] ⊢Δ) ([F₂] [ρ] ⊢Δ) ([F₁≡F₂] [ρ] ⊢Δ) [b₁≡b₂]′
        [G₁b₁≡G₂b₂] = transEq ([G₁] [ρ] ⊢Δ [b₁]) ([G₂] [ρ] ⊢Δ [b₁:F₂]) ([G₂] [ρ] ⊢Δ [b₂])
          ([G₁≡G₂] [ρ] ⊢Δ [b₁]) (G₂-ext [ρ] ⊢Δ [b₁:F₂] [b₂] [b₁≡b₂:F₂])
        [x₃:F₄] = convTerm₁ ([F₃] [ρ] ⊢Δ) ([F₄] [ρ] ⊢Δ) ([F₃≡F₄] [ρ] ⊢Δ) [x₃]
        [x₃≡x₄:F₄] = convEqTerm₁ ([F₃] [ρ] ⊢Δ) ([F₄] [ρ] ⊢Δ) ([F₃≡F₄] [ρ] ⊢Δ) [x₃≡x₄]
        [G₃x₃≡G₄x₄] = transEq ([G₃] [ρ] ⊢Δ [x₃]) ([G₄] [ρ] ⊢Δ [x₃:F₄]) ([G₄] [ρ] ⊢Δ [x₄])
          ([G₃≡G₄] [ρ] ⊢Δ [x₃]) (G₄-ext [ρ] ⊢Δ [x₃:F₄] [x₄] [x₃≡x₄:F₄])
        [t₁] , [t₁≡f₁b₁] = redSubst*Term (appRed* (escapeTerm ([F₁] [ρ] ⊢Δ) [b₁]) (Twk.wkRed*Term [ρ] ⊢Δ Df₁))
          ([G₁] [ρ] ⊢Δ [b₁]) ([f₁] [ρ] ⊢Δ [b₁])
        [t₂] , [t₂≡f₂b₂] = redSubst*Term (appRed* (escapeTerm ([F₂] [ρ] ⊢Δ) [b₂]) (Twk.wkRed*Term [ρ] ⊢Δ Df₂))
          ([G₂] [ρ] ⊢Δ [b₂]) ([f₂] [ρ] ⊢Δ [b₂])
        [t₁≡f₂b₁] = transEqTerm ([G₁] [ρ] ⊢Δ [b₁]) [t₁≡f₁b₁] ([f₁≡f₂] [ρ] ⊢Δ [b₁])
        [f₂b₁≡t₂] = symEqTerm ([G₂] [ρ] ⊢Δ [b₂]) (transEqTerm ([G₂] [ρ] ⊢Δ [b₂]) [t₂≡f₂b₂] ([f₂ext] [ρ] ⊢Δ [b₂] [b₁:F₂] (symEqTerm ([F₂] [ρ] ⊢Δ) [b₁≡b₂:F₂])))
        [t₁≡t₂] = transEqTerm ([G₁] [ρ] ⊢Δ [b₁]) [t₁≡f₂b₁] (convEqTerm₂ ([G₁] [ρ] ⊢Δ [b₁]) ([G₂] [ρ] ⊢Δ [b₂]) [G₁b₁≡G₂b₂] [f₂b₁≡t₂])
        x = eqrecursor [ρ] ⊢Δ [b₁] [b₂] [G₁b₁≡G₂b₂] [x₃] [x₄] [G₃x₃≡G₄x₄] [t₁] [t₂] [t₁≡t₂]
                       (g₁.⊢snde′ [ρ] ⊢Δ (escapeTerm ([F₃] [ρ] ⊢Δ) [x₃])) (g₂.⊢snde′ [ρ] ⊢Δ (escapeTerm ([F₄] [ρ] ⊢Δ) [x₄]))
      in x

    g₁≡g₂ : Γ ⊢ (lam F₃ ▹ g₁.g (step id) (var 0)) ≅ (lam F₄ ▹ g₂.g (step id) (var 0)) ∷ Π F₃ ^ rF ° ⁰ ▹ G₃ ° ⁰ ^ [ ! , ι ⁰ ]
    g₁≡g₂ =
      let
        Δ₁ = g₁.Δ₁
        ⊢Δ₁ = g₁.⊢Δ₁
        [ρ₁] = g₁.[ρ₁]
        ⊢F₃′ = Twk.wk (Twk.step Twk.id) ⊢Δ₁ ⊢F₃
        ⊢g₁0 = escapeTerm ([G₃] [ρ₁] ⊢Δ₁ g₁.[0]) (g₁.[g] [ρ₁] ⊢Δ₁ g₁.[0])
        ⊢g₁0′ = (PE.subst (λ X → Δ₁ ⊢ g₁.g (step id) (var 0) ∷ X ^ [ ! , ι ⁰ ]) (wkSingleSubstId G₃) ⊢g₁0)
        ⊢g₁0″ = Twk.wkTerm (Twk.lift (Twk.step Twk.id)) (⊢Δ₁ ∙ ⊢F₃′) ⊢g₁0′
        ⊢F₄′ = Twk.wk (Twk.step Twk.id) ⊢Δ₁ ⊢F₄
        ⊢g₂0 = escapeTerm ([G₄] g₂.[ρ₁] g₂.⊢Δ₁ g₂.[0]) (g₂.[g] g₂.[ρ₁] g₂.⊢Δ₁ g₂.[0])
        ⊢g₂0′ = (PE.subst (λ X → g₂.Δ₁ ⊢ g₂.g (step id) (var 0) ∷ X ^ [ ! , ι ⁰ ]) (wkSingleSubstId G₄) ⊢g₂0)
        ⊢g₂0″ = Twk.wkTerm (Twk.lift (Twk.step Twk.id)) (⊢Δ₁ ∙ ⊢F₄′) ⊢g₂0′
        D₁ : Δ₁ ⊢ (lam (wk1 F₃) ▹ wk1d (g₁.g (step id) (var 0))) ∘ (var 0) ⇒* g₁.g (step id) (var 0) ∷ wk1d G₃ [ var 0 ] ^ ι ⁰
        D₁ = PE.subst (λ X → Δ₁ ⊢ (lam (wk1 F₃) ▹ wk1d (g₁.g (step id) (var 0))) ∘ (var 0) ⇒ X ∷ wk1d G₃ [ var 0 ] ^ ι ⁰)
          (wkSingleSubstId (g₁.g (step id) (var 0))) (β-red ⊢F₃′ ⊢g₁0″ (var ⊢Δ₁ here))
          ⇨ id ⊢g₁0
        F₃≡F₄ = escapeEq ([F₃] [ρ₁] ⊢Δ₁) ([F₃≡F₄] [ρ₁] ⊢Δ₁)
        [0:F₄] : Δ₁ ⊩⟨ ι ⁰ ⟩ var 0 ∷ wk (step id) F₄ ^ [ rF , ι ⁰ ] / [F₄] [ρ₁] ⊢Δ₁
        [0:F₄] = neuTerm ([F₄] [ρ₁] ⊢Δ₁) (var 0) (conv (var ⊢Δ₁ here) (≅-eq F₃≡F₄)) (~-var (conv (var ⊢Δ₁ here) (≅-eq F₃≡F₄)))
        D₂ : Δ₁ ⊢ (lam (wk1 F₄) ▹ wk1d (g₂.g (step id) (var 0))) ∘ (var 0) ⇒* g₂.g (step id) (var 0) ∷ wk1d G₄ [ var 0 ] ^ ι ⁰
        D₂ = PE.subst (λ X → Δ₁ ⊢ (lam (wk1 F₄) ▹ wk1d (g₂.g (step id) (var 0))) ∘ (var 0) ⇒ X ∷ wk1d G₄ [ var 0 ] ^ ι ⁰)
          (wkSingleSubstId (g₂.g (step id) (var 0))) (β-red ⊢F₄′ ⊢g₂0″ (conv (var ⊢Δ₁ here) (≅-eq F₃≡F₄)))
          ⇨ id (escapeTerm ([G₄] [ρ₁] ⊢Δ₁ [0:F₄]) (g₂.[g] [ρ₁] ⊢Δ₁ [0:F₄]))
        [g₁0≡g₁] : Δ₁ ⊩⟨ ι ⁰ ⟩ (lam (wk1 F₃) ▹ wk1d (g₁.g (step id) (var 0))) ∘ (var 0) ≡ g₁.g (step id) (var 0) ∷ wk1d G₃ [ var 0 ] ^ [ ! , ι ⁰ ] / [G₃] [ρ₁] ⊢Δ₁ g₁.[0]
        [g₁0≡g₁] = proj₂ (redSubst*Term D₁ ([G₃] [ρ₁] ⊢Δ₁ g₁.[0]) (g₁.[g] [ρ₁] ⊢Δ₁ g₁.[0]))
        [g₂0≡g₂] : Δ₁ ⊩⟨ ι ⁰ ⟩ (lam (wk1 F₄) ▹ wk1d (g₂.g (step id) (var 0))) ∘ (var 0) ≡ g₂.g (step id) (var 0) ∷ wk1d G₄ [ var 0 ] ^ [ ! , ι ⁰ ] / [G₄] [ρ₁] ⊢Δ₁ [0:F₄]
        [g₂0≡g₂] = proj₂ (redSubst*Term D₂ ([G₄] [ρ₁] ⊢Δ₁ [0:F₄]) (g₂.[g] [ρ₁] ⊢Δ₁ [0:F₄]))
        [g₁≡g₂]′ : Δ₁ ⊩⟨ ι ⁰ ⟩ g₁.g (step id) (var 0) ≡ g₂.g (step id) (var 0) ∷ wk1d G₃ [ var 0 ] ^ [ ! , ι ⁰ ] / [G₃] [ρ₁] ⊢Δ₁ g₁.[0]
        [g₁≡g₂]′ = [g₁≡g₂] [ρ₁] ⊢Δ₁ g₁.[0] (convTerm₁ ([F₃] [ρ₁] ⊢Δ₁) ([F₄] [ρ₁] ⊢Δ₁) ([F₃≡F₄] [ρ₁] ⊢Δ₁) g₁.[0]) (reflEqTerm ([F₃] [ρ₁] ⊢Δ₁) g₁.[0])
        [g₁0≡g₂0] = transEqTerm ([G₃] [ρ₁] ⊢Δ₁ g₁.[0]) (transEqTerm ([G₃] [ρ₁] ⊢Δ₁ g₁.[0]) [g₁0≡g₁] [g₁≡g₂]′)
          (convEqTerm₂ ([G₃] [ρ₁] ⊢Δ₁ g₁.[0]) ([G₄] [ρ₁] ⊢Δ₁ [0:F₄]) ([G₃≡G₄] [ρ₁] ⊢Δ₁ g₁.[0]) (symEqTerm ([G₄] [ρ₁] ⊢Δ₁ [0:F₄]) [g₂0≡g₂]))
        x₀ = escapeTermEq ([G₃] [ρ₁] ⊢Δ₁ g₁.[0]) [g₁0≡g₂0]
        x₁ = PE.subst (λ X → Δ₁ ⊢ (lam (wk1 F₃) ▹ wk1d (g₁.g (step id) (var 0))) ∘ (var 0) ≅ (lam (wk1 F₄) ▹ wk1d (g₂.g (step id) (var 0))) ∘ (var 0) ∷ X ^ [ ! , ι ⁰ ]) (wkSingleSubstId G₃) x₀
      in ≅-η-eq ⊢F₃ g₁.⊢λg (conv g₂.⊢λg (sym (≅-eq A₃≡A₄))) lamₙ lamₙ x₁

    [g₁a≡g₂a] : ∀ {ρ Δ a} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
        → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F₃ ^ [ rF , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
        → (Δ ⊩⟨ ι ⁰ ⟩ wk ρ (lam F₃ ▹ g₁.g (step id) (var 0)) ∘ a ≡ wk ρ (lam F₄ ▹ g₂.g (step id) (var 0)) ∘ a
            ∷ wk (lift ρ) G₃ [ a ] ^ [ ! , ι ⁰ ] / [G₃] [ρ] ⊢Δ [a])
    [g₁a≡g₂a] [ρ] ⊢Δ [a] =
      let
        [a]′ = convTerm₁ ([F₃] [ρ] ⊢Δ) ([F₄] [ρ] ⊢Δ) ([F₃≡F₄] [ρ] ⊢Δ) [a]
        [a≡a] = reflEqTerm ([F₃] [ρ] ⊢Δ) [a]
      in redSubst*EqTerm (g₁.g∘a≡ga [ρ] ⊢Δ [a]) (g₂.g∘a≡ga [ρ] ⊢Δ [a]′)
         ([G₃] [ρ] ⊢Δ [a]) ([G₄] [ρ] ⊢Δ [a]′) ([G₃≡G₄] [ρ] ⊢Δ [a])
         (g₁.[g] [ρ] ⊢Δ [a]) (g₂.[g] [ρ] ⊢Δ [a]′) ([g₁≡g₂] [ρ] ⊢Δ [a] [a]′ [a≡a])
