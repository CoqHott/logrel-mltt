{-# OPTIONS --allow-unsolved-metas #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Idlemmas {{eqrel : EqRelSet}} where
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
open import Definition.LogicalRelation.Substitution.MaybeEmbed
open import Definition.LogicalRelation.Substitution.Introductions.Cast
-- open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Definition.LogicalRelation.Substitution.Introductions.Universe

open import Tools.Product
open import Tools.Empty
import Tools.Unit as TU
import Tools.PropositionalEquality as PE
import Data.Nat as Nat


[proj₁cast] : ∀ {A B Γ r}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ r , ι ⁰ ])
         ([B] : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ r , ι ⁰ ])
       → (∀ {t e} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ r , ι ⁰ ] / [A]) → (⊢e : Γ ⊢ e ∷ Id (Univ r ⁰) A B ^ [ % , ι ¹ ]) → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ∷ B ^ [ r , ι ⁰ ] / [B])
[proj₁cast] ⊢Γ [A] [B] = proj₁ ([cast] ⊢Γ [A] [B])

[proj₁castext] : ∀ {A A′ B B′ Γ r}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ r , ι ⁰ ])
         ([A′] : Γ ⊩⟨ ι ⁰ ⟩ A′ ^ [ r , ι ⁰ ])
         ([A≡A′] : Γ ⊩⟨ ι ⁰ ⟩ A ≡ A′ ^ [ r , ι ⁰ ] / [A])
         ([B] : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ r , ι ⁰ ])
         ([B′] : Γ ⊩⟨ ι ⁰ ⟩ B′ ^ [ r , ι ⁰ ])
         ([B≡B′] : Γ ⊩⟨ ι ⁰ ⟩ B ≡ B′ ^ [ r , ι ⁰ ] / [B])
       → (∀ {t t′ e e′} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ r , ι ⁰ ] / [A])
                        → ([t′] : Γ ⊩⟨ ι ⁰ ⟩ t′ ∷ A′ ^ [ r , ι ⁰ ] / [A′])
                        → ([t≡t′] : Γ ⊩⟨ ι ⁰ ⟩ t ≡ t′ ∷ A ^ [ r , ι ⁰ ] / [A])
                        → (⊢e : Γ ⊢ e ∷ Id (Univ r ⁰) A B ^ [ % , ι ¹ ])
                        → (⊢e′ : Γ ⊢ e′ ∷ Id (Univ r ⁰) A′ B′ ^ [ % , ι ¹ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ≡ cast ⁰ A′ B′ e′ t′ ∷ B ^ [ r , ι ⁰ ] / [B])
[proj₁castext] ⊢Γ [A] [A′] [A≡A′] [B] [B′] [B≡B′] = proj₁ ([castext] ⊢Γ [A] [A′] [A≡A′] [B] [B′] [B≡B′])


[nondep] : ∀ {Γ A B l} → Γ ⊩⟨ l ⟩ B ^ [ % , l ]
  → ([A] : ∀ {ρ} {Δ} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ) → Δ ⊩⟨ l ⟩ wk ρ A ^ [ % , l ])
  → ∀ {ρ} {Δ} {a} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ)
  → ([a] : Δ ⊩⟨ l ⟩ a ∷ wk ρ A ^ [ % , l ] / [A] [ρ] ⊢Δ)
  → Δ ⊩⟨ l ⟩ wk (lift ρ) (wk1 B) [ a ] ^ [ % , l ]
[nondep] {Γ} {A} {B} {l} [B] [A] {ρ} {Δ} {a} [ρ] ⊢Δ [a] = PE.subst (λ X → Δ ⊩⟨ l ⟩ X ^ [ % , l ]) (Id-subst-lemma ρ B a) (Lwk.wk [ρ] ⊢Δ [B])

[nondepext] : ∀ {Γ A B l} → ([B] : Γ ⊩⟨ l ⟩ B ^ [ % , l ])
  → ([A] : ∀ {ρ} {Δ} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ) → Δ ⊩⟨ l ⟩ wk ρ A ^ [ % , l ])
  → ∀ {ρ} {Δ} {a} {b} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ)
  → ([a] : Δ ⊩⟨ l ⟩ a ∷ wk ρ A ^ [ % , l ] / [A] [ρ] ⊢Δ)
  → ([b] : Δ ⊩⟨ l ⟩ b ∷ wk ρ A ^ [ % , l ] / [A] [ρ] ⊢Δ)
  → ([a≡b] : Δ ⊩⟨ l ⟩ a ≡ b ∷ wk ρ A ^ [ % , l ] / [A] [ρ] ⊢Δ)
  → Δ ⊩⟨ l ⟩ wk (lift ρ) (wk1 B) [ a ] ≡ wk (lift ρ) (wk1 B) [ b ] ^ [ % , l ] / [nondep] [B] [A] [ρ] ⊢Δ [a]
[nondepext] {Γ} {A} {B} {l} [B] [A] {ρ} {Δ} {a} {b} [ρ] ⊢Δ [a] [b] [a≡b] =
  irrelevanceEq″ (Id-subst-lemma ρ B a) (Id-subst-lemma ρ B b) PE.refl PE.refl
    (Lwk.wk [ρ] ⊢Δ [B]) ([nondep] [B] [A] [ρ] ⊢Δ [a]) (reflEq (Lwk.wk [ρ] ⊢Δ [B]))

[nondepext'] : ∀ {Γ A A' B B' l}
  → ([B] : Γ ⊩⟨ l ⟩ B ^ [ % , l ])
  → ([B'] : Γ ⊩⟨ l ⟩ B' ^ [ % , l ])
  → ([B≡B'] : Γ ⊩⟨ l ⟩ B ≡ B' ^ [ % , l ] / [B])
  → ([A] : ∀ {ρ} {Δ} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ) → Δ ⊩⟨ l ⟩ wk ρ A ^ [ % , l ])
  → ([A'] : ∀ {ρ} {Δ} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ) → Δ ⊩⟨ l ⟩ wk ρ A' ^ [ % , l ])
  → ∀ {ρ} {Δ} {a} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ)
  → ([a] : Δ ⊩⟨ l ⟩ a ∷ wk ρ A ^ [ % , l ] / [A] [ρ] ⊢Δ)
  → Δ ⊩⟨ l ⟩ wk (lift ρ) (wk1 B) [ a ] ≡ wk (lift ρ) (wk1 B') [ a ] ^ [ % , l ] / [nondep] [B] [A] [ρ] ⊢Δ [a]
[nondepext'] {Γ} {A} {A'} {B} {B'} {l} [B] [B'] [B≡B'] [A] [A'] {ρ} {Δ} {a} [ρ] ⊢Δ [a] =
  irrelevanceEq″ (Id-subst-lemma ρ B a) (Id-subst-lemma ρ B' a) PE.refl PE.refl
    (Lwk.wk [ρ] ⊢Δ [B]) ([nondep] [B] [A] [ρ] ⊢Δ [a]) (Lwk.wkEq [ρ] ⊢Δ [B] [B≡B'])

module IdTypeU-lemmas
       {Γ rF A B F G F₁ G₁}
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
       (B≡B  : Γ ⊢ (Π F₁ ^ rF ° ⁰ ▹ G₁ ° ⁰) ≅ (Π F₁ ^ rF ° ⁰ ▹ G₁ ° ⁰) ^ [ ! , ι ⁰ ])
       ([F₁] : ∀ {ρ} {Δ} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Δ ⊩⟨ ι ⁰ ⟩ wk ρ F₁ ^ [ rF , ι ⁰ ])
       ([G₁] : ∀ {ρ} {Δ} {a} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷  wk ρ F₁ ^ [ rF , ι ⁰ ] / ([F₁] [ρ] ⊢Δ))
          → (Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₁ [ a ] ^ [ ! , ι ⁰ ]))
       (G₁-ext : ∀ {ρ} {Δ} {a} {b} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷  wk ρ F₁ ^ [ rF , ι ⁰ ] / ([F₁] [ρ] ⊢Δ))
          ([b] : Δ ⊩⟨ ι ⁰ ⟩ b ∷  wk ρ F₁ ^ [ rF , ι ⁰ ] / ([F₁] [ρ] ⊢Δ))
          ([a≡b] : Δ ⊩⟨ ι ⁰ ⟩ a ≡ b ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / ([F₁] [ρ] ⊢Δ))
          → (Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₁ [ a ] ≡ wk (lift ρ) G₁ [ b ] ^ [ ! , ι ⁰ ] / ([G₁] [ρ] ⊢Δ [a])))
       (recursor₁ : ∀ {ρ Δ}
          ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          → Δ ⊩⟨ ι ¹ ⟩ Id (Univ rF ⁰) (wk ρ F) (wk ρ F₁) ^ [ % , ι ¹ ])
       (recursor₂ : ∀ {ρ Δ x y}
          ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([x] : Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F ^ [ rF , ι ⁰ ] / [F] [ρ] ⊢Δ)
          ([y] : Δ ⊩⟨ ι ⁰ ⟩ y ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
          → Δ ⊩⟨ ι ¹ ⟩ Id (U ⁰) (wk (lift ρ) G [ x ]) (wk (lift ρ) G₁ [ y ]) ^ [ % , ι ¹ ])
       (extrecursor : ∀ {ρ Δ x y x′ y′}
          ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([x] : Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F ^ [ rF , ι ⁰ ] / [F] [ρ] ⊢Δ)
          ([x′] : Δ ⊩⟨ ι ⁰ ⟩ x′ ∷ wk ρ F ^ [ rF , ι ⁰ ] / [F] [ρ] ⊢Δ)
          ([x≡x′] : Δ ⊩⟨ ι ⁰ ⟩ x ≡ x′ ∷ wk ρ F ^ [ rF , ι ⁰ ] / [F] [ρ] ⊢Δ)
          ([y] : Δ ⊩⟨ ι ⁰ ⟩ y ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
          ([y′] : Δ ⊩⟨ ι ⁰ ⟩ y′ ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
          ([y≡y′] : Δ ⊩⟨ ι ⁰ ⟩ y ≡ y′ ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
          → Δ ⊩⟨ ι ¹ ⟩ Id (U ⁰) (wk (lift ρ) G [ x ]) (wk (lift ρ) G₁ [ y ]) ≡ Id (U ⁰) (wk (lift ρ) G [ x′ ]) (wk (lift ρ) G₁ [ y′ ]) ^ [ % , ι ¹ ] / recursor₂ [ρ] ⊢Δ [x] [y])
  where
    ⊢IdFF₁ : Γ ⊢ Id (Univ rF ⁰) F F₁ ^ [ % , ι ¹ ]
    ⊢IdFF₁ = univ (Idⱼ (univ 0<1 ⊢Γ) (un-univ ⊢F) (un-univ ⊢F₁))

    [IdFF₁] : ∀ {ρ Δ} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ) → Δ ⊩⟨ ι ¹ ⟩ wk ρ (Id (Univ rF ⁰) F F₁) ^ [ % , ι ¹ ]
    [IdFF₁] [ρ] ⊢Δ = recursor₁ [ρ] ⊢Δ

    b = λ ρ e x → cast ⁰ (wk ρ F₁) (wk ρ F) (Idsym (Univ rF ⁰) (wk ρ F) (wk ρ F₁) e) x
    IdGG₁ = λ ρ e → Π (wk ρ F₁) ^ rF ° ⁰ ▹ Id (U ⁰) (wk (lift (step ρ)) G [ b (step ρ) (wk1 e) (var 0) ]) (wk (lift ρ) G₁) ° ¹

    abstract
      IdTel₂-prettify : ∀ ρ₁ ρ e a → wk (lift ρ₁) (Id (U ⁰) (wk (lift (step ρ)) G [ b (step ρ) (wk1 e) (var 0) ]) (wk (lift ρ) G₁)) [ a ]
        PE.≡ Id (U ⁰) (wk (lift (ρ₁ • ρ)) G [ b (ρ₁ • ρ) (wk ρ₁ e) a ]) (wk (lift (ρ₁ • ρ)) G₁ [ a ])
      IdTel₂-prettify ρ₁ ρ e a = let
          x₂ = PE.trans (PE.cong (subst (sgSubst a)) (wk-Idsym (lift ρ₁) (Univ rF ⁰) (wk (step ρ) F) (wk (step ρ) F₁) (wk1 e)))
            (PE.trans (subst-Idsym (sgSubst a) (Univ rF ⁰) (wk _ (wk (step ρ) F)) (wk _ (wk (step ρ) F₁)) (wk _ (wk1 e)))
              (PE.cong₃ (λ X Y Z → Idsym (Univ rF ⁰) X Y Z) (Id-subst-lemma4 ρ ρ₁ F a) (Id-subst-lemma4 ρ ρ₁ F₁ a) (irrelevant-subst′ ρ₁ e a)))
          x₁ = PE.cong₂ (λ X Y → X [ Y ]) (Id-subst-lemma3 ρ ρ₁ G a) (PE.cong₃ (λ X Y Z → cast ⁰ X Y Z a) (Id-subst-lemma4 ρ ρ₁ F₁ a) ((Id-subst-lemma4 ρ ρ₁ F a)) x₂)
          x = PE.trans (PE.cong (λ X → X [ a ]) (wk-β (wk (lift (step ρ)) G)))
            (PE.trans (singleSubstLift (wk (lift (lift ρ₁)) (wk (lift (step ρ)) G)) (wk (lift ρ₁) (b (step ρ) (wk1 e) (var 0)))) x₁)
        in PE.cong₂ (λ X Y → Id (U ⁰) X Y) x (PE.cong (λ X → X [ a ]) (wk-comp (lift ρ₁) (lift ρ) G₁))

    abstract
      [Id] : ∀ {ρ Δ e} →([ρ] : ρ Twk.∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ)
        → ([e] : Δ ⊩⟨ ι ¹ ⟩ e ∷ wk ρ (Id (Univ rF ⁰) F F₁) ^ [ % , ι ¹ ] / [IdFF₁] [ρ] ⊢Δ)
        → ∀ {ρ₁ Δ₁ a} → ([ρ₁] : ρ₁ Twk.∷ Δ₁ ⊆ Δ) → (⊢Δ₁ : ⊢ Δ₁)
        → ([a] : Δ₁ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ₁ (wk ρ F₁) ^ [ rF , ι ⁰ ] / (Lwk.wk [ρ₁] ⊢Δ₁ ([F₁] [ρ] ⊢Δ)))
        → Δ₁ ⊩⟨ ι ¹ ⟩ wk (lift ρ₁) (Id (U ⁰) (wk (lift (step ρ)) G [ b (step ρ) (wk1 e) (var 0) ]) (wk (lift ρ) G₁)) [ a ] ^ [ % , ι ¹ ]
      [Id] {ρ} {Δ} {e} [ρ] ⊢Δ [e] {ρ₁} {Δ₁} {a} [ρ₁] ⊢Δ₁ [a] =
        let
          [a] : Δ₁ ⊩⟨ ι ⁰ ⟩ a ∷ wk (ρ₁ • ρ) F₁ ^ [ rF , ι ⁰ ] / [F₁] ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁
          [a] = irrelevanceTerm′ (wk-comp ρ₁ ρ F₁) PE.refl PE.refl (Lwk.wk [ρ₁] ⊢Δ₁ ([F₁] [ρ] ⊢Δ)) ([F₁] ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁) [a]
          ⊢e″ = PE.subst (λ X → Δ₁ ⊢ wk ρ₁ e ∷ X ^ [ % , ι ¹ ]) (wk-comp ρ₁ ρ _) (Twk.wkTerm [ρ₁] ⊢Δ₁ (escapeTerm ([IdFF₁] [ρ] ⊢Δ) [e]))
          ⊢e′ = Idsymⱼ (univ 0<1 ⊢Δ₁) (un-univ (escape ([F] ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁))) (un-univ (escape ([F₁] ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁))) ⊢e″
          [b] : Δ₁ ⊩⟨ ι ⁰ ⟩ b (ρ₁ • ρ) (wk ρ₁ e) a ∷ wk (ρ₁ • ρ) F ^ [ rF , ι ⁰ ] / [F] ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁
          [b] = [proj₁cast] ⊢Δ₁ ([F₁] ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁) ([F] ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁) [a] ⊢e′
          x = recursor₂ ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁ [b] [a]
        in PE.subst (λ X → Δ₁ ⊩⟨ ι ¹ ⟩ X ^ [ % , ι ¹ ]) (PE.sym (IdTel₂-prettify ρ₁ ρ e a)) x

    abstract
      [Idext] : ∀ {ρ Δ e e′} →([ρ] : ρ Twk.∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ)
        → ([e] : Δ ⊩⟨ ι ¹ ⟩ e ∷ wk ρ (Id (Univ rF ⁰) F F₁) ^ [ % , ι ¹ ] / [IdFF₁] [ρ] ⊢Δ)
        → ([e′] : Δ ⊩⟨ ι ¹ ⟩ e′ ∷ wk ρ (Id (Univ rF ⁰) F F₁) ^ [ % , ι ¹ ] / [IdFF₁] [ρ] ⊢Δ)
        → ∀ {ρ₁ Δ₁ a a′} → ([ρ₁] : ρ₁ Twk.∷ Δ₁ ⊆ Δ) → (⊢Δ₁ : ⊢ Δ₁)
        → ([a] : Δ₁ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ₁ (wk ρ F₁) ^ [ rF , ι ⁰ ] / (Lwk.wk [ρ₁] ⊢Δ₁ ([F₁] [ρ] ⊢Δ)))
        → ([a′] : Δ₁ ⊩⟨ ι ⁰ ⟩ a′ ∷ wk ρ₁ (wk ρ F₁) ^ [ rF , ι ⁰ ] / (Lwk.wk [ρ₁] ⊢Δ₁ ([F₁] [ρ] ⊢Δ)))
        → ([a≡a′] : Δ₁ ⊩⟨ ι ⁰ ⟩ a ≡ a′ ∷ wk ρ₁ (wk ρ F₁) ^ [ rF , ι ⁰ ] / (Lwk.wk [ρ₁] ⊢Δ₁ ([F₁] [ρ] ⊢Δ)))
        → Δ₁ ⊩⟨ ι ¹ ⟩ wk (lift ρ₁) (Id (U ⁰) (wk (lift (step ρ)) G [ b (step ρ) (wk1 e) (var 0) ]) (wk (lift ρ) G₁)) [ a ]
             ≡ wk (lift ρ₁) (Id (U ⁰) (wk (lift (step ρ)) G [ b (step ρ) (wk1 e′) (var 0) ]) (wk (lift ρ) G₁)) [ a′ ] ^ [ % , ι ¹ ]
             / [Id] [ρ] ⊢Δ [e] [ρ₁] ⊢Δ₁ [a]
      [Idext] {ρ} {Δ} {e} {e′} [ρ] ⊢Δ [e] [e′] {ρ₁} {Δ₁} {a} {a′} [ρ₁] ⊢Δ₁ [a] [a′] [a≡a′] =
        let
          [a]₁ : Δ₁ ⊩⟨ ι ⁰ ⟩ a ∷ wk (ρ₁ • ρ) F₁ ^ [ rF , ι ⁰ ] / [F₁] ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁
          [a]₁ = irrelevanceTerm′ (wk-comp ρ₁ ρ F₁) PE.refl PE.refl (Lwk.wk [ρ₁] ⊢Δ₁ ([F₁] [ρ] ⊢Δ)) ([F₁] ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁) [a]
          [a′] = irrelevanceTerm′ (wk-comp ρ₁ ρ F₁) PE.refl PE.refl (Lwk.wk [ρ₁] ⊢Δ₁ ([F₁] [ρ] ⊢Δ)) ([F₁] ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁) [a′]
          [a≡a′] = irrelevanceEqTerm′ (wk-comp ρ₁ ρ F₁) PE.refl PE.refl (Lwk.wk [ρ₁] ⊢Δ₁ ([F₁] [ρ] ⊢Δ)) ([F₁] ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁) [a≡a′]
          ⊢e₂ = PE.subst (λ X → Δ₁ ⊢ wk ρ₁ e ∷ X ^ [ % , ι ¹ ]) (wk-comp ρ₁ ρ _) (Twk.wkTerm [ρ₁] ⊢Δ₁ (escapeTerm ([IdFF₁] [ρ] ⊢Δ) [e]))
          ⊢e₁ = Idsymⱼ (univ 0<1 ⊢Δ₁) (un-univ (escape ([F] ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁))) (un-univ (escape ([F₁] ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁))) ⊢e₂
          ⊢e′₂ = PE.subst (λ X → Δ₁ ⊢ wk ρ₁ e′ ∷ X ^ [ % , ι ¹ ]) (wk-comp ρ₁ ρ _) (Twk.wkTerm [ρ₁] ⊢Δ₁ (escapeTerm ([IdFF₁] [ρ] ⊢Δ) [e′]))
          ⊢e′₁ = Idsymⱼ (univ 0<1 ⊢Δ₁) (un-univ (escape ([F] ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁))) (un-univ (escape ([F₁] ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁))) ⊢e′₂
          [b] : Δ₁ ⊩⟨ ι ⁰ ⟩ b (ρ₁ • ρ) (wk ρ₁ e) a ∷ wk (ρ₁ • ρ) F ^ [ rF , ι ⁰ ] / [F] ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁
          [b] = [proj₁cast] ⊢Δ₁ ([F₁] ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁) ([F] ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁) [a]₁ ⊢e₁
          [b′] = [proj₁cast] ⊢Δ₁ ([F₁] ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁) ([F] ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁) [a′] ⊢e′₁
          [b≡b′] = [proj₁castext] ⊢Δ₁ ([F₁] ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁) ([F₁] ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁) (reflEq ([F₁] ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁))
            ([F] ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁) ([F] ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁) (reflEq ([F] ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁))
            [a]₁ [a′] [a≡a′] ⊢e₁ ⊢e′₁
          x₁ = recursor₂ ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁ [b] [a]₁
          x = extrecursor ([ρ₁] Twk.•ₜ [ρ]) ⊢Δ₁ [b] [b′] [b≡b′] [a]₁ [a′] [a≡a′]
        in irrelevanceEq″ (PE.sym (IdTel₂-prettify ρ₁ ρ e a)) (PE.sym (IdTel₂-prettify ρ₁ ρ e′ a′)) PE.refl PE.refl x₁ ([Id] [ρ] ⊢Δ [e] [ρ₁] ⊢Δ₁ [a]) x

    [IdGG₁] : ∀ {ρ Δ e} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ)
      → ([e] : Δ ⊩⟨ ι ¹ ⟩ e ∷ wk ρ (Id (Univ rF ⁰) F F₁) ^ [ % , ι ¹ ] / [IdFF₁] [ρ] ⊢Δ)
      → Δ ⊩⟨ ι ¹ ⟩ IdGG₁ ρ e ^ [ % , ι ¹ ]
    [IdGG₁] {ρ} {Δ} {e} [ρ] ⊢Δ [e] =
      let
        ⊢wkF₁ = escape ([F₁] [ρ] ⊢Δ)
        [0] = let ⊢0 = (var (⊢Δ ∙ ⊢wkF₁) here) in
          neuTerm (Lwk.wk (Twk.step Twk.id) (⊢Δ ∙ escape ([F₁] [ρ] ⊢Δ)) ([F₁] [ρ] ⊢Δ)) (var 0) ⊢0 (~-var ⊢0)
        x : Δ ∙ wk ρ F₁ ^ [ rF , ι ⁰ ] ⊩⟨ ι ¹ ⟩ Id (U ⁰) (wk (lift (step ρ)) G [ b (step ρ) (wk1 e) (var 0) ]) (wk (lift ρ) G₁) ^ [ % , ι ¹ ]
        x = PE.subst (λ X → Δ ∙ wk ρ F₁ ^ [ rF , ι ⁰ ] ⊩⟨ ι ¹ ⟩ X ^ [ % , ι ¹ ]) (wkSingleSubstId _) ([Id] [ρ] ⊢Δ [e] (Twk.step Twk.id) (⊢Δ ∙ ⊢wkF₁) [0])
        ⊢Id = escape x
      in
      Πᵣ′ rF ⁰ ¹ (<is≤ 0<1) (≡is≤ PE.refl) (wk ρ F₁) (Id (U ⁰) (wk (lift (step ρ)) G [ b (step ρ) (wk1 e) (var 0) ]) (wk (lift ρ) G₁))
        (idRed:*: (univ (Πⱼ <is≤ 0<1 ▹ ≡is≤ PE.refl ▹ un-univ ⊢wkF₁ ▹ un-univ ⊢Id)))
        ⊢wkF₁ ⊢Id (≅-univ (≅ₜ-Π-cong ⊢wkF₁ (≅-un-univ (escapeEqRefl ([F₁] [ρ] ⊢Δ))) (≅-un-univ (escapeEqRefl x))))
        (λ [ρ₁] ⊢Δ₁ → emb emb< (Lwk.wk [ρ₁] ⊢Δ₁ ([F₁] [ρ] ⊢Δ))) ([Id] [ρ] ⊢Δ [e]) ([Idext] [ρ] ⊢Δ [e] [e])

    abstract
      [IdGG₁-ext] : ∀ {ρ Δ e e′} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ)
        → ([e] : Δ ⊩⟨ ι ¹ ⟩ e ∷ wk ρ (Id (Univ rF ⁰) F F₁) ^ [ % , ι ¹ ] / [IdFF₁] [ρ] ⊢Δ)
        → ([e′] : Δ ⊩⟨ ι ¹ ⟩ e′ ∷ wk ρ (Id (Univ rF ⁰) F F₁) ^ [ % , ι ¹ ] / [IdFF₁] [ρ] ⊢Δ)
        → ([e≡e′] : Δ ⊩⟨ ι ¹ ⟩ e ≡ e′ ∷ wk ρ (Id (Univ rF ⁰) F F₁) ^ [ % , ι ¹ ] / [IdFF₁] [ρ] ⊢Δ)
        → Δ ⊩⟨ ι ¹ ⟩ IdGG₁ ρ e ≡ IdGG₁ ρ e′ ^ [ % , ι ¹ ] / [IdGG₁] [ρ] ⊢Δ [e]
      [IdGG₁-ext] {ρ} {Δ} {e} {e′} [ρ] ⊢Δ [e] [e′] _ =
        let
          ⊢wkF₁ = escape ([F₁] [ρ] ⊢Δ)
          [0] = let ⊢0 = (var (⊢Δ ∙ ⊢wkF₁) here) in
            neuTerm (Lwk.wk (Twk.step Twk.id) (⊢Δ ∙ escape ([F₁] [ρ] ⊢Δ)) ([F₁] [ρ] ⊢Δ)) (var 0) ⊢0 (~-var ⊢0)
          x = [Id] [ρ] ⊢Δ [e′] (Twk.step Twk.id) (⊢Δ ∙ ⊢wkF₁) [0]
          ⊢x = PE.subst (λ X → Δ ∙ wk ρ F₁ ^ [ rF , ι ⁰ ] ⊢ X ^ [ % , ι ¹ ]) (wkSingleSubstId _) (escape x)
          x₁ = [Idext] [ρ] ⊢Δ [e′] [e] (Twk.step Twk.id) (⊢Δ ∙ ⊢wkF₁) [0] [0] (reflEqTerm (Lwk.wk (Twk.step Twk.id) (⊢Δ ∙ escape ([F₁] [ρ] ⊢Δ)) ([F₁] [ρ] ⊢Δ)) [0])
          ⊢x₁ = PE.subst₂ (λ X Y → Δ ∙ wk ρ F₁ ^ [ rF , ι ⁰ ] ⊢ X ≅ Y ^ [ % , ι ¹ ]) (wkSingleSubstId _) (wkSingleSubstId _) (escapeEq x x₁)
        in
        Π₌ (wk ρ F₁) (Id (U ⁰) (wk (lift (step ρ)) G [ b (step ρ) (wk1 e′) (var 0) ]) (wk (lift ρ) G₁))
           (id (univ (Πⱼ <is≤ 0<1 ▹ ≡is≤ PE.refl ▹ un-univ ⊢wkF₁ ▹ un-univ ⊢x)))
           (≅-univ (≅ₜ-Π-cong ⊢wkF₁ (≅-un-univ (escapeEqRefl ([F₁] [ρ] ⊢Δ))) (≅-un-univ (≅-sym ⊢x₁))))
           (λ [ρ]₁ ⊢Δ₁ → reflEq (Lwk.wk [ρ]₁ ⊢Δ₁ ([F₁] [ρ] ⊢Δ)))
           (λ [ρ₁] ⊢Δ₁ [a] → [Idext] [ρ] ⊢Δ [e] [e′] [ρ₁] ⊢Δ₁ [a] [a] (reflEqTerm (Lwk.wk [ρ₁] ⊢Δ₁ ([F₁] [ρ] ⊢Δ)) [a]))

    abstract
      IdTel≡IdUΠΠ : ∃ Id (Univ rF ⁰) F F₁ ▹ (IdGG₁ (step id) (var 0)) PE.≡
        ∃ (Id (Univ rF ⁰) F F₁) ▹ (Π (wk1 F₁) ^ rF ° ⁰ ▹
          Id (U ⁰) ((wk1d G) [ cast ⁰ (wk1 (wk1 F₁)) (wk1 (wk1 F)) (Idsym (Univ rF ⁰) (wk1 (wk1 F)) (wk1 (wk1 F₁)) (var 1)) (var 0) ]↑) (wk1d G₁) ° ¹)
      IdTel≡IdUΠΠ = PE.cong (λ X → ∃ Id (Univ rF ⁰) F F₁ ▹ Π (wk1 F₁) ^ rF ° ⁰ ▹ Id (U ⁰) X (wk1d G₁) ° ¹)
        (PE.trans
          (PE.cong₃ (λ X Y Z → X [ cast ⁰ Z Y (Idsym (Univ rF ⁰) Y Z (var 1)) (var 0) ])
            (PE.sym (wk-comp (lift (step id)) (lift (step id)) G))
            (PE.sym (wk-comp (step id) (step id) F))
            (PE.sym (wk-comp (step id) (step id) F₁)))
          (PE.sym (wk1d[]-[]↑ (wk1d G) _)))

    abstract
      wksubst-IdTel : ∀ ρ e → wk (lift ρ) (IdGG₁ (step id) (var 0)) [ e ] PE.≡ IdGG₁ ρ e
      wksubst-IdTel ρ e =
        let
          x₃ = PE.trans (PE.cong (subst (liftSubst (sgSubst e))) (wk-Idsym (lift (lift ρ)) (Univ rF ⁰) (wk (step (step id)) F) (wk (step (step id)) F₁) (var 1)))
            (PE.trans (subst-Idsym (liftSubst (sgSubst e)) (Univ rF ⁰) (wk _ (wk (step (step id)) F)) (wk _ (wk (step (step id)) F₁)) (var 1))
              (PE.cong₂ (λ X Y → Idsym (Univ rF ⁰) X Y (wk1 e)) (Id-subst-lemma1 ρ F e) (Id-subst-lemma1 ρ F₁ e)))
          x₂ = PE.cong₃ (λ X Y Z → cast ⁰ X Y Z (var 0)) (Id-subst-lemma1 ρ F₁ e) (Id-subst-lemma1 ρ F e) x₃
          x₁ = PE.cong₂ (λ X Y → X [ Y ]) (Id-subst-lemma2 ρ G e) x₂
          x₀ = (PE.trans (PE.cong (subst (liftSubst (sgSubst e))) (wk-β (wk (lift (step (step id))) G)))
            (PE.trans (singleSubstLift (wk (lift (lift (lift ρ))) (wk (lift (step (step id))) G)) (wk (lift (lift ρ)) (b (step (step id)) (var 1) (var 0)))) x₁))
        in PE.cong₃ (λ X Y Z → Π X ^ rF ° ⁰ ▹ Id (U ⁰) Y Z ° ¹) (irrelevant-subst′ ρ F₁ e) x₀ (cast-subst-lemma4 ρ e G₁)

    [IdGG₁0] : Γ ∙ Id (Univ rF ⁰) F F₁ ^ [ % , ι ¹ ] ⊩⟨ ι ¹ ⟩ IdGG₁ (step id) (var 0) ^ [ % , ι ¹ ]
    [IdGG₁0] = let
        ⊢0 = var (⊢Γ ∙ ⊢IdFF₁) here
        [0] = neuTerm ([IdFF₁] (Twk.step Twk.id) (⊢Γ ∙ ⊢IdFF₁)) (var 0) ⊢0 (~-var ⊢0)
      in [IdGG₁] (Twk.step Twk.id) (⊢Γ ∙ ⊢IdFF₁) [0]

    ⊢IdGG₁ : Γ ∙ Id (Univ rF ⁰) F F₁ ^ [ % , ι ¹ ] ⊢ IdGG₁ (step id) (var 0) ^ [ % , ι ¹ ]
    ⊢IdGG₁ = escape [IdGG₁0]

    ⊢∃ : Γ ⊢ ∃ Id (Univ rF ⁰) F F₁ ▹ IdGG₁ (step id) (var 0) ^ [ % , ι ¹ ]
    ⊢∃ = univ (∃ⱼ un-univ ⊢IdFF₁ ▹ un-univ ⊢IdGG₁)

    ∃≡∃ : Γ ⊢ ∃ Id (Univ rF ⁰) F F₁ ▹ IdGG₁ (step id) (var 0) ≅ ∃ Id (Univ rF ⁰) F F₁ ▹ IdGG₁ (step id) (var 0) ^ [ % , ι ¹ ]
    ∃≡∃ = (≅-univ (≅ₜ-∃-cong
      ⊢IdFF₁
      (≅-un-univ (escapeEqRefl (PE.subst (λ X → Γ ⊩⟨ ι ¹ ⟩ X ^ [ % , ι ¹ ]) (wk-id (Id (Univ rF ⁰) F F₁)) ([IdFF₁] Twk.id ⊢Γ))))
      (≅-un-univ (escapeEqRefl [IdGG₁0]))))

    D∃ : Γ ⊢ Id (U ⁰) A B ⇒* ∃ Id (Univ rF ⁰) F F₁ ▹ IdGG₁ (step id) (var 0) ^ [ % , ι ¹ ]
    D∃ = univ⇒* (IdURed*Term′ (un-univ ⊢A) (un-univ ⊢ΠFG) (un-univ⇒* D) (un-univ ⊢B)
      ⇨∷* IdUΠRed*Term′ (un-univ ⊢F) (un-univ ⊢G) (un-univ ⊢B) (un-univ ⊢ΠF₁G₁) (un-univ⇒* D₁))
      ⇨* PE.subst (λ X → Γ ⊢ Id (U ⁰) (Π F ^ rF ° ⁰ ▹ G ° ⁰) (Π F₁ ^ rF ° ⁰ ▹ G₁ ° ⁰) ⇒* X ^ [ % , ι ¹ ]) (PE.sym IdTel≡IdUΠΠ)
        (univ (Id-U-ΠΠ (un-univ ⊢F) (un-univ ⊢G) (un-univ ⊢F₁) (un-univ ⊢G₁))
      ⇨ id (PE.subst (λ X → Γ ⊢ X ^ [ % , ι ¹ ]) IdTel≡IdUΠΠ ⊢∃))


module IdTypeU-lemmas-2
       {Γ rF A₁ A₂ A₃ A₄ F₁ F₂ F₃ F₄ G₁ G₂ G₃ G₄}
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

       (recursor₁ : ∀ {ρ Δ}
          ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          → Δ ⊩⟨ ι ¹ ⟩ Id (Univ rF ⁰) (wk ρ F₁) (wk ρ F₃) ^ [ % , ι ¹ ])
       (recursor₂ : ∀ {ρ Δ x y}
          ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([x] : Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
          ([y] : Δ ⊩⟨ ι ⁰ ⟩ y ∷ wk ρ F₃ ^ [ rF , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
          → Δ ⊩⟨ ι ¹ ⟩ Id (U ⁰) (wk (lift ρ) G₁ [ x ]) (wk (lift ρ) G₃ [ y ]) ^ [ % , ι ¹ ])
       (recursor₃ : ∀ {ρ Δ}
          ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          → Δ ⊩⟨ ι ¹ ⟩ Id (Univ rF ⁰) (wk ρ F₂) (wk ρ F₄) ^ [ % , ι ¹ ])
       (recursor₄ : ∀ {ρ Δ x y}
          ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([x] : Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F₂ ^ [ rF , ι ⁰ ] / [F₂] [ρ] ⊢Δ)
          ([y] : Δ ⊩⟨ ι ⁰ ⟩ y ∷ wk ρ F₄ ^ [ rF , ι ⁰ ] / [F₄] [ρ] ⊢Δ)
          → Δ ⊩⟨ ι ¹ ⟩ Id (U ⁰) (wk (lift ρ) G₂ [ x ]) (wk (lift ρ) G₄ [ y ]) ^ [ % , ι ¹ ])
       (extrecursor₁ : ∀ {ρ Δ x y x′ y′}
          ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([x] : Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
          ([x′] : Δ ⊩⟨ ι ⁰ ⟩ x′ ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
          ([x≡x′] : Δ ⊩⟨ ι ⁰ ⟩ x ≡ x′ ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
          ([y] : Δ ⊩⟨ ι ⁰ ⟩ y ∷ wk ρ F₃ ^ [ rF , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
          ([y′] : Δ ⊩⟨ ι ⁰ ⟩ y′ ∷ wk ρ F₃ ^ [ rF , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
          ([y≡y′] : Δ ⊩⟨ ι ⁰ ⟩ y ≡ y′ ∷ wk ρ F₃ ^ [ rF , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
          → Δ ⊩⟨ ι ¹ ⟩ Id (U ⁰) (wk (lift ρ) G₁ [ x ]) (wk (lift ρ) G₃ [ y ]) ≡ Id (U ⁰) (wk (lift ρ) G₁ [ x′ ]) (wk (lift ρ) G₃ [ y′ ]) ^ [ % , ι ¹ ] / recursor₂ [ρ] ⊢Δ [x] [y])
       (extrecursor₂ : ∀ {ρ Δ x y x′ y′}
          ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([x] : Δ ⊩⟨ ι ⁰ ⟩ x ∷ wk ρ F₂ ^ [ rF , ι ⁰ ] / [F₂] [ρ] ⊢Δ)
          ([x′] : Δ ⊩⟨ ι ⁰ ⟩ x′ ∷ wk ρ F₂ ^ [ rF , ι ⁰ ] / [F₂] [ρ] ⊢Δ)
          ([x≡x′] : Δ ⊩⟨ ι ⁰ ⟩ x ≡ x′ ∷ wk ρ F₂ ^ [ rF , ι ⁰ ] / [F₂] [ρ] ⊢Δ)
          ([y] : Δ ⊩⟨ ι ⁰ ⟩ y ∷ wk ρ F₄ ^ [ rF , ι ⁰ ] / [F₄] [ρ] ⊢Δ)
          ([y′] : Δ ⊩⟨ ι ⁰ ⟩ y′ ∷ wk ρ F₄ ^ [ rF , ι ⁰ ] / [F₄] [ρ] ⊢Δ)
          ([y≡y′] : Δ ⊩⟨ ι ⁰ ⟩ y ≡ y′ ∷ wk ρ F₄ ^ [ rF , ι ⁰ ] / [F₄] [ρ] ⊢Δ)
          → Δ ⊩⟨ ι ¹ ⟩ Id (U ⁰) (wk (lift ρ) G₂ [ x ]) (wk (lift ρ) G₄ [ y ]) ≡ Id (U ⁰) (wk (lift ρ) G₂ [ x′ ]) (wk (lift ρ) G₄ [ y′ ]) ^ [ % , ι ¹ ] / recursor₄ [ρ] ⊢Δ [x] [y])
       (eqrecursor₁ : ∀ {ρ Δ}
          ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          → Δ ⊩⟨ ι ¹ ⟩ Id (Univ rF ⁰) (wk ρ F₁) (wk ρ F₃) ≡ Id (Univ rF ⁰) (wk ρ F₂) (wk ρ F₄) ^ [ % , ι ¹ ] / recursor₁ [ρ] ⊢Δ)
       (eqrecursor₂ : ∀ {ρ Δ x₁ x₂ x₃ x₄}
          → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          → ([x₁] : Δ ⊩⟨ ι ⁰ ⟩ x₁ ∷ wk ρ F₁ ^ [ rF , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
          → ([x₂] : Δ ⊩⟨ ι ⁰ ⟩ x₂ ∷ wk ρ F₂ ^ [ rF , ι ⁰ ] / [F₂] [ρ] ⊢Δ)
          → ([G₁x₁≡G₂x₂] : Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₁ [ x₁ ] ≡ wk (lift ρ) G₂ [ x₂ ] ^ [ ! , ι ⁰ ] / [G₁] [ρ] ⊢Δ [x₁])
          → ([x₃] : Δ ⊩⟨ ι ⁰ ⟩ x₃ ∷ wk ρ F₃ ^ [ rF , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
          → ([x₄] : Δ ⊩⟨ ι ⁰ ⟩ x₄ ∷ wk ρ F₄ ^ [ rF , ι ⁰ ] / [F₄] [ρ] ⊢Δ)
          → ([G₃x₃≡G₄x₄] : Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₃ [ x₃ ] ≡ wk (lift ρ) G₄ [ x₄ ] ^ [ ! , ι ⁰ ] / [G₃] [ρ] ⊢Δ [x₃])
          → Δ ⊩⟨ ι ¹ ⟩ Id (U ⁰) (wk (lift ρ) G₁ [ x₁ ]) (wk (lift ρ) G₃ [ x₃ ]) ≡ Id (U ⁰) (wk (lift ρ) G₂ [ x₂ ]) (wk (lift ρ) G₄ [ x₄ ]) ^ [ % , ι ¹ ] / recursor₂ [ρ] ⊢Δ [x₁] [x₃])
  where
    module E₁ = IdTypeU-lemmas ⊢Γ ⊢A₁ ⊢ΠF₁G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext ⊢A₃ ⊢ΠF₃G₃ D₃ ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext
      recursor₁ recursor₂ extrecursor₁
    module E₂ = IdTypeU-lemmas ⊢Γ ⊢A₂ ⊢ΠF₂G₂ D₂ ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext ⊢A₄ ⊢ΠF₄G₄ D₄ ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext
      recursor₃ recursor₄ extrecursor₂

    [IdFF₁≡IdFF₂] : ∀ {ρ Δ} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ)
      → Δ ⊩⟨ ι ¹ ⟩ wk ρ (Id (Univ rF ⁰) F₁ F₃) ≡ wk ρ (Id (Univ rF ⁰) F₂ F₄) ^ [ % , ι ¹ ] / E₁.[IdFF₁] [ρ] ⊢Δ
    [IdFF₁≡IdFF₂] = (λ [ρ] ⊢Δ → irrelevanceEq (recursor₁ [ρ] ⊢Δ) (E₁.[IdFF₁] [ρ] ⊢Δ) (eqrecursor₁ [ρ] ⊢Δ))

    abstract
      [Ideq] : ∀ {ρ Δ e} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ)
        → ([e] : Δ ⊩⟨ ι ¹ ⟩ e ∷ wk ρ (Id (Univ rF ⁰) F₁ F₃) ^ [ % , ι ¹ ] / E₁.[IdFF₁] [ρ] ⊢Δ)
        → ∀ {ρ₁ Δ₁ a} → ([ρ₁] : ρ₁ Twk.∷ Δ₁ ⊆ Δ) → (⊢Δ₁ : ⊢ Δ₁)
        → ([a] : Δ₁ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ₁ (wk ρ F₃) ^ [ rF , ι ⁰ ] / (Lwk.wk [ρ₁] ⊢Δ₁ ([F₃] [ρ] ⊢Δ)))
        → Δ₁ ⊩⟨ ι ¹ ⟩ wk (lift ρ₁) (Id (U ⁰) (wk (lift (step ρ)) G₁ [ E₁.b (step ρ) (wk1 e) (var 0) ]) (wk (lift ρ) G₃)) [ a ]
             ≡ wk (lift ρ₁) (Id (U ⁰) (wk (lift (step ρ)) G₂ [ E₂.b (step ρ) (wk1 e) (var 0) ]) (wk (lift ρ) G₄)) [ a ] ^ [ % , ι ¹ ]
             / E₁.[Id] [ρ] ⊢Δ [e] [ρ₁] ⊢Δ₁ [a]
      [Ideq] {ρ} {Δ} {e} [ρ] ⊢Δ [e] {ρ₁} {Δ₁} {a} [ρ₁] ⊢Δ₁ [a] =
        let
          ρ′ = ρ₁ • ρ
          [ρ′] : ρ′ Twk.∷ Δ₁ ⊆ Γ
          [ρ′] = [ρ₁] Twk.•ₜ [ρ]
          [a₃] : Δ₁ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ′ F₃ ^ [ rF , ι ⁰ ] / [F₃] [ρ′] ⊢Δ₁
          [a₃] = irrelevanceTerm′ (wk-comp ρ₁ ρ F₃) PE.refl PE.refl (Lwk.wk [ρ₁] ⊢Δ₁ ([F₃] [ρ] ⊢Δ)) ([F₃] [ρ′] ⊢Δ₁) [a]
          [a₄] = convTerm₁ ([F₃] [ρ′] ⊢Δ₁) ([F₄] [ρ′] ⊢Δ₁) ([F₃≡F₄] [ρ′] ⊢Δ₁) [a₃]
          [a₃≡a₄] = reflEqTerm ([F₃] [ρ′] ⊢Δ₁) [a₃]
          ⊢e′ = PE.subst (λ X → Δ₁ ⊢ wk ρ₁ e ∷ X ^ [ % , ι ¹ ]) (wk-comp ρ₁ ρ _) (Twk.wkTerm [ρ₁] ⊢Δ₁ (escapeTerm (E₁.[IdFF₁] [ρ] ⊢Δ) [e]))
          ⊢e₁ = Idsymⱼ (univ 0<1 ⊢Δ₁) (un-univ (escape ([F₁] [ρ′] ⊢Δ₁))) (un-univ (escape ([F₃] [ρ′] ⊢Δ₁))) ⊢e′
          ⊢e″ = conv ⊢e′ (≅-eq (escapeEq (E₁.[IdFF₁] [ρ′] ⊢Δ₁) ([IdFF₁≡IdFF₂] [ρ′] ⊢Δ₁)))
          ⊢e₂ = Idsymⱼ (univ 0<1 ⊢Δ₁) (un-univ (escape ([F₂] [ρ′] ⊢Δ₁))) (un-univ (escape ([F₄] [ρ′] ⊢Δ₁))) ⊢e″
          [b₁] = [proj₁cast] ⊢Δ₁ ([F₃] [ρ′] ⊢Δ₁) ([F₁] [ρ′] ⊢Δ₁) [a₃] ⊢e₁
          [b₂] = [proj₁cast] ⊢Δ₁ ([F₄] [ρ′] ⊢Δ₁) ([F₂] [ρ′] ⊢Δ₁) [a₄] ⊢e₂
          [b₁≡b₂] = [proj₁castext] ⊢Δ₁ ([F₃] [ρ′] ⊢Δ₁) ([F₄] [ρ′] ⊢Δ₁) ([F₃≡F₄] [ρ′] ⊢Δ₁)
            ([F₁] [ρ′] ⊢Δ₁) ([F₂] [ρ′] ⊢Δ₁) ([F₁≡F₂] [ρ′] ⊢Δ₁)
            [a₃] [a₄] [a₃≡a₄] ⊢e₁ ⊢e₂
          [b₁:F₂] = convTerm₁ ([F₁] [ρ′] ⊢Δ₁) ([F₂] [ρ′] ⊢Δ₁) ([F₁≡F₂] [ρ′] ⊢Δ₁) [b₁]
          [b₁≡b₂:F₂] = convEqTerm₁ ([F₁] [ρ′] ⊢Δ₁) ([F₂] [ρ′] ⊢Δ₁) ([F₁≡F₂] [ρ′] ⊢Δ₁) [b₁≡b₂]
          [G₁b₁≡G₂b₂] = transEq ([G₁] [ρ′] ⊢Δ₁ [b₁]) ([G₂] [ρ′] ⊢Δ₁ [b₁:F₂]) ([G₂] [ρ′] ⊢Δ₁ [b₂])
            ([G₁≡G₂] [ρ′] ⊢Δ₁ [b₁]) (G₂-ext [ρ′] ⊢Δ₁ [b₁:F₂] [b₂] [b₁≡b₂:F₂])
          [a₃≡a₄:F₄] = convEqTerm₁ ([F₃] [ρ′] ⊢Δ₁) ([F₄] [ρ′] ⊢Δ₁) ([F₃≡F₄] [ρ′] ⊢Δ₁) [a₃≡a₄]
          [G₃a₃≡G₄a₄] = transEq ([G₃] [ρ′] ⊢Δ₁ [a₃]) ([G₄] [ρ′] ⊢Δ₁ [a₄]) ([G₄] [ρ′] ⊢Δ₁ [a₄])
            ([G₃≡G₄] [ρ′] ⊢Δ₁ [a₃]) (G₄-ext [ρ′] ⊢Δ₁ [a₄] [a₄] [a₃≡a₄:F₄])
          x₁ = recursor₂ [ρ′] ⊢Δ₁ [b₁] [a₃]
          x = eqrecursor₂ [ρ′] ⊢Δ₁ [b₁] [b₂] [G₁b₁≡G₂b₂] [a₃] [a₄] [G₃a₃≡G₄a₄]
        in irrelevanceEq″ (PE.sym (E₁.IdTel₂-prettify ρ₁ ρ e a)) (PE.sym (E₂.IdTel₂-prettify ρ₁ ρ e a)) PE.refl PE.refl x₁ (E₁.[Id] [ρ] ⊢Δ [e] [ρ₁] ⊢Δ₁ [a]) x

    abstract
      [IdGG₁≡IdGG₂] : ∀ {ρ Δ e} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ)
          → ([e] : Δ ⊩⟨ ι ¹ ⟩ e ∷ wk ρ (Id (Univ rF ⁰) F₁ F₃) ^ [ % , ι ¹ ] / E₁.[IdFF₁] [ρ] ⊢Δ)
          → Δ ⊩⟨ ι ¹ ⟩ E₁.IdGG₁ ρ e ≡ E₂.IdGG₁ ρ e ^ [ % , ι ¹ ] / E₁.[IdGG₁] [ρ] ⊢Δ [e]
      [IdGG₁≡IdGG₂] {ρ} {Δ} {e} [ρ] ⊢Δ [e] = let
          [e]′ = convTerm₁ (E₁.[IdFF₁] [ρ] ⊢Δ) (E₂.[IdFF₁] [ρ] ⊢Δ) ([IdFF₁≡IdFF₂] [ρ] ⊢Δ) [e]
          ⊢wkF₃ = escape ([F₃] [ρ] ⊢Δ)
          ⊢wkF₄ = escape ([F₄] [ρ] ⊢Δ)
          [0:F₃] : Δ ∙ wk ρ F₃ ^ [ rF , ι ⁰ ] ⊩⟨ ι ⁰ ⟩ var 0 ∷ wk1 (wk ρ F₃) ^ [ rF , ι ⁰ ] / (Lwk.wk (Twk.step Twk.id) (⊢Δ ∙ ⊢wkF₃) ([F₃] [ρ] ⊢Δ))
          [0:F₃] = let ⊢0 = (var (⊢Δ ∙ ⊢wkF₃) here) in
            neuTerm (Lwk.wk (Twk.step Twk.id) (⊢Δ ∙ ⊢wkF₃) ([F₃] [ρ] ⊢Δ)) (var 0) ⊢0 (~-var ⊢0)
          [0:F₄] = let ⊢0 = (var (⊢Δ ∙ ⊢wkF₄) here) in
            neuTerm (Lwk.wk (Twk.step Twk.id) (⊢Δ ∙ ⊢wkF₄) ([F₄] [ρ] ⊢Δ)) (var 0) ⊢0 (~-var ⊢0)
          x = E₁.[Id] [ρ] ⊢Δ [e] (Twk.step Twk.id) (⊢Δ ∙ ⊢wkF₃) [0:F₃]
          x₁ = [Ideq] [ρ] ⊢Δ [e] (Twk.step Twk.id) (⊢Δ ∙ ⊢wkF₃) [0:F₃]
          ⊢x₁ = PE.subst₂ (λ X Y → Δ ∙ wk ρ F₃ ^ [ rF , ι ⁰ ] ⊢ X ≅ Y ^ [ % , ι ¹ ]) (wkSingleSubstId _) (wkSingleSubstId _) (escapeEq x x₁)
          x₂ = E₂.[Id] [ρ] ⊢Δ [e]′ (Twk.step Twk.id) (⊢Δ ∙ ⊢wkF₄) [0:F₄]
          ⊢x₂ = PE.subst (λ X → Δ ∙ wk ρ F₄ ^ [ rF , ι ⁰ ] ⊢ X ^ [ % , ι ¹ ]) (wkSingleSubstId _) (escape x₂)
        in Π₌ (wk ρ F₄) (Id (U ⁰) (wk (lift (step ρ)) G₂ [ E₂.b (step ρ) (wk1 e) (var 0) ]) (wk (lift ρ) G₄))
          (id (univ (Πⱼ <is≤ 0<1 ▹ ≡is≤ PE.refl ▹ un-univ ⊢wkF₄ ▹ un-univ ⊢x₂)))
          (≅-univ (≅ₜ-Π-cong ⊢wkF₃ (≅-un-univ (escapeEq ([F₃] [ρ] ⊢Δ) ([F₃≡F₄] [ρ] ⊢Δ))) (≅-un-univ ⊢x₁)))
          (λ [ρ₁] ⊢Δ₁ → Lwk.wkEq [ρ₁] ⊢Δ₁ ([F₃] [ρ] ⊢Δ) ([F₃≡F₄] [ρ] ⊢Δ))
          (λ [ρ₁] ⊢Δ₁ [a] → [Ideq] [ρ] ⊢Δ [e] [ρ₁] ⊢Δ₁ [a])

    [IdGG₁≡IdGG₂0] : Γ ∙ Id (Univ rF ⁰) F₁ F₃ ^ [ % , ι ¹ ] ⊩⟨ ι ¹ ⟩ E₁.IdGG₁ (step id) (var 0) ≡ E₂.IdGG₁ (step id) (var 0) ^ [ % , ι ¹ ] / E₁.[IdGG₁0]
    [IdGG₁≡IdGG₂0] = let
        ⊢0 = var (⊢Γ ∙ E₁.⊢IdFF₁) here
        [0] = neuTerm (E₁.[IdFF₁] (Twk.step Twk.id) (⊢Γ ∙ E₁.⊢IdFF₁)) (var 0) ⊢0 (~-var ⊢0)
      in [IdGG₁≡IdGG₂] (Twk.step Twk.id) (⊢Γ ∙ E₁.⊢IdFF₁) [0]

    ∃₁≡∃₂ : Γ ⊢ ∃ Id (Univ rF ⁰) F₁ F₃ ▹ E₁.IdGG₁ (step id) (var 0) ≅ ∃ Id (Univ rF ⁰) F₂ F₄ ▹ E₂.IdGG₁ (step id) (var 0) ^ [ % , ι ¹ ]
    ∃₁≡∃₂ = (≅-univ (≅ₜ-∃-cong
      E₁.⊢IdFF₁
      (≅-un-univ (PE.subst₂ (λ X Y → Γ ⊢ X ≅ Y ^ [ % , ι ¹ ]) (wk-id (Id (Univ rF ⁰) F₁ F₃)) (wk-id (Id (Univ rF ⁰) F₂ F₄)) (escapeEq (E₁.[IdFF₁] Twk.id ⊢Γ) ([IdFF₁≡IdFF₂] Twk.id ⊢Γ))))
      (≅-un-univ (escapeEq E₁.[IdGG₁0] [IdGG₁≡IdGG₂0]))))
