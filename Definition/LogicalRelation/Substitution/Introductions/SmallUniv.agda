{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.SmallUniv {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.Typed.Weakening
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Introductions.Universe

open import Tools.Product
open import Tools.Empty

import Definition.LogicalRelation.Weakening as wkLR
import Tools.PropositionalEquality as PE
import Data.Nat as Nat

-- SPropᵗᵛ : ∀ {Γ}
--     → ([Γ] : ⊩ᵛ Γ)
--     → Γ ⊩ᵛ⟨ ∞ ⟩ SProp ⁰ ∷ Univ ! ¹ ^ [ ! , ∞ ] / [Γ] / (Uᵛ (Nat.s≤s (Nat.s≤s Nat.z≤n)) [Γ])
-- SPropᵗᵛ {Γ} [Γ] ⊢Δ [σ] =
--   Uₜ
--     (SProp ⁰)
--     [[ univ 0<1 ⊢Δ , univ 0<1 ⊢Δ , id (univ 0<1 ⊢Δ) ]]
--     Uₙ (≅-U⁰refl ⊢Δ)
--     (λ [ρ] ⊢Δ₁ → [SProp⁰] ⊢Δ₁)
--     (λ x [ρ] ⊢Δ₁ [a] [b] → [IdSProp] ⊢Δ₁ [a] [b])
--     {!!} {!!} {!!}
--   , {!!}
--   where
--     [SProp⁰] : ∀ {Γ} → (⊢Γ : ⊢ Γ) → Γ ⊩⟨ ι ¹ ⟩ SProp ⁰ ^ [ ! , ι ¹ ]
--     [SProp⁰] ⊢Γ = Uᵣ (Uᵣ % ⁰ (Nat.s≤s Nat.z≤n) PE.refl
--       [[ U⁰ⱼ ⊢Γ , U⁰ⱼ ⊢Γ , id (U⁰ⱼ ⊢Γ) ]])

--     [IdSProp] : ∀ {Γ a b} → (⊢Γ : ⊢ Γ) → ([a] : Γ ⊩⟨ ι ¹ ⟩ a ∷ SProp ⁰ ^ [ ! , ι ¹ ] / [SProp⁰] ⊢Γ) → ([b] : Γ ⊩⟨ ι ¹ ⟩ b ∷ SProp ⁰ ^ [ ! , ι ¹ ] / [SProp⁰] ⊢Γ) → Γ ⊩⟨ ι ¹ ⟩ Id (SProp ⁰) a b ^ [ % , ι ¹ ]
--     [IdSProp] {Γ} {a} {b} ⊢Γ [a] [b] =
--       let
--         ⊢a : Γ ⊢ a ∷ SProp ⁰ ^ [ ! , ι ¹ ]
--         ⊢a = escapeTerm ([SProp⁰] ⊢Γ) [a]
--         ⊢b = escapeTerm ([SProp⁰] ⊢Γ) [b]
--         ⊢▹▹ : Γ ⊢ a ^ % ▹▹ b ∷ SProp ¹ ^ [ ! , ∞ ]
--         ⊢▹▹ = {!!}
--         ⊢◃◃ : Γ ⊢ b ^ % ▹▹ a ∷ SProp ¹ ^ [ ! , ∞ ]
--         ⊢◃◃ = {!!}
--         [wk1] : step id ∷ Γ ∙ a ^ % ▹▹ b ^ [ % , ι ¹ ] ⊆ Γ
--         [wk1] = step id
--         ⊢◃◃wk : Γ ∙ a ^ % ▹▹ b ^ [ % , ι ¹ ] ⊢ wk1 b ^ % ▹▹ wk1 a ∷ SProp ¹ ^ [ ! , ∞ ]
--         ⊢◃◃wk = PE.subst (λ X → Γ ∙ a ^ % ▹▹ b ^ _ ⊢ Π _ ^ % ▹ X ∷ _ ^ _)
--           (PE.sym (wk1-wk≡lift-wk1 (step id) a)) (wkTerm [wk1] (⊢Γ ∙ univ ⊢▹▹) ⊢◃◃)
--         ⊢∃ : Γ ⊢ ∃ a ^ % ▹▹ b ▹ (wk1 b ^ % ▹▹ wk1 a) ^ [ % , ι ¹ ]
--         ⊢∃ = univ (∃ⱼ ⊢▹▹ ▹ ⊢◃◃wk)
--         [▹▹] : Γ ⊩⟨ ι ¹ ⟩ a ^ % ▹▹ b ^ [ % , ι ¹ ]
--         [▹▹] = Πᵣ (Πᵣ % a (wk1 b) [[ univ ⊢▹▹ , univ ⊢▹▹ , id (univ ⊢▹▹) ]]
--           {!univ ⊢a!} {!something ⊢b!} {!yea ok!} {!!} {!!} {!!})
--         [∃] : Γ ⊩⟨ ι ¹ ⟩ ∃ a ^ % ▹▹ b ▹ (wk1 b ^ % ▹▹ wk1 a) ^ [ % , ι ¹ ]
--         [∃] = ∃ᵣ (∃ᵣ (a ^ % ▹▹ b) (wk1 b ^ % ▹▹ wk1 a) [[ ⊢∃ , ⊢∃ , id ⊢∃ ]]
--           (univ ⊢▹▹) (univ ⊢◃◃wk)
--           (≅-univ (≅ₜ-∃-cong (univ ⊢▹▹) {!!} {!!}))
--           (λ [ρ] ⊢Δ₁ → wkLR.wk [ρ] ⊢Δ₁ [▹▹]) {!!} {!!})
--         [Id] , _ = redSubst* (univ (Id-SProp ⊢a ⊢b) ⇨ id ⊢∃) [∃]
--       in [Id]

univ-red : ∀ {Γ A B r l}
           (D : Γ ⊢ A ⇒* B ∷ Univ r l ^ next l )
         → Γ ⊢ A ⇒* B ^ [ r , ι l ]
univ-red (id x) = id (univ x)
univ-red (x ⇨ D) = univ x ⇨ univ-red D

un-univ-red :  ∀ {Γ A B r l}
           (D : Γ ⊢ A ⇒* B ^ [ r , ι l ] )
         → Γ ⊢ A ⇒* B ∷ Univ r l ^ next l
un-univ-red (id x) = id (un-univ x)
un-univ-red (univ x ⇨ D) = x ⇨ un-univ-red D

IdURed* : ∀ {Γ t t′ u}
             → (d : Γ ⊢ t ⇒* t′ ∷ U ⁰ ^ ι ¹)
             → (⊢u : Γ ⊢ u ∷ U ⁰ ^ [ ! , ι ¹ ])
             → Γ ⊢ Id (U ⁰) t u ⇒* Id (U ⁰) t′ u ^ [ % , ι ¹ ]
IdURed* (id x) ⊢u = id (univ (Idⱼ (univ 0<1 (wfTerm ⊢u)) x ⊢u))
IdURed* (x ⇨ d) ⊢u = _⇨_ (univ (Id-U-subst x ⊢u)) (IdURed* d ⊢u)

IdUℕRed* : ∀ {Γ t t′}
             → (⊢Γ : ⊢ Γ)
             → (d : Γ ⊢ t ⇒* t′ ∷ U ⁰ ^ ι ¹)
             → Γ ⊢ Id (U ⁰) ℕ t ⇒* Id (U ⁰) ℕ t′ ^ [ % , ι ¹ ]
IdUℕRed* ⊢Γ (id x) = id (univ (Idⱼ (univ 0<1 ⊢Γ) (ℕⱼ ⊢Γ) x))
IdUℕRed* ⊢Γ (x ⇨ d) = _⇨_ (univ (Id-U-ℕ-subst x)) (IdUℕRed* ⊢Γ d)

IdUΠRed* : ∀ {Γ F rF G t t′}
             → (⊢F : Γ ⊢ F ∷ Univ rF ⁰ ^ [ ! , ι ¹ ])
             → (⊢G : Γ ∙ F ^ [ rF , ι ⁰ ] ⊢ G ∷ U ⁰ ^ [ ! , ι ¹ ])
             → (d : Γ ⊢ t ⇒* t′ ∷ U ⁰ ^ ι ¹)
             → Γ ⊢ Id (U ⁰) (Π F ^ rF ▹ G) t ⇒* Id (U ⁰) (Π F ^ rF ▹ G) t′ ^ [ % , ι ¹ ]
IdUΠRed* ⊢F ⊢G (id x) = id (univ (Idⱼ (univ 0<1 (wfTerm ⊢F)) (Πⱼ ≡is≤ PE.refl ▹ ⊢F ▹ ⊢G) x))
IdUΠRed* ⊢F ⊢G (x ⇨ d) = _⇨_ (univ (Id-U-Π-subst ⊢F ⊢G x)) (IdUΠRed* ⊢F ⊢G d)

wk-inv : ∀ t → (Definition.Untyped.wk (lift (step id)) t) [ var 0 ] PE.≡ t
wk-inv t = PE.trans
  (subst-wk t)
  (PE.trans (substVar-to-subst (λ { 0 → PE.refl ; (Nat.suc x) → PE.refl }) t)
  (subst-id t))

⊢Empty : ∀ {Γ} → ⊢ Γ → Γ ⊢ Empty ^ [ % , ι ¹ ]
⊢Empty = {!!}

⊩Empty : ∀ {Γ} → ⊢ Γ → Γ ⊩⟨ ι ¹ ⟩ Empty ^ [ % , ι ¹ ]
⊩Empty = {!!}

⊢Unit : ∀ {Γ} → ⊢ Γ → Γ ⊢ Unit ^ [ % , ι ¹ ]
⊢Unit = {!!}

⊩Unit : ∀ {Γ} → ⊢ Γ → Γ ⊩⟨ ι ¹ ⟩ Unit ^ [ % , ι ¹ ]
⊩Unit = {!!}

Uᵗᵛ : ∀ {Γ}
    → ([Γ] : ⊩ᵛ Γ)
    → Γ ⊩ᵛ⟨ ∞ ⟩ U ⁰ ∷ Univ ! ¹ ^ [ ! , ∞ ] / [Γ] / (Uᵛ (Nat.s≤s (Nat.s≤s Nat.z≤n)) [Γ])
Uᵗᵛ {Γ} [Γ] {Δ = Δ} ⊢Δ [σ] =
  let
    ⊩U¹ = proj₁ (Uᵛ (Nat.s≤s (Nat.s≤s Nat.z≤n)) [Γ] ⊢Δ [σ])
    ⊩U⁰ : Δ ⊩⟨ ∞ ⟩ U ⁰ ∷ U ¹ ^ [ ! , ∞ ] / ⊩U¹
    ⊩U⁰ = Uₜ (U ⁰)
      [[ univ 0<1 ⊢Δ , univ 0<1 ⊢Δ , id (univ 0<1 ⊢Δ) ]]
      Uₙ (≅-U⁰refl ⊢Δ)
      (λ [ρ] ⊢Δ₁ → [U⁰] ⊢Δ₁)
      (λ x [ρ] ⊢Δ₁ [a] [b] → [IdU] ⊢Δ₁ [a] [b])
      (λ r≡! [ρ] ⊢Δ₁ [a] [a′] x [b] [b′] x₁ → {!to do later: is it necessary?!})
      (λ x → ⊥-elim (⁰≢¹ (PE.sym x)))
      (λ x → ⊥-elim (⁰≢¹ (PE.sym x)))
  in
  ⊩U⁰ , λ [σ] [σ≡σ] → reflEqTerm ⊩U¹ ⊩U⁰
  where
    [U⁰] : ∀ {Γ} → (⊢Γ : ⊢ Γ) → Γ ⊩⟨ ι ¹ ⟩ U ⁰ ^ [ ! , ι ¹ ]
    [U⁰] ⊢Γ = Uᵣ (Uᵣ ! ⁰ (Nat.s≤s Nat.z≤n) PE.refl
      [[ U⁰ⱼ ⊢Γ , U⁰ⱼ ⊢Γ , id (U⁰ⱼ ⊢Γ) ]])

    [IdU]′ : ∀ {Γ a b} → (⊢Γ : ⊢ Γ)
           → ([a] : Γ ⊩⟨ ι ⁰ ⟩ a ^ [ ! , ι ⁰ ])
           → ([b] : Γ ⊩⟨ ι ⁰ ⟩ b ^ [ ! , ι ⁰ ])
           → Γ ⊩⟨ ι ¹ ⟩ Id (U ⁰) a b ^ [ % , ι ¹ ]
    [IdU]′ {Γ} {a} {b} ⊢Γ (ne′ K [[ ⊢A , ⊢B , D ]] neK K≡K) [b] =
      let
        b≡b = escapeEq [b] (reflEq [b])
        ⊢b = escape [b]
        ⊢IdUab = univ (Idⱼ (univ 0<1 ⊢Γ) (un-univ ⊢A) (un-univ ⊢b))
        ⊢IdUKb = univ (Idⱼ (univ 0<1 ⊢Γ) (un-univ ⊢B) (un-univ ⊢b))
        Id⇒Id = IdURed* (un-univ-red D) (un-univ ⊢b)
      in
      ne (ne (Id (U ⁰) K b) [[ ⊢IdUab , ⊢IdUKb , Id⇒Id ]] (IdUₙ neK)
        (~-IdU ⊢Γ K≡K (≅-un-univ b≡b)))
    [IdU]′ {Γ} {a} {b} ⊢Γ (ℕᵣ [[ ⊢A , ⊢B , D ]]) (ne′ K [[ ⊢A₁ , ⊢B₁ , D₁ ]] neK K≡K) =
      let
        ⊢IdUab = univ (Idⱼ (univ 0<1 ⊢Γ) (un-univ ⊢A) (un-univ ⊢A₁))
        ⊢IdUℕK = univ (Idⱼ (univ 0<1 ⊢Γ) (un-univ ⊢B) (un-univ ⊢B₁))
        Id⇒Id = IdURed* (un-univ-red D) (un-univ ⊢A₁)
          ⇨* IdUℕRed* ⊢Γ (un-univ-red D₁)
      in
      ne (ne (Id (U ⁰) ℕ K) [[ ⊢IdUab , ⊢IdUℕK , Id⇒Id ]] (IdUℕₙ neK) (~-IdUℕ ⊢Γ K≡K))
    [IdU]′ {Γ} {a} {b} ⊢Γ (ℕᵣ [[ ⊢A , ⊢B , D ]]) (ℕᵣ [[ ⊢A₁ , ⊢B₁ , D₁ ]]) =
      let
        Id⇒Unit : Γ ⊢ Id (U ⁰) a b ⇒* Unit ^ [ % , ι ¹ ]
        Id⇒Unit = (IdURed* (un-univ-red D) (un-univ ⊢A₁)
          ⇨* IdUℕRed* ⊢Γ (un-univ-red D₁))
          ⇨* (univ (Id-U-ℕℕ ⊢Γ) ⇨ id (⊢Unit ⊢Γ))
        [IdUab] , _ = redSubst* Id⇒Unit (⊩Unit ⊢Γ)
      in [IdUab]
    [IdU]′ {Γ} {a} {b} ⊢Γ (ℕᵣ [[ ⊢A , ⊢B , D ]]) (Πᵣ′ rF F G [[ ⊢A₁ , ⊢B₁ , D₁ ]] ⊢F ⊢G A≡A [F] [G] G-ext) =
      let
        Id⇒Empty : Γ ⊢ Id (U ⁰) a b ⇒* Empty ^ [ % , ι ¹ ]
        Id⇒Empty = (IdURed* (un-univ-red D) (un-univ ⊢A₁)
          ⇨* IdUℕRed* ⊢Γ (un-univ-red D₁))
          ⇨* (univ (Id-U-ℕΠ (un-univ ⊢F) (un-univ ⊢G)) ⇨ id (⊢Empty ⊢Γ))
        [IdUab] , _ = redSubst* Id⇒Empty (⊩Empty ⊢Γ)
      in [IdUab]
    [IdU]′ {Γ} ⊢Γ (Πᵣ′ rF F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext)
      (ne′ K [[ ⊢A₁ , ⊢B₁ , D₁ ]] neK K≡K) =
      let
        [F]′ = PE.subst (λ X → _ ⊩⟨ ι ⁰ ⟩ X ^ _) (wk-id F) ([F] id ⊢Γ)
        ⊢F = escape [F]′
        F≡F = escapeEq [F]′ (reflEq [F]′)
        [G]′ = PE.subst (λ X → _ ⊩⟨ ι ⁰ ⟩ X ^ _) (wk-inv G)
          ([G] {a = var 0} (step id) (⊢Γ ∙ ⊢F)
            (neuTerm ([F] (step id) (⊢Γ ∙ ⊢F)) (var 0)
              (var (⊢Γ ∙ ⊢F) here) (~-var (var (⊢Γ ∙ ⊢F) here))))
        G≡G = escapeEq [G]′ (reflEq [G]′)
      in
      ne (ne (Id (U ⁰) (Π F ^ rF ▹ G) K) {!!} (IdUΠₙ neK)
        (~-IdUΠ (un-univ ⊢F) (≅-un-univ F≡F) (≅-un-univ G≡G) K≡K))
    [IdU]′ ⊢Γ (Πᵣ x) (ℕᵣ x₁) =
      {!!}
    [IdU]′ {Γ} ⊢Γ (Πᵣ′ ! F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext)
      (Πᵣ′ ! F₁ G₁ [[ ⊢A₁ , ⊢B₁ , D₁ ]] ⊢F₁ ⊢G₁ A≡A₁ [F₁] [G₁] G-ext₁) =
      let
        IdUab⇒IdUΠΠ = (IdURed* (un-univ-red D) (un-univ ⊢A₁)
          ⇨* IdUΠRed* (un-univ ⊢F) (un-univ ⊢G) (un-univ-red D₁))
          ⇨* (univ (Id-U-ΠΠ (un-univ ⊢F) (un-univ ⊢G) (un-univ ⊢F₁) (un-univ ⊢G₁))
            ⇨ id {!!})
      in {!!}
    [IdU]′ ⊢Γ (Πᵣ′ rF F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext)
      (Πᵣ′ rF₁ F₁ G₁ [[ ⊢A₁ , ⊢B₁ , D₁ ]] ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) = {!!}

    [IdU] : ∀ {Γ a b} → (⊢Γ : ⊢ Γ)
          → ([a] : Γ ⊩⟨ ι ¹ ⟩ a ∷ U ⁰ ^ [ ! , ι ¹ ] / [U⁰] ⊢Γ)
          → ([b] : Γ ⊩⟨ ι ¹ ⟩ b ∷ U ⁰ ^ [ ! , ι ¹ ] / [U⁰] ⊢Γ)
          → Γ ⊩⟨ ι ¹ ⟩ Id (U ⁰) a b ^ [ % , ι ¹ ]
    [IdU] {Γ} {a} {b} ⊢Γ (Uₜ A d typeA A≡A [a] _ _ _ _) (Uₜ B d′ typeB B≡B [b] _ _ _ _) =
      let [a]′ = PE.subst (λ X → _ ⊩⟨ ι ⁰ ⟩ X ^ _) (wk-id a) ([a] id ⊢Γ) in
      let [b]′ = PE.subst (λ X → _ ⊩⟨ ι ⁰ ⟩ X ^ _) (wk-id b) ([b] id ⊢Γ) in
      [IdU]′ ⊢Γ [a]′ [b]′
