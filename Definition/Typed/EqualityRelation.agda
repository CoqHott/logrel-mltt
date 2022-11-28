{-# OPTIONS --safe #-}

module Definition.Typed.EqualityRelation where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening using (_∷_⊆_)
import Tools.PropositionalEquality as PE
open import Tools.Product


-- Generic equality relation used with the logical relation

record EqRelSet : Set₁ where
  constructor eqRel
  field
    ---------------
    -- Relations --
    ---------------

    -- Equality of types
    _⊢_≅_^_   : Con Term → (A B : Term) → TypeInfo → Set

    -- Equality of terms
    _⊢_≅_∷_^_ : Con Term → (t u A : Term) → TypeInfo → Set

    -- Equality of neutral terms
    _⊢_~_∷_^_ : Con Term → (t u A : Term) → TypeInfo → Set

    ----------------
    -- Properties --
    ----------------

    -- Generic equality compatibility
    ~-to-≅ₜ : ∀ {k l A r Γ}
            → Γ ⊢ k ~ l ∷ A ^ r
            → Γ ⊢ k ≅ l ∷ A ^ r

    -- Judgmental conversion compatibility
    ≅-eq  : ∀ {A B r Γ}
          → Γ ⊢ A ≅ B ^ r
          → Γ ⊢ A ≡ B ^ r
    ≅ₜ-eq : ∀ {t u A r Γ}
          → Γ ⊢ t ≅ u ∷ A ^ r
          → Γ ⊢ t ≡ u ∷ A ^ r

    -- Universe
    ≅-univ : ∀ {A B r l Γ}
           → Γ ⊢ A ≅ B ∷ (Univ r l) ^ [ ! , next l ]
           → Γ ⊢ A ≅ B ^ [ r , ι l ]

    ≅-un-univ : ∀ {A B r l Γ}
           → Γ ⊢ A ≅ B ^ [ r , ι l ]
           → Γ ⊢ A ≅ B ∷ (Univ r l) ^ [ ! , next l ]

    -- Symmetry
    ≅-sym  : ∀ {A B Γ r} → Γ ⊢ A ≅ B ^ r → Γ ⊢ B ≅ A ^ r
    ≅ₜ-sym : ∀ {t u A r Γ} → Γ ⊢ t ≅ u ∷ A ^ r → Γ ⊢ u ≅ t ∷ A ^ r
    ~-sym  : ∀ {k l A Γ r} → Γ ⊢ k ~ l ∷ A ^ r → Γ ⊢ l ~ k ∷ A ^ r

    -- Transitivity
    ≅-trans  : ∀ {A B C r Γ} → Γ ⊢ A ≅ B ^ r → Γ ⊢ B ≅ C ^ r → Γ ⊢ A ≅ C ^ r
    ≅ₜ-trans : ∀ {t u v A r Γ} → Γ ⊢ t ≅ u ∷ A ^ r → Γ ⊢ u ≅ v ∷ A ^ r → Γ ⊢ t ≅ v ∷ A ^ r
    ~-trans  : ∀ {k l m A r Γ} → Γ ⊢ k ~ l ∷ A ^ r → Γ ⊢ l ~ m ∷ A ^ r → Γ ⊢ k ~ m ∷ A ^ r

    -- Conversion
    ≅-conv : ∀ {t u A B r Γ} → Γ ⊢ t ≅ u ∷ A ^ r → Γ ⊢ A ≡ B ^ r → Γ ⊢ t ≅ u ∷ B ^ r
    ~-conv : ∀ {k l A B r Γ} → Γ ⊢ k ~ l ∷ A ^ r → Γ ⊢ A ≡ B ^ r → Γ ⊢ k ~ l ∷ B ^ r

    -- Weakening
    ≅-wk  : ∀ {A B r ρ Γ Δ}
          → ρ ∷ Δ ⊆ Γ
          → ⊢ Δ
          → Γ ⊢ A ≅ B ^ r
          → Δ ⊢ wk ρ A ≅ wk ρ B ^ r
    ≅ₜ-wk : ∀ {t u A r ρ Γ Δ}
          → ρ ∷ Δ ⊆ Γ
          → ⊢ Δ
          → Γ ⊢ t ≅ u ∷ A ^ r
          → Δ ⊢ wk ρ t ≅ wk ρ u ∷ wk ρ A ^ r
    ~-wk  : ∀ {k l A r ρ Γ Δ}
          → ρ ∷ Δ ⊆ Γ
          → ⊢ Δ
          → Γ ⊢ k ~ l ∷ A ^ r
          → Δ ⊢ wk ρ k ~ wk ρ l ∷ wk ρ A ^ r

    -- Weak head expansion
    ≅-red : ∀ {A A′ B B′ r Γ}
          → Γ ⊢ A ⇒* A′ ^ r
          → Γ ⊢ B ⇒* B′ ^ r
          → Whnf A′
          → Whnf B′
          → Γ ⊢ A′ ≅ B′ ^ r
          → Γ ⊢ A  ≅ B ^ r

    ≅ₜ-red : ∀ {a a′ b b′ A B l Γ}
           → Γ ⊢ A ⇒* B ^ [ ! , l ]
           → Γ ⊢ a ⇒* a′ ∷ B ^ l
           → Γ ⊢ b ⇒* b′ ∷ B ^ l
           → Whnf B
           → Whnf a′
           → Whnf b′
           → Γ ⊢ a′ ≅ b′ ∷ B ^ [ ! , l ]
           → Γ ⊢ a  ≅ b  ∷ A ^ [ ! , l ]

    -- Large universe type reflexivity
    ≅-U¹refl   : ∀ {r Γ} → ⊢ Γ → Γ ⊢ (Univ r ¹) ≅ (Univ r ¹) ^ [ ! , ∞ ]

    -- Small universe type reflexivity
    ≅-U⁰refl   : ∀ {r Γ} → ⊢ Γ → Γ ⊢ (Univ r ⁰) ≅ (Univ r ⁰) ∷ U ¹ ^ [ ! , ∞ ]

    -- Natural number type reflexivity
    ≅ₜ-ℕrefl  : ∀ {Γ} → ⊢ Γ → Γ ⊢ ℕ ≅ ℕ ∷ U ⁰ ^ [ ! , next ⁰ ]

    -- Empty type reflexivity
    ≅ₜ-Emptyrefl  : ∀ {Γ} → ⊢ Γ → Γ ⊢ sEmpty ≅ sEmpty ∷ SProp ^ [ ! , next ⁰ ]

    -- Π-congruence
    ≅ₜ-Π-cong : ∀ {F G H E rF lF r lG l Γ}
              → (r PE.≡ ! → lF ≤ l × lG ≤ l)
              → (r PE.≡ % → lG PE.≡ ⁰ × l PE.≡ ⁰)
              → Γ ⊢ F ^ [ rF , ι lF ]
              → Γ ⊢ F ≅ H ∷ (Univ rF lF) ^ [ ! , next lF ]
              → Γ ∙ F ^ [ rF , ι lF ] ⊢ G ≅ E ∷ (Univ r lG) ^ [ ! , next lG ]
              → Γ ⊢ Π F ^ rF ° lF ▹ G ° lG ° l ^ r ≅ Π H ^ rF ° lF ▹ E ° lG ° l ^ r ∷ (Univ r l) ^ [ ! , next l ]

    -- ∃-congruence
    -- Since ∃ types are always small, no need for a type-level rule
    ≅ₜ-∃-cong : ∀ {F G H E Γ}
              → Γ ⊢ F ^ [ % , ι ⁰ ]
              → Γ ⊢ F ≅ H ∷ SProp ^ [ ! , next ⁰ ]
              → Γ ∙ F ^ [ % , ι ⁰ ] ⊢ G ≅ E ∷ SProp ^ [ ! , next ⁰ ]
              → Γ ⊢ ∃ F ▹ G ≅ ∃ H ▹ E ∷ SProp ^ [ ! , next ⁰ ]

    -- Zero reflexivity
    ≅ₜ-zerorefl : ∀ {Γ} → ⊢ Γ → Γ ⊢ zero ≅ zero ∷ ℕ ^ [ ! , ι ⁰ ]

    -- Successor congruence
    ≅-suc-cong : ∀ {m n Γ} → Γ ⊢ m ≅ n ∷ ℕ ^ [ ! , ι ⁰ ] → Γ ⊢ suc m ≅ suc n ∷ ℕ ^ [ ! , ι ⁰ ]

    -- η-equality
    ≅-η-eq : ∀ {f g F G rF lF lG l Γ}
              → lF ≤ l
              → lG ≤ l
              → Γ ⊢ F ^ [ rF , ι lF ]
              → Γ ⊢ f ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ [ ! , ι l ]
              → Γ ⊢ g ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ [ ! , ι l ]
              → Function f
              → Function g
              → Γ ∙ F ^ [ rF , ι lF ] ⊢ wk1 f ∘ var 0 ^ l ≅ wk1 g ∘ var 0 ^ l ∷ G ^ [ ! , ι lG ]
              → Γ ⊢ f ≅ g ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ [ ! , ι l ]

    -- Variable reflexivity
    ~-var : ∀ {x A Γ r} → Γ ⊢ var x ∷ A ^ r → Γ ⊢ var x ~ var x ∷ A ^ r

    -- Application congurence
    ~-app : ∀ {a b f g F G rF lF lG l Γ}
          → Γ ⊢ f ~ g ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ [ ! , ι l ]
          → Γ ⊢ a ≅ b ∷ F ^ [ rF , ι lF ]
          → Γ ⊢ f ∘ a ^ l ~ g ∘ b ^ l ∷ G [ a ] ^ [ ! , ι lG ]

    -- Natural recursion congurence
    ~-natrec : ∀ {z z′ s s′ n n′ F F′ l Γ}
             → Γ ∙ ℕ ^ [ ! , ι ⁰ ] ⊢ F ≅ F′ ^ [ ! , ι l ]
             → Γ     ⊢ z ≅ z′ ∷ F [ zero ] ^ [ ! , ι l ]
             → Γ     ⊢ s ≅ s′ ∷ Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc (var 0) ]↑ ° l ° l ^ !) ° l ° l ^ ! ^ [ ! , ι l ]
             → Γ     ⊢ n ~ n′ ∷ ℕ ^ [ ! , ι ⁰ ]
             → Γ     ⊢ natrec l F z s n ~ natrec l F′ z′ s′ n′ ∷ F [ n ] ^ [ ! , ι l ]

    -- Empty recursion congurence
    ~-Emptyrec : ∀ {e e′ F F′ l Γ}
             → Γ ⊢ F ≅ F′ ^ [ ! , ι l ]
             → Γ ⊢ e ∷ sEmpty ^ [ % , ι ⁰ ]
             → Γ ⊢ e′ ∷ sEmpty ^ [ % , ι ⁰ ]
             → Γ     ⊢ Emptyrec l ⁰ F e ~ Emptyrec l ⁰ F′ e′ ∷ F ^ [ ! , ι l ]

    -- Id congruences
    ~-Id  : ∀ {A A' l t t' u u' Γ}
          → Γ ⊢ A ~ A' ∷ Univ ! l ^ [ ! , next l ]
          → Γ ⊢ t ≅ t' ∷ A ^ [ ! , ι l ]
          → Γ ⊢ u ≅ u' ∷ A ^ [ ! , ι l ]
          → Γ ⊢ Id A t u ~ Id A' t' u' ∷ SProp ^ [ ! , next ⁰ ]

    ~-Idℕ : ∀ {t t' u u' Γ}
          → ⊢ Γ
          → Γ ⊢ t ~ t' ∷ ℕ ^ [ ! , ι ⁰ ]
          → Γ ⊢ u ≅ u' ∷ ℕ ^ [ ! , ι ⁰ ]
          → Γ ⊢ Id ℕ t u ~ Id ℕ t' u' ∷ SProp ^ [ ! , next ⁰ ]

    ~-Idℕ0 : ∀ {u u' Γ}
           → ⊢ Γ
           → Γ ⊢ u ~ u' ∷ ℕ ^ [ ! , ι ⁰ ]
           → Γ ⊢ Id ℕ zero u ~ Id ℕ zero u' ∷ SProp ^ [ ! , next ⁰ ]

    ~-IdℕS : ∀ {t t' u u' Γ}
           → ⊢ Γ
           → Γ ⊢ t ≅ t' ∷ ℕ ^ [ ! , ι ⁰ ]
           → Γ ⊢ u ~ u' ∷ ℕ ^ [ ! , ι ⁰ ]
           → Γ ⊢ Id ℕ (suc t) u ~ Id ℕ (suc t') u' ∷ SProp ^ [ ! , next ⁰ ]

    ~-IdU : ∀ {t t' u u' Γ} →
          let l = ⁰ in
            ⊢ Γ
          → Γ ⊢ t ~ t' ∷ U l ^ [ ! , next l ]
          → Γ ⊢ u ≅ u' ∷ U l ^ [ ! , next l ]
          → Γ ⊢ Id (U l) t u ~ Id (U l) t' u' ∷ SProp ^ [ ! , next ⁰ ]

    ~-IdUℕ : ∀ {u u' Γ}
           → ⊢ Γ
           → Γ ⊢ u ~ u' ∷ U ⁰ ^ [ ! , next ⁰ ]
           → Γ ⊢ Id (U ⁰) ℕ u ~ Id (U ⁰) ℕ u' ∷ SProp ^ [ ! , next ⁰ ]

    ~-IdUΠ : ∀ {A rA B A' B' u u' Γ} →
          let l = ⁰ in
           Γ ⊢ Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ ! ≅ Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ [ ! , next ⁰ ]
           → Γ ⊢ u ~ u' ∷ U l ^ [ ! , next l ]
           → Γ ⊢ Id (U l)  (Π A ^ rA ° l ▹ B ° l ° ⁰ ^ ! ) u ~ Id (U l) (Π A' ^ rA ° l ▹ B' ° l ° ⁰ ^ !) u' ∷ SProp ^ [ ! , next ⁰ ]

    -- cast congruences

    ~-cast : ∀ {A A' B B' e e' t t' Γ} →
           let l = ⁰ in
             Γ ⊢ A ~ A' ∷ U l ^ [ ! , next l ]
           → Γ ⊢ B ~ B' ∷ U l ^ [ ! , next l ]
           → Γ ⊢ t ~ t' ∷ A ^ [ ! , ι l ]
           → Γ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ]
           → Γ ⊢ e' ∷ (Id (U ⁰) A' B') ^ [ % , ι ⁰ ]
           → Γ ⊢ cast l A B e t ~ cast l A' B' e' t' ∷ B ^ [ ! , ι l ]

    ~-castneℕ : ∀ {A A' e e' t t' Γ} →
           let l = ⁰ in
             Γ ⊢ A ~ A' ∷ U l ^ [ ! , next l ]
           → Γ ⊢ t ≅ t' ∷ A ^ [ ! , ι l ]
           → Γ ⊢ e ∷ (Id (U ⁰) A ℕ) ^ [ % , ι ⁰ ]
           → Γ ⊢ e' ∷ (Id (U ⁰) A' ℕ) ^ [ % , ι ⁰ ]
           → Γ ⊢ cast l A ℕ e t ~ cast l A' ℕ e' t' ∷ ℕ ^ [ ! , ι l ]

    ~-castneΠ : ∀ {A A' P P' B B' rB e e' t t' Γ} →
           let l = ⁰ in
           Γ ⊢ A ~ A' ∷ U l ^ [ ! , next l ]
           → Γ ⊢ Π B ^ rB ° ⁰ ▹ P ° ⁰ ° ⁰ ^ ! ≅ Π B' ^ rB ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ [ ! , next ⁰ ]
           → Γ ⊢ t ≅ t' ∷ A ^ [ ! , ι l ]
           → Γ ⊢ e ∷ (Id (U ⁰) A (Π B ^ rB ° l ▹ P ° l ° l ^ !)) ^ [ % , ι ⁰ ]
           → Γ ⊢ e' ∷ (Id (U ⁰) A' (Π B' ^ rB ° l ▹ P' ° l ° l ^ !)) ^ [ % , ι ⁰ ]
           → Γ ⊢ cast l A (Π B ^ rB ° l ▹ P ° l ° l ^ !) e t ~ cast l A' (Π B' ^ rB ° l ▹ P' ° l ° l ^ !) e' t' ∷ Π B ^ rB ° l ▹ P ° l ° l ^ ! ^ [ ! , ι l ]

    ~-cast-refl : ∀ {A B e t u Γ} →
           let l = ⁰ in
             Γ ⊢ A ~ B ∷ U l ^ [ ! , next l ]
           → Γ ⊢ t ~ u ∷ A ^ [ ! , ι l ]
           → Γ ⊢ t ∷ A ^ [ ! , ι l ]
           → Γ ⊢ e ∷ Id (U ⁰) A B ^ [ % , ι ⁰ ]
           → Γ ⊢ cast l A B e t ~ u ∷ B ^ [ ! , ι l ]

    ~-castℕ-refl : ∀ {e t u Γ} →
           let l = ⁰ in
             Γ ⊢ t ~ u ∷ ℕ ^ [ ! , ι l ]
           → Γ ⊢ t ∷ ℕ ^ [ ! , ι l ]
           → Γ ⊢ e ∷ (Id (U ⁰) ℕ ℕ) ^ [ % , ι ⁰ ]
           → Γ ⊢ cast l ℕ ℕ e t ~ u ∷ ℕ ^ [ ! , ι l ]

    ~-castℕ : ∀ {B B' e e' t t' Γ}
            → ⊢ Γ
            → Γ ⊢ B ~ B' ∷ U ⁰ ^ [ ! , next ⁰ ]
            → Γ ⊢ t ≅ t' ∷ ℕ ^ [ ! , ι ⁰ ]
            → Γ ⊢ e ∷ (Id (U ⁰) ℕ B) ^ [ % , ι ⁰ ]
            → Γ ⊢ e' ∷ (Id (U ⁰) ℕ B') ^ [ % , ι ⁰ ]
            → Γ ⊢ cast ⁰ ℕ B e t ~ cast ⁰ ℕ B' e' t' ∷ B ^ [ ! , ι ⁰ ]

    ~-castΠ : ∀ {A A' rA P P' B B' e e' t t' Γ} →
           let l = ⁰ in
           Γ ⊢ Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰ ^ ! ≅ Π A' ^ rA ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ [ ! , next ⁰ ]
           → Γ ⊢ B ~ B' ∷ U l ^ [ ! , next l ]
           → Γ ⊢ t ≅ t' ∷ Π A ^ rA ° l ▹ P ° l ° l ^ ! ^ [ ! , ι l ]
           → Γ ⊢ e ∷ (Id (U ⁰) (Π A ^ rA ° l ▹ P ° l ° l ^ !) B) ^ [ % , ι ⁰ ]
           → Γ ⊢ e' ∷ (Id (U ⁰) (Π A' ^ rA ° l ▹ P' ° l ° l ^ !) B') ^ [ % , ι ⁰ ]
           → Γ ⊢ cast l (Π A ^ rA ° l ▹ P ° l ° l ^ !) B e t ~ cast l (Π A' ^ rA ° l ▹ P' ° l ° l ^ !) B' e' t' ∷ B ^ [ ! , ι l ]

    ~-castℕΠ : ∀ {A A' rA P P' e e' t t' Γ}
             → Γ ⊢ A ∷ Univ rA ⁰ ^ [ ! , next ⁰ ]
             → Γ ∙ A ^ [ rA , ι ⁰ ] ⊢ P ∷ U ⁰ ^ [ ! , next ⁰ ]
             → Γ ⊢ Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰ ^ ! ≅ Π A' ^ rA ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ [ ! , next ⁰ ]
             → Γ ⊢ t ≅ t' ∷ ℕ ^ [ ! , ι ⁰ ]
             → Γ ⊢ e ∷ (Id (U ⁰) ℕ (Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰ ^ !)) ^ [ % , ι ⁰ ]
             → Γ ⊢ e' ∷ (Id (U ⁰) ℕ (Π A' ^ rA ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ !)) ^ [ % , ι ⁰ ]
             → Γ ⊢ cast ⁰ ℕ (Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰ ^ !) e t ~ cast ⁰ ℕ (Π A' ^ rA ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ !) e' t' ∷ (Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰ ^ !) ^ [ ! , ι ⁰ ]

    ~-castΠℕ : ∀ {A A' rA P P' e e' t t' Γ} →
             let l = ⁰ in
               Γ ⊢ A ∷ Univ rA l ^ [ ! , next l ]
             → Γ ∙ A ^ [ rA , ι l ] ⊢ P ∷ U l ^ [ ! , next l ]
             → Γ ⊢ Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰ ^ ! ≅ Π A' ^ rA ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ [ ! , next ⁰ ]
             → Γ ⊢ t ≅ t' ∷ (Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰ ^ !) ^ [ ! , ι l ]
             → Γ ⊢ e ∷ (Id (U ⁰) (Π A ^ rA ° l ▹ P ° l ° ⁰ ^ !) ℕ) ^ [ % , ι ⁰ ]
             → Γ ⊢ e' ∷ (Id (U ⁰) (Π A' ^ rA ° l ▹ P' ° l  ° ⁰ ^ !) ℕ) ^ [ % , ι ⁰ ]
             → Γ ⊢ cast l (Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰ ^ !) ℕ e t ~ cast l (Π A' ^ rA ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ !) ℕ e' t' ∷ ℕ ^ [ ! , ι ⁰ ]

    ~-castΠΠ%! : ∀ {A A' P P' B B' Q Q' e e' t t' Γ}
             → Γ ⊢ A ∷ Univ % ⁰ ^ [ ! , next ⁰ ]
             → Γ ∙ A ^ [ % , ι ⁰ ] ⊢ P ∷ U ⁰ ^ [ ! , next ⁰ ]
             → Γ ⊢ Π A ^ % ° ⁰ ▹ P ° ⁰  ° ⁰  ^ ! ≅ Π A' ^ % ° ⁰ ▹ P' ° ⁰ ° ⁰  ^ ! ∷ U ⁰ ^ [ ! , next ⁰ ]
             → Γ ⊢ B ∷ Univ ! ⁰ ^ [ ! , next ⁰ ]
             → Γ ∙ B ^ [ ! , ι ⁰ ] ⊢ Q ∷ U ⁰ ^ [ ! , next ⁰ ]
             → Γ ⊢ Π B ^ ! ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ ! ≅ Π B' ^ ! ° ⁰ ▹ Q' ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ [ ! , next ⁰ ]
             → Γ ⊢ t ≅ t' ∷ Π A ^ % ° ⁰ ▹ P ° ⁰  ° ⁰  ^ ! ^ [ ! , ι ⁰ ]
             → Γ ⊢ e ∷ (Id (U ⁰) (Π A ^ % ° ⁰ ▹ P ° ⁰ ° ⁰ ^ !) (Π B ^ ! ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ !)) ^ [ % , ι ⁰ ]
             → Γ ⊢ e' ∷ (Id (U ⁰) (Π A' ^ % ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ !) (Π B' ^ ! ° ⁰ ▹ Q' ° ⁰ ° ⁰ ^ !)) ^ [ % , ι ⁰ ]
             → Γ ⊢ cast ⁰ (Π A ^ % ° ⁰ ▹ P ° ⁰ ° ⁰ ^ !) (Π B ^ ! ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ !) e t ~ cast ⁰ (Π A' ^ % ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ !) (Π B' ^ ! ° ⁰ ▹ Q' ° ⁰ ° ⁰ ^ !) e' t' ∷ Π B ^ ! ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ ! ^ [ ! , ι ⁰ ]

    ~-castΠΠ!% : ∀ {A A' P P' B B' Q Q' e e' t t' Γ}
             → Γ ⊢ A ∷ Univ ! ⁰ ^ [ ! , next ⁰ ]
             → Γ ∙ A ^ [ ! , ι ⁰ ] ⊢ P ∷ U ⁰ ^ [ ! , next ⁰ ]
             → Γ ⊢ Π A ^ ! ° ⁰ ▹ P ° ⁰ ° ⁰ ^ ! ≅ Π A' ^ ! ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ [ ! , next ⁰ ]
             → Γ ⊢ B ∷ Univ % ⁰ ^ [ ! , next ⁰ ]
             → Γ ∙ B ^ [ % , ι ⁰ ] ⊢ Q ∷ U ⁰ ^ [ ! , next ⁰ ]
             → Γ ⊢ Π B ^ % ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ ! ≅ Π B' ^ % ° ⁰ ▹ Q' ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ [ ! , next ⁰ ]
             → Γ ⊢ t ≅ t' ∷ Π A ^ ! ° ⁰ ▹ P ° ⁰ ° ⁰ ^ ! ^ [ ! , ι ⁰ ]
             → Γ ⊢ e ∷ (Id (U ⁰) (Π A ^ ! ° ⁰ ▹ P ° ⁰ ° ⁰ ^ !) (Π B ^ % ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ !)) ^ [ % , ι ⁰ ]
             → Γ ⊢ e' ∷ (Id (U ⁰) (Π A' ^ ! ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ !) (Π B' ^ % ° ⁰ ▹ Q' ° ⁰ ° ⁰ ^ !)) ^ [ % , ι ⁰ ]
             → Γ ⊢ cast ⁰ (Π A ^ ! ° ⁰ ▹ P ° ⁰ ° ⁰ ^ !) (Π B ^ % ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ !) e t ~ cast ⁰ (Π A' ^ ! ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ !) (Π B' ^ % ° ⁰ ▹ Q' ° ⁰ ° ⁰ ^ !) e' t' ∷ Π B ^ % ° ⁰ ▹ Q ° ⁰  ° ⁰ ^ ! ^ [ ! , ι ⁰ ]

    ~-irrelevance : ∀ {n n′ A l Γ} → Γ ⊢ n ∷ A ^ [ % , l ] → Γ ⊢ n′ ∷ A ^ [ % , l ]
                  → Γ ⊢ n ~ n′ ∷ A ^ [ % , l ]

  -- Composition of universe and generic equality compatibility
  ~-to-≅ : ∀ {t u r l Γ} → Γ ⊢ t ~ u ∷ (Univ r l) ^ [ ! , next l ] → Γ ⊢ t ≅ u ^ [ r , ι l ]
  ~-to-≅ t~u = ≅-univ (~-to-≅ₜ t~u)


open EqRelSet {{...}}

~-castℕℕ : ∀ {{eqrel : EqRelSet}} {e e' t t' Γ}
             → Γ ⊢ t ~ t' ∷ ℕ ^ [ ! , ι ⁰ ]
             → Γ ⊢ t ∷ ℕ ^ [ ! , ι ⁰ ]
             → Γ ⊢ t' ∷ ℕ ^ [ ! , ι ⁰ ]
             → Γ ⊢ e ∷ (Id (U ⁰) ℕ ℕ) ^ [ % , ι ⁰ ]
             → Γ ⊢ e' ∷ (Id (U ⁰) ℕ ℕ) ^ [ % , ι ⁰ ]
             → Γ ⊢ cast ⁰ ℕ ℕ e t ~ cast ⁰ ℕ ℕ e' t' ∷ ℕ ^ [ ! , ι ⁰ ]
~-castℕℕ t~t ⊢t ⊢t' ⊢e ⊢e' = ~-castℕ-refl (~-sym (~-castℕ-refl (~-sym t~t) ⊢t' ⊢e')) ⊢t ⊢e
