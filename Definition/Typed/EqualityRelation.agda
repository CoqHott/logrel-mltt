{-# OPTIONS --without-K --safe #-}

module Definition.Typed.EqualityRelation where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening using (_∷_⊆_)


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

    -- Universe type reflexivity
    ≅-Urefl   : ∀ {r l Γ} → ⊢ Γ → Γ ⊢ (Univ r l) ≅ (Univ r l) ^ [ ! , next l ]

    -- Natural number type reflexivity
    ≅-ℕrefl   : ∀ {Γ} → ⊢ Γ → Γ ⊢ ℕ ≅ ℕ ^ [ ! , ι ⁰ ]
    ≅ₜ-ℕrefl  : ∀ {Γ} → ⊢ Γ → Γ ⊢ ℕ ≅ ℕ ∷ U ⁰ ^ [ ! , next ⁰ ]

    -- Empty type reflexivity
    ≅-Emptyrefl   : ∀ {Γ} → ⊢ Γ → Γ ⊢ Empty ≅ Empty ^ [ % , ι ⁰ ]
    ≅ₜ-Emptyrefl  : ∀ {Γ} → ⊢ Γ → Γ ⊢ Empty ≅ Empty ∷ SProp ⁰ ^ [ ! , next ⁰ ]

    -- Π-congruence

    ≅-Π-cong  : ∀ {F G H E rF rG l Γ}
              → Γ ⊢ F ^ [ rF , l ]
              → Γ ⊢ F ≅ H ^ [ rF , l ]
              → Γ ∙ F ^ [ rF , l ] ⊢ G ≅ E ^ [ rG , l ]
              → Γ ⊢ Π F ^ rF ▹ G ≅ Π H ^ rF ▹ E ^ [ rG , l ]

    ≅ₜ-Π-cong : ∀ {F G H E rF rG l Γ}
              → Γ ⊢ F ^ [ rF , ι l ]
              → Γ ⊢ F ≅ H ∷ (Univ rF l) ^ [ ! , next l ]
              → Γ ∙ F ^ [ rF , ι l ] ⊢ G ≅ E ∷ (Univ rG l) ^ [ ! , next l ]
              → Γ ⊢ Π F ^ rF ▹ G ≅ Π H ^ rF ▹ E ∷ (Univ rG l) ^ [ ! , next l ]

    -- ∃-congruence
    -- Since ∃ types are always small, no need for a type-level rule
    ≅ₜ-∃-cong : ∀ {F G H E l Γ}
              → Γ ⊢ F ^ [ % , ι l ]
              → Γ ⊢ F ≅ H ∷ SProp l ^ [ ! , next l ]
              → Γ ∙ F ^ [ % , ι l ] ⊢ G ≅ E ∷ SProp l ^ [ ! , next l ]
              → Γ ⊢ ∃ F ▹ G ≅ ∃ H ▹ E ∷ SProp l ^ [ ! , next l ]

    -- Zero reflexivity
    ≅ₜ-zerorefl : ∀ {Γ} → ⊢ Γ → Γ ⊢ zero ≅ zero ∷ ℕ ^ [ ! , ι ⁰ ]

    -- Successor congurence
    ≅-suc-cong : ∀ {m n Γ} → Γ ⊢ m ≅ n ∷ ℕ ^ [ ! , ι ⁰ ] → Γ ⊢ suc m ≅ suc n ∷ ℕ ^ [ ! , ι ⁰ ]

    -- η-equality
    ≅-η-eq : ∀ {f g F G rF l Γ}
              → Γ ⊢ F ^ [ rF , l ]
              → Γ ⊢ f ∷ Π F ^ rF ▹ G ^ [ ! , l ]
              → Γ ⊢ g ∷ Π F ^ rF ▹ G ^ [ ! , l ]
              → Function f
              → Function g
              → Γ ∙ F ^ [ rF , l ] ⊢ wk1 f ∘ var 0 ≅ wk1 g ∘ var 0 ∷ G ^ [ ! , l ]
              → Γ ⊢ f ≅ g ∷ Π F ^ rF ▹ G ^ [ ! , l ]

    -- Variable reflexivity
    ~-var : ∀ {x A Γ r} → Γ ⊢ var x ∷ A ^ r → Γ ⊢ var x ~ var x ∷ A ^ r

    -- Application congurence
    ~-app : ∀ {a b f g F G rF l Γ}
          → Γ ⊢ f ~ g ∷ Π F ^ rF ▹ G ^ [ ! , l ]
          → Γ ⊢ a ≅ b ∷ F ^ [ rF , l ]
          → Γ ⊢ f ∘ a ~ g ∘ b ∷ G [ a ] ^ [ ! , l ]

    -- Natural recursion congurence
    ~-natrec : ∀ {z z′ s s′ n n′ F F′ l Γ}
             → Γ ∙ ℕ ^ [ ! , ι ⁰ ] ⊢ F ≅ F′ ^ [ ! , l ]
             → Γ     ⊢ z ≅ z′ ∷ F [ zero ] ^ [ ! , l ]
             → Γ     ⊢ s ≅ s′ ∷ Π ℕ ^ ! ▹ (F ^ ! ▹▹ F [ suc (var 0) ]↑) ^ [ ! , l ]
             → Γ     ⊢ n ~ n′ ∷ ℕ ^ [ ! , ι ⁰ ]
             → Γ     ⊢ natrec F z s n ~ natrec F′ z′ s′ n′ ∷ F [ n ] ^ [ ! , l ]

    -- Empty recursion congurence
    ~-Emptyrec : ∀ {n n′ F F′ l Γ}
             → Γ ⊢ F ≅ F′ ^ [ ! , l ]
             → Γ     ⊢ n ~ n′ ∷ Empty ^ [ % , ι ⁰ ]
             → Γ     ⊢ Emptyrec F n ~ Emptyrec F′ n′ ∷ F ^ [ ! , l ]

    -- Id congruences
    ~-Id  : ∀ {A A' l t t' u u' Γ}
          → Γ ⊢ A ~ A' ∷ U l ^ [ ! , next l ]
          → Γ ⊢ t ≅ t' ∷ A ^ [ ! , ι l ]
          → Γ ⊢ u ≅ u' ∷ A ^ [ ! , ι l ]
          → Γ ⊢ Id A t u ~ Id A' t' u' ∷ SProp l ^ [ ! , next l ]

    ~-Idℕ : ∀ {t t' u u' Γ}
          → ⊢ Γ
          → Γ ⊢ t ~ t' ∷ ℕ ^ [ ! , ι ⁰ ]
          → Γ ⊢ u ≅ u' ∷ ℕ ^ [ ! , ι ⁰ ]
          → Γ ⊢ Id ℕ t u ~ Id ℕ t' u' ∷ SProp ⁰ ^ [ ! , next ⁰ ]

    ~-Idℕ0 : ∀ {u u' Γ}
           → ⊢ Γ
           → Γ ⊢ u ~ u' ∷ ℕ ^ [ ! , ι ⁰ ]
           → Γ ⊢ Id ℕ zero u ~ Id ℕ zero u' ∷ SProp ⁰ ^ [ ! , next ⁰ ]

    ~-IdℕS : ∀ {t t' u u' Γ}
           → ⊢ Γ
           → Γ ⊢ t ≅ t' ∷ ℕ ^ [ ! , ι ⁰ ]
           → Γ ⊢ u ~ u' ∷ ℕ ^ [ ! , ι ⁰ ]
           → Γ ⊢ Id ℕ (suc t) u ~ Id ℕ (suc t') u' ∷ SProp ⁰ ^ [ ! , next ⁰ ]

    ~-IdU : ∀ {t t' u u' Γ} →
          let l = ⁰ in
          let l' = ¹ in
            ⊢ Γ
          → Γ ⊢ t ~ t' ∷ U l ^ [ ! , next l ]
          → Γ ⊢ u ≅ u' ∷ U l ^ [ ! , next l ]
          → Γ ⊢ Id (U l) t u ~ Id (U l) t' u' ∷ SProp l' ^ [ ! , next l ]

    ~-IdUℕ : ∀ {u u' Γ}
           → ⊢ Γ
           → Γ ⊢ u ~ u' ∷ U ⁰ ^ [ ! , next ⁰ ]
           → Γ ⊢ Id (U ⁰) ℕ u ~ Id (U ⁰) ℕ u' ∷ SProp ¹ ^ [ ! , next ¹ ]

    ~-IdUΠ : ∀ {A rA B A' B' u u' Γ} →
          let l = ⁰ in
          let l' = ¹ in
             Γ ⊢ A ∷ Univ rA l ^ [ ! , next l ]
           → Γ ⊢ A ≅ A' ∷ Univ rA l ^ [ ! , next l ]
           → Γ ∙ A ^ [ rA , ι l ] ⊢ B ≅ B' ∷ U l ^ [ ! , next l ]
           → Γ ⊢ u ~ u' ∷ U l ^ [ ! , next l ]
           → Γ ⊢ Id (U l)  (Π A ^ rA ▹ B) u ~ Id (U l) (Π A' ^ rA ▹ B') u' ∷ SProp l' ^ [ ! , next l' ]

    -- cast congruences

    ~-cast : ∀ {A A' B B' l e e' t t' Γ}
           → Γ ⊢ A ~ A' ∷ U l ^ [ ! , next l ]
           → Γ ⊢ B ≅ B' ∷ U l ^ [ ! , next l ]
           → Γ ⊢ t ≅ t' ∷ A ^ [ ! , ι l ]
           → Γ ⊢ cast l A B e t ~ cast l A' B' e' t' ∷ B ^ [ ! , ι l ]

    ~-castℕ : ∀ {B B' e e' t t' Γ}
            → ⊢ Γ
            → Γ ⊢ B ~ B' ∷ U ⁰ ^ [ ! , next ⁰ ]
            → Γ ⊢ e ≅ e' ∷ Id (U ⁰) ℕ B ^ [ % , next ⁰ ]
            → Γ ⊢ t ≅ t' ∷ ℕ ^ [ ! , ι ⁰ ]
            → Γ ⊢ cast ⁰ ℕ B e t ~ cast ⁰ ℕ B' e' t' ∷ B ^ [ ! , ι ⁰ ]

    ~-castℕℕ : ∀ {e e' t t' Γ}
             → ⊢ Γ
             → Γ ⊢ e ≅ e' ∷ Id (U ⁰) ℕ ℕ ^ [ % , next ⁰ ]
             → Γ ⊢ t ~ t' ∷ ℕ ^ [ ! , ι ⁰ ]
             → Γ ⊢ cast ⁰ ℕ ℕ e t ~ cast ⁰ ℕ ℕ e' t' ∷ ℕ ^ [ ! , ι ⁰ ]

    ~-castΠ : ∀ {A A' rA l P P' B B' e e' t t' Γ}
           → Γ ⊢ A ^ [ rA , ι l ]
           → Γ ⊢ A ≅ A' ∷ Univ rA l ^ [ ! , next l ]
           → Γ ∙ A ^ [ rA , ι l ] ⊢ P ≅ P' ∷ U l ^ [ ! , next l ]
           → Γ ⊢ B ~ B' ∷ U l ^ [ ! , next l ]
           → Γ ⊢ e ≅ e' ∷ Id (U l) (Π A ^ rA ▹ P) B ^ [ % , next l ]
           → Γ ⊢ t ≅ t' ∷ Π A ^ rA ▹ P ^ [ ! , ι l ]
           → Γ ⊢ cast l (Π A ^ rA ▹ P) B e t ~ cast l (Π A' ^ rA ▹ P') B' e' t' ∷ B ^ [ ! , ι l ]

    ~-castℕΠ : ∀ {A A' rA P P' e e' t t' Γ}
             → Γ ⊢ A ∷ Univ rA ⁰ ^ [ ! , next ⁰ ]
             → Γ ⊢ A ≅ A' ∷ Univ rA ⁰ ^ [ ! , next ⁰ ]
             → Γ ∙ A ^ [ rA , ι ⁰ ] ⊢ P ∷ U ⁰ ^ [ ! , next ⁰ ]
             → Γ ∙ A ^ [ rA , ι ⁰ ] ⊢ P ≅ P' ∷ U ⁰ ^ [ ! , next ⁰ ]
             → Γ ⊢ e ≅ e' ∷ Empty ^ [ % , ι ⁰ ]
             → Γ ⊢ t ≅ t' ∷ ℕ ^ [ ! , ι ⁰ ]
             → Γ ⊢ cast ⁰ ℕ (Π A ^ rA ▹ P) e t ~ cast ⁰ ℕ (Π A' ^ rA ▹ P') e' t' ∷ (Π A ^ rA ▹ P) ^ [ ! , ι ⁰ ]

    ~-castΠℕ : ∀ {A A' rA l P P' e e' t t' Γ}
             → Γ ⊢ A ∷ Univ rA l ^ [ ! , next l ]
             → Γ ⊢ A ≅ A' ∷ Univ rA l ^ [ ! , next l ]
             → Γ ∙ A ^ [ rA , ι l ] ⊢ P ∷ U l ^ [ ! , next l ]
             → Γ ∙ A ^ [ rA , ι l ] ⊢ P ≅ P' ∷ U l ^ [ ! , next l ]
             → Γ ⊢ e ≅ e' ∷ Empty ^ [ % , ι ⁰ ]
             → Γ ⊢ t ≅ t' ∷ (Π A ^ rA ▹ P) ^ [ ! , ι l ]
             → Γ ⊢ cast l (Π A ^ rA ▹ P) ℕ e t ~ cast l (Π A' ^ rA ▹ P') ℕ e' t' ∷ ℕ ^ [ ! , ι ⁰ ]

    ~-irrelevance : ∀ {n n′ A l Γ} → Γ ⊢ n ∷ A ^ [ % , l ] → Γ ⊢ n′ ∷ A ^ [ % , l ]
                  → Γ ⊢ n ~ n′ ∷ A ^ [ % , l ]

  -- Composition of universe and generic equality compatibility
  ~-to-≅ : ∀ {t u r l Γ} → Γ ⊢ t ~ u ∷ (Univ r l) ^ [ ! , next l ] → Γ ⊢ t ≅ u ^ [ r , ι l ]
  ~-to-≅ t~u = ≅-univ (~-to-≅ₜ t~u)
