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
    _⊢_≅_^_   : Con Term → (A B : Term) → Relevance → Set

    -- Equality of terms
    _⊢_≅_∷_^_ : Con Term → (t u A : Term) → Relevance → Set

    -- Equality of neutral terms
    _⊢_~_∷_^_ : Con Term → (t u A : Term) → Relevance → Set

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
           → Γ ⊢ A ≅ B ∷ (Univ r l) ^ !
           → Γ ⊢ A ≅ B ^ r

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

    ≅ₜ-red : ∀ {a a′ b b′ A B Γ}
           → Γ ⊢ A ⇒* B ^ !
           → Γ ⊢ a ⇒* a′ ∷ B
           → Γ ⊢ b ⇒* b′ ∷ B
           → Whnf B
           → Whnf a′
           → Whnf b′
           → Γ ⊢ a′ ≅ b′ ∷ B ^ !
           → Γ ⊢ a  ≅ b  ∷ A ^ !

    -- Universe type reflexivity
    ≅-Urefl   : ∀ {r l Γ} → ⊢ Γ → Γ ⊢ (Univ r l) ≅ (Univ r l) ^ !

    -- Natural number type reflexivity
    ≅-ℕrefl   : ∀ {Γ} → ⊢ Γ → Γ ⊢ ℕ ≅ ℕ ^ !
    ≅ₜ-ℕrefl  : ∀ {Γ} → ⊢ Γ → Γ ⊢ ℕ ≅ ℕ ∷ U ⁰ ^ !

    -- Empty type reflexivity
    ≅-Emptyrefl   : ∀ {Γ} → ⊢ Γ → Γ ⊢ Empty ≅ Empty ^ %
    ≅ₜ-Emptyrefl  : ∀ {Γ} → ⊢ Γ → Γ ⊢ Empty ≅ Empty ∷ SProp ⁰ ^ !

    -- Π-congruence

    ≅-Π-cong  : ∀ {F G H E rF rG Γ}
              → Γ ⊢ F ^ rF
              → Γ ⊢ F ≅ H ^ rF
              → Γ ∙ F ^ rF ⊢ G ≅ E ^ rG
              → Γ ⊢ Π F ^ rF ▹ G ≅ Π H ^ rF ▹ E ^ rG

    ≅ₜ-Π-cong : ∀ {F G H E rF rG l Γ}
              → Γ ⊢ F ^ rF
              → Γ ⊢ F ≅ H ∷ (Univ rF l) ^ !
              → Γ ∙ F ^ rF ⊢ G ≅ E ∷ (Univ rG l) ^ !
              → Γ ⊢ Π F ^ rF ▹ G ≅ Π H ^ rF ▹ E ∷ (Univ rG l) ^ !

    -- ∃-congruence
    -- Since ∃ types are always small, no need for a type-level rule
    ≅ₜ-∃-cong : ∀ {F G H E l Γ}
              → Γ ⊢ F ^ %
              → Γ ⊢ F ≅ H ∷ SProp l ^ !
              → Γ ∙ F ^ % ⊢ G ≅ E ∷ SProp l ^ !
              → Γ ⊢ ∃ F ▹ G ≅ ∃ H ▹ E ∷ SProp l ^ !

    -- Zero reflexivity
    ≅ₜ-zerorefl : ∀ {Γ} → ⊢ Γ → Γ ⊢ zero ≅ zero ∷ ℕ ^ !

    -- Successor congurence
    ≅-suc-cong : ∀ {m n Γ} → Γ ⊢ m ≅ n ∷ ℕ ^ ! → Γ ⊢ suc m ≅ suc n ∷ ℕ ^ !

    -- η-equality
    ≅-η-eq : ∀ {f g F G rF Γ}
              → Γ ⊢ F ^ rF
              → Γ ⊢ f ∷ Π F ^ rF ▹ G ^ !
              → Γ ⊢ g ∷ Π F ^ rF ▹ G ^ !
              → Function f
              → Function g
              → Γ ∙ F ^ rF ⊢ wk1 f ∘ var 0 ≅ wk1 g ∘ var 0 ∷ G ^ !
              → Γ ⊢ f ≅ g ∷ Π F ^ rF ▹ G ^ !

    -- Variable reflexivity
    ~-var : ∀ {x A Γ r} → Γ ⊢ var x ∷ A ^ r → Γ ⊢ var x ~ var x ∷ A ^ r

    -- Application congurence
    ~-app : ∀ {a b f g F G rF Γ}
          → Γ ⊢ f ~ g ∷ Π F ^ rF ▹ G ^ !
          → Γ ⊢ a ≅ b ∷ F ^ rF
          → Γ ⊢ f ∘ a ~ g ∘ b ∷ G [ a ] ^ !

    -- Natural recursion congurence
    ~-natrec : ∀ {z z′ s s′ n n′ F F′ Γ}
             → Γ ∙ ℕ ^ ! ⊢ F ≅ F′ ^ !
             → Γ     ⊢ z ≅ z′ ∷ F [ zero ] ^ !
             → Γ     ⊢ s ≅ s′ ∷ Π ℕ ^ ! ▹ (F ^ ! ▹▹ F [ suc (var 0) ]↑) ^ !
             → Γ     ⊢ n ~ n′ ∷ ℕ ^ !
             → Γ     ⊢ natrec F z s n ~ natrec F′ z′ s′ n′ ∷ F [ n ] ^ !

    -- Empty recursion congurence
    ~-Emptyrec : ∀ {n n′ F F′ Γ}
             → Γ ⊢ F ≅ F′ ^ !
             → Γ     ⊢ n ~ n′ ∷ Empty ^ %
             → Γ     ⊢ Emptyrec F n ~ Emptyrec F′ n′ ∷ F ^ !

    -- Id congruences
    ~-Id  : ∀ {A A' l t t' u u' Γ}
          → Γ ⊢ A ~ A' ∷ U l ^ !
          → Γ ⊢ t ≅ t' ∷ A ^ !
          → Γ ⊢ u ≅ u' ∷ A ^ !
          → Γ ⊢ Id A t u ~ Id A' t' u' ∷ SProp l ^ !

    ~-Idℕ : ∀ {t t' u u' Γ}
          → ⊢ Γ
          → Γ ⊢ t ~ t' ∷ ℕ ^ !
          → Γ ⊢ u ≅ u' ∷ ℕ ^ !
          → Γ ⊢ Id ℕ t u ~ Id ℕ t' u' ∷ SProp ⁰ ^ !

    ~-Idℕ0 : ∀ {u u' Γ}
           → ⊢ Γ
           → Γ ⊢ u ~ u' ∷ ℕ ^ !
           → Γ ⊢ Id ℕ zero u ~ Id ℕ zero u' ∷ SProp ⁰ ^ !

    ~-IdℕS : ∀ {t t' u u' Γ}
           → ⊢ Γ
           → Γ ⊢ t ≅ t' ∷ ℕ ^ !
           → Γ ⊢ u ~ u' ∷ ℕ ^ !
           → Γ ⊢ Id ℕ (suc t) u ~ Id ℕ (suc t') u' ∷ SProp ⁰ ^ !

    ~-IdU : ∀ {t t' u u' l l' Γ}
          → l < l'
          → ⊢ Γ
          → Γ ⊢ t ~ t' ∷ U l ^ !
          → Γ ⊢ u ≅ u' ∷ U l ^ !
          → Γ ⊢ Id (U l) t u ~ Id (U l) t' u' ∷ SProp l' ^ !

    ~-IdUℕ : ∀ {u u' Γ}
           → ⊢ Γ
           → Γ ⊢ u ~ u' ∷ U ⁰ ^ !
           → Γ ⊢ Id (U ⁰) ℕ u ~ Id (U ⁰) ℕ u' ∷ SProp ¹ ^ !

    ~-IdUΠ : ∀ {A rA l l' B A' B' u u' Γ}
           → l < l'
           → Γ ⊢ A ∷ Univ rA l ^ !
           → Γ ⊢ A ≅ A' ∷ Univ rA l ^ !
           → Γ ∙ A ^ rA ⊢ B ≅ B' ∷ U l ^ !
           → Γ ⊢ u ~ u' ∷ U l ^ !
           → Γ ⊢ Id (U l)  (Π A ^ rA ▹ B) u ~ Id (U l) (Π A' ^ rA ▹ B') u' ∷ SProp l' ^ !

    -- cast congruences

    ~-cast : ∀ {A A' B B' l e e' t t' Γ}
           → Γ ⊢ A ~ A' ∷ U l ^ !
           → Γ ⊢ B ≅ B' ∷ U l ^ !
           → Γ ⊢ t ≅ t' ∷ A ^ !
           → Γ ⊢ cast l A B e t ~ cast l A' B' e' t' ∷ B ^ !

    ~-castℕ : ∀ {B B' e e' t t' Γ}
            → ⊢ Γ
            → Γ ⊢ B ~ B' ∷ U ⁰ ^ !
            → Γ ⊢ e ≅ e' ∷ Id (U ⁰) ℕ B ^ %
            → Γ ⊢ t ≅ t' ∷ ℕ ^ !
            → Γ ⊢ cast ⁰ ℕ B e t ~ cast ⁰ ℕ B' e' t' ∷ B ^ !

    ~-castℕℕ : ∀ {e e' t t' Γ}
             → ⊢ Γ
             → Γ ⊢ e ≅ e' ∷ Id (U ⁰) ℕ ℕ ^ %
             → Γ ⊢ t ~ t' ∷ ℕ ^ !
             → Γ ⊢ cast ⁰ ℕ ℕ e t ~ cast ⁰ ℕ ℕ e' t' ∷ ℕ ^ !

    ~-castΠ : ∀ {A A' rA l P P' B B' e e' t t' Γ}
           → Γ ⊢ A ^ rA
           → Γ ⊢ A ≅ A' ∷ Univ rA l ^ !
           → Γ ∙ A ^ rA ⊢ P ≅ P' ∷ U l ^ !
           → Γ ⊢ B ~ B' ∷ U l ^ !
           → Γ ⊢ e ≅ e' ∷ Id (U l) (Π A ^ rA ▹ P) B ^ %
           → Γ ⊢ t ≅ t' ∷ Π A ^ rA ▹ P ^ !
           → Γ ⊢ cast l (Π A ^ rA ▹ P) B e t ~ cast l (Π A' ^ rA ▹ P') B' e' t' ∷ B ^ !

    ~-castℕΠ : ∀ {A A' rA P P' e e' t t' Γ}
             → Γ ⊢ A ∷ Univ rA ⁰ ^ !
             → Γ ⊢ A ≅ A' ∷ Univ rA ⁰ ^ !
             → Γ ∙ A ^ rA ⊢ P ∷ U ⁰ ^ !
             → Γ ∙ A ^ rA ⊢ P ≅ P' ∷ U ⁰ ^ !
             → Γ ⊢ e ≅ e' ∷ Empty ^ %
             → Γ ⊢ t ≅ t' ∷ ℕ ^ !
             → Γ ⊢ cast ⁰ ℕ (Π A ^ rA ▹ P) e t ~ cast ⁰ ℕ (Π A' ^ rA ▹ P') e' t' ∷ (Π A ^ rA ▹ P) ^ !

    ~-castΠℕ : ∀ {A A' rA l P P' e e' t t' Γ}
             → Γ ⊢ A ∷ Univ rA l ^ !
             → Γ ⊢ A ≅ A' ∷ Univ rA l ^ !
             → Γ ∙ A ^ rA ⊢ P ∷ U l ^ !
             → Γ ∙ A ^ rA ⊢ P ≅ P' ∷ U l ^ !
             → Γ ⊢ e ≅ e' ∷ Empty ^ %
             → Γ ⊢ t ≅ t' ∷ (Π A ^ rA ▹ P) ^ !
             → Γ ⊢ cast l (Π A ^ rA ▹ P) ℕ e t ~ cast l (Π A' ^ rA ▹ P') ℕ e' t' ∷ ℕ ^ !

    ~-irrelevance : ∀ {n n′ A Γ} → Γ ⊢ n ∷ A ^ % → Γ ⊢ n′ ∷ A ^ %
                  → Γ ⊢ n ~ n′ ∷ A ^ %

  -- Composition of universe and generic equality compatibility
  ~-to-≅ : ∀ {t u r l Γ} → Γ ⊢ t ~ u ∷ (Univ r l) ^ ! → Γ ⊢ t ≅ u ^ r
  ~-to-≅ t~u = ≅-univ (~-to-≅ₜ t~u)
