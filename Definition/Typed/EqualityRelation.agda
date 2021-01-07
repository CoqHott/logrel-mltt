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
    ≅-univ : ∀ {A B r Γ}
           → Γ ⊢ A ≅ B ∷ (Univ r) ^ !
           → Γ ⊢ A ≅ B ^ r

    -- Symmetry
    ≅-sym  : ∀ {A B r Γ} → Γ ⊢ A ≅ B ^ r → Γ ⊢ B ≅ A ^ r
    ≅ₜ-sym : ∀ {t u A r Γ} → Γ ⊢ t ≅ u ∷ A ^ r → Γ ⊢ u ≅ t ∷ A ^ r
    ~-sym  : ∀ {k l A r Γ} → Γ ⊢ k ~ l ∷ A ^ r → Γ ⊢ l ~ k ∷ A ^ r

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

    ≅ₜ-red : ∀ {a a′ b b′ A B r Γ}
           → Γ ⊢ A ⇒* B ^ r
           → Γ ⊢ a ⇒* a′ ∷ B ^ r
           → Γ ⊢ b ⇒* b′ ∷ B ^ r
           → Whnf B
           → Whnf a′
           → Whnf b′
           → Γ ⊢ a′ ≅ b′ ∷ B ^ r
           → Γ ⊢ a  ≅ b  ∷ A ^ r

    -- Universe type reflexivity
    ≅-Urefl   : ∀ {r Γ} → ⊢ Γ → Γ ⊢ (Univ r) ≅ (Univ r) ^ !

    -- Natural number type reflexivity
    ≅-ℕrefl   : ∀ {Γ} → ⊢ Γ → Γ ⊢ ℕ ≅ ℕ ^ !
    ≅ₜ-ℕrefl  : ∀ {Γ} → ⊢ Γ → Γ ⊢ ℕ ≅ ℕ ∷ U ^ !

    -- Empty type reflexivity
    ≅-Emptyrefl   : ∀ {Γ} → ⊢ Γ → Γ ⊢ Empty ≅ Empty ^ %
    ≅ₜ-Emptyrefl  : ∀ {Γ} → ⊢ Γ → Γ ⊢ Empty ≅ Empty ∷ SProp ^ !

    -- Π-congruence

    ≅-Π-cong  : ∀ {F G H E rF rG Γ}
              → Γ ⊢ F ^ rF
              → Γ ⊢ F ≅ H ^ rF
              → Γ ∙ F ^ rF ⊢ G ≅ E ^ rG
              → Γ ⊢ Π F ^ rF ▹ G ≅ Π H ^ rF ▹ E ^ rG

    ≅ₜ-Π-cong : ∀ {F G H E rF rG Γ}
              → Γ ⊢ F ^ rF
              → Γ ⊢ F ≅ H ∷ (Univ rF) ^ !
              → Γ ∙ F ^ rF ⊢ G ≅ E ∷ (Univ rG) ^ !
              → Γ ⊢ Π F ^ rF ▹ G ≅ Π H ^ rF ▹ E ∷ (Univ rG) ^ !

    -- Σ-congruence
    -- Since Σ types are always small, no need for a type-level rule
    ≅ₜ-Σ-cong : ∀ {F G H E Γ}
              → Γ ⊢ F ^ %
              → Γ ⊢ F ≅ H ∷ SProp ^ !
              → Γ ∙ F ^ % ⊢ G ≅ E ∷ SProp ^ !
              → Γ ⊢ Σ F ▹ G ≅ Σ H ▹ E ∷ SProp ^ !

    -- Zero reflexivity
    ≅ₜ-zerorefl : ∀ {Γ} → ⊢ Γ → Γ ⊢ zero ≅ zero ∷ ℕ ^ !

    -- Successor congurence
    ≅-suc-cong : ∀ {m n Γ} → Γ ⊢ m ≅ n ∷ ℕ ^ ! → Γ ⊢ suc m ≅ suc n ∷ ℕ ^ !

    -- η-equality
    ≅-η-eq : ∀ {f g F G rF rG Γ}
              → Γ ⊢ F ^ rF
              → Γ ⊢ f ∷ Π F ^ rF ▹ G ^ rG
              → Γ ⊢ g ∷ Π F ^ rF ▹ G ^ rG
              → Function f
              → Function g
              → Γ ∙ F ^ rF ⊢ wk1 f ∘ var 0 ≅ wk1 g ∘ var 0 ∷ G ^ rG
              → Γ ⊢ f ≅ g ∷ Π F ^ rF ▹ G ^ rG

    -- Variable reflexivity
    ~-var : ∀ {x A r Γ} → Γ ⊢ var x ∷ A ^ r → Γ ⊢ var x ~ var x ∷ A ^ r

    -- Application congurence
    ~-app : ∀ {a b f g F G rF rG Γ}
          → Γ ⊢ f ~ g ∷ Π F ^ rF ▹ G ^ rG
          → Γ ⊢ a ≅ b ∷ F ^ rF
          → Γ ⊢ f ∘ a ~ g ∘ b ∷ G [ a ] ^ rG

    -- Natural recursion congurence
    ~-natrec : ∀ {z z′ s s′ n n′ F F′ rF Γ}
             → Γ ∙ ℕ ^ ! ⊢ F ≅ F′ ^ rF
             → Γ     ⊢ z ≅ z′ ∷ F [ zero ] ^ rF
             → Γ     ⊢ s ≅ s′ ∷ Π ℕ ^ ! ▹ (F ^ rF ▹▹ F [ suc (var 0) ]↑) ^ rF
             → Γ     ⊢ n ~ n′ ∷ ℕ ^ !
             → Γ     ⊢ natrec F z s n ~ natrec F′ z′ s′ n′ ∷ F [ n ] ^ rF

    -- Empty recursion congurence
    ~-Emptyrec : ∀ {n n′ F F′ rF Γ}
             → Γ ⊢ F ≅ F′ ^ rF
             → Γ     ⊢ n ~ n′ ∷ Empty ^ %
             → Γ     ⊢ Emptyrec F n ~ Emptyrec F′ n′ ∷ F ^ rF

    -- Id congruences
    ~-Id  : ∀ {A A' t t' u u' Γ}
          → Γ ⊢ A ~ A' ∷ U ^ !
          → Γ ⊢ t ≅ t' ∷ A ^ !
          → Γ ⊢ u ≅ u' ∷ A ^ !
          → Γ ⊢ Id A t u ~ Id A' t' u' ∷ SProp ^ !

    ~-Idℕ : ∀ {t t' u u' Γ}
          → Γ ⊢ t ~ t' ∷ ℕ ^ !
          → Γ ⊢ u ≅ u' ∷ ℕ ^ !
          → Γ ⊢ Id ℕ t u ~ Id ℕ t' u' ∷ SProp ^ !

    ~-Idℕ0 : ∀ {u u' Γ}
           → Γ ⊢ u ~ u' ∷ ℕ ^ !
           → Γ ⊢ Id ℕ zero u ~ Id ℕ zero u' ∷ SProp ^ !

    ~-IdℕS : ∀ {t t' u u' Γ}
           → Γ ⊢ t ≅ t' ∷ ℕ ^ !
           → Γ ⊢ u ~ u' ∷ ℕ ^ !
           → Γ ⊢ Id ℕ (suc t) u ~ Id ℕ (suc t') u' ∷ SProp ^ !

    ~-IdU : ∀ {t t' u u' Γ}
          → Γ ⊢ t ~ t' ∷ U ^ !
          → Γ ⊢ u ≅ u' ∷ U ^ !
          → Γ ⊢ Id U t u ~ Id U t' u' ∷ SProp ^ !

    ~-IdUℕ : ∀ {u u' Γ}
           → Γ ⊢ u ~ u' ∷ U ^ !
           → Γ ⊢ Id U ℕ u ~ Id U ℕ u' ∷ SProp ^ !

    ~-IdUΠ : ∀ {A rA B A' B' u u' Γ}
           → Γ ⊢ A ≅ A' ∷ Univ rA ^ !
           → Γ ∙ A ^ rA ⊢ B ≅ B' ∷ U ^ !
           → Γ ⊢ u ~ u' ∷ U ^ !
           → Γ ⊢ Id U (Π A ^ rA ▹ B) u ~ Id U (Π A' ^ rA ▹ B) u' ∷ SProp ^ !

    -- cast congruences

    ~-cast : ∀ {A A' B B' e e' t t' Γ}
           → Γ ⊢ A ~ A' ∷ U ^ !
           → Γ ⊢ B ≅ B' ∷ U ^ !
           → Γ ⊢ e ≅ e' ∷ Id U A B ^ %
           → Γ ⊢ t ≅ t' ∷ A ^ !
           → Γ ⊢ cast A B e t ~ cast A' B' e' t' ∷ B ^ !

    ~-castℕ : ∀ {B B' e e' t t' Γ}
           → Γ ⊢ B ~ B' ∷ U ^ !
           → Γ ⊢ e ≅ e' ∷ Id U ℕ B ^ %
           → Γ ⊢ t ≅ t' ∷ ℕ ^ !
           → Γ ⊢ cast ℕ B e t ~ cast ℕ B' e' t' ∷ B ^ !

    ~-castℕℕ : ∀ {e e' t t' Γ}
           → Γ ⊢ e ≅ e' ∷ Id U ℕ ℕ ^ %
           → Γ ⊢ t ~ t' ∷ ℕ ^ !
           → Γ ⊢ cast ℕ ℕ e t ~ cast ℕ ℕ e' t' ∷ ℕ ^ !

    ~-castΠ : ∀ {A A' rA P P' B B' e e' t t' Γ}
           → Γ ⊢ A ≅ A' ∷ Univ rA ^ !
           → Γ ∙ A ^ rA ⊢ P ≅ P' ∷ U ^ !
           → Γ ⊢ B ~ B' ∷ U ^ !
           → Γ ⊢ e ≅ e' ∷ Id U (Π A ^ rA ▹ P) B ^ %
           → Γ ⊢ t ≅ t' ∷ Π A ^ rA ▹ P ^ !
           → Γ ⊢ cast (Π A ^ rA ▹ P) B e t ~ cast (Π A' ^ rA ▹ P') B' e' t' ∷ B ^ !

    ~-irrelevance : ∀ {n n′ A Γ} → Γ ⊢ n ∷ A ^ % → Γ ⊢ n′ ∷ A ^ %
                  → Γ ⊢ n ~ n ∷ A ^ %
                  → Γ ⊢ n′ ~ n′ ∷ A ^ %
                  → Γ ⊢ n ~ n′ ∷ A ^ %

  -- Composition of universe and generic equality compatibility
  ~-to-≅ : ∀ {k l r Γ} → Γ ⊢ k ~ l ∷ (Univ r) ^ ! → Γ ⊢ k ≅ l ^ r
  ~-to-≅ k~l = ≅-univ (~-to-≅ₜ k~l)
