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
          → Nf A′
          → Nf B′
          → Γ ⊢ A′ ≅ B′ ^ r
          → Γ ⊢ A  ≅ B ^ r

    ≅ₜ-red : ∀ {a a′ b b′ A B r Γ}
           → Γ ⊢ A ⇒* B ^ r
           → Γ ⊢ a ⇒* a′ ∷ B ^ r
           → Γ ⊢ b ⇒* b′ ∷ B ^ r
           → Nf B
           → Nf a′
           → Nf b′
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

    -- Π-congurence

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


    ~-irrelevance : ∀ {n n′ A Γ} → Γ ⊢ n ∷ A ^ % → Γ ⊢ n′ ∷ A ^ %
                  → Γ ⊢ n ~ n ∷ A ^ %
                  → Γ ⊢ n′ ~ n′ ∷ A ^ %
                  → Γ ⊢ n ~ n′ ∷ A ^ %

  -- Composition of universe and generic equality compatibility
  ~-to-≅ : ∀ {k l r Γ} → Γ ⊢ k ~ l ∷ (Univ r) ^ ! → Γ ⊢ k ≅ l ^ r
  ~-to-≅ k~l = ≅-univ (~-to-≅ₜ k~l)
