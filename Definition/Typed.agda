{-# OPTIONS --without-K --safe #-}

module Definition.Typed where

open import Definition.Untyped

open import Tools.Nat using (Nat)
open import Tools.Product


infixl 30 _∙_
infix 30 Πⱼ_▹_


-- Well-typed variables
data _∷_^_∈_ : (x : Nat) (A : Term) (r : Relevance) (Γ : Con Term) → Set where
  here  : ∀ {Γ A r}                     →         0 ∷ wk1 A ^ r ∈ (Γ ∙ A ^ r )
  there : ∀ {Γ A rA B rB x} (h : x ∷ A ^ rA ∈ Γ) → Nat.suc x ∷ wk1 A ^ rA ∈ (Γ ∙ B ^ rB)

mutual
  -- Well-formed context
  data ⊢_ : Con Term → Set where
    ε   : ⊢ ε
    _∙_ : ∀ {Γ A r}
        → ⊢ Γ
        → Γ ⊢ A ^ r
        → ⊢ Γ ∙ A ^ r

  -- Well-formed type
  data _⊢_^_ (Γ : Con Term) : Term → Relevance → Set where
    ℕⱼ    : ⊢ Γ → Γ ⊢ ℕ ^ !
    Emptyⱼ : ⊢ Γ -> Γ ⊢ Empty ^ %
    Uⱼ    : ∀ {r} → ⊢ Γ → Γ ⊢ (Univ r) ^ !
    Πⱼ_▹_ : ∀ {F rF G rG}
         → Γ     ⊢ F ^ rF
         → Γ ∙ F ^ rF ⊢ G ^ rG
         → Γ     ⊢ Π F ^ rF ▹ G ^ rG
    univ : ∀ {A r}
         → Γ ⊢ A ∷ (Univ r) ^ !
         → Γ ⊢ A ^ r

  -- Well-formed term of a type
  data _⊢_∷_^_ (Γ : Con Term) : Term → Term → Relevance → Set where
    ℕⱼ      : ⊢ Γ → Γ ⊢ ℕ ∷ U ^ !
    Emptyⱼ :  ⊢ Γ → Γ ⊢ Empty ∷ SProp ^ !
    Πⱼ_▹_   : ∀ {F rF G rG}
           → Γ     ⊢ F ∷ (Univ rF) ^ !
           → Γ ∙ F ^ rF ⊢ G ∷ (Univ rG) ^ !
           → Γ     ⊢ Π F ^ rF ▹ G ∷ (Univ rG) ^ !
    var    : ∀ {A r x}
           → ⊢ Γ
           → x ∷ A ^ r ∈ Γ
           → Γ ⊢ var x ∷ A ^ r
    lamⱼ    : ∀ {F rF G rG t}
           → Γ     ⊢ F ^ rF
           → Γ ∙ F ^ rF ⊢ t ∷ G ^ rG
           → Γ     ⊢ lam F ▹ t ∷ Π F ^ rF ▹ G ^ rG
    _∘ⱼ_    : ∀ {g a F rF G rG}
           → Γ ⊢     g ∷ Π F ^ rF ▹ G ^ rG
           → Γ ⊢     a ∷ F ^ rF
           → Γ ⊢ g ∘ a ∷ G [ a ] ^ rG
    zeroⱼ   : ⊢ Γ
           → Γ ⊢ zero ∷ ℕ ^ !
    sucⱼ    : ∀ {n}
           → Γ ⊢ n ∷ ℕ ^ !
           → Γ ⊢ suc n ∷ ℕ ^ !
    natrecⱼ : ∀ {G rG s z n}
           → Γ ∙ ℕ ^ ! ⊢ G ^ rG
           → Γ       ⊢ z ∷ G [ zero ] ^ rG
           → Γ       ⊢ s ∷ Π ℕ ^ ! ▹ (G ^ rG ▹▹ G [ suc (var Nat.zero) ]↑) ^ rG
           → Γ       ⊢ n ∷ ℕ ^ !
           → Γ       ⊢ natrec G z s n ∷ G [ n ] ^ rG
    Emptyrecⱼ : ∀ {A rA e}
           → Γ ⊢ A ^ rA → Γ ⊢ e ∷ Empty ^ % -> Γ ⊢ Emptyrec A e ∷ A ^ rA
    conv   : ∀ {t A B r}
           → Γ ⊢ t ∷ A ^ r
           → Γ ⊢ A ≡ B ^ r
           → Γ ⊢ t ∷ B ^ r

  -- Type equality
  data _⊢_≡_^_ (Γ : Con Term) : Term → Term → Relevance → Set where
    univ   : ∀ {A B r}
           → Γ ⊢ A ≡ B ∷ (Univ r) ^ !
           → Γ ⊢ A ≡ B ^ r
    refl   : ∀ {A r}
           → Γ ⊢ A ^ r
           → Γ ⊢ A ≡ A ^ r
    sym    : ∀ {A B r}
           → Γ ⊢ A ≡ B ^ r
           → Γ ⊢ B ≡ A ^ r
    trans  : ∀ {A B C r}
           → Γ ⊢ A ≡ B ^ r
           → Γ ⊢ B ≡ C ^ r
           → Γ ⊢ A ≡ C ^ r
    Π-cong : ∀ {F H rF G E rG}
           → Γ     ⊢ F ^ rF
           → Γ     ⊢ F ≡ H ^ rF
           → Γ ∙ F ^ rF ⊢ G ≡ E ^ rG
           → Γ     ⊢ Π F ^ rF ▹ G ≡ Π H ^ rF ▹ E ^ rG

  -- Term equality
  data _⊢_≡_∷_^_ (Γ : Con Term) : Term → Term → Term → Relevance → Set where
    refl        : ∀ {t A}
                → Γ ⊢ t ∷ A ^ !
                → Γ ⊢ t ≡ t ∷ A ^ !
    sym         : ∀ {t u A}
                → Γ ⊢ t ≡ u ∷ A ^ !
                → Γ ⊢ u ≡ t ∷ A ^ !
    trans       : ∀ {t u v A}
                → Γ ⊢ t ≡ u ∷ A ^ !
                → Γ ⊢ u ≡ v ∷ A ^ !
                → Γ ⊢ t ≡ v ∷ A ^ !
    conv        : ∀ {A B r t u}
                → Γ ⊢ t ≡ u ∷ A ^ r
                → Γ ⊢ A ≡ B ^ r
                → Γ ⊢ t ≡ u ∷ B ^ r
    Π-cong      : ∀ {E F G H rF rG}
                → Γ     ⊢ F ^ rF
                → Γ     ⊢ F ≡ H       ∷ (Univ rF) ^ !
                → Γ ∙ F ^ rF ⊢ G ≡ E       ∷ (Univ rG) ^ !
                → Γ     ⊢ Π F ^ rF ▹ G ≡ Π H ^ rF ▹ E ∷ (Univ rG) ^ !
    app-cong    : ∀ {a b f g F G rF}
                → Γ ⊢ f ≡ g ∷ Π F ^ rF ▹ G ^ !
                → Γ ⊢ a ≡ b ∷ F ^ rF
                → Γ ⊢ f ∘ a ≡ g ∘ b ∷ G [ a ] ^ !
    β-red       : ∀ {a t F rF G}
                → Γ     ⊢ F ^ rF
                → Γ ∙ F ^ rF ⊢ t ∷ G ^ !
                → Γ     ⊢ a ∷ F ^ rF
                → Γ     ⊢ (lam F ▹ t) ∘ a ≡ t [ a ] ∷ G [ a ] ^ !
    η-eq        : ∀ {f g F rF G}
                → Γ     ⊢ F ^ rF
                → Γ     ⊢ f ∷ Π F ^ rF ▹ G ^ !
                → Γ     ⊢ g ∷ Π F ^ rF ▹ G ^ !
                → Γ ∙ F ^ rF ⊢ wk1 f ∘ var Nat.zero ≡ wk1 g ∘ var Nat.zero ∷ G ^ !
                → Γ     ⊢ f ≡ g ∷ Π F ^ rF ▹ G ^ !
    suc-cong    : ∀ {m n}
                → Γ ⊢ m ≡ n ∷ ℕ ^ !
                → Γ ⊢ suc m ≡ suc n ∷ ℕ ^ !
    natrec-cong : ∀ {z z′ s s′ n n′ F F′}
                → Γ ∙ ℕ ^ ! ⊢ F ≡ F′ ^ !
                → Γ     ⊢ z ≡ z′ ∷ F [ zero ] ^ !
                → Γ     ⊢ s ≡ s′ ∷ Π ℕ ^ ! ▹ (F ^ ! ▹▹ F [ suc (var Nat.zero) ]↑) ^ !
                → Γ     ⊢ n ≡ n′ ∷ ℕ ^ !
                → Γ     ⊢ natrec F z s n ≡ natrec F′ z′ s′ n′ ∷ F [ n ] ^ !
    natrec-zero : ∀ {z s F}
                → Γ ∙ ℕ ^ ! ⊢ F ^ !
                → Γ     ⊢ z ∷ F [ zero ] ^ !
                → Γ     ⊢ s ∷ Π ℕ ^ ! ▹ (F ^ ! ▹▹ F [ suc (var Nat.zero) ]↑) ^ !
                → Γ     ⊢ natrec F z s zero ≡ z ∷ F [ zero ] ^ !
    natrec-suc  : ∀ {n z s F}
                → Γ     ⊢ n ∷ ℕ ^ !
                → Γ ∙ ℕ ^ ! ⊢ F ^ !
                → Γ     ⊢ z ∷ F [ zero ] ^ !
                → Γ     ⊢ s ∷ Π ℕ ^ ! ▹ (F ^ ! ▹▹ F [ suc (var Nat.zero) ]↑) ^ !
                → Γ     ⊢ natrec F z s (suc n) ≡ (s ∘ n) ∘ (natrec F z s n)
                        ∷ F [ suc n ] ^ !
    Emptyrec-cong : ∀ {A A' e e'}
                → Γ ⊢ A ≡ A' ^ !
                → Γ ⊢ e ≡ e' ∷ Empty ^ %
                → Γ ⊢ Emptyrec A e ≡ Emptyrec A' e' ∷ A ^ !
    proof-irrelevance : ∀ {t u A}
                      → Γ ⊢ t ∷ A ^ %
                      → Γ ⊢ u ∷ A ^ %
                      → Γ ⊢ t ≡ u ∷ A ^ %

-- Term reduction
data _⊢_⇒_∷_ (Γ : Con Term) : Term → Term → Term → Set where
  conv         : ∀ {A B t u}
               → Γ ⊢ t ⇒ u ∷ A 
               → Γ ⊢ A ≡ B ^ !
               → Γ ⊢ t ⇒ u ∷ B 
  app-subst    : ∀ {A B t u a rA}
               → Γ ⊢ t ⇒ u ∷ Π A ^ rA ▹ B
               → Γ ⊢ a ∷ A ^ rA
               → Γ ⊢ t ∘ a ⇒ u ∘ a ∷ B [ a ] 
  β-red        : ∀ {A B a t rA}
               → Γ     ⊢ A ^ rA
               → Γ ∙ A ^ rA ⊢ t ∷ B ^ !
               → Γ     ⊢ a ∷ A ^ rA
               → Γ     ⊢ (lam A ▹ t) ∘ a ⇒ t [ a ] ∷ B [ a ] 
  natrec-subst : ∀ {z s n n′ F}
               → Γ ∙ ℕ ^ ! ⊢ F ^ !
               → Γ     ⊢ z ∷ F [ zero ] ^ !
               → Γ     ⊢ s ∷ Π ℕ ^ ! ▹ (F ^ ! ▹▹ F [ suc (var Nat.zero) ]↑) ^ !
               → Γ     ⊢ n ⇒ n′ ∷ ℕ 
               → Γ     ⊢ natrec F z s n ⇒ natrec F z s n′ ∷ F [ n ]
  natrec-zero  : ∀ {z s F}
               → Γ ∙ ℕ ^ ! ⊢ F ^ !
               → Γ     ⊢ z ∷ F [ zero ] ^ !
               → Γ     ⊢ s ∷ Π ℕ ^ ! ▹ (F ^ ! ▹▹ F [ suc (var Nat.zero) ]↑) ^ !
               → Γ     ⊢ natrec F z s zero ⇒ z ∷ F [ zero ] 
  natrec-suc   : ∀ {n z s F}
               → Γ     ⊢ n ∷ ℕ ^ !
               → Γ ∙ ℕ ^ ! ⊢ F ^ !
               → Γ     ⊢ z ∷ F [ zero ] ^ !
               → Γ     ⊢ s ∷ Π ℕ ^ ! ▹ (F ^ ! ▹▹ F [ suc (var Nat.zero) ]↑) ^ !
               → Γ     ⊢ natrec F z s (suc n) ⇒ (s ∘ n) ∘ (natrec F z s n)
                       ∷ F [ suc n ] 

-- Type reduction
data _⊢_⇒_^_ (Γ : Con Term) : Term → Term → Relevance → Set where
  univ : ∀ {A B r}
       → Γ ⊢ A ⇒ B ∷ (Univ r)
       → Γ ⊢ A ⇒ B ^ r

-- Term reduction closure
data _⊢_⇒*_∷_ (Γ : Con Term) : Term → Term → Term → Set where
  id  : ∀ {A t}
      → Γ ⊢ t ∷ A ^ !
      → Γ ⊢ t ⇒* t ∷ A
  _⇨_ : ∀ {A t t′ u}
      → Γ ⊢ t  ⇒  t′ ∷ A 
      → Γ ⊢ t′ ⇒* u  ∷ A
      → Γ ⊢ t  ⇒* u  ∷ A

-- Type reduction closure
data _⊢_⇒*_^_ (Γ : Con Term) : Term → Term → Relevance → Set where
  id  : ∀ {A r}
      → Γ ⊢ A ^ r
      → Γ ⊢ A ⇒* A ^ r
  _⇨_ : ∀ {A A′ B r}
      → Γ ⊢ A  ⇒  A′ ^ r
      → Γ ⊢ A′ ⇒* B  ^ r
      → Γ ⊢ A  ⇒* B  ^ r

-- Type reduction to whnf
_⊢_↘_^_ : (Γ : Con Term) → Term → Term → Relevance → Set
Γ ⊢ A ↘ B ^ r = Γ ⊢ A ⇒* B ^ r × Whnf B

-- Term reduction to whnf
_⊢_↘_∷_ : (Γ : Con Term) → Term → Term → Term → Set
Γ ⊢ t ↘ u ∷ A = Γ ⊢ t ⇒* u ∷ A × Whnf u

-- Type equality with well-formed types
_⊢_:≡:_^_ : (Γ : Con Term) → Term → Term → Relevance → Set
Γ ⊢ A :≡: B ^ r = Γ ⊢ A ^ r × Γ ⊢ B ^ r × (Γ ⊢ A ≡ B ^ r)

-- Term equality with well-formed terms
_⊢_:≡:_∷_^_ : (Γ : Con Term) → Term → Term → Term → Relevance → Set
Γ ⊢ t :≡: u ∷ A ^ r = Γ ⊢ t ∷ A ^ r × Γ ⊢ u ∷ A ^ r × (Γ ⊢ t ≡ u ∷ A ^ r)

-- Type reduction closure with well-formed types
record _⊢_:⇒*:_^_ (Γ : Con Term) (A B : Term) (r : Relevance) : Set where
  constructor [_,_,_]
  field
    ⊢A : Γ ⊢ A ^ r
    ⊢B : Γ ⊢ B ^ r
    D  : Γ ⊢ A ⇒* B ^ r

open _⊢_:⇒*:_^_ using () renaming (D to red) public

-- Term reduction closure with well-formed terms
record _⊢_:⇒*:_∷_ (Γ : Con Term) (t u A : Term) : Set where
  constructor [_,_,_]
  field
    ⊢t : Γ ⊢ t ∷ A ^ !
    ⊢u : Γ ⊢ u ∷ A ^ !
    d  : Γ ⊢ t ⇒* u ∷ A

open _⊢_:⇒*:_∷_ using () renaming (d to redₜ) public

-- Well-formed substitutions.
data _⊢ˢ_∷_ (Δ : Con Term) (σ : Subst) : (Γ : Con Term) → Set where
  id : Δ ⊢ˢ σ ∷ ε
  _,_ : ∀ {Γ A rA}
      → Δ ⊢ˢ tail σ ∷ Γ
      → Δ ⊢ head σ ∷ subst (tail σ) A ^ rA
      → Δ ⊢ˢ σ ∷ Γ ∙ A ^ rA

-- Conversion of well-formed substitutions.
data _⊢ˢ_≡_∷_ (Δ : Con Term) (σ σ′ : Subst) : (Γ : Con Term) → Set where
  id : Δ ⊢ˢ σ ≡ σ′ ∷ ε
  _,_ : ∀ {Γ A rA}
      → Δ ⊢ˢ tail σ ≡ tail σ′ ∷ Γ
      → Δ ⊢ head σ ≡ head σ′ ∷ subst (tail σ) A ^ rA
      → Δ ⊢ˢ σ ≡ σ′ ∷ Γ ∙ A ^ rA

-- Note that we cannot use the well-formed substitutions.
-- For that, we need to prove the fundamental theorem for substitutions.
