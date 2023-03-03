{-# OPTIONS   --safe  #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Reduction

open import Tools.Product
import Tools.PropositionalEquality as PE

import Data.Fin as Fin
import Data.Nat as Nat

-- The different cases of the logical relation are spread out through out
-- this file. This is due to them having different dependencies.

-- We will refer to expressions that satisfies the logical relation as reducible.

-- Reducibility of Neutrals:

-- Neutral type
record _⊩ne_^[_,_] (Γ : Con Term) (A : Term) (r : Relevance) (l : Level) : Set where
  constructor ne
  field
    K   : Term
    D   : Γ ⊢ A :⇒*: K ^ [ r , ι l ]
    neK : Neutral K
    K≡K : Γ ⊢ K ~ K ∷ (Univ r l) ^ [ ! , next l ]

-- Neutral type equality
record _⊩ne_≡_^[_,_]/_ (Γ : Con Term) (A B : Term) (r : Relevance) (l : Level) ([A] : Γ ⊩ne A ^[ r , l ]) : Set where
  constructor ne₌
  open _⊩ne_^[_,_] [A]
  field
    M   : Term
    D′  : Γ ⊢ B :⇒*: M ^ [ r , ι l ]
    neM : Neutral M
    K≡M : Γ ⊢ K ~ M ∷ (Univ r l) ^ [ ! , next l ]

-- Neutral term in NF
record _⊩neNf_∷_^_ (Γ : Con Term) (k A : Term) (r : TypeInfo) : Set where
  inductive
  constructor neNfₜ
  field
    neK  : Neutral k
    ⊢k   : Γ ⊢ k ∷ A ^ r
    k≡k  : Γ ⊢ k ~ k ∷ A ^ r

-- Neutral relevant term
record _⊩ne_∷_^_/_ (Γ : Con Term) (t A : Term) (l : Level) ([A] : Γ ⊩ne A ^[ ! , l ]) : Set where
  inductive
  constructor neₜ
  open _⊩ne_^[_,_] [A]
  field
    k   : Term
    d   : Γ ⊢ t :⇒*: k ∷ K ^ ι l
    nf  : Γ ⊩neNf k ∷ K ^ [ ! , ι l ]

-- Neutral irrelevant term
record _⊩neIrr_∷_^_/_ (Γ : Con Term) (t A : Term) (l : Level) ([A] : Γ ⊩ne A ^[ % , l ]) : Set where
  inductive
  constructor neₜ
  open _⊩ne_^[_,_] [A]
  field
    d : Γ ⊢ t ∷ A ^ [ % , ι l ]

-- Neutral term equality in NF
record _⊩neNf_≡_∷_^_ (Γ : Con Term) (k m A : Term) (r : TypeInfo) : Set where
  inductive
  constructor neNfₜ₌
  field
    neK  : Neutral k
    neM  : Neutral m
    k≡m  : Γ ⊢ k ~ m ∷ A ^ r

-- Neutral relevant term equality
record _⊩ne_≡_∷_^_/_ (Γ : Con Term) (t u A : Term) (l : Level) ([A] : Γ ⊩ne A ^[ ! , l ]) : Set where
  constructor neₜ₌
  open _⊩ne_^[_,_] [A]
  field
    k m : Term
    d   : Γ ⊢ t :⇒*: k ∷ K ^ ι l
    d′  : Γ ⊢ u :⇒*: m ∷ K ^ ι l
    nf  : Γ ⊩neNf k ≡ m ∷ K ^ [ ! , ι l ]

-- Neutral irrelevant term equality
record _⊩neIrr_≡_∷_^_/_ (Γ : Con Term) (t u A : Term) (l : Level) ([A] : Γ ⊩ne A ^[ % , l ]) : Set where
  constructor neₜ₌
  open _⊩ne_^[_,_] [A]
  field
    d   : Γ ⊢ t ∷ A ^ [ % , ι l ]
    d′  : Γ ⊢ u ∷ A ^ [ % , ι l ]

-- Reducibility of natural numbers:

-- Natural number type
_⊩ℕ_ : (Γ : Con Term) (A : Term) → Set
Γ ⊩ℕ A = Γ ⊢ A :⇒*: ℕ ^ [ ! , ι ⁰ ]

-- Natural number type equality
_⊩ℕ_≡_ : (Γ : Con Term) (A B : Term) → Set
Γ ⊩ℕ A ≡ B = Γ ⊢ B ⇒* ℕ ^ [ ! , ι ⁰ ]

mutual
  -- Natural number term
  data _⊩ℕ_∷ℕ (Γ : Con Term) (t : Term) : Set where
    ℕₜ : (n : Term) (d : Γ ⊢ t :⇒*: n ∷ ℕ ^ ι ⁰) (n≡n : Γ ⊢ n ≅ n ∷ ℕ ^ [ ! , ι ⁰ ])
         (prop : Natural-prop Γ n)
       → Γ ⊩ℕ t ∷ℕ

  -- NF property of natural number terms
  data Natural-prop (Γ : Con Term) : (n : Term) → Set where
    -- sucᵣ  : ∀ {n} → Γ ⊩ℕ n ∷ℕ → Natural-prop Γ (suc n)
    sucᵣ  : ∀ {n} → Natural-prop Γ n → Natural-prop Γ (suc n)
    zeroᵣ : Natural-prop Γ zero
    ne    : ∀ {n} → Γ ⊩neNf n ∷ ℕ ^ [ ! , ι ⁰ ] → Natural-prop Γ n

mutual
  -- Natural number term equality
  data _⊩ℕ_≡_∷ℕ (Γ : Con Term) (t u : Term) : Set where
    ℕₜ₌ : (k k′ : Term) (d : Γ ⊢ t :⇒*: k  ∷ ℕ ^ ι ⁰) (d′ : Γ ⊢ u :⇒*: k′ ∷ ℕ ^ ι ⁰)
          (k≡k′ : Γ ⊢ k ≅ k′ ∷ ℕ ^ [ ! , ι ⁰ ])
          (prop : [Natural]-prop Γ k k′) → Γ ⊩ℕ t ≡ u ∷ℕ

  -- NF property of Natural number term equality
  data [Natural]-prop (Γ : Con Term) : (n n′ : Term) → Set where
    sucᵣ  : ∀ {n n′} → [Natural]-prop Γ n n′ → [Natural]-prop Γ (suc n) (suc n′)
    -- sucᵣ  : ∀ {n n′} → Γ ⊩ℕ n ≡ n′ ∷ℕ → [Natural]-prop Γ (suc n) (suc n′)
    zeroᵣ : [Natural]-prop Γ zero zero
    ne    : ∀ {n n′} → Γ ⊩neNf n ≡ n′ ∷ ℕ ^ [ ! , ι ⁰ ] → [Natural]-prop Γ n n′

-- Natural extraction from term NF property
natural : ∀ {Γ n} → Natural-prop Γ n → Natural n
natural (sucᵣ x) = sucₙ (natural x)
natural zeroᵣ = zeroₙ
natural (ne (neNfₜ neK ⊢k k≡k)) = ne neK

-- Natural extraction from term equality NF property
split : ∀ {Γ a b} → [Natural]-prop Γ a b → Natural a × Natural b
split (sucᵣ x) = let a , b = split x in sucₙ a , sucₙ b
split zeroᵣ = zeroₙ , zeroₙ
split (ne (neNfₜ₌ neK neM k≡m)) = ne neK , ne neM

-- Reducibility of Empty

-- Empty type
_⊩Empty_ : (Γ : Con Term) (A : Term) → Set
Γ ⊩Empty A = Γ ⊢ A :⇒*: Empty ⁰ ^ [ % , ι ⁰ ]

-- Empty type equality
_⊩Empty_≡_ : (Γ : Con Term) (A B : Term) → Set
Γ ⊩Empty A ≡ B = Γ ⊢ B ⇒* Empty ⁰ ^ [ % , ι ⁰ ]

data Empty-prop (Γ : Con Term) (n : Term) : Set where
  ne    : Γ ⊢ n ∷ Empty ⁰ ^ [ % , ι ⁰ ] → Empty-prop Γ n

-- -- Empty term

data _⊩Empty_∷Empty (Γ : Con Term) (t : Term) : Set where
  Emptyₜ : (prop : Empty-prop Γ t) → Γ ⊩Empty t ∷Empty

data [Empty]-prop (Γ : Con Term) : (n n′ : Term) → Set where
  ne    : ∀ {n n′} → Γ ⊢ n ∷ Empty ⁰ ^ [ % , ι ⁰ ] → Γ ⊢ n′ ∷ Empty ⁰ ^ [ % , ι ⁰ ]  → [Empty]-prop Γ n n′

-- Empty term equality
data _⊩Empty_≡_∷Empty (Γ : Con Term) (t u : Term) : Set where
  Emptyₜ₌ : (prop : [Empty]-prop Γ t u) → Γ ⊩Empty t ≡ u ∷Empty

-- impredicative and irrelevant Π-type
record _⊩Πirr_ (Γ : Con Term) (A : Term) : Set where
  inductive
  eta-equality
  constructor Πirrᵣ
  field
    rF : Relevance
    lF : Level
    F : Term
    G : Term
    D : Γ ⊢ A :⇒*: Π F ^ rF ° lF ▹ G ° ⁰ ° ⁰ ^ % ^ [ % , ι ⁰ ]
    nf : Nf (Π F ^ rF ° lF ▹ G ° ⁰ ° ⁰ ^ %)
    ⊢F : Γ ⊢ F ^ [ rF , ι lF ]
    ⊢G : Γ ∙ F ^ [ rF , ι lF ] ⊢ G ^ [ % , ι ⁰ ]
    A≡A : Γ ⊢ Π F ^ rF ° lF ▹ G ° ⁰ ° ⁰ ^ % ≅ Π F ^ rF ° lF ▹ G ° ⁰ ° ⁰ ^ % ^ [ % , ι ⁰ ]
          
-- impredicative Π-type equality
record _⊩Πirr_≡_/_ (Γ : Con Term) (A B : Term) ([A] : Γ ⊩Πirr A ) : Set where
  inductive
  eta-equality
  constructor Πirr₌
  open _⊩Πirr_ [A]
  field
    F′     : Term
    G′     : Term
    D′     : Γ ⊢ B ⇒* Π F′ ^ rF ° lF ▹ G′ ° ⁰ ° ⁰ ^ % ^ [ % , ι ⁰ ]
    nf′     : Nf (Π F′ ^ rF ° lF ▹ G′ ° ⁰ ° ⁰ ^ %)
    A≡B    : Γ ⊢ Π F ^ rF ° lF ▹ G ° ⁰ ° ⁰ ^ % ≅ Π F′ ^ rF ° lF ▹ G′ ° ⁰ ° ⁰ ^ % ^ [ % , ι ⁰ ]

-- Irrelevant term of Π-type
_⊩Πirr_∷_/_ : (Γ : Con Term) (t A : Term) ([A] : Γ ⊩Πirr A ) → Set
Γ ⊩Πirr t ∷ A / Πirrᵣ rF lF F G D nf ⊢F ⊢G A≡A =
  Γ ⊢ t ∷ Π F ^ rF ° lF ▹ G ° ⁰ ° ⁰ ^ % ^ [ % , ι ⁰ ]

-- Irrelevant term equality of Π-type
_⊩Πirr_≡_∷_/_ : (Γ : Con Term) (t u A : Term) ([A] : Γ ⊩Πirr A ) → Set
Γ ⊩Πirr t ≡ u ∷ A / Πirrᵣ rF lF F G D nf ⊢F ⊢G A≡A =
      (Γ ⊢ t ∷ Π F ^ rF ° lF ▹ G ° ⁰ ° ⁰ ^ % ^ [ % , ι ⁰ ])
      ×
      (Γ ⊢ u ∷ Π F ^ rF ° lF ▹ G ° ⁰ ° ⁰ ^ % ^ [ % , ι ⁰ ])



-- Identity types
record _⊩Id_ (Γ : Con Term) (A : Term) : Set where
  inductive
  eta-equality
  constructor Idᵣ
  field
    B : Term
    t : Term
    u : Term
    l : Level
    D : Γ ⊢ A :⇒*: Id B t u ^ [ % , ι ⁰ ]
    nf : Nf (Id B t u)
    ⊢B : Γ ⊢ B ^ [ ! , ι l ]
    ⊢t : Γ ⊢ t ∷ B ^ [ ! , ι l ]
    ⊢u : Γ ⊢ u ∷ B ^ [ ! , ι l ]
    A≡A : Γ ⊢ (Id B t u) ≅ (Id B t u) ^ [ % , ι ⁰ ]

-- Id-type equality
record _⊩Id_≡_/_ (Γ : Con Term) (A A' : Term) ([A] : Γ ⊩Id A ) : Set where
  inductive
  eta-equality
  constructor Id₌
  open _⊩Id_ [A]
  field
    B′     : Term
    t′     : Term
    u′     : Term
    D′     : Γ ⊢ A' ⇒* Id B′ t′ u′ ^ [ % , ι ⁰ ]
    nf′     : Nf (Id B′ t′ u′)
    A≡B    : Γ ⊢ Id B t u ≅ Id B′ t′ u′ ^ [ % , ι ⁰ ]

-- Terms of Id-types (always irrelevant)
_⊩Id_∷_/_ : (Γ : Con Term) (e A : Term) ([A] : Γ ⊩Id A ) → Set
Γ ⊩Id e ∷ A / Idᵣ B t u l D nf ⊢B ⊢t ⊢u A≡A =
  Γ ⊢ e ∷ Id B t u ^ [ % , ι ⁰ ]

-- Term equality for Id-types
_⊩Id_≡_∷_/_ : (Γ : Con Term) (e e' A : Term) ([A] : Γ ⊩Id A) → Set
Γ ⊩Id e ≡ e' ∷ A / Idᵣ B t u l D nf ⊢B ⊢t ⊢u A≡A =
      (Γ ⊢ e ∷ Id B t u ^ [ % , ι ⁰ ])
      ×
      (Γ ⊢ e' ∷ Id B t u ^ [ % , ι ⁰ ])

-- Logical relation

record LogRelKit : Set₁ where
  constructor Kit
  field
    _⊩U_^_ : (Γ : Con Term) → Term → TypeLevel → Set
    _⊩Π_^[_] : (Γ : Con Term) → Term → Level → Set

    _⊩_^_ : (Γ : Con Term) → Term → TypeInfo → Set
    _⊩_≡_^_/_ : (Γ : Con Term) (A B : Term) (r : TypeInfo) → Γ ⊩ A ^ r → Set
    _⊩_∷_^_/_ : (Γ : Con Term) (t A : Term) (r : TypeInfo) → Γ ⊩ A ^ r → Set
    _⊩_≡_∷_^_/_ : (Γ : Con Term) (t u A : Term) (r : TypeInfo) → Γ ⊩ A ^ r → Set

module LogRel (l : TypeLevel) (rec : ∀ {l′} → l′ <∞ l → LogRelKit) where

  -- Reducibility of Universe:

  -- Universe type
  record _⊩¹U_^_ (Γ : Con Term) (A : Term) (ll : TypeLevel) : Set where
    constructor Uᵣ
    field
      r : Relevance
      l′ : Level
      l< : ι l′ <∞ l
      eq : next l′ PE.≡ ll
      d : Γ ⊢ A :⇒*: Univ r l′ ^ [ ! , next l′ ]

  -- Universe type equality
  _⊩¹U_≡_^_/_ : (Γ : Con Term) (A B : Term) (ll : TypeLevel) ([A] : Γ ⊩¹U A ^ ll) → Set
  Γ ⊩¹U A ≡ B ^ ll / [A] = Γ ⊢ B ⇒* Univ (_⊩¹U_^_.r [A]) (_⊩¹U_^_.l′ [A]) ^ [ ! , ll ]

  -- Universe term
  record _⊩¹U_∷_^_/_  (Γ : Con Term) (t : Term) (A : Term) (ll : TypeLevel) ([A] : Γ ⊩¹U A ^ ll) : Set where
    constructor Uₜ
    open _⊩¹U_^_ [A]
    open LogRelKit (rec l<)
    field
      K    : Term
      d     : Γ ⊢ t :⇒*: K ∷ Univ r l′ ^ next l′
      typeK : Type K
      K≡K   : Γ ⊢ K ≅ K ∷ Univ r l′ ^ [ ! , next l′ ]
      [t]   : ∀ {ρ Δ} → ρ ∷ Δ ⊆ Γ → (⊢Δ : ⊢ Δ) → Δ ⊩ U.wk ρ t ^ [ r , ι l′ ]

  -- Universe term equality
  record _⊩¹U_≡_∷_^_/_ (Γ : Con Term) (t u : Term) (X : Term) (ll : TypeLevel) ([X] : Γ ⊩¹U X ^ ll) : Set where
    constructor Uₜ₌
    open _⊩¹U_^_ [X]
    open LogRelKit (rec l<)
    field
      [t]   : Γ ⊩¹U t ∷ X ^ ll / [X]
      [u]   : Γ ⊩¹U u ∷ X ^ ll / [X]
      A≡B   : Γ ⊢ _⊩¹U_∷_^_/_.K [t] ≅ _⊩¹U_∷_^_/_.K [u] ∷ Univ r l′ ^ [ ! , next l′ ]
      [t≡u] : ∀ {ρ Δ} → ([ρ] : ρ ∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ) → Δ ⊩ U.wk ρ t ≡ U.wk ρ u ^ [ r , ι l′ ] / _⊩¹U_∷_^_/_.[t] [t] [ρ] ⊢Δ

  mutual

    -- Reducibility of Π:

    -- Π-type
    record _⊩¹Π_^[_] (Γ : Con Term) (A : Term) (lΠ : Level)  : Set where
      inductive
      eta-equality
      constructor Πᵣ
      field
        rF : Relevance
        lF : Level
        lG : Level
        l≤F : lF ≤ lΠ 
        l≤G : lG ≤ lΠ
        F : Term
        G : Term
        D : Γ ⊢ A :⇒*: Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ ! ^ [ ! , ι lΠ ]
        nf : Nf (Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ !)
        ⊢F : Γ ⊢ F ^ [ rF , ι lF ]
        ⊢G : Γ ∙ F ^ [ rF , ι lF ] ⊢ G ^ [ ! , ι lG ]
        A≡A : Γ ⊢ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ ! ≅ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ ! ^ [ ! , ι lΠ ]
        [F] : ∀ {ρ Δ} → ρ ∷ Δ ⊆ Γ → (⊢Δ : ⊢ Δ) → Δ ⊩¹ U.wk ρ F ^ [ rF , ι lF ]
        [G] : ∀ {ρ Δ a}
            → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
            → Δ ⊩¹ a ∷ U.wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ
            → Δ ⊩¹ U.wk (lift ρ) G [ a ] ^ [ ! , ι lG ]
        G-ext : ∀ {ρ Δ a b}
              → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
              → ([a] : Δ ⊩¹ a ∷ U.wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ)
              → ([b] : Δ ⊩¹ b ∷ U.wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ)
              → Δ ⊩¹ a ≡ b ∷ U.wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ
              → Δ ⊩¹ U.wk (lift ρ) G [ a ] ≡ U.wk (lift ρ) G [ b ] ^ [ ! , ι lG ] / [G] [ρ] ⊢Δ [a]
    
    -- Π-type equality
    record _⊩¹Π_≡_^[_]/_ (Γ : Con Term) (A B : Term) (lΠ : Level) ([A] : Γ ⊩¹Π A ^[ lΠ ]) : Set where
      inductive
      eta-equality
      constructor Π₌
      open _⊩¹Π_^[_] [A]
      field
        F′     : Term
        G′     : Term
        D′     : Γ ⊢ B ⇒* Π F′ ^ rF ° lF ▹ G′ ° lG ° lΠ ^ ! ^ [ ! , ι lΠ ]
        nf′    : Nf (Π F′ ^ rF ° lF ▹ G′ ° lG ° lΠ ^ !)
        A≡B    : Γ ⊢ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ ! ≅ Π F′ ^ rF ° lF ▹ G′ ° lG ° lΠ ^ ! ^ [ ! , ι lΠ ]
        [F≡F′] : ∀ {ρ Δ}
               → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
               → Δ ⊩¹ U.wk ρ F ≡ U.wk ρ F′ ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ
        [G≡G′] : ∀ {ρ Δ a}
               → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
               → ([a] : Δ ⊩¹ a ∷ U.wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ)
               → Δ ⊩¹ U.wk (lift ρ) G [ a ] ≡ U.wk (lift ρ) G′ [ a ] ^ [ ! , ι lG ] / [G] [ρ] ⊢Δ [a]

    -- relevant Term of Π-type
    _⊩¹Π_∷_^_/_ : (Γ : Con Term) (t A : Term) (lΠ : Level) ([A] : Γ ⊩¹Π A ^[ lΠ ]) → Set
    Γ ⊩¹Π t ∷ A ^ lΠ / Πᵣ rF lF lG lF≤ lG≤ F G D nf ⊢F ⊢G A≡A [F] [G] G-ext =
      ∃ λ f → Γ ⊢ t :⇒*: f ∷ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ ! ^ ι lΠ
            × Function f
            × Γ ⊢ f ≅ f ∷ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ ! ^ [ ! , ι lΠ ]
            × (∀ {ρ Δ a b}
              → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
                ([a] : Δ ⊩¹ a ∷ U.wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ)
                ([b] : Δ ⊩¹ b ∷ U.wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ)
                ([a≡b] : Δ ⊩¹ a ≡ b ∷ U.wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ)
              → Δ ⊩¹ U.wk ρ f ∘ a ^ lΠ ≡ U.wk ρ f ∘ b ^ lΠ ∷ U.wk (lift ρ) G [ a ] ^ [ ! , ι lG ] / [G] [ρ] ⊢Δ [a])
            × (∀ {ρ Δ a} → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
              → ([a] : Δ ⊩¹ a ∷ U.wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ)
              → Δ ⊩¹ U.wk ρ f ∘ a ^ lΠ ∷ U.wk (lift ρ) G [ a ] ^ [ ! , ι lG ] / [G] [ρ] ⊢Δ [a])
    -- Issue: Agda complains about record use not being strictly positive.
    --        Therefore we have to use ×

    -- Term equality of Π-type
    _⊩¹Π_≡_∷_^_/_ : (Γ : Con Term) (t u A : Term) (l′ : Level) ([A] : Γ ⊩¹Π A ^[ l′ ]) → Set
    Γ ⊩¹Π t ≡ u ∷ A ^ l′ / Πᵣ rF lF lG lF≤ lG≤ F G D nf ⊢F ⊢G A≡A [F] [G] G-ext =
      let [A] = Πᵣ rF lF lG lF≤ lG≤ F G D nf ⊢F ⊢G A≡A [F] [G] G-ext
      in  ∃₂ λ f g →
          ( Γ ⊢ t :⇒*: f ∷ Π F ^ rF ° lF ▹ G ° lG ° l′ ^ ! ^ ι l′ )
      ×   ( Γ ⊢ u :⇒*: g ∷ Π F ^ rF ° lF ▹ G ° lG ° l′ ^ ! ^ ι l′ )
      ×   Function f
      ×   Function g
      ×   Γ ⊢ f ≅ g ∷ Π F ^ rF ° lF ▹ G ° lG ° l′ ^ ! ^ [ ! , ι l′ ]
      ×   Γ ⊩¹Π t ∷ A ^ l′ / [A]
      ×   Γ ⊩¹Π u ∷ A ^ l′ / [A]
      ×   (∀ {ρ Δ a} → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          → ([a] : Δ ⊩¹ a ∷ U.wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ)
          → Δ ⊩¹ U.wk ρ f ∘ a ^ l′ ≡ U.wk ρ g ∘ a ^ l′ ∷ U.wk (lift ρ) G [ a ] ^ [ ! , ι lG ] / [G] [ρ] ⊢Δ [a])
    -- Issue: Same as above.

    -- Logical relation definition

    data _⊩¹_^_ (Γ : Con Term) : Term → TypeInfo → Set where
      Uᵣ  : ∀ {A ll} → (UA : Γ ⊩¹U A ^ ll) → Γ ⊩¹ A ^ [ ! , ll ]
      ℕᵣ  : ∀ {A} → Γ ⊩ℕ A → Γ ⊩¹ A ^ [ ! , ι ⁰ ]
      Emptyᵣ : ∀ {A} → Γ ⊩Empty A → Γ ⊩¹ A ^ [ % , ι ⁰ ]
      ne  : ∀ {A r l} → Γ ⊩ne A ^[ r , l ] → Γ ⊩¹ A ^ [ r , ι l ]
      Πᵣ  : ∀ {A l} → Γ ⊩¹Π A ^[ l ] → Γ ⊩¹ A ^ [ ! , ι l ]
      Πirrᵣ  : ∀ {A} → Γ ⊩Πirr A → Γ ⊩¹ A ^ [ % , ι ⁰ ]
      Idᵣ  : ∀ {A} → Γ ⊩Id A → Γ ⊩¹ A ^ [ % , ι ⁰ ]
      emb : ∀ {A r l′} (l< : l′ <∞ l) (let open LogRelKit (rec l<))
            ([A] : Γ ⊩ A ^ r) → Γ ⊩¹ A ^ r

    _⊩¹_≡_^_/_ : (Γ : Con Term) (A B : Term) (r : TypeInfo) → Γ ⊩¹ A ^ r  → Set
    Γ ⊩¹ A ≡ B ^ [ .! , l ] / Uᵣ UA = Γ ⊩¹U A ≡ B ^ l / UA
    Γ ⊩¹ A ≡ B ^ [ .! , .ι ⁰ ] / ℕᵣ D = Γ ⊩ℕ A ≡ B
    Γ ⊩¹ A ≡ B ^ [ .% , .ι ⁰ ] / Emptyᵣ D = Γ ⊩Empty A ≡ B
    Γ ⊩¹ A ≡ B ^ [ r , ι l ] / ne neA = Γ ⊩ne A ≡ B ^[ r , l ]/ neA
    Γ ⊩¹ A ≡ B ^ [ .! , ι l ] / Πᵣ ΠA =  Γ ⊩¹Π A ≡ B ^[ l ]/ ΠA
    Γ ⊩¹ A ≡ B ^ [ .% , .ι ⁰ ] / Πirrᵣ ΠA =  Γ ⊩Πirr A ≡ B / ΠA
    Γ ⊩¹ A ≡ B ^ [ .% , .ι ⁰ ] / Idᵣ IdA = Γ ⊩Id A ≡ B / IdA
    Γ ⊩¹ A ≡ B ^ r / emb l< [A] = Γ ⊩ A ≡ B ^ r / [A]
      where open LogRelKit (rec l<)

    _⊩¹_∷_^_/_ : (Γ : Con Term) (t A : Term) (r : TypeInfo) → Γ ⊩¹ A ^ r  → Set
    Γ ⊩¹ t ∷ A ^ [ .! , ll ] / Uᵣ UA = Γ ⊩¹U t ∷ A ^ ll / UA
    Γ ⊩¹ t ∷ A ^ .([ ! , ι ⁰ ]) / ℕᵣ x = Γ ⊩ℕ t ∷ℕ
    Γ ⊩¹ t ∷ A ^ [ .% , ι ⁰ ] / Emptyᵣ x =  Γ ⊩Empty t ∷Empty
    Γ ⊩¹ t ∷ A ^ .([ ! , ι l ]) / ne {r = !} {l} neA = Γ ⊩ne t ∷ A ^ l / neA
    Γ ⊩¹ t ∷ A ^ .([ % , ι l ]) / ne {r = %} {l} neA = Γ ⊩neIrr t ∷ A ^ l / neA
    Γ ⊩¹ t ∷ A ^ [ .! , ι l ] / Πᵣ ΠA  = Γ ⊩¹Π t ∷ A ^ l / ΠA
    Γ ⊩¹ t ∷ A ^ [ .% , .ι ⁰ ] / Πirrᵣ ΠA  = Γ ⊩Πirr t ∷ A / ΠA
    Γ ⊩¹ t ∷ A ^ .([ % , ι ⁰ ]) / Idᵣ IdA = Γ ⊩Id t ∷ A / IdA
    Γ ⊩¹ t ∷ A ^ r / emb l< [A] =  Γ ⊩ t ∷ A ^ r / [A]
      where open LogRelKit (rec l<)

    _⊩¹_≡_∷_^_/_ : (Γ : Con Term) (t u A : Term) (r : TypeInfo) → Γ ⊩¹ A ^ r → Set
    Γ ⊩¹ t ≡ u ∷ A ^ [ .! , ll ] / Uᵣ UA = Γ ⊩¹U t ≡ u ∷ A ^ ll / UA
    Γ ⊩¹ t ≡ u ∷ A ^ .([ ! , ι ⁰ ]) / ℕᵣ D = Γ ⊩ℕ t ≡ u ∷ℕ
    Γ ⊩¹ t ≡ u ∷ A ^ [ .% , ι ⁰ ] / Emptyᵣ D = Γ ⊩Empty t ≡ u ∷Empty
    Γ ⊩¹ t ≡ u ∷ A ^ .([ ! , ι l ]) / ne {r = !} {l} neA = Γ ⊩ne t ≡ u ∷ A ^  l / neA
    Γ ⊩¹ t ≡ u ∷ A ^ .([ % , ι l ]) / ne {r = %} {l} neA = Γ ⊩neIrr t ≡ u ∷ A ^ l / neA
    Γ ⊩¹ t ≡ u ∷ A ^ [ .! , ι l ] / Πᵣ ΠA = Γ ⊩¹Π t ≡ u ∷ A ^ l / ΠA
    Γ ⊩¹ t ≡ u ∷ A ^ [ .% , .ι ⁰ ] / Πirrᵣ ΠA = Γ ⊩Πirr t ≡ u ∷ A / ΠA
    Γ ⊩¹ t ≡ u ∷ A ^ .([ % , ι ⁰ ]) / Idᵣ IdA = Γ ⊩Id t ≡ u ∷ A / IdA
    Γ ⊩¹ t ≡ u ∷ A ^ r / emb l< [A] = Γ ⊩ t ≡ u ∷ A ^ r / [A]
      where open LogRelKit (rec l<)

    kit : LogRelKit
    kit = Kit _⊩¹U_^_ _⊩¹Π_^[_] _⊩¹_^_ _⊩¹_≡_^_/_ _⊩¹_∷_^_/_ _⊩¹_≡_∷_^_/_

open LogRel public using (Uᵣ; ℕᵣ; Emptyᵣ; ne; Πᵣ ; Πirrᵣ ; Idᵣ ; emb; Uₜ; Uₜ₌; Π₌)

-- Patterns for the non-records of Π
pattern Πₜ a b c d e f = a , b , c , d , e , f
pattern Πₜ₌ a b c d e f g h i j = a , b , c , d , e , f , g , h , i , j

pattern Uᵣ′ A ll r l a e d = Uᵣ {A = A} {ll = ll} (Uᵣ r l a e d)
pattern ne′ b c d e = ne (ne b c d e)
pattern Πᵣ′  a a' a'' lf lg b c d e f g h i j k = Πᵣ (Πᵣ a a' a'' lf lg b c d e f g h i j k)
pattern Πirrᵣ′ a b c d e f g h i = Πirrᵣ (Πirrᵣ a b c d e f g h i)
pattern Idᵣ′ a b c d e f g h i j = Idᵣ (Idᵣ a b c d e f g h i j)


-- we need to split the LogRelKit into the level part and the general part to convince Agda termination checker

logRelRec : ∀ l {l′} → l′ <∞ l → LogRelKit
logRelRec (ι ⁰) = λ ()
logRelRec (ι ¹) X = LogRel.kit (ι ⁰) λ ()
logRelRec ∞ X = LogRel.kit (ι ¹) (λ X → LogRel.kit (ι ⁰) λ ())

kit : ∀ (i : TypeLevel) → LogRelKit
kit l =  LogRel.kit l (logRelRec l)

_⊩′⟨_⟩U_^_ : (Γ : Con Term) (l : TypeLevel) → Term → TypeLevel → Set
Γ ⊩′⟨ l ⟩U A ^ ll = Γ ⊩U A ^ ll where open LogRelKit (kit l)

_⊩′⟨_⟩Π_^[_] : (Γ : Con Term) (l : TypeLevel) → Term → Level → Set
Γ ⊩′⟨ l ⟩Π A ^[ lΠ ] = Γ ⊩Π A ^[ lΠ ]  where open LogRelKit (kit l)

_⊩⟨_⟩_^_ : (Γ : Con Term) (l : TypeLevel) → Term → TypeInfo → Set
Γ ⊩⟨ l ⟩ A ^ r = Γ ⊩ A ^ r where open LogRelKit (kit l)

_⊩⟨_⟩_≡_^_/_ : (Γ : Con Term) (l : TypeLevel) (A B : Term) (r : TypeInfo) → Γ ⊩⟨ l ⟩ A ^ r → Set
Γ ⊩⟨ l ⟩ A ≡ B ^ r / [A] = Γ ⊩ A ≡ B ^ r / [A] where open LogRelKit (kit l)

_⊩⟨_⟩_∷_^_/_ : (Γ : Con Term) (l : TypeLevel) (t A : Term) (r : TypeInfo) → Γ ⊩⟨ l ⟩ A ^ r → Set
Γ ⊩⟨ l ⟩ t ∷ A ^ r / [A] = Γ ⊩ t ∷ A ^ r / [A] where open LogRelKit (kit l)

_⊩⟨_⟩_≡_∷_^_/_ : (Γ : Con Term) (l : TypeLevel) (t u A : Term) (r : TypeInfo) → Γ ⊩⟨ l ⟩ A ^ r → Set
Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ r / [A] = Γ ⊩ t ≡ u ∷ A ^ r / [A] where open LogRelKit (kit l)

-- Well-typed irrelevant terms are always reducible
logRelIrr : ∀ {l t Γ l' A} ([A] : Γ ⊩⟨ l ⟩ A ^ [ % , l' ]) (⊢t : Γ ⊢ t ∷ A ^ [ % , l' ]) → Γ ⊩⟨ l ⟩ t ∷ A ^ [ % , l' ] / [A]
logRelIrr (Emptyᵣ [[ ⊢A , ⊢B , D ]]) ⊢t = Emptyₜ (ne (conv ⊢t (reduction D (id ⊢B) (refl ⊢B))))
logRelIrr (Πirrᵣ′ rF lF F G D _ ⊢F ⊢G A≡A) ⊢t = conv ⊢t
  (reduction (red D) (id (_⊢_:⇒*:_^_.⊢B D))  (refl (_⊢_:⇒*:_^_.⊢B D)))
logRelIrr (ne x) ⊢t = neₜ ⊢t
logRelIrr (Idᵣ′ B t u l D _ ⊢B ⊢t' ⊢u A≡A) ⊢t = conv ⊢t (reduction (red D) (id (_⊢_:⇒*:_^_.⊢B D)) (refl (_⊢_:⇒*:_^_.⊢B D)))
logRelIrr {ι ¹} (emb X [A]) ⊢t = logRelIrr [A] ⊢t
logRelIrr {∞} (emb X [A]) ⊢t = logRelIrr [A] ⊢t


-- Well-typed irrelevant terms are reducibly equal as soon as they have the same type
logRelIrrEq : ∀ {l t u Γ l' A} ([A] : Γ ⊩⟨ l ⟩ A ^ [ % , l' ]) (⊢t : Γ ⊢ t ∷ A ^ [ % , l' ]) (⊢u : Γ ⊢ u ∷ A ^ [ % , l' ]) → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ [ % , l' ] / [A]
logRelIrrEq (Emptyᵣ [[ ⊢A , ⊢B , D ]]) ⊢t ⊢u = Emptyₜ₌ (ne ((conv ⊢t (reduction D (id ⊢B) (refl ⊢B))))
                                                         (conv ⊢u (reduction D (id ⊢B) (refl ⊢B))))
logRelIrrEq (ne x) ⊢t ⊢u = neₜ₌ ⊢t ⊢u
logRelIrrEq (Πirrᵣ′ rF lF F G D _ ⊢F ⊢G A≡A) ⊢t ⊢u = (conv ⊢t (reduction (red D) (id (_⊢_:⇒*:_^_.⊢B D)) (refl (_⊢_:⇒*:_^_.⊢B D))) ) , (conv ⊢u (reduction (red D) (id (_⊢_:⇒*:_^_.⊢B D)) (refl (_⊢_:⇒*:_^_.⊢B D))) )
logRelIrrEq (Idᵣ′ _ _ _ _ D _ _ _ _ A≡A) ⊢t ⊢u = (conv ⊢t (reduction (red D) (id (_⊢_:⇒*:_^_.⊢B D)) (refl (_⊢_:⇒*:_^_.⊢B D))) ) ,
                                            (conv ⊢u (reduction (red D) (id (_⊢_:⇒*:_^_.⊢B D)) (refl (_⊢_:⇒*:_^_.⊢B D))) )
logRelIrrEq {ι ¹} (emb X [A]) ⊢t = logRelIrrEq [A] ⊢t
logRelIrrEq {∞} (emb X [A]) ⊢t = logRelIrrEq [A] ⊢t

