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

-- Neutral term in WHNF
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

-- Neutral term equality in WHNF
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

  -- WHNF property of natural number terms
  data Natural-prop (Γ : Con Term) : (n : Term) → Set where
    sucᵣ  : ∀ {n} → Γ ⊩ℕ n ∷ℕ → Natural-prop Γ (suc n)
    zeroᵣ : Natural-prop Γ zero
    ne    : ∀ {n} → Γ ⊩neNf n ∷ ℕ ^ [ ! , ι ⁰ ] → Natural-prop Γ n

mutual
  -- Natural number term equality
  data _⊩ℕ_≡_∷ℕ (Γ : Con Term) (t u : Term) : Set where
    ℕₜ₌ : (k k′ : Term) (d : Γ ⊢ t :⇒*: k  ∷ ℕ ^ ι ⁰) (d′ : Γ ⊢ u :⇒*: k′ ∷ ℕ ^ ι ⁰)
          (k≡k′ : Γ ⊢ k ≅ k′ ∷ ℕ ^ [ ! , ι ⁰ ])
          (prop : [Natural]-prop Γ k k′) → Γ ⊩ℕ t ≡ u ∷ℕ

  -- WHNF property of Natural number term equality
  data [Natural]-prop (Γ : Con Term) : (n n′ : Term) → Set where
    sucᵣ  : ∀ {n n′} → Γ ⊩ℕ n ≡ n′ ∷ℕ → [Natural]-prop Γ (suc n) (suc n′)
    zeroᵣ : [Natural]-prop Γ zero zero
    ne    : ∀ {n n′} → Γ ⊩neNf n ≡ n′ ∷ ℕ ^ [ ! , ι ⁰ ] → [Natural]-prop Γ n n′

-- Natural extraction from term WHNF property
natural : ∀ {Γ n} → Natural-prop Γ n → Natural n
natural (sucᵣ x) = sucₙ
natural zeroᵣ = zeroₙ
natural (ne (neNfₜ neK ⊢k k≡k)) = ne neK

-- Natural extraction from term equality WHNF property
split : ∀ {Γ a b} → [Natural]-prop Γ a b → Natural a × Natural b
split (sucᵣ x) = sucₙ , sucₙ
split zeroᵣ = zeroₙ , zeroₙ
split (ne (neNfₜ₌ neK neM k≡m)) = ne neK , ne neM

-- Reducibility of Empty

-- Empty type
_⊩Empty_^_ : (Γ : Con Term) (A : Term) (l : Level) → Set
Γ ⊩Empty A ^ l = Γ ⊢ A :⇒*: Empty ^ [ % , ι l ]

-- Empty type equality
_⊩Empty_≡_^_ : (Γ : Con Term) (A B : Term) (l : Level) → Set
Γ ⊩Empty A ≡ B ^ l = Γ ⊢ B ⇒* Empty ^ [ % , ι l ]

data Empty-prop (Γ : Con Term) (n : Term) (l : Level) : Set where
  ne    : Γ ⊢ n ∷ Empty ^ [ % , ι l ] → Empty-prop Γ n l

-- -- Empty term

data _⊩Empty_∷Empty^_ (Γ : Con Term) (t : Term) (l : Level) : Set where
  Emptyₜ :  -- (n : Term) (d : Γ ⊢ t :⇒*: n ∷ Empty ^ %) (n≡n : Γ ⊢ n ≅ n ∷ Empty ^ %)
         (prop : Empty-prop Γ t l)
         → Γ ⊩Empty t ∷Empty^ l

data [Empty]-prop (Γ : Con Term) : (n n′ : Term)  (l : Level) → Set where
  ne    : ∀ {n n′ l} → Γ ⊢ n ∷ Empty ^ [ % , ι l ] → Γ ⊢ n′ ∷ Empty ^ [ % , ι l ]  → [Empty]-prop Γ n n′ l

-- Empty term equality
data _⊩Empty_≡_∷Empty^_ (Γ : Con Term) (t u : Term) (l : Level) : Set where
  Emptyₜ₌ : -- (k k′ : Term) (d : Γ ⊢ t :⇒*: k ∷ Empty ^ %) (d′ : Γ ⊢ u :⇒*: k′ ∷ Empty ^ %)
    -- (k≡k′ : Γ ⊢ k ≅ k′ ∷ Empty ^ %)
      (prop : [Empty]-prop Γ t u l) → Γ ⊩Empty t ≡ u ∷Empty^ l

-- empty : ∀ {Γ n} → Empty-prop Γ n → Neutral n
-- empty (ne (neNfₜ neK _ _)) = neK

-- esplit : ∀ {Γ a b} → [Empty]-prop Γ a b → Neutral a × Neutral b
-- esplit (ne (neNfₜ₌ neK neM k≡m)) = neK , neM

-- Logical relation

record LogRelKit : Set₁ where
  constructor Kit
  field
    _⊩U_^_ : (Γ : Con Term) → Term → TypeLevel → Set
    _⊩Π_^_ : (Γ : Con Term) → Term → TypeInfo → Set
    _⊩∃_^_ : (Γ : Con Term) → Term → TypeLevel → Set

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
      [IdK] : ∀ {ρ Δ a b} → r PE.≡ !
            → ([ρ] : ρ ∷ Δ ⊆ Γ)
            → (⊢Δ : ⊢ Δ)
            → Δ ⊩ a ∷ U.wk ρ t ^ [ r , ι l′ ] / [t] [ρ] ⊢Δ
            → Δ ⊩ b ∷ U.wk ρ t ^ [ r , ι l′ ] / [t] [ρ] ⊢Δ
            → Δ ⊩ Id (U.wk ρ t) a b ^ [ % , ι l′ ]
      IdKExt : ∀ {ρ Δ a a′ b b′} → (r≡! : r PE.≡ !)
            → ([ρ] : ρ ∷ Δ ⊆ Γ)
            → (⊢Δ : ⊢ Δ)
            → ([a] : Δ ⊩ a ∷ U.wk ρ t ^ [ r , ι l′ ] / [t] [ρ] ⊢Δ)
            → ([a′] : Δ ⊩ a′ ∷ U.wk ρ t ^ [ r , ι l′ ] / [t] [ρ] ⊢Δ)
            → Δ ⊩ a ≡ a′ ∷ U.wk ρ t ^ [ r , ι l′ ] / [t] [ρ] ⊢Δ
            → ([b] : Δ ⊩ b ∷ U.wk ρ t ^ [ r , ι l′ ] / [t] [ρ] ⊢Δ)
            → ([b′] : Δ ⊩ b′ ∷ U.wk ρ t ^ [ r , ι l′ ] / [t] [ρ] ⊢Δ)
            → Δ ⊩ b ≡ b′ ∷ U.wk ρ t ^ [ r , ι l′ ] / [t] [ρ] ⊢Δ
            → Δ ⊩ Id (U.wk ρ t) a b ≡ Id (U.wk ρ t) a′ b′ ^ [ % , ι l′ ] / [IdK] r≡! [ρ] ⊢Δ [a] [b]
      [castK] : ∀ {ρ Δ B a e} → l′ PE.≡ ⁰ → r PE.≡ !
            → ([ρ] : ρ ∷ Δ ⊆ Γ)
            → (⊢Δ : ⊢ Δ)
            → ([B] : Δ ⊩ B ^ [ ! , ι l′ ])
            → Δ ⊢ e ∷ Id (U ⁰) (U.wk ρ t) B ^ [ % , next ⁰ ]
            → Δ ⊩ a ∷ U.wk ρ t ^ [ r , ι l′ ] / [t] [ρ] ⊢Δ
            → Δ ⊩ cast l′ (U.wk ρ t) B e a ∷ B ^ [ ! , ι l′ ] / [B]
      castKext : ∀ {ρ Δ B B′ a a′ e e′} → l′ PE.≡ ⁰ → r PE.≡ !
            → ([ρ] : ρ ∷ Δ ⊆ Γ)
            → (⊢Δ : ⊢ Δ)
            → ([B] : Δ ⊩ B ^ [ ! , ι l′ ])
            → ([B′] : Δ ⊩ B′ ^ [ ! , ι l′ ])
            → Δ ⊩ B ≡ B′ ^ [ ! , ι l′ ] / [B]
            → ([e] : Δ ⊢ e ∷ Id (U ⁰) (U.wk ρ t) B ^ [ % , next ⁰ ])
            → ([e′] : Δ ⊢ e′ ∷ Id (U ⁰) (U.wk ρ t) B′ ^ [ % , next ⁰ ])
            → ([a] : Δ ⊩ a ∷ U.wk ρ t ^ [ r , ι l′ ] / [t] [ρ] ⊢Δ)
            → ([a′] : Δ ⊩ a′ ∷ U.wk ρ t ^ [ r , ι l′ ] / [t] [ρ] ⊢Δ)
            → Δ ⊩ a ≡ a′ ∷ U.wk ρ t ^ [ r , ι l′ ] / [t] [ρ] ⊢Δ
            → Δ ⊩ cast l′ (U.wk ρ t) B e a ≡ cast l′ (U.wk ρ t) B′ e′ a′ ∷ B ^ [ ! , ι l′ ] / [B]

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
      IdHo : ∀ {ρ Δ a b} → (r≡! : r PE.≡ !)
           → ([ρ] : ρ ∷ Δ ⊆ Γ)
           → (⊢Δ : ⊢ Δ)
           → ([a] : Δ ⊩ a ∷ U.wk ρ t ^ [ r , ι l′ ]
                      / _⊩¹U_∷_^_/_.[t] [t] [ρ] ⊢Δ)
           → ([b] : Δ ⊩ b ∷ U.wk ρ t ^ [ r , ι l′ ]
                      / _⊩¹U_∷_^_/_.[t] [t] [ρ] ⊢Δ)
           → Δ ⊩ Id (U.wk ρ t) a b ≡ Id (U.wk ρ u) a b ^ [ % , ι l′ ]
                      / _⊩¹U_∷_^_/_.[IdK] [t] r≡! [ρ] ⊢Δ [a] [b]
      castHo : ∀ {ρ Δ B a e} → l′ PE.≡ ⁰ → r PE.≡ !
           → ([ρ] : ρ ∷ Δ ⊆ Γ)
           → (⊢Δ : ⊢ Δ)
           → ([B] : Δ ⊩ B ^ [ ! , ι l′ ])
           → ([e] : Δ ⊢ e ∷ Id (U ⁰) (U.wk ρ t) B ^ [ % , next ⁰ ])
           → ([a] : Δ ⊩ a ∷ U.wk ρ t ^ [ r , ι l′ ]
                      / _⊩¹U_∷_^_/_.[t] [t] [ρ] ⊢Δ)
           → Δ ⊩ cast l′ (U.wk ρ t) B e a ≡ cast l′ (U.wk ρ u) B e a ∷ B ^ [ ! , ι l′ ] / [B]

  mutual

    -- Reducibility of Π:

    -- Π-type
    record _⊩¹Π_^_ (Γ : Con Term) (A : Term) (r : TypeInfo)  : Set where
      inductive
      eta-equality
      constructor Πᵣ
      field
        rF : Relevance
        lF : Level
        lG : Level
        F : Term
        G : Term
        D : Γ ⊢ A :⇒*: Π F ^ rF ° lF ▹ G ° lG ^ r
        ⊢F : Γ ⊢ F ^ [ rF , ι lF ]
        ⊢G : Γ ∙ F ^ [ rF , ι lF ] ⊢ G ^ [ TypeInfo.r r , ι lG ]
        A≡A : Γ ⊢ Π F ^ rF ° lF ▹ G ° lG  ≅ Π F ^ rF ° lF ▹ G ° lG ^ r
        [F] : ∀ {ρ Δ} → ρ ∷ Δ ⊆ Γ → (⊢Δ : ⊢ Δ) → Δ ⊩¹ U.wk ρ F ^ [ rF , ι lF ]
        [G] : ∀ {ρ Δ a}
            → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
            → Δ ⊩¹ a ∷ U.wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ
            → Δ ⊩¹ U.wk (lift ρ) G [ a ] ^ [ TypeInfo.r r , ι lG ]
        G-ext : ∀ {ρ Δ a b}
              → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
              → ([a] : Δ ⊩¹ a ∷ U.wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ)
              → ([b] : Δ ⊩¹ b ∷ U.wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ)
              → Δ ⊩¹ a ≡ b ∷ U.wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ
              → Δ ⊩¹ U.wk (lift ρ) G [ a ] ≡ U.wk (lift ρ) G [ b ] ^ [ TypeInfo.r r , ι lG ] / [G] [ρ] ⊢Δ [a]

    -- Π-type equality
    record _⊩¹Π_≡_^_/_ (Γ : Con Term) (A B : Term) (r : TypeInfo) ([A] : Γ ⊩¹Π A ^ r) : Set where
      inductive
      eta-equality
      constructor Π₌
      open _⊩¹Π_^_ [A]
      field
        F′     : Term
        G′     : Term
        D′     : Γ ⊢ B ⇒* Π F′ ^ rF ° lF ▹ G′ ° lG ^ r
        A≡B    : Γ ⊢ Π F ^ rF ° lF ▹ G ° lG ≅ Π F′ ^ rF ° lF ▹ G′ ° lG ^ r
        [F≡F′] : ∀ {ρ Δ}
               → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
               → Δ ⊩¹ U.wk ρ F ≡ U.wk ρ F′ ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ
        [G≡G′] : ∀ {ρ Δ a}
               → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
               → ([a] : Δ ⊩¹ a ∷ U.wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ)
               → Δ ⊩¹ U.wk (lift ρ) G [ a ] ≡ U.wk (lift ρ) G′ [ a ] ^ [ TypeInfo.r r , ι lG ] / [G] [ρ] ⊢Δ [a]

    -- relevant Term of Π-type
    _⊩¹Π_∷_^_/_ : (Γ : Con Term) (t A : Term) (l : TypeLevel) ([A] : Γ ⊩¹Π A ^ [ ! , l ]) → Set
    Γ ⊩¹Π t ∷ A ^ l / Πᵣ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext =
      ∃ λ f → Γ ⊢ t :⇒*: f ∷ Π F ^ rF ° lF ▹ G ° lG ^ l
            × Function f
            × Γ ⊢ f ≅ f ∷ Π F ^ rF ° lF ▹ G ° lG ^ [ ! , l ]
            × (∀ {ρ Δ a b}
              → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
                ([a] : Δ ⊩¹ a ∷ U.wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ)
                ([b] : Δ ⊩¹ b ∷ U.wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ)
                ([a≡b] : Δ ⊩¹ a ≡ b ∷ U.wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ)
              → Δ ⊩¹ U.wk ρ f ∘ a ≡ U.wk ρ f ∘ b ∷ U.wk (lift ρ) G [ a ] ^ [ ! , ι lG ] / [G] [ρ] ⊢Δ [a])
            × (∀ {ρ Δ a} → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
              → ([a] : Δ ⊩¹ a ∷ U.wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ)
              → Δ ⊩¹ U.wk ρ f ∘ a ∷ U.wk (lift ρ) G [ a ] ^ [ ! , ι lG ] / [G] [ρ] ⊢Δ [a])
    -- Issue: Agda complains about record use not being strictly positive.
    --        Therefore we have to use ×

    -- relevant Term of Π-type
    _⊩¹Πirr_∷_^_/_ : (Γ : Con Term) (t A : Term) (l′ : TypeLevel) ([A] : Γ ⊩¹Π A ^ [ % , l′ ]) → Set
    Γ ⊩¹Πirr t ∷ A ^ l′ / Πᵣ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext =
      Γ ⊢ t ∷ Π F ^ rF ° lF ▹ G ° lG  ^ [ % , l′ ]

    -- Term equality of Π-type
    _⊩¹Π_≡_∷_^_/_ : (Γ : Con Term) (t u A : Term) (l′ : TypeLevel) ([A] : Γ ⊩¹Π A ^ [ ! , l′ ]) → Set
    Γ ⊩¹Π t ≡ u ∷ A ^ l′ / Πᵣ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext =
      let [A] = Πᵣ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext
      in  ∃₂ λ f g →
          ( Γ ⊢ t :⇒*: f ∷ Π F ^ rF ° lF ▹ G ° lG ^ l′ )
      ×   ( Γ ⊢ u :⇒*: g ∷ Π F ^ rF ° lF ▹ G ° lG ^ l′ )
      ×   Function f
      ×   Function g
      ×   Γ ⊢ f ≅ g ∷ Π F ^ rF ° lF ▹ G ° lG ^ [ ! , l′ ]
      ×   Γ ⊩¹Π t ∷ A ^ l′ / [A]
      ×   Γ ⊩¹Π u ∷ A ^ l′ / [A]
      ×   (∀ {ρ Δ a} → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          → ([a] : Δ ⊩¹ a ∷ U.wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ)
          → Δ ⊩¹ U.wk ρ f ∘ a ≡ U.wk ρ g ∘ a ∷ U.wk (lift ρ) G [ a ] ^ [ ! , ι lG ] / [G] [ρ] ⊢Δ [a])
    -- Issue: Same as above.

    -- Term equality of Π-type
    _⊩¹Πirr_≡_∷_^_/_ : (Γ : Con Term) (t u A : Term) (l′ : TypeLevel) ([A] : Γ ⊩¹Π A ^ [ % , l′ ] ) → Set
    Γ ⊩¹Πirr t ≡ u ∷ A ^ l′ / Πᵣ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext =
          (Γ ⊢ t ∷ Π F ^ rF ° lF ▹ G ° lG ^ [ % , l′ ])
          ×
          (Γ ⊢ u ∷ Π F ^ rF ° lF ▹ G ° lG ^ [ % , l′ ])

    record _⊩¹∃_^_ (Γ : Con Term) (A : Term) (l′ : TypeLevel) : Set where
      inductive
      eta-equality
      constructor ∃ᵣ
      field
        F : Term
        G : Term
        D : Γ ⊢ A :⇒*: ∃ F ▹ G ^ [ % , l′ ]
        ⊢F : Γ ⊢ F ^ [ % , l′ ]
        ⊢G : Γ ∙ F ^ [ % , l′ ] ⊢ G ^ [ % , l′ ]
        A≡A : Γ ⊢ (∃ F ▹ G) ≅ (∃ F ▹ G) ^ [ % , l′ ]
        [F] : ∀ {ρ Δ} → ρ ∷ Δ ⊆ Γ → (⊢Δ : ⊢ Δ) → Δ ⊩¹ U.wk ρ F ^ [ % , l′ ]
        [G] : ∀ {ρ Δ a}
            → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
            → Δ ⊩¹ a ∷ U.wk ρ F ^ [ % , l′ ] / [F] [ρ] ⊢Δ
            → Δ ⊩¹ U.wk (lift ρ) G [ a ] ^ [ % , l′ ]
        G-ext : ∀ {ρ Δ a b}
              → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
              → ([a] : Δ ⊩¹ a ∷ U.wk ρ F ^ [ % , l′ ] / [F] [ρ] ⊢Δ)
              → ([b] : Δ ⊩¹ b ∷ U.wk ρ F ^ [ % , l′ ] / [F] [ρ] ⊢Δ)
              → Δ ⊩¹ a ≡ b ∷ U.wk ρ F ^ [ % , l′ ] / [F] [ρ] ⊢Δ
              → Δ ⊩¹ U.wk (lift ρ) G [ a ] ≡ U.wk (lift ρ) G [ b ] ^ [ % , l′ ] / [G] [ρ] ⊢Δ [a]

    -- Π-type equality
    record _⊩¹∃_≡_^_/_ (Γ : Con Term) (A B : Term) (l′ : TypeLevel) ([A] : Γ ⊩¹∃ A ^ l′) : Set where
      inductive
      eta-equality
      constructor ∃₌
      open _⊩¹∃_^_ [A]
      field
        F′     : Term
        G′     : Term
        D′     : Γ ⊢ B ⇒* ∃ F′ ▹ G′ ^ [ % , l′ ]
        A≡B    : Γ ⊢ ∃ F ▹ G ≅ ∃ F′ ▹ G′ ^ [ % , l′ ]
        [F≡F′] : ∀ {ρ Δ}
               → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
               → Δ ⊩¹ U.wk ρ F ≡ U.wk ρ F′ ^ [ % , l′ ] / [F] [ρ] ⊢Δ
        [G≡G′] : ∀ {ρ Δ a}
               → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
               → ([a] : Δ ⊩¹ a ∷ U.wk ρ F ^ [ % , l′ ] / [F] [ρ] ⊢Δ)
               → Δ ⊩¹ U.wk (lift ρ) G [ a ] ≡ U.wk (lift ρ) G′ [ a ] ^ [ % , l′ ] / [G] [ρ] ⊢Δ [a]

    _⊩¹∃_∷_^_/_ : (Γ : Con Term) (t A : Term) (l′ : TypeLevel) ([A] : Γ ⊩¹∃ A ^ l′) → Set
    Γ ⊩¹∃ t ∷ A ^ l′ / ∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext =
      Γ ⊢ t ∷ ∃ F ▹ G ^ [ % , l′ ]

    _⊩¹∃_≡_∷_^_/_ : (Γ : Con Term) (t u A : Term) (l′ : TypeLevel) ([A] : Γ ⊩¹∃ A ^ l′) → Set
    Γ ⊩¹∃ t ≡ u ∷ A ^ l′ / ∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext =
          (Γ ⊢ t ∷ ∃ F ▹ G ^ [ % , l′ ])
          ×
          (Γ ⊢ u ∷ ∃ F ▹ G ^ [ % , l′ ])

    -- Logical relation definition

    data _⊩¹_^_ (Γ : Con Term) : Term → TypeInfo → Set where
      Uᵣ  : ∀ {A ll} → (UA : Γ ⊩¹U A ^ ll) → Γ ⊩¹ A ^ [ ! , ll ]
      ℕᵣ  : ∀ {A} → Γ ⊩ℕ A → Γ ⊩¹ A ^ [ ! , ι ⁰ ]
      Emptyᵣ : ∀ {A l} → Γ ⊩Empty A ^ l → Γ ⊩¹ A ^ [ % , ι l ]
      ne  : ∀ {A r l} → Γ ⊩ne A ^[ r , l ] → Γ ⊩¹ A ^ [ r , ι l ]
      Πᵣ  : ∀ {A r} → Γ ⊩¹Π A ^ r → Γ ⊩¹ A ^ r
      ∃ᵣ  : ∀ {A l} → Γ ⊩¹∃ A ^ l → Γ ⊩¹ A ^ [ % , l ]
      emb : ∀ {A r l′} (l< : l′ <∞ l) (let open LogRelKit (rec l<))
            ([A] : Γ ⊩ A ^ r) → Γ ⊩¹ A ^ r

    _⊩¹_≡_^_/_ : (Γ : Con Term) (A B : Term) (r : TypeInfo) → Γ ⊩¹ A ^ r  → Set
    Γ ⊩¹ A ≡ B ^ [ .! , l ] / Uᵣ UA = Γ ⊩¹U A ≡ B ^ l / UA
    Γ ⊩¹ A ≡ B ^ [ .! , .ι ⁰ ] / ℕᵣ D = Γ ⊩ℕ A ≡ B
    Γ ⊩¹ A ≡ B ^ [ .% , .ι l ] / Emptyᵣ D = Γ ⊩Empty A ≡ B ^ l
    Γ ⊩¹ A ≡ B ^ [ r , ι l ] / ne neA = Γ ⊩ne A ≡ B ^[ r , l ]/ neA
    Γ ⊩¹ A ≡ B ^ r / Πᵣ ΠA = Γ ⊩¹Π A ≡ B ^ r / ΠA
    Γ ⊩¹ A ≡ B ^ [ .% , l ] / ∃ᵣ ∃A = Γ ⊩¹∃ A ≡ B ^ l / ∃A
    Γ ⊩¹ A ≡ B ^ r / emb l< [A] = Γ ⊩ A ≡ B ^ r / [A]
      where open LogRelKit (rec l<)

    _⊩¹_∷_^_/_ : (Γ : Con Term) (t A : Term) (r : TypeInfo) → Γ ⊩¹ A ^ r  → Set
    Γ ⊩¹ t ∷ A ^ [ .! , ll ] / Uᵣ UA = Γ ⊩¹U t ∷ A ^ ll / UA
    Γ ⊩¹ t ∷ A ^ .([ ! , ι ⁰ ]) / ℕᵣ x = Γ ⊩ℕ t ∷ℕ
    Γ ⊩¹ t ∷ A ^ [ .% , ι ll ] / Emptyᵣ x =  Γ ⊩Empty t ∷Empty^ ll
    Γ ⊩¹ t ∷ A ^ .([ ! , ι l ]) / ne {r = !} {l} neA = Γ ⊩ne t ∷ A ^ l / neA
    Γ ⊩¹ t ∷ A ^ .([ % , ι l ]) / ne {r = %} {l} neA = Γ ⊩neIrr t ∷ A ^ l / neA
    Γ ⊩¹ t ∷ A ^ [ ! , l ] / Πᵣ ΠA  = Γ ⊩¹Π t ∷ A ^ l / ΠA
    Γ ⊩¹ t ∷ A ^ [ % , l ] / Πᵣ ΠA  = Γ ⊩¹Πirr t ∷ A ^ l / ΠA
    Γ ⊩¹ t ∷ A ^ .([ % , l ]) / ∃ᵣ {l = l} ∃A = Γ ⊩¹∃ t ∷ A ^ l / ∃A
    Γ ⊩¹ t ∷ A ^ r / emb l< [A] =  Γ ⊩ t ∷ A ^ r / [A]
      where open LogRelKit (rec l<)

    _⊩¹_≡_∷_^_/_ : (Γ : Con Term) (t u A : Term) (r : TypeInfo) → Γ ⊩¹ A ^ r → Set
    Γ ⊩¹ t ≡ u ∷ A ^ [ .! , ll ] / Uᵣ UA = Γ ⊩¹U t ≡ u ∷ A ^ ll / UA
    Γ ⊩¹ t ≡ u ∷ A ^ .([ ! , ι ⁰ ]) / ℕᵣ D = Γ ⊩ℕ t ≡ u ∷ℕ
    Γ ⊩¹ t ≡ u ∷ A ^ [ .% , ι ll ] / Emptyᵣ D = Γ ⊩Empty t ≡ u ∷Empty^ ll
    Γ ⊩¹ t ≡ u ∷ A ^ .([ ! , ι l ]) / ne {r = !} {l} neA = Γ ⊩ne t ≡ u ∷ A ^  l / neA
    Γ ⊩¹ t ≡ u ∷ A ^ .([ % , ι l ]) / ne {r = %} {l} neA = Γ ⊩neIrr t ≡ u ∷ A ^ l / neA
    Γ ⊩¹ t ≡ u ∷ A ^ [ ! , l ] / Πᵣ ΠA = Γ ⊩¹Π t ≡ u ∷ A ^ l  / ΠA
    Γ ⊩¹ t ≡ u ∷ A ^ [ % , l ] / Πᵣ ΠA = Γ ⊩¹Πirr t ≡ u ∷ A ^ l / ΠA
    Γ ⊩¹ t ≡ u ∷ A ^ .([ % , l ]) / ∃ᵣ {l = l} ∃A = Γ ⊩¹∃ t ≡ u ∷ A ^ l / ∃A
    Γ ⊩¹ t ≡ u ∷ A ^ r / emb l< [A] = Γ ⊩ t ≡ u ∷ A ^ r / [A]
      where open LogRelKit (rec l<)

    kit : LogRelKit
    kit = Kit _⊩¹U_^_ _⊩¹Π_^_ _⊩¹∃_^_
              _⊩¹_^_ _⊩¹_≡_^_/_ _⊩¹_∷_^_/_ _⊩¹_≡_∷_^_/_

open LogRel public using (Uᵣ; ℕᵣ; Emptyᵣ; ne; Πᵣ ; ∃ᵣ ; emb; Uₜ; Uₜ₌; Π₌; ∃₌)

-- Patterns for the non-records of Π
pattern Πₜ a b c d e f = a , b , c , d , e , f
pattern Πₜ₌ a b c d e f g h i j = a , b , c , d , e , f , g , h , i , j

pattern Uᵣ′ A ll r l a e d = Uᵣ {A = A} {ll = ll} (Uᵣ r l a e d)
pattern ne′ b c d e = ne (ne b c d e)
pattern Πᵣ′  a a' a'' b c d e f g h i j = Πᵣ (Πᵣ a a' a'' b c d e f g h i j)
pattern ∃ᵣ′  a b c d e f g h i = ∃ᵣ (∃ᵣ a b c d e f g h i)


-- we need to split the LogRelKit into the level part and the general part to convince Agda termination checker

logRelRec : ∀ l {l′} → l′ <∞ l → LogRelKit
logRelRec (ι ⁰) = λ ()
logRelRec (ι ¹) X = LogRel.kit (ι ⁰) (λ ())
logRelRec ∞ {ι ⁰} X = LogRel.kit (ι ⁰) (λ ())
logRelRec ∞ {ι ¹} X = LogRel.kit (ι ¹) λ x → LogRel.kit (ι ⁰) (λ ())
logRelRec ∞ {∞} (Nat.s≤s (Nat.s≤s ()))

kit : ∀ (i : TypeLevel) → LogRelKit
kit l =  LogRel.kit l (logRelRec l)

-- a bit of repetition in "kit ¹" definition, would work better with Fin 2 for
-- TypeLevel because you could recurse.

_⊩′⟨_⟩U_^_ : (Γ : Con Term) (l : TypeLevel) → Term → TypeLevel → Set
Γ ⊩′⟨ l ⟩U A ^ ll = Γ ⊩U A ^ ll where open LogRelKit (kit l)

_⊩′⟨_⟩Π_^_ : (Γ : Con Term) (l : TypeLevel) → Term → TypeInfo → Set
Γ ⊩′⟨ l ⟩Π A ^ r = Γ ⊩Π A ^ r where open LogRelKit (kit l)

_⊩′⟨_⟩∃_^_ : (Γ : Con Term) (l : TypeLevel) → Term → TypeLevel → Set
Γ ⊩′⟨ l ⟩∃ A ^ l' = Γ ⊩∃ A ^ l' where open LogRelKit (kit l)

_⊩⟨_⟩_^_ : (Γ : Con Term) (l : TypeLevel) → Term → TypeInfo → Set
Γ ⊩⟨ l ⟩ A ^ r = Γ ⊩ A ^ r where open LogRelKit (kit l)

_⊩⟨_⟩_≡_^_/_ : (Γ : Con Term) (l : TypeLevel) (A B : Term) (r : TypeInfo) → Γ ⊩⟨ l ⟩ A ^ r → Set
Γ ⊩⟨ l ⟩ A ≡ B ^ r / [A] = Γ ⊩ A ≡ B ^ r / [A] where open LogRelKit (kit l)

_⊩⟨_⟩_∷_^_/_ : (Γ : Con Term) (l : TypeLevel) (t A : Term) (r : TypeInfo) → Γ ⊩⟨ l ⟩ A ^ r → Set
Γ ⊩⟨ l ⟩ t ∷ A ^ r / [A] = Γ ⊩ t ∷ A ^ r / [A] where open LogRelKit (kit l)

_⊩⟨_⟩_≡_∷_^_/_ : (Γ : Con Term) (l : TypeLevel) (t u A : Term) (r : TypeInfo) → Γ ⊩⟨ l ⟩ A ^ r → Set
Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ r / [A] = Γ ⊩ t ≡ u ∷ A ^ r / [A] where open LogRelKit (kit l)


logRelIrr : ∀ {l t Γ l' A} ([A] : Γ ⊩⟨ l ⟩ A ^ [ % , l' ]) (⊢t : Γ ⊢ t ∷ A ^ [ % , l' ]) → Γ ⊩⟨ l ⟩ t ∷ A ^ [ % , l' ] / [A]
logRelIrr (Emptyᵣ [[ ⊢A , ⊢B , D ]]) ⊢t = Emptyₜ (ne (conv ⊢t (reduction D (id ⊢B) Emptyₙ Emptyₙ (refl ⊢B))))
logRelIrr (ne x) ⊢t = neₜ ⊢t
logRelIrr (Πᵣ′ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext) ⊢t = conv ⊢t (reduction (red D) (id (_⊢_:⇒*:_^_.⊢B D)) Πₙ Πₙ (refl (_⊢_:⇒*:_^_.⊢B D)))
logRelIrr (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) ⊢t = conv ⊢t (reduction (red D) (id (_⊢_:⇒*:_^_.⊢B D)) ∃ₙ ∃ₙ (refl (_⊢_:⇒*:_^_.⊢B D)))
logRelIrr {ι ¹} (emb {l′ = ι ⁰} (Nat.s≤s X) [A]) ⊢t = logRelIrr [A] ⊢t
logRelIrr {∞} (emb {l′ = ι ⁰} (Nat.s≤s X) [A]) ⊢t = logRelIrr [A] ⊢t
logRelIrr {∞} (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) [A]) ⊢t = logRelIrr [A] ⊢t
logRelIrr {∞} (emb {l′ = ∞} (Nat.s≤s (Nat.s≤s ())) [A]) ⊢t


logRelIrrEq : ∀ {l t u Γ l' A} ([A] : Γ ⊩⟨ l ⟩ A ^ [ % , l' ]) (⊢t : Γ ⊢ t ∷ A ^ [ % , l' ]) (⊢u : Γ ⊢ u ∷ A ^ [ % , l' ]) → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ [ % , l' ] / [A]
logRelIrrEq (Emptyᵣ [[ ⊢A , ⊢B , D ]]) ⊢t ⊢u = Emptyₜ₌ (ne ((conv ⊢t (reduction D (id ⊢B) Emptyₙ Emptyₙ (refl ⊢B))))
                                                         (conv ⊢u (reduction D (id ⊢B) Emptyₙ Emptyₙ (refl ⊢B))))
logRelIrrEq (ne x) ⊢t ⊢u = neₜ₌ ⊢t ⊢u
logRelIrrEq (Πᵣ′ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext) ⊢t ⊢u = (conv ⊢t (reduction (red D) (id (_⊢_:⇒*:_^_.⊢B D)) Πₙ Πₙ (refl (_⊢_:⇒*:_^_.⊢B D))) ) , (conv ⊢u (reduction (red D) (id (_⊢_:⇒*:_^_.⊢B D)) Πₙ Πₙ (refl (_⊢_:⇒*:_^_.⊢B D))) )
logRelIrrEq (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) ⊢t ⊢u = (conv ⊢t (reduction (red D) (id (_⊢_:⇒*:_^_.⊢B D)) ∃ₙ ∃ₙ (refl (_⊢_:⇒*:_^_.⊢B D))) ) , (conv ⊢u (reduction (red D) (id (_⊢_:⇒*:_^_.⊢B D)) ∃ₙ ∃ₙ (refl (_⊢_:⇒*:_^_.⊢B D))) )
logRelIrrEq {ι ¹} (emb {l′ = ι ⁰} (Nat.s≤s X) [A]) ⊢t = logRelIrrEq [A] ⊢t
logRelIrrEq {∞} (emb {l′ = ι ⁰} (Nat.s≤s X) [A]) ⊢t = logRelIrrEq [A] ⊢t
logRelIrrEq {∞} (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) [A]) ⊢t = logRelIrrEq [A] ⊢t
logRelIrrEq {∞} (emb {l′ = ∞} (Nat.s≤s (Nat.s≤s ())) [A]) ⊢t
