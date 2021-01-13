{-# OPTIONS --without-K --safe  #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Reduction

open import Tools.Product
import Tools.PropositionalEquality as PE


-- The different cases of the logical relation are spread out through out
-- this file. This is due to them having different dependencies.

-- We will refer to expressions that satisfies the logical relation as reducible.

-- Reducibility of Neutrals:

-- Neutral type
record _⊩ne_^_ (Γ : Con Term) (A : Term) (r : Relevance) : Set where
  constructor ne
  field
    K   : Term
    D   : Γ ⊢ A :⇒*: K ^ r
    neK : Neutral K
    K≡K : Γ ⊢ K ~ K ∷ (Univ r) ^ !

-- Neutral type equality
record _⊩ne_≡_^_/_ (Γ : Con Term) (A B : Term) (r : Relevance) ([A] : Γ ⊩ne A ^ r) : Set where
  constructor ne₌
  open _⊩ne_^_ [A]
  field
    M   : Term
    D′  : Γ ⊢ B :⇒*: M ^ r
    neM : Neutral M
    K≡M : Γ ⊢ K ~ M ∷ (Univ r) ^ !

-- Neutral term in WHNF
record _⊩neNf_∷_^_ (Γ : Con Term) (k A : Term) (r : Relevance) : Set where
  inductive
  constructor neNfₜ
  field
    neK  : Neutral k
    ⊢k   : Γ ⊢ k ∷ A ^ r
    k≡k  : Γ ⊢ k ~ k ∷ A ^ r

-- Neutral relevant term
record _⊩ne_∷_/_ (Γ : Con Term) (t A : Term) ([A] : Γ ⊩ne A ^ !) : Set where
  inductive
  constructor neₜ
  open _⊩ne_^_ [A]
  field
    k   : Term
    d   : Γ ⊢ t :⇒*: k ∷ K 
    nf  : Γ ⊩neNf k ∷ K ^ !

-- Neutral irrelevant term
record _⊩neIrr_∷_/_ (Γ : Con Term) (t A : Term) ([A] : Γ ⊩ne A ^ %) : Set where
  inductive
  constructor neₜ
  open _⊩ne_^_ [A]
  field
    d : Γ ⊢ t ∷ A ^ %

-- Neutral term equality in WHNF
record _⊩neNf_≡_∷_^_ (Γ : Con Term) (k m A : Term) (r : Relevance) : Set where
  inductive
  constructor neNfₜ₌
  field
    neK  : Neutral k
    neM  : Neutral m
    k≡m  : Γ ⊢ k ~ m ∷ A ^ r

-- Neutral relevant term equality
record _⊩ne_≡_∷_/_ (Γ : Con Term) (t u A : Term) ([A] : Γ ⊩ne A ^ !) : Set where
  constructor neₜ₌
  open _⊩ne_^_ [A]
  field
    k m : Term
    d   : Γ ⊢ t :⇒*: k ∷ K 
    d′  : Γ ⊢ u :⇒*: m ∷ K
    nf  : Γ ⊩neNf k ≡ m ∷ K ^ !

-- Neutral irrelevant term equality
record _⊩neIrr_≡_∷_/_ (Γ : Con Term) (t u A : Term) ([A] : Γ ⊩ne A ^ %) : Set where
  constructor neₜ₌
  open _⊩ne_^_ [A]
  field
    d   : Γ ⊢ t ∷ A ^ %
    d′  : Γ ⊢ u ∷ A ^ %

-- Reducibility of natural numbers:

-- Natural number type
_⊩ℕ_ : (Γ : Con Term) (A : Term) → Set
Γ ⊩ℕ A = Γ ⊢ A :⇒*: ℕ ^ !

-- Natural number type equality
_⊩ℕ_≡_ : (Γ : Con Term) (A B : Term) → Set
Γ ⊩ℕ A ≡ B = Γ ⊢ B ⇒* ℕ ^ !

mutual
  -- Natural number term
  data _⊩ℕ_∷ℕ (Γ : Con Term) (t : Term) : Set where
    ℕₜ : (n : Term) (d : Γ ⊢ t :⇒*: n ∷ ℕ ) (n≡n : Γ ⊢ n ≅ n ∷ ℕ ^ !)
         (prop : Natural-prop Γ n)
       → Γ ⊩ℕ t ∷ℕ

  -- WHNF property of natural number terms
  data Natural-prop (Γ : Con Term) : (n : Term) → Set where
    sucᵣ  : ∀ {n} → Γ ⊩ℕ n ∷ℕ → Natural-prop Γ (suc n)
    zeroᵣ : Natural-prop Γ zero
    ne    : ∀ {n} → Γ ⊩neNf n ∷ ℕ ^ ! → Natural-prop Γ n

mutual
  -- Natural number term equality
  data _⊩ℕ_≡_∷ℕ (Γ : Con Term) (t u : Term) : Set where
    ℕₜ₌ : (k k′ : Term) (d : Γ ⊢ t :⇒*: k  ∷ ℕ) (d′ : Γ ⊢ u :⇒*: k′ ∷ ℕ)
          (k≡k′ : Γ ⊢ k ≅ k′ ∷ ℕ ^ !)
          (prop : [Natural]-prop Γ k k′) → Γ ⊩ℕ t ≡ u ∷ℕ

  -- WHNF property of Natural number term equality
  data [Natural]-prop (Γ : Con Term) : (n n′ : Term) → Set where
    sucᵣ  : ∀ {n n′} → Γ ⊩ℕ n ≡ n′ ∷ℕ → [Natural]-prop Γ (suc n) (suc n′)
    zeroᵣ : [Natural]-prop Γ zero zero
    ne    : ∀ {n n′} → Γ ⊩neNf n ≡ n′ ∷ ℕ ^ ! → [Natural]-prop Γ n n′

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
_⊩Empty_ : (Γ : Con Term) (A : Term) → Set
Γ ⊩Empty A = Γ ⊢ A :⇒*: Empty ^ %

-- Empty type equality
_⊩Empty_≡_ : (Γ : Con Term) (A B : Term) → Set
Γ ⊩Empty A ≡ B = Γ ⊢ B ⇒* Empty ^ %

data Empty-prop (Γ : Con Term) : (n : Term) → Set where
  ne    : ∀ {n} → Γ ⊢ n ∷ Empty ^ % → Empty-prop Γ n

-- -- Empty term

data _⊩Empty_∷Empty (Γ : Con Term) (t : Term) : Set where
  Emptyₜ :  -- (n : Term) (d : Γ ⊢ t :⇒*: n ∷ Empty ^ %) (n≡n : Γ ⊢ n ≅ n ∷ Empty ^ %)
         (prop : Empty-prop Γ t)
         → Γ ⊩Empty t ∷Empty

data [Empty]-prop (Γ : Con Term) : (n n′ : Term) → Set where
  ne    : ∀ {n n′} → Γ ⊢ n ∷ Empty ^ % → Γ ⊢ n′ ∷ Empty ^ %  → [Empty]-prop Γ n n′

-- Empty term equality
data _⊩Empty_≡_∷Empty (Γ : Con Term) (t u : Term) : Set where
  Emptyₜ₌ : -- (k k′ : Term) (d : Γ ⊢ t :⇒*: k ∷ Empty ^ %) (d′ : Γ ⊢ u :⇒*: k′ ∷ Empty ^ %)
    -- (k≡k′ : Γ ⊢ k ≅ k′ ∷ Empty ^ %)
      (prop : [Empty]-prop Γ t u) → Γ ⊩Empty t ≡ u ∷Empty

-- empty : ∀ {Γ n} → Empty-prop Γ n → Neutral n
-- empty (ne (neNfₜ neK _ _)) = neK

-- esplit : ∀ {Γ a b} → [Empty]-prop Γ a b → Neutral a × Neutral b
-- esplit (ne (neNfₜ₌ neK neM k≡m)) = neK , neM

-- Type levels

data TypeLevel : Set where
  ⁰ : TypeLevel
  ¹ : TypeLevel

data _<_ : (i j : TypeLevel) → Set where
  0<1 : ⁰ < ¹

-- Logical relation

record LogRelKit : Set₁ where
  constructor Kit
  field
    _⊩U : (Γ : Con Term) → Set
    _⊩Π_^_ : (Γ : Con Term) → Term → Relevance → Set

    _⊩_^_ : (Γ : Con Term) → Term → Relevance → Set
    _⊩_≡_^_/_ : (Γ : Con Term) (A B : Term) (r : Relevance) → Γ ⊩ A ^ r → Set
    _⊩_∷_^_/_ : (Γ : Con Term) (t A : Term) (r : Relevance) → Γ ⊩ A ^ r → Set
    _⊩_≡_∷_^_/_ : (Γ : Con Term) (t u A : Term) (r : Relevance) → Γ ⊩ A ^ r → Set

module LogRel (l : TypeLevel) (rec : ∀ {l′} → l′ < l → LogRelKit) where

  -- Reducibility of Universe:

  -- Universe type
  record _⊩¹U (Γ : Con Term) : Set where
    constructor Uᵣ
    field
      l′ : TypeLevel
      l< : l′ < l
      ⊢Γ : ⊢ Γ

  -- Universe type equality
  _⊩¹U_≡_ : (Γ : Con Term) (r : Relevance) (B : Term) → Set
  Γ ⊩¹U r ≡ B = B PE.≡ Univ r

  -- Universe term
  record _⊩¹U_∷U_/_ {l′} (Γ : Con Term) (t : Term) (r : Relevance) (l< : l′ < l) : Set where
    constructor Uₜ
    open LogRelKit (rec l<)
    field
      A     : Term
      d     : Γ ⊢ t :⇒*: A ∷ (Univ r) 
      typeA : Type A
      A≡A   : Γ ⊢ A ≅ A ∷ Univ r ^ !
      [t]   : Γ ⊩ t ^ r

  -- Universe term equality
  record _⊩¹U_≡_∷U_/_ {l′} (Γ : Con Term) (t u : Term) (r : Relevance) (l< : l′ < l) : Set where
    constructor Uₜ₌
    open LogRelKit (rec l<)
    field
      A B   : Term
      d     : Γ ⊢ t :⇒*: A ∷ Univ r 
      d′    : Γ ⊢ u :⇒*: B ∷ Univ r 
      typeA : Type A
      typeB : Type B
      A≡B   : Γ ⊢ A ≅ B ∷ Univ r ^ !
      [t]   : Γ ⊩ t ^ r
      [u]   : Γ ⊩ u ^ r
      [t≡u] : Γ ⊩ t ≡ u ^ r / [t]

  mutual

    -- Reducibility of Π:

    -- Π-type
    record _⊩¹Π_^_ (Γ : Con Term) (A : Term) (r : Relevance) : Set where
      inductive
      pattern
      constructor Πᵣ
      field
        rF : Relevance
        F : Term
        G : Term
        D : Γ ⊢ A :⇒*: Π F ^ rF ▹ G ^ r
        ⊢F : Γ ⊢ F ^ rF
        ⊢G : Γ ∙ F ^ rF ⊢ G ^ r
        A≡A : Γ ⊢ Π F ^ rF ▹ G ≅ Π F ^ rF ▹ G ^ r
        [F] : ∀ {ρ Δ} → ρ ∷ Δ ⊆ Γ → (⊢Δ : ⊢ Δ) → Δ ⊩¹ U.wk ρ F ^ rF
        [G] : ∀ {ρ Δ a}
            → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
            → Δ ⊩¹ a ∷ U.wk ρ F ^ rF / [F] [ρ] ⊢Δ
            → Δ ⊩¹ U.wk (lift ρ) G [ a ] ^ r
        G-ext : ∀ {ρ Δ a b}
              → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
              → ([a] : Δ ⊩¹ a ∷ U.wk ρ F ^ rF / [F] [ρ] ⊢Δ)
              → ([b] : Δ ⊩¹ b ∷ U.wk ρ F ^ rF / [F] [ρ] ⊢Δ)
              → Δ ⊩¹ a ≡ b ∷ U.wk ρ F ^ rF / [F] [ρ] ⊢Δ
              → Δ ⊩¹ U.wk (lift ρ) G [ a ] ≡ U.wk (lift ρ) G [ b ] ^ r / [G] [ρ] ⊢Δ [a]

    -- Π-type equality
    record _⊩¹Π_≡_^_/_ (Γ : Con Term) (A B : Term) (r : Relevance) ([A] : Γ ⊩¹Π A ^ r) : Set where
      inductive
      pattern
      constructor Π₌
      open _⊩¹Π_^_ [A]
      field
        F′     : Term
        G′     : Term
        D′     : Γ ⊢ B ⇒* Π F′ ^ rF ▹ G′ ^ r
        A≡B    : Γ ⊢ Π F ^ rF ▹ G ≅ Π F′ ^ rF ▹ G′ ^ r
        [F≡F′] : ∀ {ρ Δ}
               → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
               → Δ ⊩¹ U.wk ρ F ≡ U.wk ρ F′ ^ rF / [F] [ρ] ⊢Δ
        [G≡G′] : ∀ {ρ Δ a}
               → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
               → ([a] : Δ ⊩¹ a ∷ U.wk ρ F ^ rF / [F] [ρ] ⊢Δ)
               → Δ ⊩¹ U.wk (lift ρ) G [ a ] ≡ U.wk (lift ρ) G′ [ a ] ^ r / [G] [ρ] ⊢Δ [a]

    -- relevant Term of Π-type
    _⊩¹Π_∷_/_ : (Γ : Con Term) (t A : Term) ([A] : Γ ⊩¹Π A ^ !) → Set
    Γ ⊩¹Π t ∷ A / Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext =
      ∃ λ f → Γ ⊢ t :⇒*: f ∷ Π F ^ rF ▹ G 
            × Function f
            × Γ ⊢ f ≅ f ∷ Π F ^ rF ▹ G ^ !
            × (∀ {ρ Δ a b}
              → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
                ([a] : Δ ⊩¹ a ∷ U.wk ρ F ^ rF / [F] [ρ] ⊢Δ)
                ([b] : Δ ⊩¹ b ∷ U.wk ρ F ^ rF / [F] [ρ] ⊢Δ)
                ([a≡b] : Δ ⊩¹ a ≡ b ∷ U.wk ρ F ^ rF / [F] [ρ] ⊢Δ)
              → Δ ⊩¹ U.wk ρ f ∘ a ≡ U.wk ρ f ∘ b ∷ U.wk (lift ρ) G [ a ] ^ ! / [G] [ρ] ⊢Δ [a])
            × (∀ {ρ Δ a} → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
              → ([a] : Δ ⊩¹ a ∷ U.wk ρ F ^ rF / [F] [ρ] ⊢Δ)
              → Δ ⊩¹ U.wk ρ f ∘ a ∷ U.wk (lift ρ) G [ a ] ^ ! / [G] [ρ] ⊢Δ [a])
    -- Issue: Agda complains about record use not being strictly positive.
    --        Therefore we have to use ×

    -- relevant Term of Π-type
    _⊩¹Πirr_∷_/_ : (Γ : Con Term) (t A : Term) ([A] : Γ ⊩¹Π A ^ %) → Set
    Γ ⊩¹Πirr t ∷ A / Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext =
      Γ ⊢ t ∷ Π F ^ rF ▹ G ^ %
      
    -- Term equality of Π-type
    _⊩¹Π_≡_∷_/_ : (Γ : Con Term) (t u A : Term) ([A] : Γ ⊩¹Π A ^ !) → Set
    Γ ⊩¹Π t ≡ u ∷ A / Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext =
      let [A] = Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext
      in  ∃₂ λ f g →
          (Γ ⊢ t :⇒*: f ∷ Π F ^ rF ▹ G )
      ×   (Γ ⊢ u :⇒*: g ∷ Π F ^ rF ▹ G )
      ×   Function f
      ×   Function g
      ×   Γ ⊢ f ≅ g ∷ Π F ^ rF ▹ G ^ !
      ×   Γ ⊩¹Π t ∷ A / [A]
      ×   Γ ⊩¹Π u ∷ A / [A]
      ×   (∀ {ρ Δ a} → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          → ([a] : Δ ⊩¹ a ∷ U.wk ρ F ^ rF / [F] [ρ] ⊢Δ)
          → Δ ⊩¹ U.wk ρ f ∘ a ≡ U.wk ρ g ∘ a ∷ U.wk (lift ρ) G [ a ] ^ ! / [G] [ρ] ⊢Δ [a])
    -- Issue: Same as above.

    -- Term equality of Π-type
    _⊩¹Πirr_≡_∷_/_ : (Γ : Con Term) (t u A : Term) ([A] : Γ ⊩¹Π A ^ %) → Set
    Γ ⊩¹Πirr t ≡ u ∷ A / Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext =
          (Γ ⊢ t ∷ Π F ^ rF ▹ G ^ %)
          ×
          (Γ ⊢ u ∷ Π F ^ rF ▹ G ^ %)
    

    -- Logical relation definition

    data _⊩¹_^_ (Γ : Con Term) : Term → Relevance → Set where
      Uᵣ  : ∀ {r} → Γ ⊩¹U → Γ ⊩¹ Univ r ^ !
      ℕᵣ  : ∀ {A} → Γ ⊩ℕ A → Γ ⊩¹ A ^ !
      Emptyᵣ : ∀ {A} → Γ ⊩Empty A → Γ ⊩¹ A ^ %
      ne  : ∀ {A r} → Γ ⊩ne A ^ r → Γ ⊩¹ A ^ r
      Πᵣ  : ∀ {A r} → Γ ⊩¹Π A ^ r → Γ ⊩¹ A ^ r
      emb : ∀ {A r l′} (l< : l′ < l) (let open LogRelKit (rec l<))
            ([A] : Γ ⊩ A ^ r) → Γ ⊩¹ A ^ r

    _⊩¹_≡_^_/_ : (Γ : Con Term) (A B : Term) (r : Relevance) → Γ ⊩¹ A ^ r → Set
    Γ ⊩¹ A ≡ B ^ .! / Uᵣ {r = r'} UA = Γ ⊩¹U r' ≡ B
    Γ ⊩¹ A ≡ B ^ .! / ℕᵣ D = Γ ⊩ℕ A ≡ B
    Γ ⊩¹ A ≡ B ^ .% / Emptyᵣ D = Γ ⊩Empty A ≡ B
    Γ ⊩¹ A ≡ B ^ r / ne neA = Γ ⊩ne A ≡ B ^ r / neA
    Γ ⊩¹ A ≡ B ^ r / Πᵣ ΠA = Γ ⊩¹Π A ≡ B ^ r / ΠA
    Γ ⊩¹ A ≡ B ^ r / emb l< [A] = Γ ⊩ A ≡ B ^ r / [A]
      where open LogRelKit (rec l<)

    _⊩¹_∷_^_/_ : (Γ : Con Term) (t A : Term) (r : Relevance) → Γ ⊩¹ A ^ r → Set
    Γ ⊩¹ t ∷ .(Univ r') ^ .! / Uᵣ {r = r'} (Uᵣ l′ l< ⊢Γ) = Γ ⊩¹U t ∷U r' / l<
    Γ ⊩¹ t ∷ A ^ .! / ℕᵣ D = Γ ⊩ℕ t ∷ℕ
    Γ ⊩¹ t ∷ A ^ .% / Emptyᵣ D = Γ ⊩Empty t ∷Empty
    Γ ⊩¹ t ∷ A ^ ! / ne neA = Γ ⊩ne t ∷ A / neA
    Γ ⊩¹ t ∷ A ^ % / ne neA = Γ ⊩neIrr t ∷ A / neA
    Γ ⊩¹ f ∷ A ^ ! / Πᵣ ΠA  = Γ ⊩¹Π f ∷ A / ΠA
    Γ ⊩¹ f ∷ A ^ % / Πᵣ ΠA  = Γ ⊩¹Πirr f ∷ A / ΠA
    Γ ⊩¹ t ∷ A ^ r / emb l< [A] = Γ ⊩ t ∷ A ^ r / [A]
      where open LogRelKit (rec l<)

    _⊩¹_≡_∷_^_/_ : (Γ : Con Term) (t u A : Term) (r : Relevance) → Γ ⊩¹ A ^ r → Set
    Γ ⊩¹ t ≡ u ∷ .(Univ r') ^ .! / Uᵣ {r = r'} (Uᵣ l′ l< ⊢Γ) = Γ ⊩¹U t ≡ u ∷U r' / l<
    Γ ⊩¹ t ≡ u ∷ A ^ .! / ℕᵣ D = Γ ⊩ℕ t ≡ u ∷ℕ
    Γ ⊩¹ t ≡ u ∷ A ^ .% / Emptyᵣ D = Γ ⊩Empty t ≡ u ∷Empty
    Γ ⊩¹ t ≡ u ∷ A ^ ! / ne neA = Γ ⊩ne t ≡ u ∷ A / neA
    Γ ⊩¹ t ≡ u ∷ A ^ % / ne neA = Γ ⊩neIrr t ≡ u ∷ A / neA
    Γ ⊩¹ t ≡ u ∷ A ^ ! / Πᵣ ΠA = Γ ⊩¹Π t ≡ u ∷ A / ΠA
    Γ ⊩¹ t ≡ u ∷ A ^ % / Πᵣ ΠA = Γ ⊩¹Πirr t ≡ u ∷ A / ΠA
    Γ ⊩¹ t ≡ u ∷ A ^ r / emb l< [A] = Γ ⊩ t ≡ u ∷ A ^ r / [A]
      where open LogRelKit (rec l<)

    kit : LogRelKit
    kit = Kit _⊩¹U _⊩¹Π_^_
              _⊩¹_^_ _⊩¹_≡_^_/_ _⊩¹_∷_^_/_ _⊩¹_≡_∷_^_/_

open LogRel public using (Uᵣ; ℕᵣ; Emptyᵣ; ne; Πᵣ; emb; Uₜ; Uₜ₌; Π₌)

-- Patterns for the non-records of Π
pattern Πₜ a b c d e f = a , b , c , d , e , f
pattern Πₜ₌ a b c d e f g h i j = a , b , c , d , e , f , g , h , i , j

pattern Uᵣ′ r a b c = Uᵣ {r = r} (Uᵣ a b c)
pattern ne′ a b c d = ne (ne a b c d)
pattern Πᵣ′  a b c d e f g h i j = Πᵣ (Πᵣ a b c d e f g h i j)

logRelRec : ∀ l {l′} → l′ < l → LogRelKit
logRelRec ⁰ = λ ()
logRelRec ¹ 0<1 = LogRel.kit ⁰ (λ ())

kit : ∀ (i : TypeLevel) → LogRelKit
kit l = LogRel.kit l (logRelRec l)
-- a bit of repetition in "kit ¹" definition, would work better with Fin 2 for
-- TypeLevel because you could recurse.

_⊩′⟨_⟩U : (Γ : Con Term) (l : TypeLevel) → Set
Γ ⊩′⟨ l ⟩U = Γ ⊩U where open LogRelKit (kit l)

_⊩′⟨_⟩Π_^_ : (Γ : Con Term) (l : TypeLevel) → Term → Relevance → Set
Γ ⊩′⟨ l ⟩Π A ^ r = Γ ⊩Π A ^ r where open LogRelKit (kit l)

_⊩⟨_⟩_^_ : (Γ : Con Term) (l : TypeLevel) → Term → Relevance → Set
Γ ⊩⟨ l ⟩ A ^ r = Γ ⊩ A ^ r where open LogRelKit (kit l)

_⊩⟨_⟩_≡_^_/_ : (Γ : Con Term) (l : TypeLevel) (A B : Term) (r : Relevance) → Γ ⊩⟨ l ⟩ A ^ r → Set
Γ ⊩⟨ l ⟩ A ≡ B ^ r / [A] = Γ ⊩ A ≡ B ^ r / [A] where open LogRelKit (kit l)

_⊩⟨_⟩_∷_^_/_ : (Γ : Con Term) (l : TypeLevel) (t A : Term) (r : Relevance) → Γ ⊩⟨ l ⟩ A ^ r → Set
Γ ⊩⟨ l ⟩ t ∷ A ^ r / [A] = Γ ⊩ t ∷ A ^ r / [A] where open LogRelKit (kit l)

_⊩⟨_⟩_≡_∷_^_/_ : (Γ : Con Term) (l : TypeLevel) (t u A : Term) (r : Relevance) → Γ ⊩⟨ l ⟩ A ^ r → Set
Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ r / [A] = Γ ⊩ t ≡ u ∷ A ^ r / [A] where open LogRelKit (kit l)


logRelIrr : ∀ {l t Γ A} ([A] : Γ ⊩⟨ l ⟩ A ^ %) (⊢t : Γ ⊢ t ∷ A ^ %) → Γ ⊩⟨ l ⟩ t ∷ A ^ % / [A]
logRelIrr (Emptyᵣ [ ⊢A , ⊢B , D ]) ⊢t = Emptyₜ (ne (conv ⊢t (reduction D (id ⊢B) Emptyₙ Emptyₙ (refl ⊢B))))
logRelIrr (ne x) ⊢t = neₜ ⊢t
logRelIrr (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) ⊢t = conv ⊢t (reduction (red D) (id (_⊢_:⇒*:_^_.⊢B D)) Πₙ Πₙ (refl (_⊢_:⇒*:_^_.⊢B D))) 
logRelIrr (emb 0<1 [A]) ⊢t = logRelIrr [A] ⊢t

logRelIrrEq : ∀ {l t u Γ A} ([A] : Γ ⊩⟨ l ⟩ A ^ %) (⊢t : Γ ⊢ t ∷ A ^ %) (⊢u : Γ ⊢ u ∷ A ^ %) → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ % / [A]
logRelIrrEq (Emptyᵣ [ ⊢A , ⊢B , D ]) ⊢t ⊢u = Emptyₜ₌ (ne ((conv ⊢t (reduction D (id ⊢B) Emptyₙ Emptyₙ (refl ⊢B))))
                                                         (conv ⊢u (reduction D (id ⊢B) Emptyₙ Emptyₙ (refl ⊢B))))
logRelIrrEq (ne x) ⊢t ⊢u = neₜ₌ ⊢t ⊢u
logRelIrrEq (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) ⊢t ⊢u = (conv ⊢t (reduction (red D) (id (_⊢_:⇒*:_^_.⊢B D)) Πₙ Πₙ (refl (_⊢_:⇒*:_^_.⊢B D))) ) , (conv ⊢u (reduction (red D) (id (_⊢_:⇒*:_^_.⊢B D)) Πₙ Πₙ (refl (_⊢_:⇒*:_^_.⊢B D))) )
logRelIrrEq (emb 0<1 [A]) ⊢t ⊢u = logRelIrrEq [A] ⊢t ⊢u 
