{-# OPTIONS --without-K  #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U
open import Definition.Typed
open import Definition.Typed.Weakening

open import Tools.Product
import Tools.PropositionalEquality as PE


-- The different cases of the logical relation are spread out through out
-- this file. This is due to them having different dependencies.

-- We will refer to expressions that satisfies the logical relation as reducible.

-- Reducibility of Neutrals:

-- Neutral type
record _⊩ne_⦂_ (Γ : Con Term) (A : Term) (s : 𝕊) : Set where
  constructor ne
  field
    K   : Term
    D   : Γ ⊢ A :⇒*: K ⦂ s
    neK : Neutral K
    K≡K : Γ ⊢ K ~ K ∷ (Univ s) ⦂ 𝕥y

-- Neutral type equality
record _⊩ne_≡_⦂_/_ (Γ : Con Term) (A B : Term) (s : 𝕊) ([A] : Γ ⊩ne A ⦂ s) : Set where
  constructor ne₌
  open _⊩ne_⦂_ [A]
  field
    M   : Term
    D′  : Γ ⊢ B :⇒*: M ⦂ s
    neM : Neutral M
    K≡M : Γ ⊢ K ~ M ∷ (Univ s) ⦂ 𝕥y

-- Neutral term in WHNF
record _⊩neNf_∷_⦂_ (Γ : Con Term) (k A : Term) (s : 𝕊) : Set where
  inductive
  constructor neNfₜ
  field
    neK  : Neutral k
    ⊢k   : Γ ⊢ k ∷ A ⦂ s
    k≡k  : Γ ⊢ k ~ k ∷ A ⦂ s

-- Neutral term
record _⊩ne_∷_⦂_/_ (Γ : Con Term) (t A : Term) (s : 𝕊) ([A] : Γ ⊩ne A ⦂ s) : Set where
  inductive
  constructor neₜ
  open _⊩ne_⦂_ [A]
  field
    k   : Term
    d   : Γ ⊢ t :⇒*: k ∷ K ⦂ s
    nf  : Γ ⊩neNf k ∷ K ⦂ s

-- Neutral term equality in WHNF
record _⊩neNf_≡_∷_⦂_ (Γ : Con Term) (k m A : Term) (s : 𝕊) : Set where
  inductive
  constructor neNfₜ₌
  field
    neK  : Neutral k
    neM  : Neutral m
    k≡m  : Γ ⊢ k ~ m ∷ A ⦂ s

-- Neutral term equality
record _⊩ne_≡_∷_⦂_/_ (Γ : Con Term) (t u A : Term) (s : 𝕊) ([A] : Γ ⊩ne A ⦂ s) : Set where
  constructor neₜ₌
  open _⊩ne_⦂_ [A]
  field
    k m : Term
    d   : Γ ⊢ t :⇒*: k ∷ K ⦂ s
    d′  : Γ ⊢ u :⇒*: m ∷ K ⦂ s
    nf  : Γ ⊩neNf k ≡ m ∷ K ⦂ s


-- Reducibility at constructor type:

data Cstr-prop (K : constructors) (Γ : Con Term) (Pi : ∀ ki → [ K ]-cstr (cstr-cod ki) → Term → Set) (a : Term) (s : 𝕊) : (t : Term) → Set where
  cstrᵣ : ∀ {k x}
        → (kK : [ K ]-cstr (cstr-cod k))
        -- Main problem: how to have the following hypothesis in a strictly positive fashion
        -- → Γ ⊩¹ x ∷ wkAll Γ (cstr-dom k) ⦂ 𝕥y / [domk] k Γ
        → Pi k kK x
        -- How should a be constrained ?
        -- first version, too rigid, breaks in Conversion because it is not stable under conversion
        -- a PE.≡ [ K ]-cstr-params kK [ x ]
        → Cstr-prop K Γ Pi a s (cstr k ∘ x)
  ne   : ∀ {t} → Γ ⊩neNf t ∷ cstr K ∘ a ⦂ s → Cstr-prop K Γ Pi a s t

data [Cstr]-prop (K : constructors) (Γ : Con Term) (Pi : ∀ ki → [ K ]-cstr (cstr-cod ki) → Term → Term → Set) (a : Term) (s : 𝕊) : (t t' : Term) → Set where
  cstrᵣ : ∀ {k x x'}
        → (kK : [ K ]-cstr (cstr-cod k))
        → Pi k kK x x'
        → [Cstr]-prop K Γ Pi a s (cstr k ∘ x) (cstr k ∘ x')
  ne   : ∀ {t t'} → Γ ⊩neNf t ≡ t' ∷ cstr K ∘ a ⦂ s → [Cstr]-prop K Γ Pi a s t t'


Cstr-prop-Whnf : ∀ {K Γ Pi t a s} (d : Cstr-prop K Γ Pi a s t) → Whnf t
Cstr-prop-Whnf (cstrᵣ kK x) = cstrₙ
Cstr-prop-Whnf (ne x) = ne (_⊩neNf_∷_⦂_.neK x)

[Cstr]-prop-left-Whnf : ∀ {K Γ Pi t t' a s} (d : [Cstr]-prop K Γ Pi a s t t') → Whnf t
[Cstr]-prop-left-Whnf (cstrᵣ kK x) = cstrₙ
[Cstr]-prop-left-Whnf (ne x) = ne (_⊩neNf_≡_∷_⦂_.neK x)

[Cstr]-prop-right-Whnf : ∀ {K Γ Pi t t' a s} (d : [Cstr]-prop K Γ Pi a s t t') → Whnf t'
[Cstr]-prop-right-Whnf (cstrᵣ kK x) = cstrₙ
[Cstr]-prop-right-Whnf (ne x) = ne (_⊩neNf_≡_∷_⦂_.neM x)

-- Reducibility of Boxes:
-- Box-prop (λ x → Γ ⊩¹ x ∷ F ⦂ sF / [F]) Γ F sF

data Box-prop (P : Term → Set) (Γ : Con Term) (F : Term) (sF : sorts) : Term → Set where
  boxᵣ : ∀ {b} → P b → Box-prop P Γ F sF (box sF b)
  ne   : ∀ {t} → Γ ⊩neNf t ∷ Box sF F ⦂ 𝕥y → Box-prop P Γ F sF t

data [Box]-prop (P : Term → Term → Set) (Γ : Con Term) (F : Term) (sF : sorts) : Term → Term → Set where
  boxᵣ : ∀ {b b'} → P b b' → [Box]-prop P Γ F sF (box sF b) (box sF b')
  ne   : ∀ {t t'} → Γ ⊩neNf t ≡ t' ∷ Box sF F ⦂ 𝕥y → [Box]-prop P Γ F sF t t'

Box-prop-Whnf : ∀ {P Γ F sF t} (d : Box-prop P Γ F sF t) → Whnf t
Box-prop-Whnf (boxᵣ x) = boxₙ
Box-prop-Whnf (ne x) = ne (_⊩neNf_∷_⦂_.neK x)

[Box]-prop-Whnf : ∀ {P Γ F sF t t'} (d : [Box]-prop P Γ F sF t t') → Whnf t × Whnf t'
[Box]-prop-Whnf (boxᵣ x) = boxₙ , boxₙ
[Box]-prop-Whnf (ne (neNfₜ₌ neK neM k≡m)) = (ne neK) , (ne neM)

-- Reducibility of natural numbers:

-- Natural number type
_⊩ℕ_ : (Γ : Con Term) (A : Term) → Set
Γ ⊩ℕ A = Γ ⊢ A :⇒*: ℕ ⦂ 𝕥y

-- Natural number type equality
_⊩ℕ_≡_ : (Γ : Con Term) (A B : Term) → Set
Γ ⊩ℕ A ≡ B = Γ ⊢ B ⇒* ℕ ⦂ 𝕥y

mutual
  -- Natural number term
  data _⊩ℕ_∷ℕ (Γ : Con Term) (t : Term) : Set where
    ℕₜ : (n : Term) (d : Γ ⊢ t :⇒*: n ∷ ℕ ⦂ 𝕥y) (n≡n : Γ ⊢ n ≅ n ∷ ℕ ⦂ 𝕥y)
         (prop : Natural-prop Γ n)
       → Γ ⊩ℕ t ∷ℕ

  -- WHNF property of natural number terms
  data Natural-prop (Γ : Con Term) : (n : Term) → Set where
    sucᵣ  : ∀ {n} → Γ ⊩ℕ n ∷ℕ → Natural-prop Γ (suc n)
    zeroᵣ : Natural-prop Γ zero
    ne    : ∀ {n} → Γ ⊩neNf n ∷ ℕ ⦂ 𝕥y → Natural-prop Γ n

mutual
  -- Natural number term equality
  data _⊩ℕ_≡_∷ℕ (Γ : Con Term) (t u : Term) : Set where
    ℕₜ₌ : (k k′ : Term) (d : Γ ⊢ t :⇒*: k  ∷ ℕ ⦂ 𝕥y) (d′ : Γ ⊢ u :⇒*: k′ ∷ ℕ ⦂ 𝕥y)
          (k≡k′ : Γ ⊢ k ≅ k′ ∷ ℕ ⦂ 𝕥y)
          (prop : [Natural]-prop Γ k k′) → Γ ⊩ℕ t ≡ u ∷ℕ

  -- WHNF property of Natural number term equality
  data [Natural]-prop (Γ : Con Term) : (n n′ : Term) → Set where
    sucᵣ  : ∀ {n n′} → Γ ⊩ℕ n ≡ n′ ∷ℕ → [Natural]-prop Γ (suc n) (suc n′)
    zeroᵣ : [Natural]-prop Γ zero zero
    ne    : ∀ {n n′} → Γ ⊩neNf n ≡ n′ ∷ ℕ ⦂ 𝕥y → [Natural]-prop Γ n n′

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
Γ ⊩Empty A = Γ ⊢ A :⇒*: Empty ⦂ 𝕥y

-- Empty type equality
_⊩Empty_≡_ : (Γ : Con Term) (A B : Term) → Set
Γ ⊩Empty A ≡ B = Γ ⊢ B ⇒* Empty ⦂ 𝕥y

data Empty-prop (Γ : Con Term) : (n : Term) → Set where
  ne    : ∀ {n} → Γ ⊩neNf n ∷ Empty ⦂ 𝕥y → Empty-prop Γ n

-- Empty term
data _⊩Empty_∷Empty (Γ : Con Term) (t : Term) : Set where
  Emptyₜ : (n : Term) (d : Γ ⊢ t :⇒*: n ∷ Empty ⦂ 𝕥y) (n≡n : Γ ⊢ n ≅ n ∷ Empty ⦂ 𝕥y)
         (prop : Empty-prop Γ n)
         → Γ ⊩Empty t ∷Empty

data [Empty]-prop (Γ : Con Term) : (n n′ : Term) → Set where
  ne    : ∀ {n n′} → Γ ⊩neNf n ≡ n′ ∷ Empty ⦂ 𝕥y → [Empty]-prop Γ n n′

-- Empty term equality
data _⊩Empty_≡_∷Empty (Γ : Con Term) (t u : Term) : Set where
  Emptyₜ₌ : (k k′ : Term) (d : Γ ⊢ t :⇒*: k ∷ Empty ⦂ 𝕥y) (d′ : Γ ⊢ u :⇒*: k′ ∷ Empty ⦂ 𝕥y)
    (k≡k′ : Γ ⊢ k ≅ k′ ∷ Empty ⦂ 𝕥y)
      (prop : [Empty]-prop Γ k k′) → Γ ⊩Empty t ≡ u ∷Empty

empty : ∀ {Γ n} → Empty-prop Γ n → Neutral n
empty (ne (neNfₜ neK _ _)) = neK

esplit : ∀ {Γ a b} → [Empty]-prop Γ a b → Neutral a × Neutral b
esplit (ne (neNfₜ₌ neK neM k≡m)) = neK , neM

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
    _⊩U_ : (Γ : Con Term) (s : 𝕊) → Set
    _⊩Π_⦂_ : (Γ : Con Term) → Term → 𝕊 → Set
    _⊩cstr_⦂_ : (Γ : Con Term) → Term → 𝕊 → Set
    _⊩Box_ : (Γ : Con Term) → Term → Set

    _⊩_⦂_ : (Γ : Con Term) → Term → 𝕊 → Set
    _⊩_≡_⦂_/_ : (Γ : Con Term) (A B : Term) (s : 𝕊) → Γ ⊩ A ⦂ s → Set
    _⊩_∷_⦂_/_ : (Γ : Con Term) (t A : Term) (s : 𝕊) → Γ ⊩ A ⦂ s → Set
    _⊩_≡_∷_⦂_/_ : (Γ : Con Term) (t u A : Term) (s : 𝕊) → Γ ⊩ A ⦂ s → Set

module LogRel (l : TypeLevel) (rec : ∀ {l′} → l′ < l → LogRelKit) where

  -- Reducibility of Universe:

  -- Universe type
  record _⊩¹U_ (Γ : Con Term) (s : 𝕊) : Set where
    constructor Uᵣ
    field
      l′ : TypeLevel
      l< : l′ < l
      ⊢Γ : ⊢ Γ

  -- Universe type equality
  _⊩¹U[_]≡_ : (Γ : Con Term) (s : 𝕊) (B : Term) → Set
  Γ ⊩¹U[ s ]≡ B = B PE.≡ Univ s

  -- Universe term
  record _⊩¹U_∷U_/_ {l′} (Γ : Con Term) (t : Term) (s : 𝕊) (l< : l′ < l) : Set where
    inductive
    constructor Uₜ
    open LogRelKit (rec l<)
    field
      A     : Term
      d     : Γ ⊢ t :⇒*: A ∷ (Univ s) ⦂ 𝕥y
      typeA : Type A
      A≡A   : Γ ⊢ A ≅ A ∷ Univ s ⦂ 𝕥y
      [t]   : Γ ⊩ t ⦂ s

  -- Universe term equality
  record _⊩¹U_≡_∷U_/_ {l′} (Γ : Con Term) (t u : Term) (s : 𝕊) (l< : l′ < l) : Set where
    constructor Uₜ₌
    open LogRelKit (rec l<)
    field
      A B   : Term
      d     : Γ ⊢ t :⇒*: A ∷ Univ s ⦂ 𝕥y
      d′    : Γ ⊢ u :⇒*: B ∷ Univ s ⦂ 𝕥y
      typeA : Type A
      typeB : Type B
      A≡B   : Γ ⊢ A ≅ B ∷ Univ s ⦂ 𝕥y
      [t]   : Γ ⊩ t ⦂ s
      [u]   : Γ ⊩ u ⦂ s
      [t≡u] : Γ ⊩ t ≡ u ⦂ s / [t]

  mutual

    -- Reducibility of Π:

    -- Π-type
    record _⊩¹Π_⦂_ (Γ : Con Term) (A : Term) (s : 𝕊) : Set where
      inductive
      constructor Πᵣ
      eta-equality
      field
        sF : 𝕊
        F : Term
        G : Term
        D : Γ ⊢ A :⇒*: Π F ⦂ sF ▹ G ⦂ s
        ⊢F : Γ ⊢ F ⦂ sF
        ⊢G : Γ ∙ F ⦂ sF ⊢ G ⦂ s
        A≡A : Γ ⊢ Π F ⦂ sF ▹ G ≅ Π F ⦂ sF ▹ G ⦂ s
        [F] : ∀ {ρ Δ} → ρ ∷ Δ ⊆ Γ → (⊢Δ : ⊢ Δ) → Δ ⊩¹ U.wk ρ F ⦂ sF
        [G] : ∀ {ρ Δ a}
            → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
            → Δ ⊩¹ a ∷ U.wk ρ F ⦂ sF / [F] [ρ] ⊢Δ
            → Δ ⊩¹ U.wk (lift ρ) G [ a ] ⦂ s
        G-ext : ∀ {ρ Δ a b}
              → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
              → ([a] : Δ ⊩¹ a ∷ U.wk ρ F ⦂ sF / [F] [ρ] ⊢Δ)
              → ([b] : Δ ⊩¹ b ∷ U.wk ρ F ⦂ sF / [F] [ρ] ⊢Δ)
              → Δ ⊩¹ a ≡ b ∷ U.wk ρ F ⦂ sF / [F] [ρ] ⊢Δ
              → Δ ⊩¹ U.wk (lift ρ) G [ a ] ≡ U.wk (lift ρ) G [ b ] ⦂ s / [G] [ρ] ⊢Δ [a]

    -- Π-type equality
    record _⊩¹Π_≡_⦂_/_ (Γ : Con Term) (A B : Term) (s : 𝕊) ([A] : Γ ⊩¹Π A ⦂ s) : Set where
      inductive
      constructor Π₌
      eta-equality
      open _⊩¹Π_⦂_ [A]
      field
        F′     : Term
        G′     : Term
        D′     : Γ ⊢ B ⇒* Π F′ ⦂ sF ▹ G′ ⦂ s
        A≡B    : Γ ⊢ Π F ⦂ sF ▹ G ≅ Π F′ ⦂ sF ▹ G′ ⦂ s
        [F≡F′] : ∀ {ρ Δ}
               → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
               → Δ ⊩¹ U.wk ρ F ≡ U.wk ρ F′ ⦂ sF / [F] [ρ] ⊢Δ
        [G≡G′] : ∀ {ρ Δ a}
               → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
               → ([a] : Δ ⊩¹ a ∷ U.wk ρ F ⦂ sF / [F] [ρ] ⊢Δ)
               → Δ ⊩¹ U.wk (lift ρ) G [ a ] ≡ U.wk (lift ρ) G′ [ a ] ⦂ s / [G] [ρ] ⊢Δ [a]

    -- Term of Π-type
    _⊩¹Π_∷_⦂_/_ : (Γ : Con Term) (t A : Term) (s : 𝕊) ([A] : Γ ⊩¹Π A ⦂ s) → Set
    Γ ⊩¹Π t ∷ A ⦂ s / Πᵣ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext =
      ∃ λ f → Γ ⊢ t :⇒*: f ∷ Π F ⦂ sF ▹ G ⦂ s
            × Function f
            × Γ ⊢ f ≅ f ∷ Π F ⦂ sF ▹ G ⦂ s
            × (∀ {ρ Δ a b}
              → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
                ([a] : Δ ⊩¹ a ∷ U.wk ρ F ⦂ sF / [F] [ρ] ⊢Δ)
                ([b] : Δ ⊩¹ b ∷ U.wk ρ F ⦂ sF / [F] [ρ] ⊢Δ)
                ([a≡b] : Δ ⊩¹ a ≡ b ∷ U.wk ρ F ⦂ sF / [F] [ρ] ⊢Δ)
              → Δ ⊩¹ U.wk ρ f ∘ a ≡ U.wk ρ f ∘ b ∷ U.wk (lift ρ) G [ a ] ⦂ s / [G] [ρ] ⊢Δ [a])
            × (∀ {ρ Δ a} → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
              → ([a] : Δ ⊩¹ a ∷ U.wk ρ F ⦂ sF / [F] [ρ] ⊢Δ)
              → Δ ⊩¹ U.wk ρ f ∘ a ∷ U.wk (lift ρ) G [ a ] ⦂ s / [G] [ρ] ⊢Δ [a])
    -- Issue: Agda complains about record use not being strictly positive.
    --        Therefore we have to use ×


    -- Term equality of Π-type
    _⊩¹Π_≡_∷_⦂_/_ : (Γ : Con Term) (t u A : Term) (s : 𝕊) ([A] : Γ ⊩¹Π A ⦂ s) → Set
    Γ ⊩¹Π t ≡ u ∷ A ⦂ s / Πᵣ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext =
      let [A] = Πᵣ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext
      in  ∃₂ λ f g →
          Γ ⊢ t :⇒*: f ∷ Π F ⦂ sF ▹ G ⦂ s
      ×   Γ ⊢ u :⇒*: g ∷ Π F ⦂ sF ▹ G ⦂ s
      ×   Function f
      ×   Function g
      ×   Γ ⊢ f ≅ g ∷ Π F ⦂ sF ▹ G ⦂ s
      ×   Γ ⊩¹Π t ∷ A ⦂ s / [A]
      ×   Γ ⊩¹Π u ∷ A ⦂ s / [A]
      ×   (∀ {ρ Δ a} → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          → ([a] : Δ ⊩¹ a ∷ U.wk ρ F ⦂ sF / [F] [ρ] ⊢Δ)
          → Δ ⊩¹ U.wk ρ f ∘ a ≡ U.wk ρ g ∘ a ∷ U.wk (lift ρ) G [ a ] ⦂ s / [G] [ρ] ⊢Δ [a])
    -- Issue: Same as above.

    -- Reducibility for constructors
    record _⊩¹cstr_⦂_ (Γ : Con Term) (A : Term) (s : 𝕊) : Set where
      inductive
      eta-equality
      constructor cstrᵣ
      field
        K : constructors
        KcodU : cstr-cod K PE.≡ Univ s
        a : Term
        D : Γ ⊢ A :⇒*: cstr K ∘ a ⦂ s
        -- Is there a way to use the hypothesis that cstr-dom is closed to simplify the argument ?
        ⊢a : Γ ⊢ a ∷ wkAll Γ (cstr-dom K) ⦂ cstr-dom-sort K -- TODO: the sort of the dom might need to be generalized
        A≡A : Γ ⊢ a ≅ a ∷ wkAll Γ (cstr-dom K) ⦂ cstr-dom-sort K -- Implies that Γ ⊢ cstr K ∘ a ≅ cstr K ∘ a ⦂ s by ≅-cstr-cong
        [domK] : Γ ⊩¹ wkAll Γ (cstr-dom K) ⦂ cstr-dom-sort K
        -- [domK] : ∀ {ρ Δ} → ρ ∷ Δ ⊆ Γ → (⊢Δ : ⊢ Δ) → Δ ⊩¹ U.wk ρ (wkAll Γ (cstr-dom K)) ⦂ 𝕥y
        [a] : Γ ⊩¹ a ∷ wkAll Γ (cstr-dom K) ⦂ cstr-dom-sort K / [domK]
        -- [a] : ∀ {ρ Δ} → ([ρ] : ρ ∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ) → Δ ⊩¹ U.wk ρ a ∷ U.wk ρ (wkAll Γ (cstr-dom k)) ⦂ 𝕥y / [dom] [ρ] ⊢Δ
        [Yi] : ∀ ki → [ K ]-cstr (cstr-cod ki) → Γ ⊩¹ wkAll Γ (cstr-dom ki) ⦂ cstr-dom-sort ki
        -- KM: Do I need an hypothesys that cstr k is extensional, e.g.
        -- k-ext : ∀ {ρ Δ a b}
        --       → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
        --       → ([a] : Δ ⊩¹ a ∷ U.wk ρ (cstr-dom k) ⦂ 𝕥y / [dom] [ρ] ⊢Δ)
        --       → ([b] : Δ ⊩¹ b ∷ U.wk ρ (cstr-dom k) ⦂ 𝕥y / [dom] [ρ] ⊢Δ)
        --       → Δ ⊩¹ a ≡ b ∷ U.wk ρ (cstr-dom k) ⦂ 𝕥y / [dom] [ρ] ⊢Δ
        --       → Δ ⊩¹ cstr k ∘ a ≡ cstr k ∘ b ⦂ cstr-𝕊 / [G] [ρ] ⊢Δ [a]

    record _⊩¹cstr_≡_⦂_/_ (Γ : Con Term) (A B : Term) (s : 𝕊) ([A] : Γ ⊩¹cstr A ⦂ s) : Set where
      inductive
      eta-equality
      constructor cstr₌
      open _⊩¹cstr_⦂_ [A]
      field
        a' : Term
        D' : Γ ⊢ B :⇒*: cstr K ∘ a' ⦂ s
        A≡B : Γ ⊢ a ≅ a' ∷ wkAll Γ (cstr-dom K) ⦂ cstr-dom-sort K
        [a≡a'] : Γ ⊩¹ a ≡ a' ∷ wkAll Γ (cstr-dom K) ⦂ cstr-dom-sort K / [domK]
        -- [a≡a'] : ∀ {ρ Δ} → ([ρ] : ρ ∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ) → Δ ⊩¹ U.wk ρ a ≡
        -- U.wk ρ a' ∷ U.wk ρ (wkAll Γ (cstr-dom K)) ⦂ 𝕥y / [domK] [ρ] ⊢Δ
        -- shouldn't there be a [Yi≡Yi'] ? Not for now because in [Cstr]-prop we
        -- only relate two values if they start with the same constructor, hence
        -- enforcing that their arguments have the same type (on the nose)
        -- However, this should probably change if we were to accept equations between constructors (in the equational theory)

    _⊩¹cstr_∷_⦂_/_ : (Γ : Con Term) (t A : Term) (s : 𝕊) ([A] : Γ ⊩¹cstr A ⦂ s) → Set
    Γ ⊩¹cstr t ∷ A ⦂ s / cstrᵣ K KcodU a D ⊢a A≡A [domK] [a] [Yi] =
      ∃ λ k → Γ ⊢ t :⇒*: k ∷ cstr K ∘ a ⦂ s
             × Γ ⊢ k ≅ k ∷ cstr K ∘ a ⦂ s
             × Cstr-prop K Γ (λ ki kiK t → Γ ⊩¹ t ∷ wkAll Γ (cstr-dom ki) ⦂ cstr-dom-sort ki / [Yi] ki kiK) a s k

    _⊩¹cstr_≡_∷_⦂_/_ : (Γ : Con Term) (t u A : Term) (s : 𝕊) ([A] : Γ ⊩¹cstr A ⦂ s) → Set
    Γ ⊩¹cstr t ≡ u ∷ A ⦂ s / cstrᵣ K KcodU a D ⊢a A≡A [domK] [a] [Yi] =
      let [A] = cstrᵣ K KcodU a D ⊢a A≡A [domK] [a] [Yi]
      in ∃₂ λ k k' →
         Γ ⊢ t :⇒*: k ∷ cstr K ∘ a ⦂ s
      ×  Γ ⊢ u :⇒*: k' ∷ cstr K ∘ a ⦂ s
      ×  Γ ⊢ k ≅ k' ∷ cstr K ∘ a ⦂ s
      ×  Γ ⊩¹cstr t ∷ A ⦂ s / [A]
      ×  Γ ⊩¹cstr u ∷ A ⦂ s / [A]
      ×  [Cstr]-prop K Γ (λ ki kiK t u → Γ ⊩¹ t ≡ u ∷ wkAll Γ (cstr-dom ki) ⦂ cstr-dom-sort ki / [Yi] ki kiK) a s k k'


    -- Reducibility of boxes

    record _⊩¹Box_ (Γ : Con Term) (A : Term) : Set where
      inductive
      constructor Boxᵣ
      eta-equality
      field
        F : Term
        sF : sorts
        D : Γ ⊢ A :⇒*: Box sF F ⦂ 𝕥y
        ⊢F : Γ ⊢ F ⦂ ‼ sF
        A≡A : Γ ⊢ Box sF F ≅ Box sF F ⦂ 𝕥y
        [F] : Γ ⊩¹ F ⦂ ‼ sF

    record _⊩¹Box_≡_/_ (Γ : Con Term) (A B : Term) ([A] : Γ ⊩¹Box A) : Set where
      inductive
      constructor Box₌
      eta-equality
      open _⊩¹Box_ [A]
      field
        F' : Term
        D' : Γ ⊢ B :⇒*: Box sF F' ⦂ 𝕥y
        A≡B : Γ ⊢ Box sF F ≅ Box sF F' ⦂ 𝕥y
        [F≡F'] : Γ ⊩¹ F ≡ F' ⦂ ‼ sF / [F]


    _⊩¹Box_∷_/_ : (Γ : Con Term) (t : Term) (A : Term) ([A] : Γ ⊩¹Box A) → Set
    Γ ⊩¹Box t ∷ A / Boxᵣ F sF D ⊢F A≡A [F] =
      ∃ λ b → Γ ⊢ t :⇒*: b ∷ Box sF F ⦂ 𝕥y
            × Γ ⊢ b ≅ b ∷ Box sF F ⦂ 𝕥y
            × Box-prop (λ x → Γ ⊩¹ x ∷ F ⦂ ‼ sF / [F]) Γ F sF b

    _⊩¹Box_≡_∷_/_ : (Γ : Con Term) (t u : Term) (A : Term) ([A] : Γ ⊩¹Box A) → Set
    Γ ⊩¹Box t ≡ u ∷ A / Boxᵣ F sF D ⊢F A≡A [F] =
      let [A] = Boxᵣ F sF D ⊢F A≡A [F]
      in ∃₂ λ b b' →
         Γ ⊢ t :⇒*: b ∷ Box sF F ⦂ 𝕥y
      ×  Γ ⊢ u :⇒*: b' ∷ Box sF F ⦂ 𝕥y
      × Γ ⊢ b ≅ b' ∷ Box sF F ⦂ 𝕥y
      × Γ ⊩¹Box t ∷ A / [A]
      × Γ ⊩¹Box u ∷ A / [A]
      × [Box]-prop (λ x x' → Γ ⊩¹ x ≡ x' ∷ F ⦂ ‼ sF / [F]) Γ F sF b b'


    -- Logical relation definition

    data _⊩¹_⦂_ (Γ : Con Term) : Term → 𝕊 → Set where
      Uᵣ  : ∀ {s} → Γ ⊩¹U s → Γ ⊩¹ Univ s ⦂ 𝕥y
      ℕᵣ  : ∀ {A} → Γ ⊩ℕ A → Γ ⊩¹ A ⦂ 𝕥y
      Emptyᵣ : ∀ {A} → Γ ⊩Empty A → Γ ⊩¹ A ⦂ 𝕥y
      Boxᵣ : ∀ {A} → Γ ⊩¹Box A → Γ ⊩¹ A ⦂ 𝕥y
      ne  : ∀ {A s} → Γ ⊩ne A ⦂ s → Γ ⊩¹ A ⦂ s
      Πᵣ  : ∀ {A s} → Γ ⊩¹Π A ⦂ s → Γ ⊩¹ A ⦂ s
      cstrᵣ : ∀ {A s} → Γ ⊩¹cstr A ⦂ s → Γ ⊩¹ A ⦂ s
      emb : ∀ {A s l′} (l< : l′ < l) (let open LogRelKit (rec l<))
            ([A] : Γ ⊩ A ⦂ s) → Γ ⊩¹ A ⦂ s


    _⊩¹_≡_⦂_/_ : (Γ : Con Term) (A B : Term) (s : 𝕊) → Γ ⊩¹ A ⦂ s → Set
    Γ ⊩¹ A ≡ B ⦂ .𝕥y / Uᵣ {s = s} UA = Γ ⊩¹U[ s ]≡ B
    Γ ⊩¹ A ≡ B ⦂ .𝕥y / ℕᵣ D = Γ ⊩ℕ A ≡ B
    Γ ⊩¹ A ≡ B ⦂ .𝕥y / Emptyᵣ D = Γ ⊩Empty A ≡ B
    Γ ⊩¹ A ≡ B ⦂ .𝕥y / Boxᵣ BoxA = Γ ⊩¹Box A ≡ B / BoxA
    Γ ⊩¹ A ≡ B ⦂ s / ne neA = Γ ⊩ne A ≡ B ⦂ s / neA
    Γ ⊩¹ A ≡ B ⦂ s / Πᵣ ΠA = Γ ⊩¹Π A ≡ B ⦂ s / ΠA
    Γ ⊩¹ A ≡ B ⦂ s / cstrᵣ cstrA = Γ ⊩¹cstr A ≡ B ⦂ s / cstrA
    Γ ⊩¹ A ≡ B ⦂ s / emb l< [A] = Γ ⊩ A ≡ B ⦂ s / [A]
      where open LogRelKit (rec l<)

    _⊩¹_∷_⦂_/_ : (Γ : Con Term) (t A : Term) (s : 𝕊) → Γ ⊩¹ A ⦂ s → Set
    Γ ⊩¹ t ∷ .(Univ s') ⦂ .𝕥y / Uᵣ {s = s'} (Uᵣ l′ l< ⊢Γ) = Γ ⊩¹U t ∷U s' / l<
    Γ ⊩¹ t ∷ A ⦂ .𝕥y / ℕᵣ D = Γ ⊩ℕ t ∷ℕ
    Γ ⊩¹ t ∷ A ⦂ .𝕥y / Emptyᵣ D = Γ ⊩Empty t ∷Empty
    Γ ⊩¹ t ∷ A ⦂ .𝕥y / Boxᵣ BoxA = Γ ⊩¹Box t ∷ A / BoxA
    Γ ⊩¹ t ∷ A ⦂ s / ne neA = Γ ⊩ne t ∷ A ⦂ s / neA
    Γ ⊩¹ f ∷ A ⦂ s / Πᵣ ΠA  = Γ ⊩¹Π f ∷ A ⦂ s / ΠA
    Γ ⊩¹ t ∷ A ⦂ s / cstrᵣ cstrA  = Γ ⊩¹cstr t ∷ A ⦂ s / cstrA
    Γ ⊩¹ t ∷ A ⦂ s / emb l< [A] = Γ ⊩ t ∷ A ⦂ s / [A]
      where open LogRelKit (rec l<)

    _⊩¹_≡_∷_⦂_/_ : (Γ : Con Term) (t u A : Term) (s : 𝕊) → Γ ⊩¹ A ⦂ s → Set
    Γ ⊩¹ t ≡ u ∷ .(Univ s') ⦂ .𝕥y / Uᵣ {s = s'} (Uᵣ l′ l< ⊢Γ) = Γ ⊩¹U t ≡ u ∷U s' / l<
    Γ ⊩¹ t ≡ u ∷ A ⦂ .𝕥y / ℕᵣ D = Γ ⊩ℕ t ≡ u ∷ℕ
    Γ ⊩¹ t ≡ u ∷ A ⦂ .𝕥y / Emptyᵣ D = Γ ⊩Empty t ≡ u ∷Empty
    Γ ⊩¹ t ≡ u ∷ A ⦂ .𝕥y / Boxᵣ BoxA = Γ ⊩¹Box t ≡ u ∷ A / BoxA
    Γ ⊩¹ t ≡ u ∷ A ⦂ s / ne neA = Γ ⊩ne t ≡ u ∷ A ⦂ s / neA
    Γ ⊩¹ t ≡ u ∷ A ⦂ s / Πᵣ ΠA = Γ ⊩¹Π t ≡ u ∷ A ⦂ s / ΠA
    Γ ⊩¹ t ≡ u ∷ A ⦂ s / cstrᵣ cstrA  = Γ ⊩¹cstr t ≡ u ∷ A ⦂ s / cstrA
    Γ ⊩¹ t ≡ u ∷ A ⦂ s / emb l< [A] = Γ ⊩ t ≡ u ∷ A ⦂ s / [A]
      where open LogRelKit (rec l<)

    kit : LogRelKit
    kit = Kit _⊩¹U_ _⊩¹Π_⦂_ _⊩¹cstr_⦂_ _⊩¹Box_
              _⊩¹_⦂_ _⊩¹_≡_⦂_/_ _⊩¹_∷_⦂_/_ _⊩¹_≡_∷_⦂_/_

open LogRel public using (Uᵣ; ℕᵣ; Emptyᵣ; ne; Πᵣ; emb; Uₜ; Uₜ₌; Π₌; cstrᵣ; cstr₌ ; Boxᵣ ; Box₌)

-- Patterns for the non-records of Π
pattern Πₜ a b c d e f = a , b , c , d , e , f
pattern Πₜ₌ a b c d e f g h i j = a , b , c , d , e , f , g , h , i , j
pattern cstrₜ a b c d = a , b , c , d
pattern cstrₜ₌ a b c d e f g h = a , b , c , d , e , f , g , h
pattern boxₜ a b c d = a , b , c , d
pattern boxₜ₌ a b c d e f g h = a , b , c , d , e , f , g , h

pattern Uᵣ′ s a b c = Uᵣ {s = s} (Uᵣ a b c)
pattern ne′ a b c d = ne (ne a b c d)
pattern Πᵣ′  a b c d e f g h i j = Πᵣ (Πᵣ a b c d e f g h i j)
pattern cstrᵣ′ K KcodU a D ⊢a A≡A [domK] [a] [Yi] = cstrᵣ (cstrᵣ K KcodU a D ⊢a A≡A [domK] [a] [Yi])
pattern Boxᵣ′ F sF D ⊢F A≡A [F] = Boxᵣ (Boxᵣ F sF D ⊢F A≡A [F])

logRelRec : ∀ l {l′} → l′ < l → LogRelKit
logRelRec ⁰ = λ ()
logRelRec ¹ 0<1 = LogRel.kit ⁰ (λ ())

kit : ∀ (i : TypeLevel) → LogRelKit
kit l = LogRel.kit l (logRelRec l)
-- a bit of repetition in "kit ¹" definition, would work better with Fin 2 for
-- TypeLevel because you could recurse.

_⊩′⟨_⟩U_ : (Γ : Con Term) (l : TypeLevel) (s : 𝕊) → Set
Γ ⊩′⟨ l ⟩U s = Γ ⊩U s where open LogRelKit (kit l)

_⊩′⟨_⟩Π_⦂_ : (Γ : Con Term) (l : TypeLevel) → Term → 𝕊 → Set
Γ ⊩′⟨ l ⟩Π A ⦂ s = Γ ⊩Π A ⦂ s where open LogRelKit (kit l)

_⊩′⟨_⟩cstr_⦂_ : (Γ : Con Term) (l : TypeLevel) → Term → 𝕊 → Set
Γ ⊩′⟨ l ⟩cstr A ⦂ s = Γ ⊩cstr A ⦂ s where open LogRelKit (kit l)

_⊩′⟨_⟩Box_ : (Γ : Con Term) (l : TypeLevel) → Term → Set
Γ ⊩′⟨ l ⟩Box A = Γ ⊩Box A where open LogRelKit (kit l)

_⊩⟨_⟩_⦂_ : (Γ : Con Term) (l : TypeLevel) → Term → 𝕊 → Set
Γ ⊩⟨ l ⟩ A ⦂ s = Γ ⊩ A ⦂ s where open LogRelKit (kit l)

_⊩⟨_⟩_≡_⦂_/_ : (Γ : Con Term) (l : TypeLevel) (A B : Term) (s : 𝕊) → Γ ⊩⟨ l ⟩ A ⦂ s → Set
Γ ⊩⟨ l ⟩ A ≡ B ⦂ s / [A] = Γ ⊩ A ≡ B ⦂ s / [A] where open LogRelKit (kit l)

_⊩⟨_⟩_∷_⦂_/_ : (Γ : Con Term) (l : TypeLevel) (t A : Term) (s : 𝕊) → Γ ⊩⟨ l ⟩ A ⦂ s → Set
Γ ⊩⟨ l ⟩ t ∷ A ⦂ s / [A] = Γ ⊩ t ∷ A ⦂ s / [A] where open LogRelKit (kit l)

_⊩⟨_⟩_≡_∷_⦂_/_ : (Γ : Con Term) (l : TypeLevel) (t u A : Term) (s : 𝕊) → Γ ⊩⟨ l ⟩ A ⦂ s → Set
Γ ⊩⟨ l ⟩ t ≡ u ∷ A ⦂ s / [A] = Γ ⊩ t ≡ u ∷ A ⦂ s / [A] where open LogRelKit (kit l)
