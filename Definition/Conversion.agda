-- Algorithmic equality.

{-# OPTIONS --without-K  #-}

module Definition.Conversion where

open import Definition.Untyped
open import Definition.Typed

open import Tools.Nat
import Tools.PropositionalEquality as PE


infix 10 _⊢_~_↑_⦂_
infix 10 _⊢_~_↓_⦂_
infix 10 _⊢_[conv↑]_⦂_
infix 10 _⊢_[conv↓]_⦂_
infix 10 _⊢_[conv↑]_∷_⦂_
infix 10 _⊢_[conv↓]_∷_⦂_

mutual
  -- Neutral equality.
  data _⊢_~_↑𝕥y_ (Γ : Con Term) : (k l A : Term) → Set where
    var-refl    : ∀ {x y A}
                → Γ ⊢ var x ∷ A ⦂ 𝕥y
                → x PE.≡ y
                → Γ ⊢ var x ~ var y ↑𝕥y A
    app-cong    : ∀ {k l t v F sF G}
                → Γ ⊢ k ~ l ↓𝕥y Π F ⦂ sF ▹ G
                → Γ ⊢ t [conv↑] v ∷ F ⦂ sF
                → Γ ⊢ k ∘ t ~ l ∘ v ↑𝕥y G [ t ]
    natrec-cong : ∀ {k l h g a₀ b₀ F G}
                → Γ ∙ ℕ ⦂ 𝕥y ⊢ F [conv↑] G ⦂ 𝕥y
                → Γ ⊢ a₀ [conv↑] b₀ ∷ F [ zero ] ⦂ 𝕥y
                → Γ ⊢ h [conv↑] g ∷ Π ℕ ⦂ 𝕥y ▹ (F ⦂ 𝕥y ▹▹ F [ suc (var 0) ]↑) ⦂ 𝕥y
                → Γ ⊢ k ~ l ↓𝕥y ℕ
                → Γ ⊢ natrec F a₀ h k ~ natrec G b₀ g l ↑𝕥y F [ k ]
    Emptyrec-cong : ∀ {k l F G}
                  → Γ ⊢ F [conv↑] G ⦂ 𝕥y
                  → Γ ⊢ k ~ l ↓𝕥y Empty
                  → Γ ⊢ Emptyrec F k ~ Emptyrec G l ↑𝕥y F

  record _⊢_~_↑𝕥y_ (Γ : Con Term) (k l A : Term) : Set where
    inductive
    constructor 𝕥y~↑
    field
      neK : Neutral k
      neL : Neutral l
      ⊢k : Γ ⊢ k ∷ A ⦂ 𝕥y
      ⊢l : Γ ⊢ l ∷ A ⦂ 𝕥y

  data _⊢_~_↑_⦂_ (Γ : Con Term) : (k l A : Term) → 𝕊 → Set where
    ~↑𝕥y : ∀ {k l A} → Γ ⊢ k ~ l ↑𝕥y A → Γ ⊢ k ~ l ↑ A ⦂ 𝕥y
    ~↑𝕥y : ∀ {k l A} → Γ ⊢ k ~ l ↑𝕥y A → Γ ⊢ k ~ l ↑ A ⦂ 𝕥y

  -- Neutral equality with types in WHNF.
  record _⊢_~_↓𝕥y_ (Γ : Con Term) (k l B : Term) : Set where
    inductive
    constructor [~]
    field
      A     : Term
      D     : Γ ⊢ A ⇒* B ⦂ 𝕥y
      whnfB : Whnf B
      k~l   : Γ ⊢ k ~ l ↑𝕥y A

  -- Neutral equality with types in WHNF.
  record _⊢_~_↓𝕥y_ (Γ : Con Term) (k l B : Term) : Set where
    inductive
    constructor [~]
    field
      A     : Term
      D     : Γ ⊢ A ⇒* B ⦂ 𝕥y
      whnfB : Whnf B
      k~l : Γ ⊢ k ~ l ↑𝕥y A

  data _⊢_~_↓_⦂_  (Γ : Con Term) (k l B : Term) : 𝕊 → Set where
    ~↓𝕥y : Γ ⊢ k ~ l ↓𝕥y B → Γ ⊢ k ~ l ↓ B ⦂ 𝕥y
    ~↓𝕥y : Γ ⊢ k ~ l ↓𝕥y B → Γ ⊢ k ~ l ↓ B ⦂ 𝕥y

  -- Type equality.
  record _⊢_[conv↑]_⦂_ (Γ : Con Term) (A B : Term) (sA : 𝕊) : Set where
    inductive
    constructor [↑]
    field
      A′ B′  : Term
      D      : Γ ⊢ A ⇒* A′ ⦂ sA
      D′     : Γ ⊢ B ⇒* B′ ⦂ sA
      whnfA′ : Whnf A′
      whnfB′ : Whnf B′
      A′<>B′ : Γ ⊢ A′ [conv↓] B′ ⦂ sA

  -- Type equality with types in WHNF.
  data _⊢_[conv↓]_⦂_ (Γ : Con Term) : (A B : Term) → 𝕊 → Set where
    U-refl    : ∀ {s s'} → s PE.≡ s' -- needed for K issues
              → ⊢ Γ → Γ ⊢ Univ s [conv↓] Univ s' ⦂ 𝕥y
    ℕ-refl    : ⊢ Γ → Γ ⊢ ℕ [conv↓] ℕ ⦂ 𝕥y
    Empty-refl : ⊢ Γ → Γ ⊢ Empty [conv↓] Empty ⦂ 𝕥y
    ne        : ∀ {s K L}
              → Γ ⊢ K ~ L ↓𝕥y Univ s
              → Γ ⊢ K [conv↓] L ⦂ s
    Π-cong    : ∀ {F G H E sF sH sG}
              → sF PE.≡ sH -- needed for K issues
              → Γ ⊢ F ⦂ sF
              → Γ ⊢ F [conv↑] H ⦂ sF
              → Γ ∙ F ⦂ sF ⊢ G [conv↑] E ⦂ sG
              → Γ ⊢ Π F ⦂ sF ▹ G [conv↓] Π H ⦂ sH ▹ E ⦂ sG

  -- Term equality.
  record _⊢_[conv↑]_∷_⦂_ (Γ : Con Term) (t u A : Term) (sA : 𝕊) : Set where
    inductive
    constructor [↑]ₜ
    field
      B t′ u′ : Term
      D       : Γ ⊢ A ⇒* B ⦂ sA
      d       : Γ ⊢ t ⇒* t′ ∷ B ⦂ sA
      d′      : Γ ⊢ u ⇒* u′ ∷ B ⦂ sA
      whnfB   : Whnf B
      whnft′  : Whnf t′
      whnfu′  : Whnf u′
      t<>u    : Γ ⊢ t′ [conv↓] u′ ∷ B ⦂ sA

  -- Term equality with types and terms in WHNF.
  data _⊢_[conv↓]_∷_⦂_ (Γ : Con Term) : (t u A : Term) → 𝕊 → Set where
    ℕ-ins     : ∀ {k l}
              → Γ ⊢ k ~ l ↓𝕥y ℕ
              → Γ ⊢ k [conv↓] l ∷ ℕ ⦂ 𝕥y
    Empty-ins : ∀ {k l}
              → Γ ⊢ k ~ l ↓𝕥y Empty
              → Γ ⊢ k [conv↓] l ∷ Empty ⦂ 𝕥y
    ne-ins    : ∀ {k l M N s} -- should we have 2 relevances here?
              → Γ ⊢ k ∷ N ⦂ s
              → Γ ⊢ l ∷ N ⦂ s
              → Neutral N
              → Γ ⊢ k ~ l ↓ M ⦂ s
              → Γ ⊢ k [conv↓] l ∷ N ⦂ s
    univ      : ∀ {A B s}
              → Γ ⊢ A ∷ Univ s ⦂ 𝕥y
              → Γ ⊢ B ∷ Univ s ⦂ 𝕥y
              → Γ ⊢ A [conv↓] B ⦂ s
              → Γ ⊢ A [conv↓] B ∷ Univ s ⦂ 𝕥y
    zero-refl : ⊢ Γ → Γ ⊢ zero [conv↓] zero ∷ ℕ ⦂ 𝕥y
    suc-cong  : ∀ {m n}
              → Γ ⊢ m [conv↑] n ∷ ℕ ⦂ 𝕥y
              → Γ ⊢ suc m [conv↓] suc n ∷ ℕ ⦂ 𝕥y
    η-eq      : ∀ {f g F G sF sG}
              → Γ ⊢ F ⦂ sF
              → Γ ⊢ f ∷ Π F ⦂ sF ▹ G ⦂ sG
              → Γ ⊢ g ∷ Π F ⦂ sF ▹ G ⦂ sG
              → Function f
              → Function g
              → Γ ∙ F ⦂ sF ⊢ wk1 f ∘ var 0 [conv↑] wk1 g ∘ var 0 ∷ G ⦂ sG
              → Γ ⊢ f [conv↓] g ∷ Π F ⦂ sF ▹ G ⦂ sG

var-refl′ : ∀ {Γ x A sA}
          → Γ ⊢ var x ∷ A ⦂ sA
          → Γ ⊢ var x ~ var x ↑ A ⦂ sA
var-refl′ {sA = 𝕥y} ⊢x = ~↑𝕥y (var-refl ⊢x PE.refl)
var-refl′ {sA = 𝕥y} ⊢x = ~↑𝕥y (𝕥y~↑ (var _) (var _) ⊢x ⊢x)

[~]′ : ∀ {Γ k l B s} (A : Term) (D : Γ ⊢ A ⇒* B ⦂ s)
     → Whnf B → Γ ⊢ k ~ l ↑ A ⦂ s
     → Γ ⊢ k ~ l ↓ B ⦂ s
[~]′ A D whnfB (~↑𝕥y x) = ~↓𝕥y ([~] A D whnfB x)
[~]′ A D whnfB (~↑𝕥y x) = ~↓𝕥y ([~] A D whnfB x)
