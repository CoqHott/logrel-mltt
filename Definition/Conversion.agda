-- Algorithmic equality.

{-# OPTIONS --without-K --safe #-}

module Definition.Conversion where

open import Definition.Untyped
open import Definition.Typed

open import Tools.Nat
import Tools.PropositionalEquality as PE


infix 10 _⊢_~_↑_^_
infix 10 _⊢_~_↓_^_
infix 10 _⊢_[conv↑]_^_
infix 10 _⊢_[conv↓]_^_
infix 10 _⊢_[conv↑]_∷_^_
infix 10 _⊢_[conv↓]_∷_^_

mutual
  -- Neutral equality.
  data _⊢_~_↑!_ (Γ : Con Term) : (k l A : Term) → Set where
    var-refl    : ∀ {x y A}
                → Γ ⊢ var x ∷ A ^ !
                → x PE.≡ y
                → Γ ⊢ var x ~ var y ↑! A
    app-cong    : ∀ {k l t v F rF G}
                → Γ ⊢ k ~ l ↓! Π F ^ rF ▹ G
                → Γ ⊢ t [conv↑] v ∷ F ^ rF
                → Γ ⊢ k ∘ t ~ l ∘ v ↑! G [ t ]
    natrec-cong : ∀ {k l h g a₀ b₀ F G}
                → Γ ∙ ℕ ^ ! ⊢ F [conv↑] G ^ !
                → Γ ⊢ a₀ [conv↑] b₀ ∷ F [ zero ] ^ !
                → Γ ⊢ h [conv↑] g ∷ Π ℕ ^ ! ▹ (F ^ ! ▹▹ F [ suc (var 0) ]↑) ^ !
                → Γ ⊢ k ~ l ↓! ℕ
                → Γ ⊢ natrec F a₀ h k ~ natrec G b₀ g l ↑! F [ k ]
    Emptyrec-cong : ∀ {k l F G}
                  → Γ ⊢ F [conv↑] G ^ !
                  → Γ ⊢ k ~ l ↓% Empty
                  → Γ ⊢ Emptyrec F k ~ Emptyrec G l ↑! F

  record _⊢_~_↑%_ (Γ : Con Term) (k l A : Term) : Set where
    inductive
    constructor %~↑
    field
      neK : Neutral k
      neL : Neutral l
      ⊢k : Γ ⊢ k ∷ A ^ %
      ⊢l : Γ ⊢ l ∷ A ^ %

  data _⊢_~_↑_^_ (Γ : Con Term) : (k l A : Term) → Relevance → Set where
    ~↑! : ∀ {k l A} → Γ ⊢ k ~ l ↑! A → Γ ⊢ k ~ l ↑ A ^ !
    ~↑% : ∀ {k l A} → Γ ⊢ k ~ l ↑% A → Γ ⊢ k ~ l ↑ A ^ %

  -- Neutral equality with types in WHNF.
  record _⊢_~_↓!_ (Γ : Con Term) (k l B : Term) : Set where
    inductive
    constructor [~]
    field
      A     : Term
      D     : Γ ⊢ A ⇒* B ^ !
      whnfB : Whnf B
      k~l   : Γ ⊢ k ~ l ↑! A

  -- Neutral equality with types in WHNF.
  record _⊢_~_↓%_ (Γ : Con Term) (k l B : Term) : Set where
    inductive
    constructor [~]
    field
      A     : Term
      D     : Γ ⊢ A ⇒* B ^ %
      whnfB : Whnf B
      k~l : Γ ⊢ k ~ l ↑% A

  data _⊢_~_↓_^_  (Γ : Con Term) (k l B : Term) : Relevance → Set where
    ~↓! : Γ ⊢ k ~ l ↓! B → Γ ⊢ k ~ l ↓ B ^ !
    ~↓% : Γ ⊢ k ~ l ↓% B → Γ ⊢ k ~ l ↓ B ^ %

  -- Type equality.
  record _⊢_[conv↑]_^_ (Γ : Con Term) (A B : Term) (rA : Relevance) : Set where
    inductive
    constructor [↑]
    field
      A′ B′  : Term
      D      : Γ ⊢ A ⇒* A′ ^ rA
      D′     : Γ ⊢ B ⇒* B′ ^ rA
      whnfA′ : Whnf A′
      whnfB′ : Whnf B′
      A′<>B′ : Γ ⊢ A′ [conv↓] B′ ^ rA

  -- Type equality with types in WHNF.
  data _⊢_[conv↓]_^_ (Γ : Con Term) : (A B : Term) → Relevance → Set where
    U-refl    : ∀ {r r'} → r PE.≡ r' -- needed for K issues
              → ⊢ Γ → Γ ⊢ Univ r [conv↓] Univ r' ^ !
    ℕ-refl    : ⊢ Γ → Γ ⊢ ℕ [conv↓] ℕ ^ !
    Empty-refl : ⊢ Γ → Γ ⊢ Empty [conv↓] Empty ^ %
    ne        : ∀ {r K L}
              → Γ ⊢ K ~ L ↓! Univ r
              → Γ ⊢ K [conv↓] L ^ r
    Π-cong    : ∀ {F G H E rF rH rG}
              → rF PE.≡ rH -- needed for K issues
              → Γ ⊢ F ^ rF
              → Γ ⊢ F [conv↑] H ^ rF
              → Γ ∙ F ^ rF ⊢ G [conv↑] E ^ rG
              → Γ ⊢ Π F ^ rF ▹ G [conv↓] Π H ^ rH ▹ E ^ rG

  -- Term equality.
  record _⊢_[conv↑]_∷_^_ (Γ : Con Term) (t u A : Term) (rA : Relevance) : Set where
    inductive
    constructor [↑]ₜ
    field
      B t′ u′ : Term
      D       : Γ ⊢ A ⇒* B ^ rA
      d       : Γ ⊢ t ⇒* t′ ∷ B ^ rA
      d′      : Γ ⊢ u ⇒* u′ ∷ B ^ rA
      whnfB   : Whnf B
      whnft′  : Whnf t′
      whnfu′  : Whnf u′
      t<>u    : Γ ⊢ t′ [conv↓] u′ ∷ B ^ rA

  -- Term equality with types and terms in WHNF.
  data _⊢_[conv↓]_∷_^_ (Γ : Con Term) : (t u A : Term) → Relevance → Set where
    ℕ-ins     : ∀ {k l}
              → Γ ⊢ k ~ l ↓! ℕ
              → Γ ⊢ k [conv↓] l ∷ ℕ ^ !
    Empty-ins : ∀ {k l}
              → Γ ⊢ k ~ l ↓% Empty
              → Γ ⊢ k [conv↓] l ∷ Empty ^ %
    ne-ins    : ∀ {k l M N r} -- should we have 2 relevances here?
              → Γ ⊢ k ∷ N ^ r
              → Γ ⊢ l ∷ N ^ r
              → Neutral N
              → Γ ⊢ k ~ l ↓ M ^ r
              → Γ ⊢ k [conv↓] l ∷ N ^ r
    univ      : ∀ {A B r}
              → Γ ⊢ A ∷ Univ r ^ !
              → Γ ⊢ B ∷ Univ r ^ !
              → Γ ⊢ A [conv↓] B ^ r
              → Γ ⊢ A [conv↓] B ∷ Univ r ^ !
    zero-refl : ⊢ Γ → Γ ⊢ zero [conv↓] zero ∷ ℕ ^ !
    suc-cong  : ∀ {m n}
              → Γ ⊢ m [conv↑] n ∷ ℕ ^ !
              → Γ ⊢ suc m [conv↓] suc n ∷ ℕ ^ !
    η-eq      : ∀ {f g F G rF rG}
              → Γ ⊢ F ^ rF
              → Γ ⊢ f ∷ Π F ^ rF ▹ G ^ rG
              → Γ ⊢ g ∷ Π F ^ rF ▹ G ^ rG
              → Function f
              → Function g
              → Γ ∙ F ^ rF ⊢ wk1 f ∘ var 0 [conv↑] wk1 g ∘ var 0 ∷ G ^ rG
              → Γ ⊢ f [conv↓] g ∷ Π F ^ rF ▹ G ^ rG

var-refl′ : ∀ {Γ x A rA}
          → Γ ⊢ var x ∷ A ^ rA
          → Γ ⊢ var x ~ var x ↑ A ^ rA
var-refl′ {rA = !} ⊢x = ~↑! (var-refl ⊢x PE.refl)
var-refl′ {rA = %} ⊢x = ~↑% (%~↑ (var _) (var _) ⊢x ⊢x)

[~]′ : ∀ {Γ k l B r} (A : Term) (D : Γ ⊢ A ⇒* B ^ r)
     → Whnf B → Γ ⊢ k ~ l ↑ A ^ r
     → Γ ⊢ k ~ l ↓ B ^ r
[~]′ A D whnfB (~↑! x) = ~↓! ([~] A D whnfB x)
[~]′ A D whnfB (~↑% x) = ~↓% ([~] A D whnfB x)
