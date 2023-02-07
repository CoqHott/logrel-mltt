-- Algorithmic equality.

{-# OPTIONS --safe #-}

module Definition.ConversionGen where

open import Definition.Untyped
open import Definition.Typed

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

infix 10 _⊢⊢_~_↑_^_
infix 10 _⊢⊢_[conv↑]_^_
infix 10 _⊢⊢_[conv↓]_^_
infix 10 _⊢⊢_[conv↑]_∷_^_
infix 10 _⊢⊢_[conv↓]_∷_^_
infix 10 _⊢⊢_[genconv↑]_∷_^_

mutual
  -- Neutral equality.
  data _⊢⊢_~_↑!_^_ (Γ : Con Term) : (k l A : Term) → TypeLevel → Set where
    var-refl    : ∀ {x y A l}
                → Γ ⊢ var x ∷ A ^ [ ! , l ]
                → x PE.≡ y
                → Γ ⊢⊢ var x ~ var y ↑! A ^ l
    app-cong    : ∀ {k l t v F rF lF lG G lΠ}
                → Γ ⊢⊢ k ~ l ↓! Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ ! ^ ι lΠ
                → Γ ⊢⊢ t [genconv↑] v ∷ F ^ [ rF , ι lF ]
                → Γ ⊢⊢ k ∘ t ^ lΠ ~ l ∘ v ^ lΠ ↑! G [ t ] ^ ι lG
    natrec-cong : ∀ {k l h g a₀ b₀ F G lF}
                → Γ ∙ ℕ ^ [ ! , ι ⁰ ] ⊢⊢ F [conv↑] G ^ [ ! , ι lF ]
                → Γ ⊢⊢ a₀ [conv↑] b₀ ∷ F [ zero ] ^ ι lF
                → Γ ⊢⊢ h [conv↑] g ∷ Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° lF ▹▹ F [ suc (var 0) ]↑ ° lF ° lF ^ !) ° lF ° lF ^ ! ^ ι lF
                → Γ ⊢⊢ k ~ l ↓! ℕ ^ ι ⁰
                → Γ ⊢⊢ natrec lF F a₀ h k ~ natrec lF G b₀ g l ↑! F [ k ] ^ ι lF
    Emptyrec-cong : ∀ {k l F G ll}
                  → Γ ⊢⊢ F [conv↑] G ^ [ ! , ι ll ]
                  → Γ ⊢⊢ k ~ l ↑% sEmpty ^ ι ⁰
                  → Γ ⊢⊢ Emptyrec ll ⁰ F k ~ Emptyrec ll ⁰ G l ↑! F ^ ι ll
    cast-cong : ∀ {A A' B B' t t' e e'}
              → Γ ⊢⊢ A [conv↓] A' ∷ U ⁰ ^ next ⁰
              → Γ ⊢⊢ B' [conv↓] B ∷ U ⁰ ^ ι ¹
              → Γ ⊢⊢ t [conv↑] t' ∷ A ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ]
              → Γ ⊢ e' ∷ (Id (U ⁰) A' B') ^ [ % , ι ⁰ ]
              → Neutral (cast ⁰ A B e t)
              → Neutral (cast ⁰ A' B' e' t')             
              → Γ ⊢⊢ cast ⁰ A B e t ~ cast ⁰ A' B' e' t' ↑! B ^ ι ⁰
    cast-refl : ∀ {A B t u e}
              → Γ ⊢⊢ A [conv↓] B ∷ U ⁰ ^ next ⁰
              → Γ ⊢⊢ t [conv↓] u ∷ A ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ]
              → Neutral (cast ⁰ A B e t)
              → Neutral u
              → Γ ⊢⊢ cast ⁰ A B e t ~ u ↑! B ^ ι ⁰
    cast-refl' : ∀ {A B t u e}
              → Γ ⊢⊢ B [conv↓] A ∷ U ⁰ ^ next ⁰
              → Γ ⊢⊢ t [conv↓] u ∷ A ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ]
              → Neutral (cast ⁰ A B e u)
              → Neutral t
              → Γ ⊢⊢ t ~ cast ⁰ A B e u ↑! A ^ ι ⁰

  record _⊢⊢_~_↑%_^_ (Γ : Con Term) (k l A : Term) (ll : TypeLevel) : Set where
    inductive
    constructor %~↑
    field
      ⊢⊢k : Γ ⊢ k ∷ A ^ [ % , ll ]
      ⊢⊢l : Γ ⊢ l ∷ A ^ [ % , ll ]

  data _⊢⊢_~_↑_^_ (Γ : Con Term) : (k l A : Term) → TypeInfo → Set where
    ~↑! : ∀ {k l A ll} → Γ ⊢⊢ k ~ l ↑! A ^ ll → Γ ⊢⊢ k ~ l ↑ A ^ [ ! , ll ]
    ~↑% : ∀ {k l A ll} → Γ ⊢⊢ k ~ l ↑% A ^ ll → Γ ⊢⊢ k ~ l ↑ A ^ [ % , ll ]

  -- Neutral equality with types in WHNF.
  record _⊢⊢_~_↓!_^_ (Γ : Con Term) (k l B : Term) (ll : TypeLevel) : Set where
    inductive
    constructor [~]
    field
      A     : Term
      D     : Γ ⊢ A ⇒* B ^ [ ! , ll ]
      whnfB : Whnf B
      k~l   : Γ ⊢⊢ k ~ l ↑! A ^ ll

  -- Type equality.
  record _⊢⊢_[conv↑]_^_ (Γ : Con Term) (A B : Term) (rA : TypeInfo) : Set where
    inductive
    constructor [↑]
    field
      A′ B′  : Term
      D      : Γ ⊢ A ⇒* A′ ^ rA
      D′     : Γ ⊢ B ⇒* B′ ^ rA
      whnfA′ : Whnf A′
      whnfB′ : Whnf B′
      A′<>B′ : Γ ⊢⊢ A′ [conv↓] B′ ^ rA

  -- Type equality with types in WHNF.
  data _⊢⊢_[conv↓]_^_ (Γ : Con Term) : (A B : Term) → TypeInfo → Set where
    U-refl    : ∀ {r r' }
              → r PE.≡ r' -- needed for K issues
              → ⊢ Γ → Γ ⊢⊢ Univ r ¹ [conv↓] Univ r' ¹ ^ [ ! , next ¹ ]
    univ      : ∀ {A B r l}
              → Γ ⊢⊢ A [conv↓] B ∷ Univ r l ^ next l
              → Γ ⊢⊢ A [conv↓] B ^ [ r , ι l ]

  -- Term equality.
  record _⊢⊢_[conv↑]_∷_^_ (Γ : Con Term) (t u A : Term) (l : TypeLevel) : Set where
    inductive
    constructor [↑]ₜ
    field
      B t′ u′ : Term
      D       : Γ ⊢ A ⇒* B ^ [ ! , l ]
      d       : Γ ⊢ t ⇒* t′ ∷ B ^ l
      d′      : Γ ⊢ u ⇒* u′ ∷ B ^ l
      whnfB   : Whnf B
      whnft′  : Whnf t′
      whnfu′  : Whnf u′
      t<>u    : Γ ⊢⊢ t′ [conv↓] u′ ∷ B ^ l

  -- Term equality with types and terms in WHNF.
  data _⊢⊢_[conv↓]_∷_^_ (Γ : Con Term) : (t u A : Term) (l : TypeLevel) → Set where
    U-refl    : ∀ {r r' }
              → r PE.≡ r' -- needed for K issues
              → ⊢ Γ → Γ ⊢⊢ Univ r ⁰ [conv↓] Univ r' ⁰ ∷ U ¹ ^ next ¹
    ℕ-refl    : ⊢ Γ → Γ ⊢⊢ ℕ [conv↓] ℕ ∷ U ⁰ ^ next ⁰
    Empty-refl : ⊢ Γ → Γ ⊢⊢ sEmpty [conv↓] sEmpty ∷ SProp ^ next ⁰
    Π-cong    : ∀ {F G H E rF rH rΠ lF lH lG lE lΠ ll}
              → ll PE.≡ next lΠ
              → rF PE.≡ rH -- needed for K issues
              → lF PE.≡ lH -- needed for K issues
              → lG PE.≡ lE -- needed for K issues
              → (rΠ PE.≡ ! → lF ≤ lΠ × lG ≤ lΠ)
              → (rΠ PE.≡ % → lG PE.≡ ⁰ × lΠ PE.≡ ⁰)
              → Γ ⊢⊢ F [conv↑] H ∷ Univ rF lF ^ next lF
              → Γ ∙ F ^ [ rF , ι lF ] ⊢⊢ G [conv↑] E  ∷ Univ rΠ lG ^ next lG
              → Γ ⊢⊢ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ rΠ [conv↓] Π H ^ rH ° lH ▹ E ° lE ° lΠ ^ rΠ ∷ Univ rΠ lΠ ^ ll
    Id-cong : ∀ {l A A' t t' u u'}
              → Γ ⊢⊢ A [conv↑] A' ∷ U l ^ next l
              → Γ ⊢⊢ t [conv↑] t' ∷ A ^ ι l
              → Γ ⊢⊢ u [conv↑] u' ∷ A ^ ι l
              → Γ ⊢⊢ Id A t u [conv↓] Id A' t' u' ∷ SProp ^ next ⁰
    ne        : ∀ {r K L lU l}
                → Γ ⊢⊢ K ~ L ↓! Univ r lU ^ l
                → Γ ⊢⊢ K [conv↓] L ∷ Univ r lU ^ l
    ℕ-ins     : ∀ {k l}
              → Γ ⊢⊢ k ~ l ↓! ℕ ^ ι ⁰
              → Γ ⊢⊢ k [conv↓] l ∷ ℕ ^ ι ⁰
    ne-ins    : ∀ {k l M N ll}
              → Γ ⊢ k ∷ N ^ [ ! , ι ll ]
              → Γ ⊢ l ∷ N ^ [ ! , ι ll ]
              → Neutral N
              → Γ ⊢⊢ k ~ l ↓! M ^ ι ll
              → Γ ⊢⊢ k [conv↓] l ∷ N ^ ι ll
    zero-refl : ⊢ Γ → Γ ⊢⊢ zero [conv↓] zero ∷ ℕ ^ ι ⁰
    suc-cong  : ∀ {m n}
              → Γ ⊢⊢ m [conv↑] n ∷ ℕ ^ ι ⁰
              → Γ ⊢⊢ suc m [conv↓] suc n ∷ ℕ ^ ι ⁰
    η-eq      : ∀ {f g F G rF lF lG l}
              → lF ≤ l
              → lG ≤ l
              → Γ ⊢ F ^ [ rF , ι lF ]
              → Γ ⊢ f ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ [ ! , ι l ]
              → Γ ⊢ g ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ [ ! , ι l ]
              → Function f
              → Function g
              → Γ ∙ F ^ [ rF , ι lF ] ⊢⊢ wk1 f ∘ var 0 ^ l [conv↑] wk1 g ∘ var 0 ^ l ∷ G ^ ι lG
                → Γ ⊢⊢ f [conv↓] g ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ ι l

  _⊢⊢_[genconv↑]_∷_^_ : (Γ : Con Term) (t u A : Term) (r : TypeInfo) → Set
  _⊢⊢_[genconv↑]_∷_^_ Γ k l A [ ! , ll ] =  Γ ⊢⊢ k [conv↑] l ∷ A ^ ll
  _⊢⊢_[genconv↑]_∷_^_ Γ k l A [ % , ll ] =  Γ ⊢⊢ k ~ l ↑% A ^  ll
