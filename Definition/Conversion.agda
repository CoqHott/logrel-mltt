-- Algorithmic equality.

{-# OPTIONS --safe #-}

module Definition.Conversion where

open import Definition.Untyped
open import Definition.Typed

open import Tools.Nat
import Tools.PropositionalEquality as PE


infix 10 _⊢_~_↑_^_
infix 10 _⊢_[conv↑]_^_
infix 10 _⊢_[conv↓]_^_
infix 10 _⊢_[conv↑]_∷_^_
infix 10 _⊢_[conv↓]_∷_^_
infix 10 _⊢_[genconv↑]_∷_^_

mutual
  -- Neutral equality.
  data _⊢_~_↑!_^_ (Γ : Con Term) : (k l A : Term) → TypeLevel → Set where
    var-refl    : ∀ {x y A l}
                → Γ ⊢ var x ∷ A ^ [ ! , l ]
                → x PE.≡ y
                → Γ ⊢ var x ~ var y ↑! A ^ l 
    app-cong    : ∀ {k l t v F rF lF lG G lΠ}
                → Γ ⊢ k ~ l ↓! Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ ι lΠ
                → Γ ⊢ t [genconv↑] v ∷ F ^ [ rF , ι lF ] 
                → Γ ⊢ k ∘ t ^ lΠ ~ l ∘ v ^ lΠ ↑! G [ t ] ^ ι lG 
    natrec-cong : ∀ {k l h g a₀ b₀ F G lF}
                → Γ ∙ ℕ ^ [ ! , ι ⁰ ] ⊢ F [conv↑] G ^ [ ! , ι lF ]
                → Γ ⊢ a₀ [conv↑] b₀ ∷ F [ zero ] ^ ι lF
                → Γ ⊢ h [conv↑] g ∷ Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° lF ▹▹ F [ suc (var 0) ]↑ ° lF ° lF) ° lF ° lF ^ ι lF
                → Γ ⊢ k ~ l ↓! ℕ ^ ι ⁰
                → Γ ⊢ natrec lF F a₀ h k ~ natrec lF G b₀ g l ↑! F [ k ] ^ ι lF
    Emptyrec-cong : ∀ {k l F G ll lEmpty}
                  → Γ ⊢ F [conv↑] G ^ [ ! , ι ll ]
                  → Γ ⊢ k ~ l ↑% Empty lEmpty ^ ι lEmpty
                  → Γ ⊢ Emptyrec ll lEmpty F k ~ Emptyrec ll lEmpty G l ↑! F ^ ι ll
    Id-cong : ∀ {l A A' t t' u u'}
              → Γ ⊢ A ~ A' ↓! U l ^ next l
              → Γ ⊢ t [conv↑] t' ∷ A ^ ι l
              → Γ ⊢ u [conv↑] u' ∷ A ^ ι l
              → Γ ⊢ Id A t u ~ Id A' t' u' ↑! SProp l ^ next l
    Id-ℕ : ∀ {t t' u u'}
              → Γ ⊢ t ~ t' ↓! ℕ ^ ι ⁰
              → Γ ⊢ u [conv↑] u' ∷ ℕ ^ ι ⁰
              → Γ ⊢ Id ℕ t u ~ Id ℕ t' u' ↑! SProp ⁰ ^ next ⁰
    Id-ℕ0 : ∀ {t t'}
              → Γ ⊢ t ~ t' ↓! ℕ ^ ι ⁰ 
              → Γ ⊢ Id ℕ zero t ~ Id ℕ zero t' ↑! SProp ⁰ ^ next ⁰
    Id-ℕS : ∀ {t t' u u'}
              → Γ ⊢ t [conv↑] t' ∷ ℕ ^ ι ⁰
              → Γ ⊢ u ~ u' ↓! ℕ ^ ι ⁰ 
              → Γ ⊢ Id ℕ (suc t) u ~ Id ℕ (suc t') u' ↑! SProp ⁰ ^ next ⁰
    Id-U : ∀ {t t' u u'}
              → Γ ⊢ t ~ t' ↓! U ⁰ ^ ι ¹
              → Γ ⊢ u [conv↑] u' ∷ U ⁰ ^ ι ¹
              → Γ ⊢ Id (U ⁰) t u ~ Id (U ⁰) t' u' ↑! SProp ¹ ^ next ¹
    Id-Uℕ : ∀ {t t'}
              → Γ ⊢ t ~ t' ↓! U ⁰ ^ ι ¹
              → Γ ⊢ Id (U ⁰) ℕ t ~ Id (U ⁰) ℕ t' ↑! SProp ¹ ^ next ¹
    Id-UΠ : ∀ {A rA B A' B' t t'}
              → Γ ⊢ Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰  [conv↑] Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ° ⁰  ∷ U ⁰ ^ ι ¹
              → Γ ⊢ t ~ t' ↓! U ⁰ ^ ι ¹
              → Γ ⊢ Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰  ) t ~ Id (U ⁰) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ° ⁰  ) t' ↑! SProp ¹ ^ next ¹
    cast-cong : ∀ {A A' B B' t t' e e'}
              → Γ ⊢ A ~ A' ↓! U ⁰ ^ next ⁰
              → Γ ⊢ B [conv↑] B' ∷ U ⁰ ^ ι ¹
              → Γ ⊢ t [conv↑] t' ∷ A ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , next ⁰ ]
              → Γ ⊢ e' ∷ (Id (U ⁰) A' B') ^ [ % , next ⁰ ]
              → Γ ⊢ cast ⁰ A B e t ~ cast ⁰ A' B' e' t' ↑! B ^ ι ⁰
    cast-ℕ : ∀ {A A' t t' e e'}
              → Γ ⊢ A ~ A' ↓! U ⁰ ^ next ⁰
              → Γ ⊢ t [conv↑] t' ∷ ℕ ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) ℕ A) ^ [ % , next ⁰ ]
              → Γ ⊢ e' ∷ (Id (U ⁰) ℕ A') ^ [ % , next ⁰ ]
              → Γ ⊢ cast ⁰ ℕ A e t ~ cast ⁰ ℕ A' e' t' ↑! A ^ ι ⁰
    cast-ℕℕ : ∀ {t t' e e'}
              → Γ ⊢ t ~ t' ↓! ℕ ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) ℕ ℕ) ^ [ % , next ⁰ ]
              → Γ ⊢ e' ∷ (Id (U ⁰) ℕ ℕ) ^ [ % , next ⁰ ]
              → Γ ⊢ cast ⁰ ℕ ℕ e t ~ cast ⁰ ℕ ℕ e' t' ↑! ℕ ^ ι ⁰
    cast-Π : ∀ {A rA P A' P' B B' t t' e e'}
              → Γ ⊢ Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰  [conv↑] Π A' ^ rA ° ⁰ ▹ P' ° ⁰ ° ⁰  ∷ U ⁰ ^ next ⁰
              → Γ ⊢ B ~ B' ↓! U ⁰ ^ next ⁰
              → Γ ⊢ t [conv↑] t' ∷ Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰  ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) (Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰ ) B) ^ [ % , next ⁰ ]
              → Γ ⊢ e' ∷ (Id (U ⁰) (Π A' ^ rA ° ⁰ ▹ P' ° ⁰ ° ⁰ ) B') ^ [ % , next ⁰ ]
              → Γ ⊢ cast ⁰ (Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰ ) B e t ~ cast ⁰ (Π A' ^ rA ° ⁰ ▹ P' ° ⁰ ° ⁰ ) B' e' t' ↑! B ^ ι ⁰
    cast-Πℕ : ∀ {A rA P A' P' t t' e e'}
              → Γ ⊢ Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰  [conv↑] Π A' ^ rA ° ⁰ ▹ P' ° ⁰ ° ⁰  ∷ U ⁰ ^ ι ¹
              → Γ ⊢ t [conv↑] t' ∷ Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰  ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) (Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰ ) ℕ) ^ [ % , next ⁰ ]
              → Γ ⊢ e' ∷ (Id (U ⁰) (Π A' ^ rA ° ⁰ ▹ P' ° ⁰ ° ⁰ ) ℕ) ^ [ % , next ⁰ ]
              → Γ ⊢ cast ⁰ (Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰ ) ℕ e t ~ cast ⁰ (Π A' ^ rA ° ⁰ ▹ P' ° ⁰ ° ⁰ ) ℕ e' t' ↑! ℕ ^ ι ⁰
    cast-ℕΠ : ∀ {A rA P A' P' t t' e e'}
              → Γ ⊢ Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰  [conv↑] Π A' ^ rA ° ⁰ ▹ P' ° ⁰ ° ⁰  ∷ U ⁰ ^ ι ¹
              → Γ ⊢ t [conv↑] t' ∷ ℕ ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) ℕ (Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰ )) ^ [ % , next ⁰ ]
              → Γ ⊢ e' ∷ (Id (U ⁰) ℕ (Π A' ^ rA ° ⁰ ▹ P' ° ⁰ ° ⁰ )) ^ [ % , next ⁰ ]
              → Γ ⊢ cast ⁰ ℕ (Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰ ) e t ~ cast ⁰ ℕ (Π A' ^ rA ° ⁰ ▹ P' ° ⁰ ° ⁰ ) e' t' ↑! (Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰ ) ^ ι ⁰
    cast-ΠΠ%! : ∀ {A P A' P' B Q B' Q' t t' e e'}
              → Γ ⊢ Π A ^ % ° ⁰ ▹ P ° ⁰ ° ⁰  [conv↑] Π A' ^ % ° ⁰ ▹ P' ° ⁰ ° ⁰  ∷ U ⁰ ^ ι ¹
              → Γ ⊢ Π B ^ ! ° ⁰ ▹ Q ° ⁰ ° ⁰  [conv↑] Π B' ^ ! ° ⁰ ▹ Q' ° ⁰ ° ⁰  ∷ U ⁰ ^ ι ¹
              → Γ ⊢ t [conv↑] t' ∷ Π A ^ % ° ⁰ ▹ P ° ⁰ ° ⁰  ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) (Π A ^ % ° ⁰ ▹ P ° ⁰ ° ⁰ ) (Π B ^ ! ° ⁰ ▹ Q ° ⁰ ° ⁰ )) ^ [ % , next ⁰ ]
              → Γ ⊢ e' ∷ (Id (U ⁰) (Π A' ^ % ° ⁰ ▹ P' ° ⁰ ° ⁰ ) (Π B' ^ ! ° ⁰ ▹ Q' ° ⁰ ° ⁰ )) ^ [ % , next ⁰ ]
              → Γ ⊢ cast ⁰ (Π A ^ % ° ⁰ ▹ P ° ⁰ ° ⁰ ) (Π B ^ ! ° ⁰ ▹ Q ° ⁰ ° ⁰ ) e t ~
                    cast ⁰ (Π A' ^ % ° ⁰ ▹ P' ° ⁰ ° ⁰ ) (Π B' ^ ! ° ⁰ ▹ Q' ° ⁰ ° ⁰ ) e' t' ↑! (Π B ^ ! ° ⁰ ▹ Q ° ⁰ ° ⁰ ) ^ ι ⁰
    cast-ΠΠ!% : ∀ {A P A' P' B Q B' Q' t t' e e'}
              → Γ ⊢ Π A ^ ! ° ⁰ ▹ P ° ⁰ ° ⁰  [conv↑] Π A' ^ ! ° ⁰ ▹ P' ° ⁰ ° ⁰  ∷ U ⁰ ^ ι ¹
              → Γ ⊢ Π B ^ % ° ⁰ ▹ Q ° ⁰ ° ⁰  [conv↑] Π B' ^ % ° ⁰ ▹ Q' ° ⁰ ° ⁰  ∷ U ⁰ ^ ι ¹
              → Γ ⊢ t [conv↑] t' ∷ Π A ^ ! ° ⁰ ▹ P ° ⁰  ° ⁰ ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) (Π A ^ ! ° ⁰ ▹ P ° ⁰ ° ⁰ ) (Π B ^ % ° ⁰ ▹ Q ° ⁰ ° ⁰ )) ^ [ % , next ⁰ ]
              → Γ ⊢ e' ∷ (Id (U ⁰) (Π A' ^ ! ° ⁰ ▹ P' ° ⁰ ° ⁰ ) (Π B' ^ % ° ⁰ ▹ Q' ° ⁰ ° ⁰ )) ^ [ % , next ⁰ ]
              → Γ ⊢ cast ⁰ (Π A ^ ! ° ⁰ ▹ P ° ⁰ ° ⁰ ) (Π B ^ % ° ⁰ ▹ Q ° ⁰ ° ⁰ ) e t ~
                    cast ⁰ (Π A' ^ ! ° ⁰ ▹ P' ° ⁰ ° ⁰ ) (Π B' ^ % ° ⁰ ▹ Q' ° ⁰ ° ⁰ ) e' t' ↑! (Π B ^ % ° ⁰ ▹ Q ° ⁰ ° ⁰ ) ^ ι ⁰


  record _⊢_~_↑%_^_ (Γ : Con Term) (k l A : Term) (ll : TypeLevel) : Set where
    inductive
    constructor %~↑
    field
      ⊢k : Γ ⊢ k ∷ A ^ [ % , ll ]
      ⊢l : Γ ⊢ l ∷ A ^ [ % , ll ]

  data _⊢_~_↑_^_ (Γ : Con Term) : (k l A : Term) → TypeInfo → Set where
    ~↑! : ∀ {k l A ll} → Γ ⊢ k ~ l ↑! A ^ ll → Γ ⊢ k ~ l ↑ A ^ [ ! , ll ]
    ~↑% : ∀ {k l A ll} → Γ ⊢ k ~ l ↑% A ^ ll → Γ ⊢ k ~ l ↑ A ^ [ % , ll ]

  -- Neutral equality with types in WHNF.
  record _⊢_~_↓!_^_ (Γ : Con Term) (k l B : Term) (ll : TypeLevel) : Set where
    inductive
    constructor [~]
    field
      A     : Term
      D     : Γ ⊢ A ⇒* B ^ [ ! , ll ]
      whnfB : Whnf B
      k~l   : Γ ⊢ k ~ l ↑! A ^ ll

  -- Type equality.
  record _⊢_[conv↑]_^_ (Γ : Con Term) (A B : Term) (rA : TypeInfo) : Set where
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
  data _⊢_[conv↓]_^_ (Γ : Con Term) : (A B : Term) → TypeInfo → Set where
    U-refl    : ∀ {r r' }
              → r PE.≡ r' -- needed for K issues
              → ⊢ Γ → Γ ⊢ Univ r ¹ [conv↓] Univ r' ¹ ^ [ ! , next ¹ ]
    univ      : ∀ {A B r l}
              → Γ ⊢ A [conv↓] B ∷ Univ r l ^ next l
              → Γ ⊢ A [conv↓] B ^ [ r , ι l ] 
              
  -- Term equality.
  record _⊢_[conv↑]_∷_^_ (Γ : Con Term) (t u A : Term) (l : TypeLevel) : Set where
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
      t<>u    : Γ ⊢ t′ [conv↓] u′ ∷ B ^ l

  -- Term equality with types and terms in WHNF.
  data _⊢_[conv↓]_∷_^_ (Γ : Con Term) : (t u A : Term) (l : TypeLevel) → Set where
    U-refl    : ∀ {r r' }
              → r PE.≡ r' -- needed for K issues
              → ⊢ Γ → Γ ⊢ Univ r ⁰ [conv↓] Univ r' ⁰ ∷ U ¹ ^ next ¹
    ne        : ∀ {r K L lU l}
                → Γ ⊢ K ~ L ↓! Univ r lU ^ l
                → Γ ⊢ K [conv↓] L ∷ Univ r lU ^ l 
    ℕ-refl    : ⊢ Γ → Γ ⊢ ℕ [conv↓] ℕ ∷ U ⁰ ^ next ⁰
    Empty-refl : ∀ {l} → ⊢ Γ → Γ ⊢ Empty l [conv↓] Empty l ∷ SProp l ^ next l 
    Π-cong    : ∀ {F G H E rF rH rΠ lF lH lG lE lΠ}
              → rF PE.≡ rH -- needed for K issues
              → lF PE.≡ lH -- needed for K issues
              → lG PE.≡ lE -- needed for K issues
              → lF ≤ lΠ
              → lG ≤ lΠ
              → Γ ⊢ F ^ [ rF , ι lF ]
              → Γ ⊢ F [conv↑] H ∷ Univ rF lF ^ next lF
              → Γ ∙ F ^ [ rF , ι lF ] ⊢ G [conv↑] E  ∷ Univ rΠ lG ^ next lG
              → Γ ⊢ Π F ^ rF ° lF ▹ G ° lG ° lΠ [conv↓] Π H ^ rH ° lH ▹ E ° lE ° lΠ ∷ Univ rΠ lΠ ^ next lΠ
    ∃-cong    : ∀ {F G H E l}
              → Γ ⊢ F ^ [ % , ι l ]
              → Γ ⊢ F [conv↑] H ∷ SProp l ^ next l
              → Γ ∙ F ^ [ % , ι l ] ⊢ G [conv↑] E  ∷ SProp l ^ next l
              → Γ ⊢ ∃ F ▹ G [conv↓] ∃ H ▹ E ∷ SProp l ^ next l
    ℕ-ins     : ∀ {k l}
              → Γ ⊢ k ~ l ↓! ℕ ^ ι ⁰
              → Γ ⊢ k [conv↓] l ∷ ℕ ^ ι ⁰
    ne-ins    : ∀ {k l M N ll} -- should we have 2 relevances here?
              → Γ ⊢ k ∷ N ^ [ ! , ι ll ]
              → Γ ⊢ l ∷ N ^ [ ! , ι ll ]
              → Neutral N
              → Γ ⊢ k ~ l ↓! M ^ ι ll
              → Γ ⊢ k [conv↓] l ∷ N ^ ι ll
    zero-refl : ⊢ Γ → Γ ⊢ zero [conv↓] zero ∷ ℕ ^ ι ⁰
    suc-cong  : ∀ {m n}
              → Γ ⊢ m [conv↑] n ∷ ℕ ^ ι ⁰
              → Γ ⊢ suc m [conv↓] suc n ∷ ℕ ^ ι ⁰
    η-eq      : ∀ {f g F G rF lF lG l}
              → lF ≤ l
              → lG ≤ l
              → Γ ⊢ F ^ [ rF , ι lF ]
              → Γ ⊢ f ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ [ ! , ι l ]
              → Γ ⊢ g ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ [ ! , ι l ]
              → Function f
              → Function g
              → Γ ∙ F ^ [ rF , ι lF ] ⊢ wk1 f ∘ var 0 ^ l [conv↑] wk1 g ∘ var 0 ^ l ∷ G ^ ι lG
                → Γ ⊢ f [conv↓] g ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ ι l

  _⊢_[genconv↑]_∷_^_ : (Γ : Con Term) (t u A : Term) (r : TypeInfo) → Set 
  _⊢_[genconv↑]_∷_^_ Γ k l A [ ! , ll ] =  Γ ⊢ k [conv↑] l ∷ A ^ ll
  _⊢_[genconv↑]_∷_^_ Γ k l A [ % , ll ] =  Γ ⊢ k ~ l ↑% A ^  ll
  

var-refl′ : ∀ {Γ x A rA ll}
          → Γ ⊢ var x ∷ A ^ [ rA , ll ]
          → Γ ⊢ var x ~ var x ↑ A ^ [ rA , ll ]
var-refl′ {rA = !} ⊢x = ~↑! (var-refl ⊢x PE.refl)
var-refl′ {rA = %} ⊢x = ~↑% (%~↑ ⊢x ⊢x)
