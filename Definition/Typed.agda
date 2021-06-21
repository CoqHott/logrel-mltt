{-# OPTIONS --without-K --safe #-}

module Definition.Typed where

open import Definition.Untyped

open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE

infixl 30 _∙_
infix 30 Πⱼ_▹_▹_▹_

-- Well-typed variables
data _∷_^_∈_ : (x : Nat) (A : Term) (r : TypeInfo) (Γ : Con Term) → Set where
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
  data _⊢_^_ (Γ : Con Term) : Term → TypeInfo → Set where
    Uⱼ    : ∀ {r} → ⊢ Γ → Γ ⊢ Univ r ¹ ^ [ ! , ∞ ]
    univ : ∀ {A r l}
         → Γ ⊢ A ∷ Univ r l ^ [ ! , next l ]
         → Γ ⊢ A ^ [ r , ι l ]
  -- Well-formed term of a type
    -- We also want:
    -- Σ Relevant ▹ Relevant ∷ Relevant
    -- Σ Relevant ▹ Irrelevant ∷ Relevant (allow us to encode relevant Empty, bool)
    -- Quotients
    -- J-types (identity types that have J)

  data _⊢_∷_^_ (Γ : Con Term) : Term → Term → TypeInfo → Set where
    univ : ∀ {r l l'}
         → l < l'
         → ⊢ Γ
         → Γ ⊢ (Univ r l) ∷ (Univ ! l') ^ [ ! , next l' ]
    ℕⱼ      : ⊢ Γ → Γ ⊢ ℕ ∷ U ⁰ ^ [ ! , ι ¹ ]
    Emptyⱼ : ∀ {l} → ⊢ Γ → Γ ⊢ Empty ∷ SProp l ^ [ ! , next l ]
    Πⱼ_▹_▹_▹_ : ∀ {F rF lF G lG r l}
           → lF ≤ l
           → lG ≤ l
           → Γ     ⊢ F ∷ (Univ rF lF) ^ [ ! , next lF ]
           → Γ ∙ F ^ [ rF , ι lF ] ⊢ G ∷ (Univ r lG) ^ [ ! , next lG ]
           → Γ     ⊢ Π F ^ rF ° lF ▹ G ° lG ∷ (Univ r l) ^ [ ! , next l ]
    ∃ⱼ_▹_ : ∀ {F G l}
            → Γ ⊢ F ∷ SProp l ^ [ ! , next l ]
            → Γ ∙ F ^ [ % , ι l ] ⊢ G ∷ SProp l ^ [ ! , next l ]
            → Γ ⊢ ∃ F ▹ G ∷ SProp l ^ [ ! , next l ]
    var    : ∀ {A rl x}
           → ⊢ Γ
           → x ∷ A ^ rl ∈ Γ
           → Γ ⊢ var x ∷ A ^ rl
    lamⱼ    : ∀ {F r l rF lF G lG t}
           → lF ≤ l
           → lG ≤ l
           → Γ     ⊢ F ^ [ rF , ι lF ]
           → Γ ∙ F ^ [ rF , ι lF ] ⊢ t ∷ G ^ [ r , ι lG ]
           → Γ     ⊢ lam F ▹ t ∷ Π F ^ rF ° lF ▹ G ° lG ^ [ r , ι l ]
    _∘ⱼ_    : ∀ {g a F rF lF G lG r lΠ}
           → Γ ⊢     g ∷ Π F ^ rF ° lF ▹ G ° lG ^ [ r , ι lΠ ]
           → Γ ⊢     a ∷ F ^ [ rF , ι lF ]
           → Γ ⊢ g ∘ a ∷ G [ a ] ^ [ r , ι lG ]
    ⦅_,_,_,_⦆ⱼ : ∀ {l F G t u}
             → Γ ⊢ F ^ [ % , ι l ]
             → Γ ∙ F ^ [ % , ι l ] ⊢ G ^ [ % , ι l ]
             → Γ ⊢ t ∷ F ^ [ % , ι l ]
             → Γ ⊢ u ∷ G [ t ] ^ [ % , ι l ]
             → Γ ⊢ ⦅ t , u ⦆ ∷ ∃ F ▹ G ^ [ % , ι l ]
    fstⱼ : ∀ {F G t l}
           → Γ ⊢ F ∷ SProp l ^ [ ! , next l ]
           → Γ ∙ F ^ [ % , ι l ] ⊢ G ∷ SProp l ^ [ ! , next l ]
           → Γ ⊢ t ∷ ∃ F ▹ G ^ [ % , ι l ]
           → Γ ⊢ fst t ∷ F ^ [ % , ι l ]
    sndⱼ : ∀ {F G t l}
           → Γ ⊢ F ∷ SProp l ^ [ ! , next l ]
           → Γ ∙ F ^ [ % , ι l ] ⊢ G ∷ SProp l ^ [ ! , next l ]
           → Γ ⊢ t ∷ ∃ F ▹ G ^ [ % , ι l ]
           → Γ ⊢ snd t ∷ G [ fst t ] ^ [ % , ι l ]
    zeroⱼ   : ⊢ Γ
           → Γ ⊢ zero ∷ ℕ ^ [ ! ,  ι ⁰ ]
    sucⱼ    : ∀ {n}
           → Γ ⊢ n ∷ ℕ ^ [ ! ,  ι ⁰ ]
           → Γ ⊢ suc n ∷ ℕ ^ [ ! ,  ι ⁰ ]
    natrecⱼ : ∀ {G rG lG s z n}
           → Γ ∙ ℕ ^ [ ! ,  ι ⁰ ] ⊢ G ^ [ rG , ι lG ]
           → Γ       ⊢ z ∷ G [ zero ] ^ [ rG , ι lG ]
           → Γ       ⊢ s ∷ Π ℕ ^ ! ° ⁰ ▹ (G ^ rG ° lG ▹▹ G [ suc (var Nat.zero) ]↑ ° lG ) ° lG ^ [ rG , ι lG ]
           → Γ       ⊢ n ∷ ℕ ^ [ ! ,  ι ⁰ ]
           → Γ       ⊢ natrec G z s n ∷ G [ n ] ^ [ rG , ι lG ]
    Emptyrecⱼ : ∀ {A l rA e}
           → Γ ⊢ A ^ rA → Γ ⊢ e ∷ Empty ^ [ % ,  ι l ] -> Γ ⊢ Emptyrec A e ∷ A ^ rA
    Idⱼ : ∀ {A l t u}
          → Γ ⊢ A ∷ U l ^ [ ! , next l ]
          → Γ ⊢ t ∷ A ^ [ ! , ι l ]
          → Γ ⊢ u ∷ A ^ [ ! , ι l ]
          → Γ ⊢ Id A t u ∷ SProp l ^ [ ! , next l ]
    Idreflⱼ : ∀ {A l t}
              → Γ ⊢ t ∷ A ^ [ ! , l ]
              → Γ ⊢ Idrefl A t ∷ (Id A t t) ^ [ % , l ]
    transpⱼ : ∀ {A l P t s u e}
              → Γ ⊢ A ^ [ ! , l ]
              → Γ ∙ A ^ [ ! , l ] ⊢ P ^ [ % , l ]
              → Γ ⊢ t ∷ A ^ [ ! , l ]
              → Γ ⊢ s ∷ P [ t ] ^ [ % , l ]
              → Γ ⊢ u ∷ A ^ [ ! , l ]
              → Γ ⊢ e ∷ (Id A t u) ^ [ % , l ]
              → Γ ⊢ transp A P t s u e ∷ P [ u ] ^ [ % , l ]
    castⱼ : ∀ {A B r e t}
            → Γ ⊢ A ∷ Univ r ⁰ ^ [ ! , next ⁰ ]
            → Γ ⊢ B ∷ Univ r ⁰ ^ [ ! , next ⁰ ]
            → Γ ⊢ e ∷ (Id (Univ r ⁰) A B) ^ [ % , next ⁰ ]
            → Γ ⊢ t ∷ A ^ [ r , ι ⁰ ]
            → Γ ⊢ cast ⁰ A B e t ∷ B ^ [ r , ι ⁰ ]
    castreflⱼ : ∀ {A t}
                 → Γ ⊢ A ∷ U ⁰ ^ [ ! , next ⁰ ]
                 → Γ ⊢ t ∷ A ^ [ ! , ι ⁰ ]
                 → Γ ⊢ castrefl A t ∷ (Id A t (cast ⁰ A A (Idrefl (U ⁰) A) t)) ^ [ % , ι ⁰ ]
    conv   : ∀ {t A B r}
           → Γ ⊢ t ∷ A ^ r
           → Γ ⊢ A ≡ B ^ r
           → Γ ⊢ t ∷ B ^ r

  -- Type equality
  data _⊢_≡_^_ (Γ : Con Term) : Term → Term → TypeInfo → Set where
    univ   : ∀ {A B r l}
           → Γ ⊢ A ≡ B ∷ (Univ r l) ^ [ ! , next l ]
           → Γ ⊢ A ≡ B ^ [ r , ι l ]
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
    -- I dont think we want ∃ and Id conversion rules, as they are always in SProp
    -- and can therefore be recovered from typed conversion


  -- Term equality
  data _⊢_≡_∷_^_ (Γ : Con Term) : Term → Term → Term → TypeInfo → Set where
    refl        : ∀ {t A l}
                → Γ ⊢ t ∷ A ^ [ ! , l ]
                → Γ ⊢ t ≡ t ∷ A ^ [ ! , l ]
    sym         : ∀ {t u A l}
                → Γ ⊢ t ≡ u ∷ A ^ [ ! , l ]
                → Γ ⊢ u ≡ t ∷ A ^ [ ! , l ]
    trans       : ∀ {t u v A l}
                → Γ ⊢ t ≡ u ∷ A ^ [ ! , l ]
                → Γ ⊢ u ≡ v ∷ A ^ [ ! , l ]
                → Γ ⊢ t ≡ v ∷ A ^ [ ! , l ]
    conv        : ∀ {A B r t u}
                → Γ ⊢ t ≡ u ∷ A ^ r
                → Γ ⊢ A ≡ B ^ r
                → Γ ⊢ t ≡ u ∷ B ^ r
    Π-cong      : ∀ {E F G H rF lF rG lG l}
                → lF ≤ l
                → lG ≤ l
                → Γ     ⊢ F ^ [ rF , ι lF ]
                → Γ     ⊢ F ≡ H       ∷ (Univ rF lF) ^ [ ! , next lF ]
                → Γ ∙ F ^ [ rF , ι lF ] ⊢ G ≡ E       ∷ (Univ rG lG) ^ [ ! , next lG ]
                → Γ     ⊢ Π F ^ rF ° lF ▹ G ° lG ≡ Π H ^ rF ° lF ▹ E ° lG  ∷ (Univ rG l) ^ [ ! , next l ]
    ∃-cong      : ∀ {E F G H l}
                → Γ     ⊢ F ^ [ % , ι l ]
                → Γ     ⊢ F ≡ H       ∷ SProp l ^ [ ! , next l ]
                → Γ ∙ F ^ [ % , ι l ] ⊢ G ≡ E       ∷ SProp l ^ [ ! , next l ]
                → Γ     ⊢ ∃ F ▹ G ≡ ∃ H ▹ E ∷ SProp l ^ [ ! , next l ]
    app-cong    : ∀ {a b f g F G rF lF lG l}
                → Γ ⊢ f ≡ g ∷ Π F ^ rF ° lF ▹ G ° lG  ^ [ ! , ι l ]
                → Γ ⊢ a ≡ b ∷ F ^ [ rF , ι lF ]
                → Γ ⊢ f ∘ a ≡ g ∘ b ∷ G [ a ] ^ [ ! , ι lG ]
    β-red       : ∀ {a t F rF lF G lG}
                → Γ     ⊢ F ^ [ rF , ι lF ]
                → Γ ∙ F ^ [ rF , ι lF ] ⊢ t ∷ G ^ [ ! , ι lG ]
                → Γ     ⊢ a ∷ F ^ [ rF , ι lF ]
                → Γ     ⊢ (lam F ▹ t) ∘ a ≡ t [ a ] ∷ G [ a ] ^ [ ! , ι lG ]
    η-eq        : ∀ {f g F rF lF lG l G}
                → lF ≤ l
                → lG ≤ l
                → Γ     ⊢ F ^ [ rF , ι lF ]
                → Γ     ⊢ f ∷ Π F ^ rF ° lF ▹ G ° lG ^ [ ! , ι l ]
                → Γ     ⊢ g ∷ Π F ^ rF ° lF ▹ G ° lG ^ [ ! , ι l ]
                → Γ ∙ F ^ [ rF , ι lF ] ⊢ wk1 f ∘ var Nat.zero ≡ wk1 g ∘ var Nat.zero ∷ G ^ [ ! , ι lG ]
                → Γ     ⊢ f ≡ g ∷ Π F ^ rF ° lF ▹ G ° lG ^ [ ! , ι l ]
    suc-cong    : ∀ {m n}
                → Γ ⊢ m ≡ n ∷ ℕ ^ [ ! ,  ι ⁰ ]
                → Γ ⊢ suc m ≡ suc n ∷ ℕ ^ [ ! ,  ι ⁰ ]
    natrec-cong : ∀ {z z′ s s′ n n′ F F′ l}
                → Γ ∙ ℕ ^ [ ! ,  ι ⁰ ] ⊢ F ≡ F′ ^ [ ! , ι l ]
                → Γ     ⊢ z ≡ z′ ∷ F [ zero ] ^ [ ! , ι l ]
                → Γ     ⊢ s ≡ s′ ∷ Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc (var Nat.zero) ]↑ ° l) ° l ^ [ ! , ι l  ]
                → Γ     ⊢ n ≡ n′ ∷ ℕ ^ [ ! ,  ι ⁰ ]
                → Γ     ⊢ natrec F z s n ≡ natrec F′ z′ s′ n′ ∷ F [ n ] ^ [ ! , ι l ]
    natrec-zero : ∀ {z s F l}
                → Γ ∙ ℕ ^ [ ! ,  ι ⁰ ] ⊢ F ^ [ ! , ι l ]
                → Γ     ⊢ z ∷ F [ zero ] ^ [ ! , ι l ]
                → Γ     ⊢ s ∷ Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc (var Nat.zero) ]↑ ° l) ° l ^ [ ! , ι l ]
                → Γ     ⊢ natrec F z s zero ≡ z ∷ F [ zero ] ^ [ ! , ι l ]
    natrec-suc  : ∀ {n z s F l}
                → Γ     ⊢ n ∷ ℕ ^ [ ! ,  ι ⁰ ]
                → Γ ∙ ℕ ^ [ ! ,  ι ⁰ ] ⊢ F ^ [ ! , ι l ]
                → Γ     ⊢ z ∷ F [ zero ] ^ [ ! , ι l ]
                → Γ     ⊢ s ∷ Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc (var Nat.zero) ]↑ ° l ) ° l ^ [ ! , ι l ]
                → Γ     ⊢ natrec F z s (suc n) ≡ (s ∘ n) ∘ (natrec F z s n)
                        ∷ F [ suc n ] ^ [ ! , ι l ]
    Emptyrec-cong : ∀ {A A' l lEmpty e e'}
                → Γ ⊢ A ≡ A' ^ [ ! , l ]
                → Γ ⊢ e ∷ Empty ^ [ % , ι lEmpty ]
                → Γ ⊢ e' ∷ Empty ^ [ % , ι lEmpty ]
                → Γ ⊢ Emptyrec A e ≡ Emptyrec A' e' ∷ A ^ [ ! , l ]
    proof-irrelevance : ∀ {t u A l}
                      → Γ ⊢ t ∷ A ^ [ % , l ]
                      → Γ ⊢ u ∷ A ^ [ % , l ]
                      → Γ ⊢ t ≡ u ∷ A ^ [ % , l ]
    Id-cong : ∀ {A A' l t t' u u'}
              → Γ ⊢ A ≡ A' ∷ Univ ! l ^ [ ! , next l ]
              → Γ ⊢ t ≡ t' ∷ A ^ [ ! , ι l ]
              → Γ ⊢ u ≡ u' ∷ A ^ [ ! , ι l ]
              → Γ ⊢ Id A t u ≡ Id A' t' u' ∷ SProp l ^ [ ! , next l ]
    Id-Π : ∀ {A rA lA lB l B t u}
           → lA ≤ l
           → lB ≤ l
           → Γ ⊢ A ∷ Univ rA lA ^ [ ! , next lA ]
           → Γ ∙ A ^ [ rA , ι lA ] ⊢ B ∷ Univ ! lB ^ [ ! , next lB ]
           → Γ ⊢ t ∷ (Π A ^ rA ° lA ▹ B ° lB) ^ [ ! , ι l ]
           → Γ ⊢ u ∷ (Π A ^ rA ° lA ▹ B ° lB) ^ [ ! , ι l ]
           → Γ ⊢ (Id (Π A ^ rA ° lA ▹ B ° lB) t u)
                 ≡ Π A ^ rA ° lA ▹ (Id B ((wk1 t) ∘ (var 0)) ((wk1 u) ∘ (var 0))) ° lB
                 ∷ SProp l ^ [ ! , next l ]
    Id-ℕ-00 : ⊢ Γ
           → Γ ⊢ (Id ℕ zero zero)
                  ≡ Unit {⁰}
                  ∷ SProp ⁰ ^ [ ! , next ⁰ ]
    Id-ℕ-SS : ∀ {m n}
              → Γ ⊢ m ∷ ℕ ^ [ ! ,  ι ⁰ ]
              → Γ ⊢ n ∷ ℕ ^ [ ! ,  ι ⁰ ]
              → Γ ⊢ (Id ℕ (suc m) (suc n))
                    ≡ (Id ℕ m n)
                    ∷ SProp ⁰ ^ [ ! , next ⁰ ]
    Id-U-ΠΠ : ∀ {A A' rA B B'}
              → Γ ⊢ A ∷ (Univ rA ⁰) ^ [ ! , next ⁰ ]
              → Γ ∙ A ^ [ rA , ι ⁰ ] ⊢ B ∷ U ⁰ ^ [ ! , next ⁰ ]
              → Γ ⊢ A' ∷ (Univ rA ⁰) ^ [ ! , next ⁰ ]
              → Γ ∙ A' ^ [ rA , ι ⁰ ] ⊢ B' ∷ U ⁰ ^ [ ! , next ⁰ ]
              → Γ ⊢ (Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰))
                    ≡ ∃ (Id (Univ rA ⁰) A A') ▹
                      (Π (wk1 A') ^ rA ° ⁰ ▹ Id (U ⁰)
                        ((wk (lift (step id)) B) [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (var 1)) (var 0) ]↑)
                        (wk (lift (step id)) B') ° ¹)
                  ∷ SProp ¹ ^ [ ! , next ¹ ]
    Id-U-ℕℕ : ⊢ Γ
            → Γ ⊢ Id (U ⁰) ℕ ℕ
                  ≡ Unit {¹}
                  ∷ (SProp ¹) ^ [ ! , next ¹ ]
    Id-SProp : ∀ {A B}
               → Γ ⊢ A ∷ SProp ⁰ ^ [ ! , next ⁰ ]
               → Γ ⊢ B ∷ SProp ⁰ ^ [ ! , next ⁰ ]
               → Γ ⊢ Id (SProp ⁰) A B
                     ≡ (A ^ % ° ⁰ ▹▹ B ° ⁰) ×× (B ^ % ° ⁰ ▹▹ A ° ⁰)
                     ∷ SProp ¹ ^ [ ! , next ¹ ]
    Id-ℕ-0S : ∀ {t}
            → Γ ⊢ t ∷ ℕ ^ [ ! , ι ⁰ ]
            → Γ ⊢ Id ℕ zero (suc t) ≡ Empty ∷ (SProp ⁰) ^ [ ! , next ⁰ ]
    Id-ℕ-S0 : ∀ {t}
            → Γ ⊢ t ∷ ℕ ^ [ ! , ι ⁰ ]
            → Γ ⊢ Id ℕ (suc t) zero ≡ Empty ∷ (SProp ⁰) ^ [ ! , next ⁰ ]
    Id-U-ℕΠ : ∀ {A rA B}
            → Γ ⊢ A ∷ Univ rA ⁰ ^ [ ! , next ⁰ ]
            → Γ ∙ A ^ [ rA , ι ⁰ ] ⊢ B ∷ U ⁰ ^ [ ! , next ⁰ ]
            → Γ ⊢ Id (U ⁰) ℕ (Π A ^ rA ° ⁰ ▹ B ° ⁰) ≡ Empty ∷ SProp ¹ ^ [ ! , next ¹ ]
    Id-U-Πℕ : ∀ {A rA B}
            → Γ ⊢ A ∷ Univ rA ⁰ ^ [ ! , next ⁰ ]
            → Γ ∙ A ^ [ rA , ι ⁰ ] ⊢ B ∷ U ⁰ ^ [ ! , next ⁰ ]
            → Γ ⊢ Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰) ℕ ≡ Empty ∷ SProp ¹ ^ [ ! , next ¹ ]
    cast-cong : ∀ {A A' B B' e e' t t'} → let l = ⁰ in
                  Γ ⊢ A ≡ A' ∷ U l ^ [ ! , next l ]
                → Γ ⊢ B ≡ B' ∷ U l ^ [ ! , next l ]
                → Γ ⊢ t ≡ t' ∷ A ^ [ ! , ι l ]
                → Γ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , next ⁰ ]
                → Γ ⊢ e' ∷ (Id (U ⁰) A' B') ^ [ % , next ⁰ ]
                → Γ ⊢ cast l A B e t ≡ cast l A' B' e' t' ∷ B ^ [ ! , ι l ]
    cast-Π : ∀ {A A' rA B B' e f} → let l = ⁰ in let lA = ⁰ in let lB = ⁰ in
               Γ ⊢ A ∷ (Univ rA lA) ^ [ ! , next lA ]
             → Γ ∙ A ^ [ rA , ι lA ] ⊢ B ∷ U lB ^ [ ! , next lB ]
             → Γ ⊢ A' ∷ (Univ rA lA) ^ [ ! , next lA ]
             → Γ ∙ A' ^ [ rA , ι lA ] ⊢ B' ∷ U lB ^ [ ! , next lB ]
             → Γ ⊢ e ∷ Id (U l) (Π A ^ rA ° lA ▹ B ° lB ) (Π A' ^ rA ° lA ▹ B' ° lB ) ^ [ % , next l ]
             → Γ ⊢ f ∷ (Π A ^ rA ° lA ▹ B ° lB) ^ [ ! , ι l ]
             → Γ ⊢ (cast l (Π A ^ rA ° lA ▹ B ° lB) (Π A' ^ rA ° lA ▹ B' ° lB) e f)
               ≡ (lam A' ▹
                 let a = cast l (wk1 A') (wk1 A) (Idsym (Univ rA l) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) in
                 cast l (B [ a ]↑) B' ((snd (wk1 e)) ∘ (var 0)) ((wk1 f) ∘ a))
                   ∷ Π A' ^ rA ° lA ▹ B' ° lB ^ [ ! , ι l ]
    cast-ℕ-0 : ∀ {e}
               → Γ ⊢ e ∷ Id (U ⁰) ℕ ℕ ^ [ % , next ⁰ ]
               → Γ ⊢ cast ⁰ ℕ ℕ e zero
                   ≡ zero
                   ∷ ℕ ^ [ ! , ι ⁰ ]
    cast-ℕ-S : ∀ {e n}
               → Γ ⊢ e ∷ Id (U ⁰) ℕ ℕ ^ [ % , next ⁰ ]
               → Γ ⊢ n ∷ ℕ ^ [ ! , ι ⁰ ]
               → Γ ⊢ cast ⁰ ℕ ℕ e (suc n)
                   ≡ suc (cast ⁰ ℕ ℕ e n)
                   ∷ ℕ ^ [ ! , ι ⁰ ]

mutual
  data _⊢_⇒_∷_^_ (Γ : Con Term) : Term → Term → Term → TypeLevel → Set where
    conv         : ∀ {A B l t u}
                 → Γ ⊢ t ⇒ u ∷ A ^ l
                 → Γ ⊢ A ≡ B ^ [ ! , l ]
                 → Γ ⊢ t ⇒ u ∷ B ^ l
    app-subst    : ∀ {A B t u a rA lA lB l}
                 → Γ ⊢ t ⇒ u ∷ Π A ^ rA ° lA ▹ B ° lB ^ ι l
                 → Γ ⊢ a ∷ A ^ [ rA , ι lA ]
                 → Γ ⊢ t ∘ a ⇒ u ∘ a ∷ B [ a ] ^ ι lB
    β-red        : ∀ {A B lA lB a t rA}
                 → Γ     ⊢ A ^ [ rA , ι lA ]
                 → Γ ∙ A ^ [ rA , ι lA ] ⊢ t ∷ B ^ [ ! , ι lB ]
                 → Γ     ⊢ a ∷ A ^ [ rA , ι lA ]
                 → Γ     ⊢ (lam A ▹ t) ∘ a ⇒ t [ a ] ∷ B [ a ] ^ ι lB
    natrec-subst : ∀ {z s n n′ F l}
                 → Γ ∙ ℕ ^ [ ! , ι ⁰ ] ⊢ F ^ [ ! , ι l ]
                 → Γ     ⊢ z ∷ F [ zero ] ^ [ ! , ι l ]
                 → Γ     ⊢ s ∷ Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc (var Nat.zero) ]↑ ° l) ° l ^ [ ! , ι l ]
                 → Γ     ⊢ n ⇒ n′ ∷ ℕ ^ ι ⁰
                 → Γ     ⊢ natrec F z s n ⇒ natrec F z s n′ ∷ F [ n ] ^ ι l
    natrec-zero  : ∀ {z s F l }
                 → Γ ∙ ℕ ^ [ ! , ι ⁰ ] ⊢ F ^ [ ! , ι l ]
                 → Γ     ⊢ z ∷ F [ zero ] ^ [ ! , ι l ]
                 → Γ     ⊢ s ∷ Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc (var Nat.zero) ]↑ ° l ) ° l  ^ [ ! , ι l ]
                 → Γ     ⊢ natrec F z s zero ⇒ z ∷ F [ zero ] ^ ι l
    natrec-suc   : ∀ {n z s F l}
                 → Γ     ⊢ n ∷ ℕ ^ [ ! , ι ⁰ ]
                 → Γ ∙ ℕ ^ [ ! , ι ⁰ ] ⊢ F ^ [ ! , ι l ]
                 → Γ     ⊢ z ∷ F [ zero ] ^ [ ! , ι l ]
                 → Γ     ⊢ s ∷ Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc (var Nat.zero) ]↑ ° l ) ° l ^ [ ! , ι l ]
                 → Γ     ⊢ natrec F z s (suc n) ⇒ (s ∘ n) ∘ (natrec F z s n)
                         ∷ F [ suc n ] ^ ι l
    Id-subst : ∀ {A A' l t u}
              → Γ ⊢ A ⇒ A' ∷ Univ ! l ^ next l
              → Γ ⊢ t ∷ A ^ [ ! , ι l ]
              → Γ ⊢ u ∷ A ^ [ ! , ι l ]
              → Γ ⊢ Id A t u ⇒ Id A' t u ∷ SProp l ^ next l
    Id-ℕ-subst : ∀ {m m' n}
              → Γ ⊢ m ⇒ m' ∷ ℕ ^ ι ⁰
              → Γ ⊢ n ∷ ℕ ^ [ ! , ι ⁰ ]
              → Γ ⊢ Id ℕ m n ⇒ Id ℕ m' n ∷ SProp ⁰ ^ next ⁰
    Id-ℕ-0-subst : ∀ {n n'}
              → Γ ⊢ n ⇒ n' ∷ ℕ ^ ι ⁰
              → Γ ⊢ Id ℕ zero n ⇒ Id ℕ zero n' ∷ SProp ⁰ ^ next ⁰
    Id-ℕ-S-subst : ∀ {m n n'}
              → Γ ⊢ m ∷ ℕ ^ [ ! , ι ⁰ ]
              → Γ ⊢ n ⇒ n' ∷ ℕ ^ ι ⁰
              → Γ ⊢ Id ℕ (suc m) n ⇒ Id ℕ (suc m) n' ∷ SProp ⁰ ^ next ⁰
    Id-U-subst : ∀ {A A' B}
              → Γ ⊢ A ⇒ A' ∷ U ⁰  ^ next ⁰
              → Γ ⊢ B ∷ U ⁰  ^ [ ! , next ⁰  ]
              → Γ ⊢ Id (U ⁰ ) A B ⇒ Id (U ⁰) A' B ∷ SProp ¹ ^ next ¹
    Id-U-ℕ-subst : ∀ {B B'}
              → Γ ⊢ B ⇒ B' ∷ U ⁰ ^ next ⁰
              → Γ ⊢ Id (U ⁰) ℕ B ⇒ Id (U ⁰) ℕ B' ∷ SProp ¹ ^ next ¹
    Id-U-Π-subst : ∀ {A rA P B B'}
              → Γ ⊢ A ∷ (Univ rA ⁰) ^ [ ! , next ⁰ ]
              → Γ ∙ A ^ [ rA , ι ⁰ ] ⊢ P ∷ U ⁰ ^ [ ! , next ⁰ ]
              → Γ ⊢ B ⇒ B' ∷ U ⁰ ^ next ⁰
              → Γ ⊢ Id (U ⁰) (Π A ^ rA ° ⁰ ▹ P ° ⁰) B ⇒ Id (U ⁰) (Π A ^ rA ° ⁰ ▹ P ° ⁰) B' ∷ SProp ¹ ^ next ¹
    Id-Π : ∀ {A rA lA lB l B t u}
           → lA ≤ l
           → lB ≤ l
           → Γ ⊢ A ∷ Univ rA lA ^ [ ! , next lA ]
           → Γ ∙ A ^ [ rA , ι lA ] ⊢ B  ∷ Univ ! lB ^ [ ! , next lB ]
           → Γ ⊢ t ∷ (Π A ^ rA ° lA ▹ B ° lB ) ^ [ ! , ι l ]
           → Γ ⊢ u ∷ (Π A ^ rA ° lA ▹ B ° lB ) ^ [ ! , ι l ]
           → Γ ⊢ (Id (Π A ^ rA ° lA ▹ B ° lB ) t u)
                 ⇒ Π A ^ rA ° lA ▹ (Id B ((wk1 t) ∘ (var 0)) ((wk1 u) ∘ (var 0))) ° lB
                 ∷ SProp l ^ next l
    Id-ℕ-00 : ⊢ Γ
            → Γ ⊢ (Id ℕ zero zero)
                  ⇒ Unit {⁰}
                  ∷ SProp ⁰ ^ next ⁰
    Id-ℕ-SS : ∀ {m n}
              → Γ ⊢ m ∷ ℕ ^ [ ! , ι ⁰ ]
              → Γ ⊢ n ∷ ℕ ^ [ ! , ι ⁰ ]
              → Γ ⊢ (Id ℕ (suc m) (suc n))
                    ⇒ (Id ℕ m n)
                    ∷ SProp ⁰ ^ next ⁰
    Id-U-ΠΠ : ∀ {A A' rA B B'}
              → Γ ⊢ A ∷ (Univ rA ⁰) ^ [ ! , next ⁰ ]
              → Γ ∙ A ^ [ rA , ι ⁰ ] ⊢ B ∷ U ⁰ ^ [ ! , next ⁰ ]
              → Γ ⊢ A' ∷ (Univ rA ⁰) ^ [ ! , next ⁰ ]
              → Γ ∙ A' ^ [ rA , ι ⁰ ] ⊢ B' ∷ U ⁰ ^ [ ! , next ⁰ ]
              → Γ ⊢ (Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰))
                    ⇒ ∃ (Id (Univ rA ⁰) A A') ▹
                      (Π (wk1 A') ^ rA ° ⁰ ▹ Id (U ⁰)
                        ((wk1d B) [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (var 1)) (var 0) ]↑)
                        (wk1d B') ° ¹)
                    ∷ SProp ¹ ^ next ¹
    Id-U-ℕℕ : ⊢ Γ
            → Γ ⊢ (Id (U ⁰) ℕ ℕ)
                  ⇒ Unit {¹}
                  ∷ SProp ¹ ^ next ¹
    Id-SProp : ∀ {A B}
               → Γ ⊢ A ∷ SProp ⁰ ^ [ ! , next ⁰ ]
               → Γ ⊢ B ∷ SProp ⁰ ^ [ ! , next ⁰ ]
               → Γ ⊢ Id (SProp ⁰) A B
                     ⇒ (A ^ % ° ⁰ ▹▹ B ° ⁰) ×× (B ^ % ° ⁰  ▹▹ A ° ⁰ )
                     ∷ SProp ¹ ^ next ¹
    Id-ℕ-0S : ∀ {t}
            → Γ ⊢ t ∷ ℕ ^ [ ! , ι ⁰ ]
            → Γ ⊢ Id ℕ zero (suc t) ⇒ Empty ∷ SProp ⁰ ^ next ⁰
    Id-ℕ-S0 : ∀ {t}
            → Γ ⊢ t ∷ ℕ ^ [ ! , ι ⁰ ]
            → Γ ⊢ Id ℕ (suc t) zero ⇒ Empty ∷ SProp ⁰ ^ next ⁰
    Id-U-ℕΠ : ∀ {A rA B}
            → Γ ⊢ A ∷ Univ rA ⁰ ^ [ ! , next ⁰ ]
            → Γ ∙ A ^ [ rA , ι ⁰ ] ⊢ B ∷ U ⁰ ^ [ ! , next ⁰ ]
            → Γ ⊢ Id (U ⁰) ℕ (Π A ^ rA ° ⁰ ▹ B ° ⁰) ⇒ Empty ∷ SProp ¹ ^ next ¹
    Id-U-Πℕ : ∀ {A rA B}
            → Γ ⊢ A ∷ Univ rA ⁰ ^ [ ! , next ⁰ ]
            → Γ ∙ A ^ [ rA , ι ⁰ ] ⊢ B ∷ U ⁰ ^ [ ! , next ⁰ ]
            → Γ ⊢ Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰) ℕ ⇒ Empty ∷ SProp ¹ ^ next ¹
    cast-subst : ∀ {A A' B e t} → let l = ⁰ in
                    Γ ⊢ A ⇒ A' ∷ U l ^ next l
                  → Γ ⊢ B ∷ U l ^ [ ! , next l ]
                  → Γ ⊢ e ∷ Id (U l) A B ^ [ % , next l ]
                  → Γ ⊢ t ∷ A ^ [ ! , ι l ]
                  → Γ ⊢ cast l A B e t ⇒ cast l A' B e t ∷ B ^ ι l
    cast-ℕ-subst : ∀ {B B' e t}
                  → Γ ⊢ B ⇒ B' ∷ U ⁰ ^ next ⁰
                  → Γ ⊢ e ∷ Id (U ⁰) ℕ B ^ [ % , next ⁰ ]
                  → Γ ⊢ t ∷ ℕ ^ [ ! , ι ⁰ ]
                  → Γ ⊢ cast ⁰ ℕ B e t ⇒ cast ⁰ ℕ B' e t ∷ B ^ ι ⁰
    cast-Π-subst : ∀ {A rA P B B' e t} → let l = ⁰ in let lA = ⁰ in let lP = ⁰ in
                    Γ ⊢ A ∷ (Univ rA lA) ^ [ ! , next lA ]
                  → Γ ∙ A ^ [ rA , ι lA ] ⊢ P ∷ U lP ^ [ ! , next lA ]
                  → Γ ⊢ B ⇒ B' ∷ U l ^ next l
                  → Γ ⊢ e ∷ Id (U l) (Π A ^ rA ° lA ▹ P ° lP) B ^ [ % , next l ]
                  → Γ ⊢ t ∷ (Π A ^ rA ° lA ▹ P ° lP) ^ [ ! , ι l ]
                  → Γ ⊢ cast l (Π A ^ rA ° lA ▹ P ° lP) B e t ⇒ cast l (Π A ^ rA ° lA ▹ P ° lP) B' e t ∷ B ^ ι l
    cast-Π : ∀ {A A' rA B B' e f} → let l = ⁰ in
               Γ ⊢ A ∷ (Univ rA l) ^ [ ! , next l ]
             → Γ ∙ A ^ [ rA , ι l ] ⊢ B ∷ U l ^ [ ! , next l ]
             → Γ ⊢ A' ∷ (Univ rA l) ^ [ ! , next l ]
             → Γ ∙ A' ^ [ rA , ι l ] ⊢ B' ∷ U l ^ [ ! , next l ]
             → Γ ⊢ e ∷ Id (U l) (Π A ^ rA ° l ▹ B ° l) (Π A' ^ rA ° l  ▹ B' ° l) ^ [ % , next l ]
             → Γ ⊢ f ∷ (Π A ^ rA ° l ▹ B ° l) ^ [ ! , ι l ]
             → Γ ⊢ (cast l (Π A ^ rA ° l ▹ B ° l) (Π A' ^ rA ° l ▹ B' ° l) e f)
               ⇒ (lam A' ▹
                 let a = cast l (wk1 A') (wk1 A) (Idsym (Univ rA l) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) in
                 cast l (B [ a ]↑) B' ((snd (wk1 e)) ∘ (var 0)) ((wk1 f) ∘ a))
                   ∷ Π A' ^ rA ° l ▹ B' ° l ^ ι l
    cast-ℕ-0 : ∀ {e}
               → Γ ⊢ e ∷ Id (U ⁰) ℕ ℕ ^ [ % , next ⁰ ]
               → Γ ⊢ cast ⁰ ℕ ℕ e zero
                   ⇒ zero
                   ∷ ℕ ^ ι ⁰
    cast-ℕ-S : ∀ {e n}
               → Γ ⊢ e ∷ Id (U ⁰) ℕ ℕ ^ [ % , next ⁰ ]
               → Γ ⊢ n ∷ ℕ ^ [ ! , ι ⁰ ]
               → Γ ⊢ cast ⁰ ℕ ℕ e (suc n)
                   ⇒ suc (cast ⁰ ℕ ℕ e n)
                   ∷ ℕ ^ ι ⁰

    cast-ℕ-cong : ∀ {e t u}
               → Γ ⊢ e ∷ Id (U ⁰) ℕ ℕ ^ [ % , next ⁰ ]
               → Γ ⊢ t ⇒ u ∷ ℕ ^ ι ⁰
               → Γ ⊢ cast ⁰ ℕ ℕ e t
                   ⇒ cast ⁰ ℕ ℕ e u
                   ∷ ℕ ^ ι ⁰

  -- Type reduction
  data _⊢_⇒_^_ (Γ : Con Term) : Term → Term → TypeInfo → Set where
    univ : ∀ {A B r l}
         → Γ ⊢ A ⇒ B ∷ (Univ r l) ^ next l
         → Γ ⊢ A ⇒ B ^ [ r , ι l ]

-- Term reduction closure
data _⊢_⇒*_∷_^_ (Γ : Con Term) : Term → Term → Term → TypeLevel → Set where
  id  : ∀ {A l t}
      → Γ ⊢ t ∷ A ^ [ ! , l ]
      → Γ ⊢ t ⇒* t ∷ A ^ l
  _⇨_ : ∀ {A l t t′ u}
      → Γ ⊢ t  ⇒  t′ ∷ A ^ l
      → Γ ⊢ t′ ⇒* u  ∷ A ^ l
      → Γ ⊢ t  ⇒* u  ∷ A ^ l

-- Type reduction closure
data _⊢_⇒*_^_ (Γ : Con Term) : Term → Term → TypeInfo → Set where
  id  : ∀ {A r}
      → Γ ⊢ A ^ r
      → Γ ⊢ A ⇒* A ^ r
  _⇨_ : ∀ {A A′ B r}
      → Γ ⊢ A  ⇒  A′ ^ r
      → Γ ⊢ A′ ⇒* B  ^ r
      → Γ ⊢ A  ⇒* B  ^ r

-- Type reduction to whnf
_⊢_↘_^_ : (Γ : Con Term) → Term → Term → TypeInfo → Set
Γ ⊢ A ↘ B ^ r = Γ ⊢ A ⇒* B ^ r × Whnf B

-- Term reduction to whnf
_⊢_↘_∷_^_ : (Γ : Con Term) → Term → Term → Term → TypeLevel → Set
Γ ⊢ t ↘ u ∷ A ^ l = Γ ⊢ t ⇒* u ∷ A ^ l × Whnf u

-- Type equality with well-formed types
_⊢_:≡:_^_ : (Γ : Con Term) → Term → Term → TypeInfo → Set
Γ ⊢ A :≡: B ^ r = Γ ⊢ A ^ r × Γ ⊢ B ^ r × (Γ ⊢ A ≡ B ^ r)

-- Term equality with well-formed terms
_⊢_:≡:_∷_^_ : (Γ : Con Term) → Term → Term → Term → TypeInfo → Set
Γ ⊢ t :≡: u ∷ A ^ r = Γ ⊢ t ∷ A ^ r × Γ ⊢ u ∷ A ^ r × (Γ ⊢ t ≡ u ∷ A ^ r)

-- Type reduction closure with well-formed types
record _⊢_:⇒*:_^_ (Γ : Con Term) (A B : Term) (r : TypeInfo) : Set where
  constructor [[_,_,_]]
  field
    ⊢A : Γ ⊢ A ^ r
    ⊢B : Γ ⊢ B ^ r
    D  : Γ ⊢ A ⇒* B ^ r

open _⊢_:⇒*:_^_ using () renaming (D to red) public

-- Term reduction closure with well-formed terms
record _⊢_:⇒*:_∷_^_ (Γ : Con Term) (t u A : Term) (l : TypeLevel) : Set where
  constructor [[_,_,_]]
  field
    ⊢t : Γ ⊢ t ∷ A ^ [ ! , l ]
    ⊢u : Γ ⊢ u ∷ A ^ [ ! , l ]
    d  : Γ ⊢ t ⇒* u ∷ A ^ l

open _⊢_:⇒*:_∷_^_ using () renaming (d to redₜ) public

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

Unitⱼ : ∀ {Γ} (⊢Γ : ⊢ Γ)
      → Γ ⊢ Unit ∷ SProp ⁰ ^ [ ! , ι ¹ ]
Unitⱼ ⊢Γ = Πⱼ ≡is≤ PE.refl ▹ ≡is≤ PE.refl ▹ Emptyⱼ ⊢Γ ▹ Emptyⱼ (⊢Γ ∙ univ (Emptyⱼ ⊢Γ))

typeUnit : ∀ {l} →  Type (Unit {l})
typeUnit = Πₙ
