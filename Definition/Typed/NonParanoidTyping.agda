{-# OPTIONS --safe #-}

module Definition.Typed.NonParanoidTyping where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Consequences.Inversion
open import Definition.Typed.Consequences.Syntactic

open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.Empty
import Tools.PropositionalEquality as PE

infixl 30 _∙_
infix 30 Πⱼ_▹_▹_▹_

mutual
  -- Well-formed context
  data ⊢⊢_ : Con Term → Set where
    ε   : ⊢⊢ ε
    _∙_ : ∀ {Γ A r}
        → ⊢⊢ Γ
        → Γ ⊢⊢ A ^ r
        → ⊢⊢ Γ ∙ A ^ r

  -- Well-formed type
  data _⊢⊢_^_ (Γ : Con Term) : Term → TypeInfo → Set where
    Uⱼ    : ∀ {r} → ⊢⊢ Γ → Γ ⊢⊢ Univ r ¹ ^ [ ! , ∞ ]
    univ : ∀ {A r l}
         → Γ ⊢⊢ A ∷ Univ r l ^ [ ! , next l ]
         → Γ ⊢⊢ A ^ [ r , ι l ]

  -- Well-formed term of a type
  data _⊢⊢_∷_^_ (Γ : Con Term) : Term → Term → TypeInfo → Set where
    univ : ∀ {r l l'}
         → l < l'
         → ⊢⊢ Γ
         → Γ ⊢⊢ (Univ r l) ∷ (Univ ! l') ^ [ ! , next l' ]
    ℕⱼ      : ⊢⊢ Γ → Γ ⊢⊢ ℕ ∷ U ⁰ ^ [ ! , ι ¹ ]
    Emptyⱼ : ⊢⊢ Γ → Γ ⊢⊢ sEmpty ∷ SProp ^ [ ! , ι ¹ ]
    Πⱼ_▹_▹_▹_ : ∀ {F rF lF G lG r l}
           → (r PE.≡ ! → lF ≤ l × lG ≤ l)
           → (r PE.≡ % → lG PE.≡ ⁰ × l PE.≡ ⁰)
           → Γ     ⊢⊢ F ∷ (Univ rF lF) ^ [ ! , next lF ]
           → Γ ∙ F ^ [ rF , ι lF ] ⊢⊢ G ∷ (Univ r lG) ^ [ ! , next lG ]
           → Γ     ⊢⊢ Π F ^ rF ° lF ▹ G ° lG ° l ^ r ∷ (Univ r l) ^ [ ! , next l ]
    ∃ⱼ_▹_ : ∀ {F G}
            → Γ ⊢⊢ F ∷ SProp ^ [ ! , ι ¹ ]
            → Γ ∙ F ^ [ % , ι ⁰ ] ⊢⊢ G ∷ SProp ^ [ ! , ι ¹ ]
            → Γ ⊢⊢ ∃ F ▹ G ∷ SProp ^ [ ! , ι ¹ ]
    var    : ∀ {A rl x}
           → ⊢⊢ Γ
           → x ∷ A ^ rl ∈ Γ
           → Γ ⊢⊢ var x ∷ A ^ rl
    lamⱼ    : ∀ {F r l rF lF G lG t}
           → (r PE.≡ ! → lF ≤ l × lG ≤ l)
           → (r PE.≡ % → lG PE.≡ ⁰ × l PE.≡ ⁰)
           → Γ ∙ F ^ [ rF , ι lF ] ⊢⊢ t ∷ G ^ [ r , ι lG ]
           → Γ     ⊢⊢ lam F ▹ t ^ l ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ r ^ [ r , ι l ]
    _▹_∘ⱼ_    : ∀ {g a F rF lF G lG r lΠ}
           → (r PE.≡ % → lG PE.≡ ⁰ × lΠ PE.≡ ⁰)
           → Γ ⊢⊢     g ∷ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ r ^ [ r , ι lΠ ]
           → Γ ⊢⊢     a ∷ F ^ [ rF , ι lF ]
           → Γ ⊢⊢ g ∘ a ^ lΠ ∷ G [ a ] ^ [ r , ι lG ]
    ⦅_,_,_⦆ⱼ : ∀ {F G t u}
             → Γ ∙ F ^ [ % , ι ⁰ ] ⊢⊢ G ^ [ % , ι ⁰ ]
             → Γ ⊢⊢ t ∷ F ^ [ % , ι ⁰ ]
             → Γ ⊢⊢ u ∷ G [ t ] ^ [ % , ι ⁰ ]
             → Γ ⊢⊢ ⦅ G , t , u ⦆ ∷ ∃ F ▹ G ^ [ % , ι ⁰ ]
    fstⱼ : ∀ {F G t}
           → Γ ⊢⊢ t ∷ ∃ F ▹ G ^ [ % , ι ⁰ ]
           → Γ ⊢⊢ fst t ∷ F ^ [ % , ι ⁰ ]
    sndⱼ : ∀ {F G t}
           → Γ ⊢⊢ t ∷ ∃ F ▹ G ^ [ % , ι ⁰ ]
           → Γ ⊢⊢ snd t ∷ G [ fst t ] ^ [ % , ι ⁰ ]
    zeroⱼ   : ⊢⊢ Γ
           → Γ ⊢⊢ zero ∷ ℕ ^ [ ! ,  ι ⁰ ]
    sucⱼ    : ∀ {n}
           → Γ ⊢⊢ n ∷ ℕ ^ [ ! ,  ι ⁰ ]
           → Γ ⊢⊢ suc n ∷ ℕ ^ [ ! ,  ι ⁰ ]
    natrecⱼ : ∀ {G rG lG s z n}
           → (rG PE.≡ % → lG PE.≡ ⁰)
           → Γ ∙ ℕ ^ [ ! ,  ι ⁰ ] ⊢⊢ G ^ [ rG , ι lG ]
           → Γ       ⊢⊢ z ∷ G [ zero ] ^ [ rG , ι lG ]
           → Γ       ⊢⊢ s ∷ Π ℕ ^ ! ° ⁰ ▹ (G ^ rG ° lG ▹▹ G [ suc (var Nat.zero) ]↑ ° lG ° lG ^ rG) ° lG ° lG ^ rG ^ [ rG , ι lG ]
           → Γ       ⊢⊢ n ∷ ℕ ^ [ ! ,  ι ⁰ ]
           → Γ       ⊢⊢ natrec lG G z s n ∷ G [ n ] ^ [ rG , ι lG ]
    Emptyrecⱼ : ∀ {A lA rA e}
           → Γ ⊢⊢ A ^ [ rA , ι lA ] → Γ ⊢⊢ e ∷ sEmpty ^ [ % ,  ι ⁰ ] -> Γ ⊢⊢ Emptyrec lA ⁰ A e ∷ A ^ [ rA , ι lA ]
    Idⱼ : ∀ {A l t u}
          → Γ ⊢⊢ A ∷ U l ^ [ ! , next l ]
          → Γ ⊢⊢ t ∷ A ^ [ ! , ι l ]
          → Γ ⊢⊢ u ∷ A ^ [ ! , ι l ]
          → Γ ⊢⊢ Id A t u ∷ SProp ^ [ ! , next ⁰ ]
    Idreflⱼ : ∀ {A l t}
              → Γ ⊢⊢ t ∷ A ^ [ ! , ι l ]
              → Γ ⊢⊢ Idrefl A t ∷ (Id A t t) ^ [ % , ι ⁰ ]
    transpⱼ : ∀ {A l P t s u e}
              → Γ ⊢⊢ A ^ [ ! , l ]
              → Γ ∙ A ^ [ ! , l ] ⊢⊢ P ^ [ % , ι ⁰ ]
              → Γ ⊢⊢ t ∷ A ^ [ ! , l ]
              → Γ ⊢⊢ s ∷ P [ t ] ^ [ % , ι ⁰ ]
              → Γ ⊢⊢ u ∷ A ^ [ ! , l ]
              → Γ ⊢⊢ e ∷ (Id A t u) ^ [ % , ι ⁰ ]
              → Γ ⊢⊢ transp A P t s u e ∷ P [ u ] ^ [ % , ι ⁰ ]
    castⱼ : ∀ {A B r e t}
            → Γ ⊢⊢ A ∷ Univ r ⁰ ^ [ ! , next ⁰ ]
            → Γ ⊢⊢ B ∷ Univ r ⁰ ^ [ ! , next ⁰ ]
            → Γ ⊢⊢ e ∷ (Id (Univ r ⁰) A B) ^ [ % , ι ⁰ ]
            → Γ ⊢⊢ t ∷ A ^ [ r , ι ⁰ ]
            → Γ ⊢⊢ cast ⁰ A B e t ∷ B ^ [ r , ι ⁰ ]
    castreflⱼ : ∀ {A t}
                 → Γ ⊢⊢ A ∷ U ⁰ ^ [ ! , next ⁰ ]
                 → Γ ⊢⊢ t ∷ A ^ [ ! , ι ⁰ ]
                 → Γ ⊢⊢ castrefl A t ∷ (Id A t (cast ⁰ A A (Idrefl (U ⁰) A) t)) ^ [ % , ι ⁰ ]
    conv   : ∀ {t A B r}
           → Γ ⊢⊢ t ∷ A ^ r
           → Γ ⊢⊢ A ≡ B ^ r
           → Γ ⊢⊢ t ∷ B ^ r

  -- Type equality
  data _⊢⊢_≡_^_ (Γ : Con Term) : Term → Term → TypeInfo → Set where
    univ   : ∀ {A B r l}
           → Γ ⊢⊢ A ≡ B ∷ (Univ r l) ^ [ ! , next l ]
           → Γ ⊢⊢ A ≡ B ^ [ r , ι l ]
    refl   : ∀ {A r}
           → Γ ⊢⊢ A ^ r
           → Γ ⊢⊢ A ≡ A ^ r
    sym    : ∀ {A B r}
           → Γ ⊢⊢ A ≡ B ^ r
           → Γ ⊢⊢ B ≡ A ^ r
    trans  : ∀ {A B C r}
           → Γ ⊢⊢ A ≡ B ^ r
           → Γ ⊢⊢ B ≡ C ^ r
           → Γ ⊢⊢ A ≡ C ^ r


  -- Term equality
  data _⊢⊢_≡_∷_^_ (Γ : Con Term) : Term → Term → Term → TypeInfo → Set where
    refl        : ∀ {t A l}
                → Γ ⊢⊢ t ∷ A ^ [ ! , l ]
                → Γ ⊢⊢ t ≡ t ∷ A ^ [ ! , l ]
    sym         : ∀ {t u A l}
                → Γ ⊢⊢ t ≡ u ∷ A ^ [ ! , l ]
                → Γ ⊢⊢ u ≡ t ∷ A ^ [ ! , l ]
    trans       : ∀ {t u v A l}
                → Γ ⊢⊢ t ≡ u ∷ A ^ [ ! , l ]
                → Γ ⊢⊢ u ≡ v ∷ A ^ [ ! , l ]
                → Γ ⊢⊢ t ≡ v ∷ A ^ [ ! , l ]
    conv        : ∀ {A B r t u}
                → Γ ⊢⊢ t ≡ u ∷ A ^ r
                → Γ ⊢⊢ A ≡ B ^ r
                → Γ ⊢⊢ t ≡ u ∷ B ^ r
    Π-cong      : ∀ {E F G H rF lF rG lG l}
                → (rG PE.≡ ! → lF ≤ l × lG ≤ l)
                → (rG PE.≡ % → lG PE.≡ ⁰ × l PE.≡ ⁰)
                → Γ     ⊢⊢ F ≡ H       ∷ (Univ rF lF) ^ [ ! , next lF ]
                → Γ ∙ F ^ [ rF , ι lF ] ⊢⊢ G ≡ E       ∷ (Univ rG lG) ^ [ ! , next lG ]
                → Γ     ⊢⊢ Π F ^ rF ° lF ▹ G ° lG ° l ^ rG ≡ Π H ^ rF ° lF ▹ E ° lG ° l ^ rG ∷ (Univ rG l) ^ [ ! , next l ]
    ∃-cong      : ∀ {E F G H}
                → Γ     ⊢⊢ F ≡ H       ∷ SProp ^ [ ! , next ⁰ ]
                → Γ ∙ F ^ [ % , ι ⁰ ] ⊢⊢ G ≡ E       ∷ SProp ^ [ ! , next ⁰ ]
                → Γ     ⊢⊢ ∃ F ▹ G ≡ ∃ H ▹ E ∷ SProp ^ [ ! , next ⁰ ]
    app-cong    : ∀ {a b f g F G rF lF lG l}
                → Γ ⊢⊢ f ≡ g ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ [ ! , ι l ]
                → Γ ⊢⊢ a ≡ b ∷ F ^ [ rF , ι lF ]
                → Γ ⊢⊢ f ∘ a ^ l ≡ g ∘ b ^ l ∷ G [ a ] ^ [ ! , ι lG ]
    β-red       : ∀ {a t F rF lF G lG l}
                → lF ≤ l
                → lG ≤ l
                → Γ ∙ F ^ [ rF , ι lF ] ⊢⊢ t ∷ G ^ [ ! , ι lG ]
                → Γ     ⊢⊢ a ∷ F ^ [ rF , ι lF ]
                → Γ     ⊢⊢ (lam F ▹ t ^ l) ∘ a ^ l ≡ t [ a ] ∷ G [ a ] ^ [ ! , ι lG ]
    η-eq        : ∀ {f g F rF lF lG l G}
                → Γ     ⊢⊢ f ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ [ ! , ι l ]
                → Γ     ⊢⊢ g ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ [ ! , ι l ]
                → Γ ∙ F ^ [ rF , ι lF ] ⊢⊢ wk1 f ∘ var Nat.zero ^ l ≡ wk1 g ∘ var Nat.zero ^ l ∷ G ^ [ ! , ι lG ]
                → Γ     ⊢⊢ f ≡ g ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ [ ! , ι l ]
    suc-cong    : ∀ {m n}
                → Γ ⊢⊢ m ≡ n ∷ ℕ ^ [ ! ,  ι ⁰ ]
                → Γ ⊢⊢ suc m ≡ suc n ∷ ℕ ^ [ ! ,  ι ⁰ ]
    natrec-cong : ∀ {z z′ s s′ n n′ F F′ l}
                → Γ ∙ ℕ ^ [ ! ,  ι ⁰ ] ⊢⊢ F ≡ F′ ^ [ ! , ι l ]
                → Γ     ⊢⊢ z ≡ z′ ∷ F [ zero ] ^ [ ! , ι l ]
                → Γ     ⊢⊢ s ≡ s′ ∷ Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc (var Nat.zero) ]↑ ° l ° l ^ !) ° l ° l ^ ! ^ [ ! , ι l  ]
                → Γ     ⊢⊢ n ≡ n′ ∷ ℕ ^ [ ! ,  ι ⁰ ]
                → Γ     ⊢⊢ natrec l F z s n ≡ natrec l F′ z′ s′ n′ ∷ F [ n ] ^ [ ! , ι l ]
    natrec-zero : ∀ {z s F l}
                → Γ     ⊢⊢ z ∷ F [ zero ] ^ [ ! , ι l ]
                → Γ     ⊢⊢ s ∷ Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc (var Nat.zero) ]↑ ° l ° l ^ !) ° l ° l ^ ! ^ [ ! , ι l ]
                → Γ     ⊢⊢ natrec l F z s zero ≡ z ∷ F [ zero ] ^ [ ! , ι l ]
    natrec-suc  : ∀ {n z s F l}
                → Γ     ⊢⊢ n ∷ ℕ ^ [ ! ,  ι ⁰ ]
                → Γ     ⊢⊢ z ∷ F [ zero ] ^ [ ! , ι l ]
                → Γ     ⊢⊢ s ∷ Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc (var Nat.zero) ]↑ ° l ° l ^ !) ° l ° l ^ ! ^ [ ! , ι l ]
                → Γ     ⊢⊢ natrec l F z s (suc n) ≡ (s ∘ n ^ l) ∘ (natrec l F z s n) ^ l
                        ∷ F [ suc n ] ^ [ ! , ι l ]
    Emptyrec-cong : ∀ {A A' l e e'}
                → Γ ⊢⊢ A ≡ A' ^ [ ! , ι l ]
                → Γ ⊢⊢ e ∷ sEmpty ^ [ % , ι ⁰ ]
                → Γ ⊢⊢ e' ∷ sEmpty ^ [ % , ι ⁰ ]
                → Γ ⊢⊢ Emptyrec l ⁰  A e ≡ Emptyrec l ⁰  A' e' ∷ A ^ [ ! , ι l ]
    proof-irrelevance : ∀ {t u A l}
                      → Γ ⊢⊢ t ∷ A ^ [ % , l ]
                      → Γ ⊢⊢ u ∷ A ^ [ % , l ]
                      → Γ ⊢⊢ t ≡ u ∷ A ^ [ % , l ]
    Id-cong : ∀ {A A' l t t' u u'}
              → Γ ⊢⊢ A ≡ A' ∷ Univ ! l ^ [ ! , next l ]
              → Γ ⊢⊢ t ≡ t' ∷ A ^ [ ! , ι l ]
              → Γ ⊢⊢ u ≡ u' ∷ A ^ [ ! , ι l ]
              → Γ ⊢⊢ Id A t u ≡ Id A' t' u' ∷ SProp ^ [ ! , next ⁰ ]
    Id-Π : ∀ {A rA lA lB l B t u}
           → Γ ⊢⊢ t ∷ (Π A ^ rA ° lA ▹ B ° lB ° l ^ !) ^ [ ! , ι l ]
           → Γ ⊢⊢ u ∷ (Π A ^ rA ° lA ▹ B ° lB ° l ^ !) ^ [ ! , ι l ]
           → Γ ⊢⊢ (Id (Π A ^ rA ° lA ▹ B ° lB ° l ^ !) t u)
                 ≡ Π A ^ rA ° lA ▹ (Id B ((wk1 t) ∘ (var 0) ^ l) ((wk1 u) ∘ (var 0) ^ l)) ° ⁰ ° ⁰
                  ^ % ∷ SProp ^ [ ! , next ⁰ ]
    Id-ℕ-00 : ⊢⊢ Γ
           → Γ ⊢⊢ (Id ℕ zero zero)
                  ≡ sUnit 
                  ∷ SProp ^ [ ! , next ⁰ ]
    Id-ℕ-SS : ∀ {m n}
              → Γ ⊢⊢ m ∷ ℕ ^ [ ! ,  ι ⁰ ]
              → Γ ⊢⊢ n ∷ ℕ ^ [ ! ,  ι ⁰ ]
              → Γ ⊢⊢ (Id ℕ (suc m) (suc n))
                    ≡ (Id ℕ m n)
                    ∷ SProp ^ [ ! , next ⁰ ]
    Id-U-ΠΠ : ∀ {A A' rA B B'}
              → Γ ⊢⊢ A ∷ (Univ rA ⁰) ^ [ ! , next ⁰ ]
              → Γ ∙ A ^ [ rA , ι ⁰ ] ⊢⊢ B ∷ U ⁰ ^ [ ! , next ⁰ ]
              → Γ ⊢⊢ A' ∷ (Univ rA ⁰) ^ [ ! , next ⁰ ]
              → Γ ∙ A' ^ [ rA , ι ⁰ ] ⊢⊢ B' ∷ U ⁰ ^ [ ! , next ⁰ ]
              → Γ ⊢⊢ (Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ !))
                    ≡ ∃ (Id (Univ rA ⁰) A A') ▹
                      (Π (wk1 A') ^ rA ° ⁰ ▹ Id (U ⁰)
                        ((wk (lift (step id)) B) [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (var 1)) (var 0) ]↑)
                        (wk (lift (step id)) B') ° ⁰ ° ⁰ ^ %)
                  ∷ SProp ^ [ ! , next ⁰ ]
    Id-U-ℕℕ : ⊢⊢ Γ
            → Γ ⊢⊢ Id (U ⁰) ℕ ℕ
                  ≡ sUnit 
                  ∷ SProp ^ [ ! , next ⁰ ]
    Id-SProp : ∀ {A B}
               → Γ ⊢⊢ A ∷ SProp ^ [ ! , next ⁰ ]
               → Γ ⊢⊢ B ∷ SProp ^ [ ! , next ⁰ ]
               → Γ ⊢⊢ Id SProp A B
                     ≡ (A ^ % ° ⁰ ▹▹ B ° ⁰ ° ⁰ ^ %) ×× (B ^ % ° ⁰ ▹▹ A ° ⁰ ° ⁰ ^ %)
                     ∷ SProp ^ [ ! , next ⁰ ]
    Id-ℕ-0S : ∀ {t}
            → Γ ⊢⊢ t ∷ ℕ ^ [ ! , ι ⁰ ]
            → Γ ⊢⊢ Id ℕ zero (suc t) ≡ sEmpty ∷ SProp ^ [ ! , next ⁰ ]
    Id-ℕ-S0 : ∀ {t}
            → Γ ⊢⊢ t ∷ ℕ ^ [ ! , ι ⁰ ]
            → Γ ⊢⊢ Id ℕ (suc t) zero ≡ sEmpty ∷ SProp ^ [ ! , next ⁰ ]
    Id-U-ℕΠ : ∀ {A rA B}
            → Γ ⊢⊢ A ∷ Univ rA ⁰ ^ [ ! , next ⁰ ]
            → Γ ∙ A ^ [ rA , ι ⁰ ] ⊢⊢ B ∷ U ⁰ ^ [ ! , next ⁰ ]
            → Γ ⊢⊢ Id (U ⁰) ℕ (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) ≡ sEmpty ∷ SProp ^ [ ! , next ⁰ ]
    Id-U-Πℕ : ∀ {A rA B}
            → Γ ⊢⊢ A ∷ Univ rA ⁰ ^ [ ! , next ⁰ ]
            → Γ ∙ A ^ [ rA , ι ⁰ ] ⊢⊢ B ∷ U ⁰ ^ [ ! , next ⁰ ]
            → Γ ⊢⊢ Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) ℕ ≡ sEmpty ∷ SProp ^ [ ! , next ⁰ ]
    Id-U-ΠΠ!% : ∀ {A rA B A' rA' B' }
            → rA PE.≢ rA'
            → Γ ⊢⊢ A ∷ Univ rA ⁰ ^ [ ! , next ⁰ ]
            → Γ ∙ A ^ [ rA , ι ⁰ ] ⊢⊢ B ∷ U ⁰ ^ [ ! , next ⁰ ]
            → Γ ⊢⊢ A' ∷ Univ rA' ⁰ ^ [ ! , next ⁰ ]
            → Γ ∙ A' ^ [ rA' , ι ⁰ ] ⊢⊢ B' ∷ U ⁰ ^ [ ! , next ⁰ ]
            → Γ ⊢⊢ Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) (Π A' ^ rA' ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ !) ≡ sEmpty ∷ SProp ^ [ ! , next ⁰ ]
    cast-cong : ∀ {A A' B B' e e' t t'} → let l = ⁰ in
                  Γ ⊢⊢ A ≡ A' ∷ U l ^ [ ! , next l ]
                → Γ ⊢⊢ B ≡ B' ∷ U l ^ [ ! , next l ]
                → Γ ⊢⊢ t ≡ t' ∷ A ^ [ ! , ι l ]
                → Γ ⊢⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ]
                → Γ ⊢⊢ e' ∷ (Id (U ⁰) A' B') ^ [ % , ι ⁰ ]
                → Γ ⊢⊢ cast l A B e t ≡ cast l A' B' e' t' ∷ B ^ [ ! , ι l ]
    cast-Π : ∀ {A A' rA B B' e f} → let l = ⁰ in let lA = ⁰ in let lB = ⁰ in
               Γ ⊢⊢ e ∷ Id (U l) (Π A ^ rA ° lA ▹ B ° lB ° l ^ !) (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ !) ^ [ % , ι l ]
             → Γ ⊢⊢ f ∷ (Π A ^ rA ° lA ▹ B ° lB ° l ^ !) ^ [ ! , ι l ]
             → Γ ⊢⊢ (cast l (Π A ^ rA ° lA ▹ B ° lB ° l ^ !) (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ !) e f)
               ≡ (lam A' ▹
                      (let a = cast l (wk1 A') (wk1 A) (Idsym (Univ rA l) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) in
                      cast l (B [ a ]↑) B' ((snd (wk1 e)) ∘ (var 0) ^ ⁰) ((wk1 f) ∘ a ^ l))
                      ^ l)
                   ∷ Π A' ^ rA ° lA ▹ B' ° lB ° l  ^ ! ^ [ ! , ι l ]
    cast-ℕ-0 : ∀ {e}
               → Γ ⊢⊢ e ∷ Id (U ⁰) ℕ ℕ ^ [ % , ι ⁰ ]
               → Γ ⊢⊢ cast ⁰ ℕ ℕ e zero
                   ≡ zero
                   ∷ ℕ ^ [ ! , ι ⁰ ]
    cast-ℕ-S : ∀ {e n}
               → Γ ⊢⊢ e ∷ Id (U ⁰) ℕ ℕ ^ [ % , ι ⁰ ]
               → Γ ⊢⊢ n ∷ ℕ ^ [ ! , ι ⁰ ]
               → Γ ⊢⊢ cast ⁰ ℕ ℕ e (suc n)
                   ≡ suc (cast ⁰ ℕ ℕ e n)
                   ∷ ℕ ^ [ ! , ι ⁰ ]

mutual
  ⊢is⊢⊢ctx : ∀ {Γ} → ⊢ Γ → ⊢⊢ Γ
  ⊢is⊢⊢ : ∀ {Γ A r} → Γ ⊢ A ^ r → Γ ⊢⊢ A ^ r
  ⊢is⊢⊢eq : ∀ {Γ A B r} → Γ ⊢ A ≡ B ^ r → Γ ⊢⊢ A ≡ B ^ r
  ⊢is⊢⊢term : ∀ {Γ A t r} → Γ ⊢ t ∷ A ^ r → Γ ⊢⊢ t ∷ A ^ r
  ⊢is⊢⊢eqterm : ∀ {Γ A t u r} → Γ ⊢ t ≡ u ∷ A ^ r → Γ ⊢⊢ t ≡ u ∷ A ^ r
  
  ⊢is⊢⊢ctx ε = ε
  ⊢is⊢⊢ctx (⊢Γ ∙ x) = ⊢is⊢⊢ctx ⊢Γ ∙ ⊢is⊢⊢ x
  
  ⊢is⊢⊢ (Uⱼ x) = Uⱼ (⊢is⊢⊢ctx x)
  ⊢is⊢⊢ (univ x) = univ (⊢is⊢⊢term x)
  
  ⊢is⊢⊢eq (univ x) = univ (⊢is⊢⊢eqterm x)
  ⊢is⊢⊢eq (refl x) = refl (⊢is⊢⊢ x)
  ⊢is⊢⊢eq (sym X) = sym (⊢is⊢⊢eq X)
  ⊢is⊢⊢eq (trans X X₁) = trans (⊢is⊢⊢eq X) (⊢is⊢⊢eq X₁)
  
  ⊢is⊢⊢term (univ x ⊢Γ) = univ x (⊢is⊢⊢ctx ⊢Γ)
  ⊢is⊢⊢term (ℕⱼ ⊢Γ) = ℕⱼ (⊢is⊢⊢ctx ⊢Γ)
  ⊢is⊢⊢term (Emptyⱼ ⊢Γ) = Emptyⱼ (⊢is⊢⊢ctx ⊢Γ)
  ⊢is⊢⊢term (Πⱼ x ▹ x₁ ▹ X ▹ X₁) = Πⱼ x ▹ x₁ ▹ ⊢is⊢⊢term X ▹ ⊢is⊢⊢term X₁
  ⊢is⊢⊢term (∃ⱼ X ▹ X₁) = ∃ⱼ ⊢is⊢⊢term X ▹ ⊢is⊢⊢term X₁
  ⊢is⊢⊢term (var ⊢Γ x) = var (⊢is⊢⊢ctx ⊢Γ) x
  ⊢is⊢⊢term (lamⱼ x x₁ x₂ X) = lamⱼ x x₁ (⊢is⊢⊢term X)
  ⊢is⊢⊢term (x ▹ X ▹ X₁ ▹ X₂ ∘ⱼ X₃) = x ▹ ⊢is⊢⊢term X₂ ∘ⱼ ⊢is⊢⊢term X₃
  ⊢is⊢⊢term (⦅_,_,_,_⦆ⱼ x x₁ X X₁) = ⦅ ⊢is⊢⊢ x₁ , ⊢is⊢⊢term X , ⊢is⊢⊢term X₁ ⦆ⱼ
  ⊢is⊢⊢term (fstⱼ X X₁ X₂) = fstⱼ (⊢is⊢⊢term X₂)
  ⊢is⊢⊢term (sndⱼ X X₁ X₂) = sndⱼ (⊢is⊢⊢term X₂)
  ⊢is⊢⊢term (zeroⱼ x) = zeroⱼ (⊢is⊢⊢ctx x)
  ⊢is⊢⊢term (sucⱼ X) = sucⱼ (⊢is⊢⊢term X)
  ⊢is⊢⊢term (natrecⱼ x x₁ X X₁ X₂) = natrecⱼ x (⊢is⊢⊢ x₁) (⊢is⊢⊢term X) (⊢is⊢⊢term X₁) (⊢is⊢⊢term X₂)
  ⊢is⊢⊢term (Emptyrecⱼ x X) = Emptyrecⱼ (⊢is⊢⊢ x) (⊢is⊢⊢term X)
  ⊢is⊢⊢term (Idⱼ X X₁ X₂) = Idⱼ (⊢is⊢⊢term X) (⊢is⊢⊢term X₁) (⊢is⊢⊢term X₂) 
  ⊢is⊢⊢term (Idreflⱼ X) = Idreflⱼ (⊢is⊢⊢term X)
  ⊢is⊢⊢term (transpⱼ x x₁ X X₁ X₂ X₃) = transpⱼ (⊢is⊢⊢ x) (⊢is⊢⊢ x₁) (⊢is⊢⊢term X) (⊢is⊢⊢term X₁) (⊢is⊢⊢term X₂) (⊢is⊢⊢term X₃)
  ⊢is⊢⊢term (castⱼ X X₁ X₂ X₃) = castⱼ (⊢is⊢⊢term X) (⊢is⊢⊢term X₁) (⊢is⊢⊢term X₂) (⊢is⊢⊢term X₃) 
  ⊢is⊢⊢term (castreflⱼ X X₁) = castreflⱼ (⊢is⊢⊢term X) (⊢is⊢⊢term X₁)
  ⊢is⊢⊢term (conv X x) = conv (⊢is⊢⊢term X) (⊢is⊢⊢eq x)

  ⊢is⊢⊢eqterm (refl x) = refl (⊢is⊢⊢term x)
  ⊢is⊢⊢eqterm (sym X) = sym (⊢is⊢⊢eqterm X)
  ⊢is⊢⊢eqterm (trans X X₁) = trans (⊢is⊢⊢eqterm X) (⊢is⊢⊢eqterm X₁)
  ⊢is⊢⊢eqterm (conv X x) = conv (⊢is⊢⊢eqterm X) (⊢is⊢⊢eq x)
  ⊢is⊢⊢eqterm (Π-cong x x₁ x₂ X X₁) = Π-cong x x₁ (⊢is⊢⊢eqterm X) (⊢is⊢⊢eqterm X₁)
  ⊢is⊢⊢eqterm (∃-cong x X X₁) = ∃-cong (⊢is⊢⊢eqterm X) (⊢is⊢⊢eqterm X₁)
  ⊢is⊢⊢eqterm (app-cong X X₁) = app-cong (⊢is⊢⊢eqterm X) (⊢is⊢⊢eqterm X₁)
  ⊢is⊢⊢eqterm (β-red x x₁ x₂ x₃ x₄) = β-red x x₁ (⊢is⊢⊢term x₃) (⊢is⊢⊢term x₄)
  ⊢is⊢⊢eqterm (η-eq x x₁ x₂ x₃ x₄ X) = η-eq (⊢is⊢⊢term x₃) (⊢is⊢⊢term x₄) (⊢is⊢⊢eqterm X)
  ⊢is⊢⊢eqterm (suc-cong X) = suc-cong (⊢is⊢⊢eqterm X)
  ⊢is⊢⊢eqterm (natrec-cong x X X₁ X₂) = natrec-cong (⊢is⊢⊢eq x) (⊢is⊢⊢eqterm X) (⊢is⊢⊢eqterm X₁) (⊢is⊢⊢eqterm X₂)
  ⊢is⊢⊢eqterm (natrec-zero x x₁ x₂) = natrec-zero (⊢is⊢⊢term x₁) (⊢is⊢⊢term x₂)
  ⊢is⊢⊢eqterm (natrec-suc x x₁ x₂ x₃) = natrec-suc (⊢is⊢⊢term x) (⊢is⊢⊢term x₂) (⊢is⊢⊢term x₃)
  ⊢is⊢⊢eqterm (Emptyrec-cong x x₁ x₂) = Emptyrec-cong (⊢is⊢⊢eq x) (⊢is⊢⊢term x₁) (⊢is⊢⊢term x₂)
  ⊢is⊢⊢eqterm (proof-irrelevance x x₁) = proof-irrelevance (⊢is⊢⊢term x) (⊢is⊢⊢term x₁)
  ⊢is⊢⊢eqterm (Id-cong X X₁ X₂) = Id-cong (⊢is⊢⊢eqterm X) (⊢is⊢⊢eqterm X₁) (⊢is⊢⊢eqterm X₂)
  ⊢is⊢⊢eqterm (Id-Π x x₁ x₂ x₃ x₄ x₅) = Id-Π  (⊢is⊢⊢term x₄) (⊢is⊢⊢term x₅)
  ⊢is⊢⊢eqterm (Id-ℕ-00 x) = Id-ℕ-00 (⊢is⊢⊢ctx x) 
  ⊢is⊢⊢eqterm (Id-ℕ-SS x x₁) = Id-ℕ-SS (⊢is⊢⊢term x) (⊢is⊢⊢term x₁)
  ⊢is⊢⊢eqterm (Id-U-ΠΠ x x₁ x₂ x₃) = Id-U-ΠΠ (⊢is⊢⊢term x) (⊢is⊢⊢term x₁) (⊢is⊢⊢term x₂) (⊢is⊢⊢term x₃) 
  ⊢is⊢⊢eqterm (Id-U-ℕℕ x) = Id-U-ℕℕ (⊢is⊢⊢ctx x)
  ⊢is⊢⊢eqterm (Id-SProp x x₁) = Id-SProp (⊢is⊢⊢term x) (⊢is⊢⊢term x₁)
  ⊢is⊢⊢eqterm (Id-ℕ-0S x) = Id-ℕ-0S (⊢is⊢⊢term x)
  ⊢is⊢⊢eqterm (Id-ℕ-S0 x) = Id-ℕ-S0 (⊢is⊢⊢term x)
  ⊢is⊢⊢eqterm (Id-U-ℕΠ x x₁) = Id-U-ℕΠ (⊢is⊢⊢term x) (⊢is⊢⊢term x₁)
  ⊢is⊢⊢eqterm (Id-U-Πℕ x x₁) = Id-U-Πℕ (⊢is⊢⊢term x) (⊢is⊢⊢term x₁)
  ⊢is⊢⊢eqterm (Id-U-ΠΠ!% r x x₁ x₂ x₃) = Id-U-ΠΠ!% r (⊢is⊢⊢term x) (⊢is⊢⊢term x₁) (⊢is⊢⊢term x₂) (⊢is⊢⊢term x₃) 
  ⊢is⊢⊢eqterm (cast-cong X X₁ X₂ x x₁) = cast-cong (⊢is⊢⊢eqterm X) (⊢is⊢⊢eqterm X₁) (⊢is⊢⊢eqterm X₂) (⊢is⊢⊢term x) (⊢is⊢⊢term x₁)
  ⊢is⊢⊢eqterm (cast-Π x x₁ x₂ x₃ x₄ x₅) = cast-Π (⊢is⊢⊢term x₄) (⊢is⊢⊢term x₅)
  ⊢is⊢⊢eqterm (cast-ℕ-0 x) = cast-ℕ-0 (⊢is⊢⊢term x)
  ⊢is⊢⊢eqterm (cast-ℕ-S x x₁) = cast-ℕ-S (⊢is⊢⊢term x) (⊢is⊢⊢term x₁)


mutual
  ⊢⊢is⊢ctx : ∀ {Γ} → ⊢⊢ Γ → ⊢ Γ
  ⊢⊢is⊢ : ∀ {Γ A r} → Γ ⊢⊢ A ^ r → Γ ⊢ A ^ r
  ⊢⊢is⊢eq : ∀ {Γ A B r} → Γ ⊢⊢ A ≡ B ^ r → Γ ⊢ A ≡ B ^ r
  ⊢⊢is⊢term : ∀ {Γ A t r} → Γ ⊢⊢ t ∷ A ^ r → Γ ⊢ t ∷ A ^ r
  ⊢⊢is⊢eqterm : ∀ {Γ A t u r} → Γ ⊢⊢ t ≡ u ∷ A ^ r → Γ ⊢ t ≡ u ∷ A ^ r
  
  ⊢⊢is⊢ctx ε = ε
  ⊢⊢is⊢ctx (⊢Γ ∙ x) = ⊢⊢is⊢ctx ⊢Γ ∙ ⊢⊢is⊢ x
  
  ⊢⊢is⊢ (Uⱼ x) = Uⱼ (⊢⊢is⊢ctx x)
  ⊢⊢is⊢ (univ x) = univ (⊢⊢is⊢term x)
  
  ⊢⊢is⊢eq (univ x) = univ (⊢⊢is⊢eqterm x)
  ⊢⊢is⊢eq (refl x) = refl (⊢⊢is⊢ x)
  ⊢⊢is⊢eq (sym X) = sym (⊢⊢is⊢eq X)
  ⊢⊢is⊢eq (trans X X₁) = trans (⊢⊢is⊢eq X) (⊢⊢is⊢eq X₁)
  
  ⊢⊢is⊢term (univ x ⊢Γ) = univ x (⊢⊢is⊢ctx ⊢Γ)
  ⊢⊢is⊢term (ℕⱼ ⊢Γ) = ℕⱼ (⊢⊢is⊢ctx ⊢Γ)
  ⊢⊢is⊢term (Emptyⱼ ⊢Γ) = Emptyⱼ (⊢⊢is⊢ctx ⊢Γ)
  ⊢⊢is⊢term (Πⱼ x ▹ x₁ ▹ X ▹ X₁) = Πⱼ x ▹ x₁ ▹ ⊢⊢is⊢term X ▹ ⊢⊢is⊢term X₁
  ⊢⊢is⊢term (∃ⱼ X ▹ X₁) = ∃ⱼ ⊢⊢is⊢term X ▹ ⊢⊢is⊢term X₁
  ⊢⊢is⊢term (var ⊢Γ x) = var (⊢⊢is⊢ctx ⊢Γ) x
  ⊢⊢is⊢term (lamⱼ x x₁ X) = let XX = ⊢⊢is⊢term X in lamⱼ x x₁ (let ⊢Γ , ⊢F = inversion-ctx (wfTerm XX) in ⊢F) XX
  ⊢⊢is⊢term (x ▹ X₂ ∘ⱼ X₃) =
    let ⊢g = ⊢⊢is⊢term X₂ 
        ⊢a = ⊢⊢is⊢term X₃
        ⊢Π = un-univ (syntacticTerm ⊢g)
        rG , _ , _ , _ , ⊢G , _ , req , _ = inversion-Π ⊢Π
    in x ▹ un-univ (syntacticTerm ⊢a) ▹ PE.subst (λ rr → _ ⊢ _ ∷ Univ rr _ ^ [ ! , _ ]) req ⊢G ▹ ⊢g ∘ⱼ ⊢a
  ⊢⊢is⊢term (⦅_,_,_⦆ⱼ x X X₁) =
    let ⊢t = ⊢⊢is⊢term X
        ⊢u = ⊢⊢is⊢term X₁
    in ⦅_,_,_,_⦆ⱼ (syntacticTerm ⊢t) (⊢⊢is⊢ x) ⊢t ⊢u
  ⊢⊢is⊢term (fstⱼ X) =
    let ⊢t = ⊢⊢is⊢term X
        ⊢A , ⊢G , _ = inversion-∃ (un-univ (syntacticTerm ⊢t))
    in fstⱼ ⊢A ⊢G ⊢t
  ⊢⊢is⊢term (sndⱼ X) =
    let ⊢t = ⊢⊢is⊢term X
        ⊢A , ⊢G , _ = inversion-∃ (un-univ (syntacticTerm ⊢t))
    in sndⱼ ⊢A ⊢G ⊢t
  ⊢⊢is⊢term (zeroⱼ x) = zeroⱼ (⊢⊢is⊢ctx x)
  ⊢⊢is⊢term (sucⱼ X) = sucⱼ (⊢⊢is⊢term X)
  ⊢⊢is⊢term (natrecⱼ x x₁ X X₁ X₂) = natrecⱼ x (⊢⊢is⊢ x₁) (⊢⊢is⊢term X) (⊢⊢is⊢term X₁) (⊢⊢is⊢term X₂)
  ⊢⊢is⊢term (Emptyrecⱼ x X) = Emptyrecⱼ (⊢⊢is⊢ x) (⊢⊢is⊢term X)
  ⊢⊢is⊢term (Idⱼ X X₁ X₂) = Idⱼ (⊢⊢is⊢term X) (⊢⊢is⊢term X₁) (⊢⊢is⊢term X₂) 
  ⊢⊢is⊢term (Idreflⱼ X) = Idreflⱼ (⊢⊢is⊢term X)
  ⊢⊢is⊢term (transpⱼ x x₁ X X₁ X₂ X₃) = transpⱼ (⊢⊢is⊢ x) (⊢⊢is⊢ x₁) (⊢⊢is⊢term X) (⊢⊢is⊢term X₁) (⊢⊢is⊢term X₂) (⊢⊢is⊢term X₃)
  ⊢⊢is⊢term (castⱼ X X₁ X₂ X₃) = castⱼ (⊢⊢is⊢term X) (⊢⊢is⊢term X₁) (⊢⊢is⊢term X₂) (⊢⊢is⊢term X₃) 
  ⊢⊢is⊢term (castreflⱼ X X₁) = castreflⱼ (⊢⊢is⊢term X) (⊢⊢is⊢term X₁)
  ⊢⊢is⊢term (conv X x) = conv (⊢⊢is⊢term X) (⊢⊢is⊢eq x)

  ⊢⊢is⊢eqterm (refl x) = refl (⊢⊢is⊢term x)
  ⊢⊢is⊢eqterm (sym X) = sym (⊢⊢is⊢eqterm X)
  ⊢⊢is⊢eqterm (trans X X₁) = trans (⊢⊢is⊢eqterm X) (⊢⊢is⊢eqterm X₁)
  ⊢⊢is⊢eqterm (conv X x) = conv (⊢⊢is⊢eqterm X) (⊢⊢is⊢eq x)
  ⊢⊢is⊢eqterm (Π-cong x x₁ X X₁) =
    let ⊢FH = ⊢⊢is⊢eqterm X
        _ , ⊢F , _ = syntacticEqTerm ⊢FH
    in Π-cong x x₁ (univ ⊢F) ⊢FH (⊢⊢is⊢eqterm X₁)
  ⊢⊢is⊢eqterm (∃-cong X X₁) =
    let ⊢FH = ⊢⊢is⊢eqterm X
        _ , ⊢F , _ = syntacticEqTerm ⊢FH
    in ∃-cong (univ ⊢F) ⊢FH (⊢⊢is⊢eqterm X₁)
  ⊢⊢is⊢eqterm (app-cong X X₁) = app-cong (⊢⊢is⊢eqterm X) (⊢⊢is⊢eqterm X₁)
  ⊢⊢is⊢eqterm (β-red x x₁ x₃ x₄) =
    let ⊢t = ⊢⊢is⊢term x₃
    in β-red x x₁ (let ⊢Γ , ⊢F = inversion-ctx (wfTerm ⊢t) in ⊢F) ⊢t (⊢⊢is⊢term x₄)
  ⊢⊢is⊢eqterm (η-eq x₃ x₄ X) =
    let ⊢t = ⊢⊢is⊢term x₃
        ⊢Π = un-univ (syntacticTerm ⊢t)
        rG , l! , l% , ⊢F , ⊢G , _ , req , _ = inversion-Π ⊢Π
    in η-eq (proj₁ (l! req)) (proj₂ (l! req)) (univ ⊢F) ⊢t (⊢⊢is⊢term x₄) (⊢⊢is⊢eqterm X)
  ⊢⊢is⊢eqterm (suc-cong X) = suc-cong (⊢⊢is⊢eqterm X)
  ⊢⊢is⊢eqterm (natrec-cong x X X₁ X₂) = natrec-cong (⊢⊢is⊢eq x) (⊢⊢is⊢eqterm X) (⊢⊢is⊢eqterm X₁) (⊢⊢is⊢eqterm X₂)
  ⊢⊢is⊢eqterm (natrec-zero x₁ x₂) =
    let ⊢s = ⊢⊢is⊢term x₂
        ⊢Π = un-univ (syntacticTerm ⊢s)
        _ , _ , _ , _ , ⊢FF , _ = inversion-Π ⊢Π
        _ , _ , _ , ⊢F , _  = inversion-Π ⊢FF
    in natrec-zero (univ ⊢F) (⊢⊢is⊢term x₁) ⊢s
  ⊢⊢is⊢eqterm (natrec-suc x x₂ x₃) =
    let ⊢s = ⊢⊢is⊢term x₃
        ⊢Π = un-univ (syntacticTerm ⊢s)
        _ , _ , _ , _ , ⊢FF , _ = inversion-Π ⊢Π
        _ , _ , _ , ⊢F , _  = inversion-Π ⊢FF
    in natrec-suc (⊢⊢is⊢term x) (univ ⊢F) (⊢⊢is⊢term x₂) ⊢s
  ⊢⊢is⊢eqterm (Emptyrec-cong x x₁ x₂) = Emptyrec-cong (⊢⊢is⊢eq x) (⊢⊢is⊢term x₁) (⊢⊢is⊢term x₂)
  ⊢⊢is⊢eqterm (proof-irrelevance x x₁) = proof-irrelevance (⊢⊢is⊢term x) (⊢⊢is⊢term x₁)
  ⊢⊢is⊢eqterm (Id-cong X X₁ X₂) = Id-cong (⊢⊢is⊢eqterm X) (⊢⊢is⊢eqterm X₁) (⊢⊢is⊢eqterm X₂)
  ⊢⊢is⊢eqterm (Id-Π x₄ x₅) =
    let ⊢t = ⊢⊢is⊢term x₄
        ⊢Π = un-univ (syntacticTerm ⊢t)
        rG , l! , l% , ⊢F , ⊢G , _ , req , _ = inversion-Π ⊢Π
    in Id-Π (proj₁ (l! req)) (proj₂ (l! req)) ⊢F (PE.subst (λ rr → _ ⊢ _ ∷ Univ rr _ ^ [ ! , _ ]) req ⊢G) ⊢t (⊢⊢is⊢term x₅)
  ⊢⊢is⊢eqterm (Id-ℕ-00 x) = Id-ℕ-00 (⊢⊢is⊢ctx x) 
  ⊢⊢is⊢eqterm (Id-ℕ-SS x x₁) = Id-ℕ-SS (⊢⊢is⊢term x) (⊢⊢is⊢term x₁)
  ⊢⊢is⊢eqterm (Id-U-ΠΠ x x₁ x₂ x₃) = Id-U-ΠΠ (⊢⊢is⊢term x) (⊢⊢is⊢term x₁) (⊢⊢is⊢term x₂) (⊢⊢is⊢term x₃) 
  ⊢⊢is⊢eqterm (Id-U-ℕℕ x) = Id-U-ℕℕ (⊢⊢is⊢ctx x)
  ⊢⊢is⊢eqterm (Id-SProp x x₁) = Id-SProp (⊢⊢is⊢term x) (⊢⊢is⊢term x₁)
  ⊢⊢is⊢eqterm (Id-ℕ-0S x) = Id-ℕ-0S (⊢⊢is⊢term x)
  ⊢⊢is⊢eqterm (Id-ℕ-S0 x) = Id-ℕ-S0 (⊢⊢is⊢term x)
  ⊢⊢is⊢eqterm (Id-U-ℕΠ x x₁) = Id-U-ℕΠ (⊢⊢is⊢term x) (⊢⊢is⊢term x₁)
  ⊢⊢is⊢eqterm (Id-U-Πℕ x x₁) = Id-U-Πℕ (⊢⊢is⊢term x) (⊢⊢is⊢term x₁)
  ⊢⊢is⊢eqterm (Id-U-ΠΠ!% r x x₁ x₂ x₃) = Id-U-ΠΠ!% r (⊢⊢is⊢term x) (⊢⊢is⊢term x₁) (⊢⊢is⊢term x₂) (⊢⊢is⊢term x₃) 
  ⊢⊢is⊢eqterm (cast-cong X X₁ X₂ x x₁) = cast-cong (⊢⊢is⊢eqterm X) (⊢⊢is⊢eqterm X₁) (⊢⊢is⊢eqterm X₂) (⊢⊢is⊢term x) (⊢⊢is⊢term x₁)
  ⊢⊢is⊢eqterm (cast-Π x₄ x₅) =
    let ⊢e = ⊢⊢is⊢term x₄
        ⊢Id = un-univ (syntacticTerm ⊢e)
        _ , _ , ⊢Π , ⊢Π' , _ = inversion-Id ⊢Id
        _ , _ , _ , ⊢F , ⊢G , _ , req , _ = inversion-Π ⊢Π
        _ , _ , _ , ⊢F' , ⊢G' , _ , req' , _ = inversion-Π ⊢Π'
    in cast-Π ⊢F (PE.subst (λ rr → _ ⊢ _ ∷ Univ rr _ ^ [ ! , _ ]) req ⊢G) ⊢F' (PE.subst (λ rr → _ ⊢ _ ∷ Univ rr _ ^ [ ! , _ ]) req' ⊢G') ⊢e (⊢⊢is⊢term x₅) 
  ⊢⊢is⊢eqterm (cast-ℕ-0 x) = cast-ℕ-0 (⊢⊢is⊢term x)
  ⊢⊢is⊢eqterm (cast-ℕ-S x x₁) = cast-ℕ-S (⊢⊢is⊢term x) (⊢⊢is⊢term x₁)
