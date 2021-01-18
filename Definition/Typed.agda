{-# OPTIONS --without-K --safe #-}

module Definition.Typed where

open import Definition.Untyped

open import Tools.Nat using (Nat)
open import Tools.Product
import Tools.PropositionalEquality as PE

infixl 30 _∙_
infix 30 Πⱼ_▹_

-- Lemmas that are useful for reduction
Unit : Term
Unit = Π Empty ^ % ▹ Empty

tt : Term -- currently not used
tt = lam Empty ▹ (Emptyrec Empty (var 0))

ap : (A B f x y e : Term) → Term -- currently not used
ap A B f x y e = transp A (Id (wk1 B) (wk1 (f ∘ x)) ((wk1 f) ∘ (var 0))) x (Idrefl B (f ∘ x)) y e

Idsym : (A x y e : Term) → Term
Idsym A x y e = transp A (Id (wk1 A) (var 0) (wk1 x)) x (Idrefl A x) y e

Idtrans : (A x y z e f : Term) → Term -- currently not used
Idtrans A x y z e f = transp A (Id (wk1 A) (wk1 x) (var 0)) y e z f

-- Well-typed variables
data _∷_^_∈_ : (x : Nat) (A : Term) (r : Relevance) (Γ : Con Term) → Set where
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
  data _⊢_^_ (Γ : Con Term) : Term → Relevance → Set where
    ℕⱼ    : ⊢ Γ → Γ ⊢ ℕ ^ !
    Emptyⱼ : ⊢ Γ -> Γ ⊢ Empty ^ %
    Uⱼ    : ∀ {r} → ⊢ Γ → Γ ⊢ (Univ r) ^ !
    Πⱼ_▹_ : ∀ {F rF G rG}
         → Γ     ⊢ F ^ rF
         → Γ ∙ F ^ rF ⊢ G ^ rG
         → Γ     ⊢ Π F ^ rF ▹ G ^ rG
    Σⱼ_▹_ : ∀ {F G} -- For now we want only irrelevant sigma
            → Γ ⊢ F ^ %
            → Γ ∙ F ^ % ⊢ G ^ %
            → Γ ⊢ Σ F ▹ G ^ %
    univ : ∀ {A r}
         → Γ ⊢ A ∷ (Univ r) ^ !
         → Γ ⊢ A ^ r
    Idⱼ : ∀ {A t u}
          → Γ ⊢ A ^ !
          → Γ ⊢ t ∷ A ^ !
          → Γ ⊢ u ∷ A ^ !
          → Γ ⊢ (Id A t u) ^ %

  -- Well-formed term of a type
  data _⊢_∷_^_ (Γ : Con Term) : Term → Term → Relevance → Set where
    ℕⱼ      : ⊢ Γ → Γ ⊢ ℕ ∷ U ^ !
    Emptyⱼ :  ⊢ Γ → Γ ⊢ Empty ∷ SProp ^ !
    Πⱼ_▹_   : ∀ {F rF G rG}
           → Γ     ⊢ F ∷ (Univ rF) ^ !
           → Γ ∙ F ^ rF ⊢ G ∷ (Univ rG) ^ !
           → Γ     ⊢ Π F ^ rF ▹ G ∷ (Univ rG) ^ !
    Σⱼ_▹_ : ∀ {F G}
            → Γ ⊢ F ∷ SProp ^ !
            → Γ ∙ F ^ % ⊢ G ∷ SProp ^ !
            → Γ ⊢ Σ F ▹ G ∷ SProp ^ !
    var    : ∀ {A r x}
           → ⊢ Γ
           → x ∷ A ^ r ∈ Γ
           → Γ ⊢ var x ∷ A ^ r
    lamⱼ    : ∀ {F rF G rG t}
           → Γ     ⊢ F ^ rF
           → Γ ∙ F ^ rF ⊢ t ∷ G ^ rG
           → Γ     ⊢ lam F ▹ t ∷ Π F ^ rF ▹ G ^ rG
    _∘ⱼ_    : ∀ {g a F rF G rG}
           → Γ ⊢     g ∷ Π F ^ rF ▹ G ^ rG
           → Γ ⊢     a ∷ F ^ rF
           → Γ ⊢ g ∘ a ∷ G [ a ] ^ rG
    ⦅_,_⦆ⱼ : ∀ {F G t u}
             → Γ ⊢ t ∷ F ^ %
             → Γ ⊢ u ∷ G [ t ] ^ %
             → Γ ⊢ ⦅ t , u ⦆ ∷ Σ F ▹ G ^ %
    fstⱼ : ∀ {F G t}
           → Γ ⊢ F ∷ SProp ^ !
           → Γ ∙ F ^ % ⊢ G ∷ SProp ^ !
           → Γ ⊢ t ∷ Σ F ▹ G ^ %
           → Γ ⊢ fst t ∷ F ^ %
    sndⱼ : ∀ {F G t}
           → Γ ⊢ F ∷ SProp ^ !
           → Γ ∙ F ^ % ⊢ G ∷ SProp ^ !
           → Γ ⊢ t ∷ Σ F ▹ G ^ %
           → Γ ⊢ snd t ∷ G [ fst t ] ^ %
    zeroⱼ   : ⊢ Γ
           → Γ ⊢ zero ∷ ℕ ^ !
    sucⱼ    : ∀ {n}
           → Γ ⊢ n ∷ ℕ ^ !
           → Γ ⊢ suc n ∷ ℕ ^ !
    natrecⱼ : ∀ {G rG s z n}
           → Γ ∙ ℕ ^ ! ⊢ G ^ rG
           → Γ       ⊢ z ∷ G [ zero ] ^ rG
           → Γ       ⊢ s ∷ Π ℕ ^ ! ▹ (G ^ rG ▹▹ G [ suc (var Nat.zero) ]↑) ^ rG
           → Γ       ⊢ n ∷ ℕ ^ !
           → Γ       ⊢ natrec G z s n ∷ G [ n ] ^ rG
    Emptyrecⱼ : ∀ {A rA e}
           → Γ ⊢ A ^ rA → Γ ⊢ e ∷ Empty ^ % -> Γ ⊢ Emptyrec A e ∷ A ^ rA
    Idⱼ : ∀ {A t u}
          → Γ ⊢ A ^ !
          → Γ ⊢ t ∷ A ^ !
          → Γ ⊢ u ∷ A ^ !
          → Γ ⊢ Id A t u ∷ SProp ^ !
    Idreflⱼ : ∀ {A t}
              → Γ ⊢ t ∷ A ^ !
              → Γ ⊢ Idrefl A t ∷ (Id A t t) ^ %
    transpⱼ : ∀ {A P t s u e}
              → Γ ⊢ A ^ !
              → Γ ∙ A ^ ! ⊢ P ^ %
              → Γ ⊢ t ∷ A ^ !
              → Γ ⊢ s ∷ P [ t ] ^ %
              → Γ ⊢ u ∷ A ^ !
              → Γ ⊢ e ∷ (Id A t u) ^ %
              → Γ ⊢ transp A P t s u e ∷ P [ u ] ^ %
    castⱼ : ∀ {A B e t}
            → Γ ⊢ A ∷ U ^ !
            → Γ ⊢ B ∷ U ^ !
            → Γ ⊢ e ∷ (Id U A B) ^ %
            → Γ ⊢ t ∷ A ^ !
            → Γ ⊢ cast A B e t ∷ B ^ !
    castreflⱼ : ∀ {A t}
                 → Γ ⊢ A ∷ U ^ !
                 → Γ ⊢ t ∷ A ^ !
                 → Γ ⊢ castrefl A t ∷ (Id A t (cast A A (Idrefl U A) t)) ^ %
    conv   : ∀ {t A B r}
           → Γ ⊢ t ∷ A ^ r
           → Γ ⊢ A ≡ B ^ r
           → Γ ⊢ t ∷ B ^ r

  -- Type equality
  data _⊢_≡_^_ (Γ : Con Term) : Term → Term → Relevance → Set where
    univ   : ∀ {A B r}
           → Γ ⊢ A ≡ B ∷ (Univ r) ^ !
           → Γ ⊢ A ≡ B ^ r
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
    Π-cong : ∀ {F H rF G E rG}
           → Γ     ⊢ F ^ rF
           → Γ     ⊢ F ≡ H ^ rF
           → Γ ∙ F ^ rF ⊢ G ≡ E ^ rG
           → Γ     ⊢ Π F ^ rF ▹ G ≡ Π H ^ rF ▹ E ^ rG
    -- I dont think we want Σ and Id conversion rules, as they are always in SProp
    -- and can therefore be recovered from typed conversion

  -- Term equality
  data _⊢_≡_∷_^_ (Γ : Con Term) : Term → Term → Term → Relevance → Set where
    refl        : ∀ {t A}
                → Γ ⊢ t ∷ A ^ !
                → Γ ⊢ t ≡ t ∷ A ^ !
    sym         : ∀ {t u A}
                → Γ ⊢ t ≡ u ∷ A ^ !
                → Γ ⊢ u ≡ t ∷ A ^ !
    trans       : ∀ {t u v A}
                → Γ ⊢ t ≡ u ∷ A ^ !
                → Γ ⊢ u ≡ v ∷ A ^ !
                → Γ ⊢ t ≡ v ∷ A ^ !
    conv        : ∀ {A B r t u}
                → Γ ⊢ t ≡ u ∷ A ^ r
                → Γ ⊢ A ≡ B ^ r
                → Γ ⊢ t ≡ u ∷ B ^ r
    Π-cong      : ∀ {E F G H rF rG}
                → Γ     ⊢ F ^ rF
                → Γ     ⊢ F ≡ H       ∷ (Univ rF) ^ !
                → Γ ∙ F ^ rF ⊢ G ≡ E       ∷ (Univ rG) ^ !
                → Γ     ⊢ Π F ^ rF ▹ G ≡ Π H ^ rF ▹ E ∷ (Univ rG) ^ !
    Σ-cong      : ∀ {E F G H}
                → Γ     ⊢ F ^ %
                → Γ     ⊢ F ≡ H       ∷ SProp ^ !
                → Γ ∙ F ^ % ⊢ G ≡ E       ∷ SProp ^ !
                → Γ     ⊢ Σ F ▹ G ≡ Σ H ▹ E ∷ SProp ^ !
    app-cong    : ∀ {a b f g F G rF}
                → Γ ⊢ f ≡ g ∷ Π F ^ rF ▹ G ^ !
                → Γ ⊢ a ≡ b ∷ F ^ rF
                → Γ ⊢ f ∘ a ≡ g ∘ b ∷ G [ a ] ^ !
    β-red       : ∀ {a t F rF G}
                → Γ     ⊢ F ^ rF
                → Γ ∙ F ^ rF ⊢ t ∷ G ^ !
                → Γ     ⊢ a ∷ F ^ rF
                → Γ     ⊢ (lam F ▹ t) ∘ a ≡ t [ a ] ∷ G [ a ] ^ !
    η-eq        : ∀ {f g F rF G}
                → Γ     ⊢ F ^ rF
                → Γ     ⊢ f ∷ Π F ^ rF ▹ G ^ !
                → Γ     ⊢ g ∷ Π F ^ rF ▹ G ^ !
                → Γ ∙ F ^ rF ⊢ wk1 f ∘ var Nat.zero ≡ wk1 g ∘ var Nat.zero ∷ G ^ !
                → Γ     ⊢ f ≡ g ∷ Π F ^ rF ▹ G ^ !
    suc-cong    : ∀ {m n}
                → Γ ⊢ m ≡ n ∷ ℕ ^ !
                → Γ ⊢ suc m ≡ suc n ∷ ℕ ^ !
    natrec-cong : ∀ {z z′ s s′ n n′ F F′}
                → Γ ∙ ℕ ^ ! ⊢ F ≡ F′ ^ !
                → Γ     ⊢ z ≡ z′ ∷ F [ zero ] ^ !
                → Γ     ⊢ s ≡ s′ ∷ Π ℕ ^ ! ▹ (F ^ ! ▹▹ F [ suc (var Nat.zero) ]↑) ^ !
                → Γ     ⊢ n ≡ n′ ∷ ℕ ^ !
                → Γ     ⊢ natrec F z s n ≡ natrec F′ z′ s′ n′ ∷ F [ n ] ^ !
    natrec-zero : ∀ {z s F}
                → Γ ∙ ℕ ^ ! ⊢ F ^ !
                → Γ     ⊢ z ∷ F [ zero ] ^ !
                → Γ     ⊢ s ∷ Π ℕ ^ ! ▹ (F ^ ! ▹▹ F [ suc (var Nat.zero) ]↑) ^ !
                → Γ     ⊢ natrec F z s zero ≡ z ∷ F [ zero ] ^ !
    natrec-suc  : ∀ {n z s F}
                → Γ     ⊢ n ∷ ℕ ^ !
                → Γ ∙ ℕ ^ ! ⊢ F ^ !
                → Γ     ⊢ z ∷ F [ zero ] ^ !
                → Γ     ⊢ s ∷ Π ℕ ^ ! ▹ (F ^ ! ▹▹ F [ suc (var Nat.zero) ]↑) ^ !
                → Γ     ⊢ natrec F z s (suc n) ≡ (s ∘ n) ∘ (natrec F z s n)
                        ∷ F [ suc n ] ^ !
    Emptyrec-cong : ∀ {A A' e e'}
                → Γ ⊢ A ≡ A' ^ !
                → Γ ⊢ e ≡ e' ∷ Empty ^ %
                → Γ ⊢ Emptyrec A e ≡ Emptyrec A' e' ∷ A ^ !
    proof-irrelevance : ∀ {t u A}
                      → Γ ⊢ t ∷ A ^ %
                      → Γ ⊢ u ∷ A ^ %
                      → Γ ⊢ t ≡ u ∷ A ^ %
    Id-cong : ∀ {A A' t t' u u'}
              → Γ ⊢ A ≡ A' ^ !
              → Γ ⊢ t ≡ t' ∷ A ^ !
              → Γ ⊢ u ≡ u' ∷ A ^ !
              → Γ ⊢ Id A t u ≡ Id A' t' u' ∷ SProp ^ !
    Id-Π : ∀ {A rA B t u}
           → Γ ⊢ A ^ rA
           → Γ ∙ A ^ rA ⊢ B ^ !
           → Γ ⊢ t ∷ (Π A ^ rA ▹ B) ^ !
           → Γ ⊢ u ∷ (Π A ^ rA ▹ B) ^ !
           → Γ ⊢ (Id (Π A ^ rA ▹ B) t u)
                 ≡ Π A ^ rA ▹ (Id B ((wk1 t) ∘ (var 0)) ((wk1 u) ∘ (var 0)))
                 ∷ SProp ^ !
    Id-ℕ-00 : ⊢ Γ
           → Γ ⊢ (Id ℕ zero zero)
                  ≡ Unit
                  ∷ SProp ^ !
    Id-ℕ-SS : ∀ {m n}
              → Γ ⊢ m ∷ ℕ ^ !
              → Γ ⊢ n ∷ ℕ ^ !
              → Γ ⊢ (Id ℕ (suc m) (suc n))
                    ≡ (Id ℕ m n)
                    ∷ SProp ^ !
    Id-U-ΠΠ : ∀ {A A' rA B B'}
              → Γ ⊢ A ∷ (Univ rA) ^ !
              → Γ ∙ A ^ rA ⊢ B ∷ U ^ !
              → Γ ⊢ A' ∷ (Univ rA) ^ !
              → Γ ∙ A' ^ rA ⊢ B' ∷ U ^ !
              → Γ ⊢ (Id U (Π A ^ rA ▹ B) (Π A' ^ rA ▹ B'))
                    ≡ Σ (Id (Univ rA) A A') ▹
                      (Π (wk1 A') ^ rA ▹ Id U
                        ((wk (lift (step id)) B) [ cast (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA) (wk1 (wk1 A)) (wk1 (wk1 A')) (var 1)) (var 0) ]↑)
                        (wk (lift (step id)) B'))
                  ∷ SProp ^ !
    Id-U-ℕℕ : ⊢ Γ
            → Γ ⊢ Id U ℕ ℕ
                  ≡ Unit
                  ∷ SProp ^ !
    Id-SProp : ∀ {A B}
               → Γ ⊢ A ∷ SProp ^ !
               → Γ ⊢ B ∷ SProp ^ !
               → Γ ⊢ (Id SProp A B)
                     ≡ (Σ (A ^ % ▹▹ B) ▹ ((wk1 B) ^ % ▹▹ (wk1 A)))
                     ∷ SProp ^ !
    Id-ℕ-0S : ∀ {t}
            → Γ ⊢ t ∷ ℕ ^ !
            → Γ ⊢ Id ℕ zero (suc t) ≡ Empty ∷ SProp ^ !
    Id-ℕ-S0 : ∀ {t}
            → Γ ⊢ t ∷ ℕ ^ !
            → Γ ⊢ Id ℕ (suc t) zero ≡ Empty ∷ SProp ^ !
    Id-U-ℕΠ : ∀ {A rA B}
            → Γ ⊢ A ∷ Univ rA ^ !
            → Γ ∙ A ^ rA ⊢ B ∷ U ^ !
            → Γ ⊢ Id U ℕ (Π A ^ rA ▹ B) ≡ Empty ∷ SProp ^ !
    Id-U-Πℕ : ∀ {A rA B}
            → Γ ⊢ A ∷ Univ rA ^ !
            → Γ ∙ A ^ rA ⊢ B ∷ U ^ !
            → Γ ⊢ Id U (Π A ^ rA ▹ B) ℕ ≡ Empty ∷ SProp ^ !
    cast-cong : ∀ {A A' B B' e e' t t'}
                → Γ ⊢ A ≡ A' ∷ U ^ !
                → Γ ⊢ B ≡ B' ∷ U ^ !
                → Γ ⊢ e ≡ e' ∷ Id U A B ^ % --actually irrelevant
                → Γ ⊢ t ≡ t' ∷ A ^ !
                → Γ ⊢ cast A B e t ≡ cast A' B' e' t' ∷ B ^ !
    cast-Π : ∀ {A A' rA B B' e f}
             → Γ ⊢ A ∷ (Univ rA) ^ !
             → Γ ∙ A ^ rA ⊢ B ∷ U ^ !
             → Γ ⊢ A' ∷ (Univ rA) ^ !
             → Γ ∙ A' ^ rA ⊢ B' ∷ U ^ !
             → Γ ⊢ e ∷ Id U (Π A ^ rA ▹ B) (Π A' ^ rA ▹ B') ^ %
             → Γ ⊢ f ∷ (Π A ^ rA ▹ B) ^ !
             → Γ ⊢ (cast (Π A ^ rA ▹ B) (Π A' ^ rA ▹ B') e f)
               ≡ (lam A' ▹
                 let a = cast (wk1 A') (wk1 A) (Idsym (Univ rA) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) in
                 cast (B [ a ]↑) B' ((snd (wk1 e)) ∘ (var 0)) ((wk1 f) ∘ a))
                   ∷ Π A' ^ rA ▹ B' ^ !
    cast-ℕ-0 : ∀ {e}
               → Γ ⊢ e ∷ Id U ℕ ℕ ^ %
               → Γ ⊢ cast ℕ ℕ e zero
                   ≡ zero
                   ∷ ℕ ^ !
    cast-ℕ-S : ∀ {e n}
               → Γ ⊢ e ∷ Id U ℕ ℕ ^ %
               → Γ ⊢ n ∷ ℕ ^ !
               → Γ ⊢ cast ℕ ℕ e (suc n)
                   ≡ suc (cast ℕ ℕ e n)
                   ∷ ℕ ^ !

-- Term reduction
data _⊢_⇒_∷_ (Γ : Con Term) : Term → Term → Term → Set where
  conv         : ∀ {A B t u}
               → Γ ⊢ t ⇒ u ∷ A
               → Γ ⊢ A ≡ B ^ !
               → Γ ⊢ t ⇒ u ∷ B
  app-subst    : ∀ {A B t u a rA}
               → Γ ⊢ t ⇒ u ∷ Π A ^ rA ▹ B
               → Γ ⊢ a ∷ A ^ rA
               → Γ ⊢ t ∘ a ⇒ u ∘ a ∷ B [ a ]
  β-red        : ∀ {A B a t rA}
               → Γ     ⊢ A ^ rA
               → Γ ∙ A ^ rA ⊢ t ∷ B ^ !
               → Γ     ⊢ a ∷ A ^ rA
               → Γ     ⊢ (lam A ▹ t) ∘ a ⇒ t [ a ] ∷ B [ a ]
  natrec-subst : ∀ {z s n n′ F}
               → Γ ∙ ℕ ^ ! ⊢ F ^ !
               → Γ     ⊢ z ∷ F [ zero ] ^ !
               → Γ     ⊢ s ∷ Π ℕ ^ ! ▹ (F ^ ! ▹▹ F [ suc (var Nat.zero) ]↑) ^ !
               → Γ     ⊢ n ⇒ n′ ∷ ℕ
               → Γ     ⊢ natrec F z s n ⇒ natrec F z s n′ ∷ F [ n ]
  natrec-zero  : ∀ {z s F}
               → Γ ∙ ℕ ^ ! ⊢ F ^ !
               → Γ     ⊢ z ∷ F [ zero ] ^ !
               → Γ     ⊢ s ∷ Π ℕ ^ ! ▹ (F ^ ! ▹▹ F [ suc (var Nat.zero) ]↑) ^ !
               → Γ     ⊢ natrec F z s zero ⇒ z ∷ F [ zero ]
  natrec-suc   : ∀ {n z s F}
               → Γ     ⊢ n ∷ ℕ ^ !
               → Γ ∙ ℕ ^ ! ⊢ F ^ !
               → Γ     ⊢ z ∷ F [ zero ] ^ !
               → Γ     ⊢ s ∷ Π ℕ ^ ! ▹ (F ^ ! ▹▹ F [ suc (var Nat.zero) ]↑) ^ !
               → Γ     ⊢ natrec F z s (suc n) ⇒ (s ∘ n) ∘ (natrec F z s n)
                       ∷ F [ suc n ]
  Id-subst : ∀ {A A' t u}
            → Γ ⊢ A ⇒ A' ∷ U
            → Γ ⊢ t ∷ A ^ !
            → Γ ⊢ u ∷ A ^ !
            → Γ ⊢ Id A t u ⇒ Id A' t u ∷ SProp
  Id-ℕ-subst : ∀ {m m' n}
            → Γ ⊢ m ⇒ m' ∷ ℕ
            → Γ ⊢ n ∷ ℕ ^ !
            → Γ ⊢ Id ℕ m n ⇒ Id ℕ m' n ∷ SProp
  Id-ℕ-0-subst : ∀ {n n'}
            → Γ ⊢ n ⇒ n' ∷ ℕ
            → Γ ⊢ Id ℕ zero n ⇒ Id ℕ zero n' ∷ SProp
  Id-ℕ-S-subst : ∀ {m n n'}
            → Γ ⊢ m ∷ ℕ ^ !
            → Γ ⊢ n ⇒ n' ∷ ℕ
            → Γ ⊢ Id ℕ (suc m) n ⇒ Id ℕ (suc m) n' ∷ SProp
  Id-U-subst : ∀ {A A' B}
            → Γ ⊢ A ⇒ A' ∷ U
            → Γ ⊢ B ∷ U ^ !
            → Γ ⊢ Id U A B ⇒ Id U A' B ∷ SProp
  Id-U-ℕ-subst : ∀ {B B'}
            → Γ ⊢ B ⇒ B' ∷ U
            → Γ ⊢ Id U ℕ B ⇒ Id U ℕ B' ∷ SProp
  Id-U-Π-subst : ∀ {A rA P B B'}
            → Γ ⊢ A ∷ (Univ rA) ^ !
            → Γ ∙ A ^ rA ⊢ P ∷ U ^ !
            → Γ ⊢ B ⇒ B' ∷ U
            → Γ ⊢ Id U (Π A ^ rA ▹ P) B ⇒ Id U (Π A ^ rA ▹ P) B' ∷ SProp
  Id-Π : ∀ {A rA B t u}
         → Γ ⊢ A ^ rA
         → Γ ∙ A ^ rA ⊢ B ^ !
         → Γ ⊢ t ∷ (Π A ^ rA ▹ B) ^ !
         → Γ ⊢ u ∷ (Π A ^ rA ▹ B) ^ !
         → Γ ⊢ (Id (Π A ^ rA ▹ B) t u)
               ⇒ Π A ^ rA ▹ (Id B ((wk1 t) ∘ (var 0)) ((wk1 u) ∘ (var 0)))
               ∷ SProp
  Id-ℕ-00 : ⊢ Γ
          → Γ ⊢ (Id ℕ zero zero)
                ⇒ Unit
                ∷ SProp
  Id-ℕ-SS : ∀ {m n}
            → Γ ⊢ m ∷ ℕ ^ !
            → Γ ⊢ n ∷ ℕ ^ !
            → Γ ⊢ (Id ℕ (suc m) (suc n))
                  ⇒ (Id ℕ m n)
                  ∷ SProp
  Id-U-ΠΠ : ∀ {A A' rA B B'}
            → Γ ⊢ A ∷ (Univ rA) ^ !
            → Γ ∙ A ^ rA ⊢ B ∷ U ^ !
            → Γ ⊢ A' ∷ (Univ rA) ^ !
            → Γ ∙ A' ^ rA ⊢ B' ∷ U ^ !
            → Γ ⊢ (Id U (Π A ^ rA ▹ B) (Π A' ^ rA ▹ B'))
                  ⇒ Σ (Id (Univ rA) A A') ▹
                    (Π (wk1 A') ^ rA ▹ Id U
                      ((wk1d B) [ cast (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA) (wk1 (wk1 A)) (wk1 (wk1 A')) (var 1)) (var 0) ]↑)
                      (wk1d B'))
                  ∷ SProp
  Id-U-ℕℕ : ⊢ Γ
          → Γ ⊢ (Id U ℕ ℕ)
                ⇒ Unit
                ∷ SProp
  Id-SProp : ∀ {A B}
             → Γ ⊢ A ∷ SProp ^ !
             → Γ ⊢ B ∷ SProp ^ !
             → Γ ⊢ (Id SProp A B)
                   ⇒ (Σ (A ^ % ▹▹ B) ▹ ((wk1 B) ^ % ▹▹ (wk1 A)))
                   ∷ SProp
  Id-ℕ-0S : ∀ {t}
          → Γ ⊢ t ∷ ℕ ^ !
          → Γ ⊢ Id ℕ zero (suc t) ⇒ Empty ∷ SProp
  Id-ℕ-S0 : ∀ {t}
          → Γ ⊢ t ∷ ℕ ^ !
          → Γ ⊢ Id ℕ (suc t) zero ⇒ Empty ∷ SProp
  Id-U-ℕΠ : ∀ {A rA B}
          → Γ ⊢ A ∷ Univ rA ^ !
          → Γ ∙ A ^ rA ⊢ B ∷ U ^ !
          → Γ ⊢ Id U ℕ (Π A ^ rA ▹ B) ⇒ Empty ∷ SProp
  Id-U-Πℕ : ∀ {A rA B}
          → Γ ⊢ A ∷ Univ rA ^ !
          → Γ ∙ A ^ rA ⊢ B ∷ U ^ !
          → Γ ⊢ Id U (Π A ^ rA ▹ B) ℕ ⇒ Empty ∷ SProp
  cast-subst : ∀ {A A' B e t}
                → Γ ⊢ A ⇒ A' ∷ U
                → Γ ⊢ B ∷ U ^ !
                → Γ ⊢ e ∷ Id U A B ^ %
                → Γ ⊢ t ∷ A ^ !
                → Γ ⊢ cast A B e t ⇒ cast A' B e t ∷ B
  cast-ℕ-subst : ∀ {B B' e t}
                → Γ ⊢ B ⇒ B' ∷ U
                → Γ ⊢ e ∷ Id U ℕ B ^ %
                → Γ ⊢ t ∷ ℕ ^ !
                → Γ ⊢ cast ℕ B e t ⇒ cast ℕ B' e t ∷ B
  cast-Π-subst : ∀ {A rA P B B' e t}
                → Γ ⊢ A ∷ (Univ rA) ^ !
                → Γ ∙ A ^ rA ⊢ P ∷ U ^ !
                → Γ ⊢ B ⇒ B' ∷ U
                → Γ ⊢ e ∷ Id U (Π A ^ rA ▹ P) B ^ %
                → Γ ⊢ t ∷ (Π A ^ rA ▹ P) ^ !
                → Γ ⊢ cast (Π A ^ rA ▹ P) B e t ⇒ cast (Π A ^ rA ▹ P) B' e t ∷ B
  cast-Π : ∀ {A A' rA B B' e f}
           → Γ ⊢ A ∷ (Univ rA) ^ !
           → Γ ∙ A ^ rA ⊢ B ∷ U ^ !
           → Γ ⊢ A' ∷ (Univ rA) ^ !
           → Γ ∙ A' ^ rA ⊢ B' ∷ U ^ !
           → Γ ⊢ e ∷ Id U (Π A ^ rA ▹ B) (Π A' ^ rA ▹ B') ^ %
           → Γ ⊢ f ∷ (Π A ^ rA ▹ B) ^ !
           → Γ ⊢ (cast (Π A ^ rA ▹ B) (Π A' ^ rA ▹ B') e f)
             ⇒ (lam A' ▹
               let a = cast (wk1 A') (wk1 A) (Idsym (Univ rA) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) in
               cast (B [ a ]↑) B' ((snd (wk1 e)) ∘ (var 0)) ((wk1 f) ∘ a))
                 ∷ Π A' ^ rA ▹ B'
  cast-ℕ-0 : ∀ {e}
             → Γ ⊢ e ∷ Id U ℕ ℕ ^ %
             → Γ ⊢ cast ℕ ℕ e zero
                 ⇒ zero
                 ∷ ℕ
  cast-ℕ-S : ∀ {e n}
             → Γ ⊢ e ∷ Id U ℕ ℕ ^ %
             → Γ ⊢ n ∷ ℕ ^ !
             → Γ ⊢ cast ℕ ℕ e (suc n)
                 ⇒ suc (cast ℕ ℕ e n)
                 ∷ ℕ

-- Type reduction
data _⊢_⇒_^_ (Γ : Con Term) : Term → Term → Relevance → Set where
  univ : ∀ {A B r}
       → Γ ⊢ A ⇒ B ∷ (Univ r)
       → Γ ⊢ A ⇒ B ^ r

-- Term reduction closure
data _⊢_⇒*_∷_ (Γ : Con Term) : Term → Term → Term → Set where
  id  : ∀ {A t}
      → Γ ⊢ t ∷ A ^ !
      → Γ ⊢ t ⇒* t ∷ A
  _⇨_ : ∀ {A t t′ u}
      → Γ ⊢ t  ⇒  t′ ∷ A
      → Γ ⊢ t′ ⇒* u  ∷ A
      → Γ ⊢ t  ⇒* u  ∷ A

-- Type reduction closure
data _⊢_⇒*_^_ (Γ : Con Term) : Term → Term → Relevance → Set where
  id  : ∀ {A r}
      → Γ ⊢ A ^ r
      → Γ ⊢ A ⇒* A ^ r
  _⇨_ : ∀ {A A′ B r}
      → Γ ⊢ A  ⇒  A′ ^ r
      → Γ ⊢ A′ ⇒* B  ^ r
      → Γ ⊢ A  ⇒* B  ^ r

-- Type reduction to whnf
_⊢_↘_^_ : (Γ : Con Term) → Term → Term → Relevance → Set
Γ ⊢ A ↘ B ^ r = Γ ⊢ A ⇒* B ^ r × Whnf B

-- Term reduction to whnf
_⊢_↘_∷_ : (Γ : Con Term) → Term → Term → Term → Set
Γ ⊢ t ↘ u ∷ A = Γ ⊢ t ⇒* u ∷ A × Whnf u

-- Type equality with well-formed types
_⊢_:≡:_^_ : (Γ : Con Term) → Term → Term → Relevance → Set
Γ ⊢ A :≡: B ^ r = Γ ⊢ A ^ r × Γ ⊢ B ^ r × (Γ ⊢ A ≡ B ^ r)

-- Term equality with well-formed terms
_⊢_:≡:_∷_^_ : (Γ : Con Term) → Term → Term → Term → Relevance → Set
Γ ⊢ t :≡: u ∷ A ^ r = Γ ⊢ t ∷ A ^ r × Γ ⊢ u ∷ A ^ r × (Γ ⊢ t ≡ u ∷ A ^ r)

-- Type reduction closure with well-formed types
record _⊢_:⇒*:_^_ (Γ : Con Term) (A B : Term) (r : Relevance) : Set where
  constructor [_,_,_]
  field
    ⊢A : Γ ⊢ A ^ r
    ⊢B : Γ ⊢ B ^ r
    D  : Γ ⊢ A ⇒* B ^ r

open _⊢_:⇒*:_^_ using () renaming (D to red) public

-- Term reduction closure with well-formed terms
record _⊢_:⇒*:_∷_ (Γ : Con Term) (t u A : Term) : Set where
  constructor [_,_,_]
  field
    ⊢t : Γ ⊢ t ∷ A ^ !
    ⊢u : Γ ⊢ u ∷ A ^ !
    d  : Γ ⊢ t ⇒* u ∷ A

open _⊢_:⇒*:_∷_ using () renaming (d to redₜ) public

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
