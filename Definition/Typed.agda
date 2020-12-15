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

tt : Term
tt = lam Empty ▹ (Emptyrec Empty (var 0))

fst : (A B t : Term) → Term
fst A B t = sigmarec (wk1 A) (var 1) t

snd : (A B t : Term) → Term
snd A B t = sigmarec (B [ fst A B (var 0) ]↑) (var 0) t

ap : (A B f x y e : Term) → Term
ap A B f x y e = transp A (Id (wk1 B) (wk1 (f ∘ x)) ((wk1 f) ∘ (var 0))) x (Idrefl B (f ∘ x)) y e

Id_sym : (A x y e : Term) → Term
Id_sym A x y e = transp A (Id (wk1 A) (var 0) (wk1 x)) x (Idrefl A x) y e

Id_trans : (A x y z e f : Term) → Term
Id_trans A x y z e f = transp A (Id (wk1 A) (wk1 x) (var 0)) y e z f

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
    sigmarecⱼ : ∀ {F G A rA t u}
                → Γ ∙ (Σ F ▹ G) ^ % ⊢ A ^ rA
                → Γ ∙ F ^ % ∙ G ^ % ⊢ t ∷ A [ ⦅ var 0 , var 1 ⦆ ]↑↑ ^ rA
                → Γ ⊢ u ∷ Σ F ▹ G ^ %
                → Γ ⊢ sigmarec A t u ∷ A [ u ] ^ rA
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
          → Γ ⊢ t ∷ A ^ !
          → Γ ⊢ u ∷ A ^ !
          → Γ ⊢ Id A t u ∷ SProp ^ !
    Idreflⱼ : ∀ {A t}
              → Γ ⊢ t ∷ A ^ !
              → Γ ⊢ Idrefl A t ∷ (Id A t t) ^ %
    transpⱼ : ∀ {A P t s u e}
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
    cast_reflⱼ : ∀ {A t}
                 → Γ ⊢ A ^ !
                 → Γ ⊢ t ∷ A ^ !
                 → Γ ⊢ cast_refl A t ∷ (Id A t (cast A A (Idrefl U A) t)) ^ %
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
    refl        : ∀ {t A r}
                → Γ ⊢ t ∷ A ^ r
                → Γ ⊢ t ≡ t ∷ A ^ r
    sym         : ∀ {t u A r}
                → Γ ⊢ t ≡ u ∷ A ^ r
                → Γ ⊢ u ≡ t ∷ A ^ r
    trans       : ∀ {t u v A r}
                → Γ ⊢ t ≡ u ∷ A ^ r
                → Γ ⊢ u ≡ v ∷ A ^ r
                → Γ ⊢ t ≡ v ∷ A ^ r
    conv        : ∀ {A B t u r}
                → Γ ⊢ t ≡ u ∷ A ^ r
                → Γ ⊢ A ≡ B ^ r
                → Γ ⊢ t ≡ u ∷ B ^ r
    Π-cong      : ∀ {E F G H rF rG}
                → Γ     ⊢ F ^ rF
                → Γ     ⊢ F ≡ H       ∷ (Univ rF) ^ !
                → Γ ∙ F ^ rF ⊢ G ≡ E       ∷ (Univ rG) ^ !
                → Γ     ⊢ Π F ^ rF ▹ G ≡ Π H ^ rF ▹ E ∷ (Univ rG) ^ !
    app-cong    : ∀ {a b f g F G rF rG}
                → Γ ⊢ f ≡ g ∷ Π F ^ rF ▹ G ^ rG
                → Γ ⊢ a ≡ b ∷ F ^ rF
                → Γ ⊢ f ∘ a ≡ g ∘ b ∷ G [ a ] ^ rG
    β-red       : ∀ {a t F rF G rG}
                → Γ     ⊢ F ^ rF
                → Γ ∙ F ^ rF ⊢ t ∷ G ^ rG
                → Γ     ⊢ a ∷ F ^ rF
                → Γ     ⊢ (lam F ▹ t) ∘ a ≡ t [ a ] ∷ G [ a ] ^ rG
    η-eq        : ∀ {f g F rF G rG}
                → Γ     ⊢ F ^ rF
                → Γ     ⊢ f ∷ Π F ^ rF ▹ G ^ rG
                → Γ     ⊢ g ∷ Π F ^ rF ▹ G ^ rG
                → Γ ∙ F ^ rF ⊢ wk1 f ∘ var Nat.zero ≡ wk1 g ∘ var Nat.zero ∷ G ^ rG
                → Γ     ⊢ f ≡ g ∷ Π F ^ rF ▹ G ^ rG
    suc-cong    : ∀ {m n}
                → Γ ⊢ m ≡ n ∷ ℕ ^ !
                → Γ ⊢ suc m ≡ suc n ∷ ℕ ^ !
    natrec-cong : ∀ {z z′ s s′ n n′ F F′ rF}
                → Γ ∙ ℕ ^ ! ⊢ F ≡ F′ ^ rF
                → Γ     ⊢ z ≡ z′ ∷ F [ zero ] ^ rF
                → Γ     ⊢ s ≡ s′ ∷ Π ℕ ^ ! ▹ (F ^ rF ▹▹ F [ suc (var Nat.zero) ]↑) ^ rF
                → Γ     ⊢ n ≡ n′ ∷ ℕ ^ !
                → Γ     ⊢ natrec F z s n ≡ natrec F′ z′ s′ n′ ∷ F [ n ] ^ rF
    natrec-zero : ∀ {z s F rF}
                → Γ ∙ ℕ ^ ! ⊢ F ^ rF
                → Γ     ⊢ z ∷ F [ zero ] ^ rF
                → Γ     ⊢ s ∷ Π ℕ ^ ! ▹ (F ^ rF ▹▹ F [ suc (var Nat.zero) ]↑) ^ rF
                → Γ     ⊢ natrec F z s zero ≡ z ∷ F [ zero ] ^ rF
    natrec-suc  : ∀ {n z s F rF}
                → Γ     ⊢ n ∷ ℕ ^ !
                → Γ ∙ ℕ ^ ! ⊢ F ^ rF
                → Γ     ⊢ z ∷ F [ zero ] ^ rF
                → Γ     ⊢ s ∷ Π ℕ ^ ! ▹ (F ^ rF ▹▹ F [ suc (var Nat.zero) ]↑) ^ rF
                → Γ     ⊢ natrec F z s (suc n) ≡ (s ∘ n) ∘ (natrec F z s n)
                        ∷ F [ suc n ] ^ rF
    sigmarec-cong : ∀ {F G A A' rA t t' u u'}
                  → Γ ∙ (Σ F ▹ G) ^ % ⊢ A ≡ A' ^ rA
                  → Γ ∙ F ^ % ∙ G ^ % ⊢ t ≡ t' ∷ A [ ⦅ var 0 , var 1 ⦆ ]↑↑ ^ rA
                  → Γ ⊢ u ≡ u' ∷ Σ F ▹ G ^ %
                  → Γ ⊢ sigmarec A t u ≡ sigmarec A' t' u' ∷ A [ u ] ^ rA
    sigmarec-pair : ∀ {F G A rA t u v}
                    → Γ ∙ (Σ F ▹ G) ^ % ⊢ A ^ rA
                    → Γ ∙ F ^ % ∙ G ^ % ⊢ t ∷ A [ ⦅ var 0 , var 1 ⦆ ]↑↑ ^ rA
                    → Γ ⊢ u ∷ F ^ %
                    → Γ ⊢ v ∷ G [ t ] ^ %
                    → Γ ⊢ sigmarec A t ⦅ u , v ⦆
                        ≡ t [ v ] [ u ]
                        ∷ A [ ⦅ u , v ⦆ ] ^ rA
    Emptyrec-cong : ∀ {A A' e e' r}
                → Γ ⊢ A ≡ A' ^ r
                → Γ ⊢ e ≡ e' ∷ Empty ^ %
                → Γ ⊢ Emptyrec A e ≡ Emptyrec A' e' ∷ A ^ r
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
           → Γ ⊢ A ∷ (Univ rA) ^ !
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
                        ((wk (lift (step id)) B) [ cast (wk1 (wk1 A')) (wk1 (wk1 A)) (Id_sym (Univ rA) (wk1 (wk1 A)) (wk1 (wk1 A')) (var 1)) (var 0) ]↑)
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
                 let fstId = Id (Univ rA) (wk1 A) (wk1 A') in
                 let sndId = Π (wk1 (wk1 A)) ^ rA ▹ Id U ((wk (lift (step (step id))) B) [ cast (wk1 (wk1 (wk1 A'))) (wk1 (wk1 (wk1 A))) (Id_sym (Univ rA) (wk1 (wk1 (wk1 A))) (wk1 (wk1 (wk1 A'))) (var 1)) (var 0) ]) (wk (lift (step (step id))) B') in
                 let a = cast (wk1 A') (wk1 A) (Id_sym (Univ rA) (wk1 A) (wk1 A') (fst fstId sndId (wk1 e))) (var 0) in
                 cast (B [ a ]↑) B' ((snd fstId sndId (wk1 e)) ∘ (var 0)) ((wk1 f) ∘ a))
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
    -- Id-U-ΠΠ-alternative : ∀ {A A' rA B B'}
    --           → Γ ⊢ A ∷ (Univ rA) ^ !
    --           → Γ ∙ A ^ rA ⊢ B ∷ U ^ !
    --           → Γ ⊢ A' ∷ (Univ rA) ^ !
    --           → Γ ∙ A ^ rA ⊢ B ∷ U ^ !
    --           → Γ ⊢ (Id U (Π A ^ rA ▹ B) (Π A' ^ rA ▹ B'))
    --                 ≡ Σ (Id (Univ rA) A A') ▹
    --                   (Π (wk1 A) ^ rA ▹ Id U
    --                     (wk (lift (step id)) B)
    --                     ((wk (lift (step id)) B') [ cast (wk1 (wk1 A)) (wk1 (wk1 A')) (var 1) (var 0) ]↑))
    --               ∷ SProp ^ !
    -- Id-ℕ-S0 : ∀ {n}
    --           → Γ ⊢ n ∷ ℕ ^ !
    --           → Γ ⊢ (Id ℕ (suc n) zero)
    --                 ≡ Empty
    --                 ∷ SProp ^ !
    -- Id-ℕ-0S : ∀ {n}
    --           → Γ ⊢ n ∷ ℕ ^ !
    --           → Γ ⊢ (Id ℕ zero (suc n))
    --                 ≡ Empty
    --                 ∷ SProp ^ !
    -- Id-U-ΠΠ%! : ∀ {A A' B B'}
    --             → Γ ⊢ A ∷ SProp ^ !
    --             → Γ ∙ A ^ % ⊢ B ∷ U ^ !
    --             → Γ ⊢ A' ∷ U ^ !
    --             → Γ ∙ A ^ ! ⊢ B ∷ U ^ !
    --             → Γ ⊢ (Id U (Π A ^ % ▹ B) (Π A' ^ ! ▹ B'))
    --                   ≡ Empty
    --                   ∷ SProp ^ !
    -- Id-U-ΠΠ!% : ∀ {A A' B B'}
    --             → Γ ⊢ A ∷ SProp ^ !
    --             → Γ ∙ A ^ ! ⊢ B ∷ U ^ !
    --             → Γ ⊢ A' ∷ U ^ !
    --             → Γ ∙ A ^ % ⊢ B ∷ U ^ !
    --             → Γ ⊢ (Id U (Π A ^ ! ▹ B) (Π A' ^ % ▹ B'))
    --                   ≡ Empty
    --                   ∷ SProp ^ !
    -- Id-U-Πℕ : ∀ {A rA B}
    --           → Γ ⊢ A ∷ (Univ rA) ^ !
    --           → Γ ∙ A ^ rA ⊢ B ∷ U ^ !
    --           → Γ ⊢ (Id U (Π A ^ rA ▹ B) ℕ)
    --                 ≡ Empty
    --                 ∷ SProp ^ !
    -- Id-U-ℕΠ : ∀ {A rA B}
    --           → Γ ⊢ A ∷ (Univ rA) ^ !
    --           → Γ ∙ A ^ rA ⊢ B ∷ U ^ !
    --           → Γ ⊢ (Id U ℕ (Π A ^ rA ▹ B))
    --                 ≡ Empty
    --                 ∷ SProp ^ !

-- Term reduction
data _⊢_⇒_∷_^_ (Γ : Con Term) : Term → Term → Term → Relevance → Set where
  conv         : ∀ {A B t u r}
               → Γ ⊢ t ⇒ u ∷ A ^ r
               → Γ ⊢ A ≡ B ^ r
               → Γ ⊢ t ⇒ u ∷ B ^ r
  app-subst    : ∀ {A B t u a rA rB}
               → Γ ⊢ t ⇒ u ∷ Π A ^ rA ▹ B ^ rB
               → Γ ⊢ a ∷ A ^ rA
               → Γ ⊢ t ∘ a ⇒ u ∘ a ∷ B [ a ] ^ rB
  β-red        : ∀ {A B a t rA rB}
               → Γ     ⊢ A ^ rA
               → Γ ∙ A ^ rA ⊢ t ∷ B ^ rB
               → Γ     ⊢ a ∷ A ^ rA
               → Γ     ⊢ (lam A ▹ t) ∘ a ⇒ t [ a ] ∷ B [ a ] ^ rB
  natrec-subst : ∀ {z s n n′ F rF}
               → Γ ∙ ℕ ^ ! ⊢ F ^ rF
               → Γ     ⊢ z ∷ F [ zero ] ^ rF
               → Γ     ⊢ s ∷ Π ℕ ^ ! ▹ (F ^ rF ▹▹ F [ suc (var Nat.zero) ]↑) ^ rF
               → Γ     ⊢ n ⇒ n′ ∷ ℕ ^ !
               → Γ     ⊢ natrec F z s n ⇒ natrec F z s n′ ∷ F [ n ] ^ rF
  natrec-zero  : ∀ {z s F rF}
               → Γ ∙ ℕ ^ ! ⊢ F ^ rF
               → Γ     ⊢ z ∷ F [ zero ] ^ rF
               → Γ     ⊢ s ∷ Π ℕ ^ ! ▹ (F ^ rF ▹▹ F [ suc (var Nat.zero) ]↑) ^ rF
               → Γ     ⊢ natrec F z s zero ⇒ z ∷ F [ zero ] ^ rF
  natrec-suc   : ∀ {n z s F rF}
               → Γ     ⊢ n ∷ ℕ ^ !
               → Γ ∙ ℕ ^ ! ⊢ F ^ rF
               → Γ     ⊢ z ∷ F [ zero ] ^ rF
               → Γ     ⊢ s ∷ Π ℕ ^ ! ▹ (F ^ rF ▹▹ F [ suc (var Nat.zero) ]↑) ^ rF
               → Γ     ⊢ natrec F z s (suc n) ⇒ (s ∘ n) ∘ (natrec F z s n)
                       ∷ F [ suc n ] ^ rF
  sigmarec-subst : ∀ {F G A rA t u u'}
                  → Γ ∙ (Σ F ▹ G) ^ % ⊢ A ^ rA
                  → Γ ∙ F ^ % ∙ G ^ % ⊢ t ∷ A [ ⦅ var 0 , var 1 ⦆ ]↑↑ ^ rA
                  → Γ ⊢ u ⇒ u' ∷ Σ F ▹ G ^ %
                  → Γ ⊢ sigmarec A t u ⇒ sigmarec A t u' ∷ A [ u ] ^ rA
  sigmarec-pair : ∀ {F G A rA t u v}
                  → Γ ∙ (Σ F ▹ G) ^ % ⊢ A ^ rA
                  → Γ ∙ F ^ % ∙ G ^ % ⊢ t ∷ A [ ⦅ var 0 , var 1 ⦆ ]↑↑ ^ rA
                  → Γ ⊢ u ∷ F ^ %
                  → Γ ⊢ v ∷ G [ t ] ^ %
                  → Γ ⊢ sigmarec A t ⦅ u , v ⦆
                      ⇒ t [ v ] [ u ]
                      ∷ A [ ⦅ u , v ⦆ ] ^ rA
  Emptyrec-subst : ∀ {n n′ A r}
               → Γ ⊢ A ^ r
               → Γ     ⊢ n ⇒ n′ ∷ Empty ^ %
               → Γ     ⊢ Emptyrec A n ⇒ Emptyrec A n′ ∷ A ^ r
  Id-subst : ∀ {A A' t u}
            → Γ ⊢ t ∷ A ^ !
            → Γ ⊢ u ∷ A ^ !
            → Γ ⊢ A ⇒ A' ∷ U ^ !
            → Γ ⊢ Id A t u ⇒ Id A' t u ∷ SProp ^ !
  Id-ℕ-subst1 : ∀ {m m' n}
            → Γ ⊢ m ⇒ m' ∷ ℕ ^ !
            → Γ ⊢ n ∷ ℕ ^ !
            → Γ ⊢ Id ℕ m n ⇒ Id ℕ m' n ∷ SProp ^ !
  Id-ℕ-subst2 : ∀ {m n n'}
            → Γ ⊢ m ∷ ℕ ^ !
            → Γ ⊢ n ⇒ n' ∷ ℕ ^ !
            → Γ ⊢ Id ℕ m n ⇒ Id ℕ m n' ∷ SProp ^ !
  Id-U-subst1 : ∀ {A A' B}
            → Γ ⊢ A ⇒ A' ∷ U ^ !
            → Γ ⊢ B ∷ U ^ !
            → Γ ⊢ Id U A B ⇒ Id U A' B ∷ SProp ^ !
  Id-U-subst2 : ∀ {A B B'}
            → Γ ⊢ A ∷ U ^ !
            → Γ ⊢ B ⇒ B' ∷ U ^ !
            → Γ ⊢ Id U A B ⇒ Id U A B' ∷ SProp ^ !
  Id-Π : ∀ {A rA B t u}
         → Γ ⊢ A ∷ (Univ rA) ^ !
         → Γ ∙ A ^ rA ⊢ B ^ !
         → Γ ⊢ t ∷ (Π A ^ rA ▹ B) ^ !
         → Γ ⊢ u ∷ (Π A ^ rA ▹ B) ^ !
         → Γ ⊢ (Id (Π A ^ rA ▹ B) t u)
               ⇒ Π A ^ rA ▹ (Id B ((wk1 t) ∘ (var 0)) ((wk1 u) ∘ (var 0)))
               ∷ SProp ^ !
  Id-ℕ-00 : ⊢ Γ
          → Γ ⊢ (Id ℕ zero zero)
                ⇒ Unit
                ∷ SProp ^ !
  Id-ℕ-SS : ∀ {m n}
            → Γ ⊢ m ∷ ℕ ^ !
            → Γ ⊢ n ∷ ℕ ^ !
            → Γ ⊢ (Id ℕ (suc m) (suc n))
                  ⇒ (Id ℕ m n)
                  ∷ SProp ^ !
  Id-U-ΠΠ : ∀ {A A' rA B B'}
            → Γ ⊢ A ∷ (Univ rA) ^ !
            → Γ ∙ A ^ rA ⊢ B ∷ U ^ !
            → Γ ⊢ A' ∷ (Univ rA) ^ !
            → Γ ∙ A' ^ rA ⊢ B' ∷ U ^ !
            → Γ ⊢ (Id U (Π A ^ rA ▹ B) (Π A' ^ rA ▹ B'))
                  ⇒ Σ (Id (Univ rA) A A') ▹
                    (Π (wk1 A') ^ rA ▹ Id U
                      ((wk (lift (step id)) B) [ cast (wk1 (wk1 A')) (wk1 (wk1 A)) (Id_sym (Univ rA) (wk1 (wk1 A)) (wk1 (wk1 A')) (var 1)) (var 0) ]↑)
                      (wk (lift (step id)) B'))
                  ∷ SProp ^ !
  Id-U-ℕℕ : ⊢ Γ
          → Γ ⊢ (Id U ℕ ℕ)
                ⇒ Unit
                ∷ SProp ^ !
  Id-SProp : ∀ {A B}
             → Γ ⊢ A ∷ SProp ^ !
             → Γ ⊢ B ∷ SProp ^ !
             → Γ ⊢ (Id SProp A B)
                   ⇒ (Σ (A ^ % ▹▹ B) ▹ ((wk1 B) ^ % ▹▹ (wk1 A)))
                   ∷ SProp ^ !
  cast-subst1 : ∀ {A A' B e t}
                → Γ ⊢ A ⇒ A' ∷ U ^ !
                → Γ ⊢ B ∷ U ^ !
                → Γ ⊢ e ∷ Id U A B ^ %
                → Γ ⊢ t ∷ A ^ !
                → Γ ⊢ cast A B e t ⇒ cast A' B e t ∷ B ^ !
  cast-subst2 : ∀ {A B B' e t}
                → Γ ⊢ A ∷ U ^ !
                → Γ ⊢ B ⇒ B' ∷ U ^ !
                → Γ ⊢ e ∷ Id U A B ^ %
                → Γ ⊢ t ∷ A ^ !
                → Γ ⊢ cast A B e t ⇒ cast A B' e t ∷ B ^ !
  cast-Π : ∀ {A A' rA B B' e f}
           → Γ ⊢ A ∷ (Univ rA) ^ !
           → Γ ∙ A ^ rA ⊢ B ∷ U ^ !
           → Γ ⊢ A' ∷ (Univ rA) ^ !
           → Γ ∙ A' ^ rA ⊢ B' ∷ U ^ !
           → Γ ⊢ e ∷ Id U (Π A ^ rA ▹ B) (Π A' ^ rA ▹ B') ^ %
           → Γ ⊢ f ∷ (Π A ^ rA ▹ B) ^ !
           → Γ ⊢ (cast (Π A ^ rA ▹ B) (Π A' ^ rA ▹ B') e f)
             ⇒ (lam A' ▹
               let fstId = Id (Univ rA) (wk1 A) (wk1 A') in
               let sndId = Π (wk1 (wk1 A)) ^ rA ▹ Id U ((wk (lift (step (step id))) B) [ cast (wk1 (wk1 (wk1 A'))) (wk1 (wk1 (wk1 A))) (Id_sym (Univ rA) (wk1 (wk1 (wk1 A))) (wk1 (wk1 (wk1 A'))) (var 1)) (var 0) ]) (wk (lift (step (step id))) B') in
               let a = cast (wk1 A') (wk1 A) (Id_sym (Univ rA) (wk1 A) (wk1 A') (fst fstId sndId (wk1 e))) (var 0) in
               cast (B [ a ]↑) B' ((snd fstId sndId (wk1 e)) ∘ (var 0)) ((wk1 f) ∘ a))
                 ∷ Π A' ^ rA ▹ B' ^ !
  cast-ℕ-0 : ∀ {e}
             → Γ ⊢ e ∷ Id U ℕ ℕ ^ %
             → Γ ⊢ cast ℕ ℕ e zero
                 ⇒ zero
                 ∷ ℕ ^ !
  cast-ℕ-S : ∀ {e n}
             → Γ ⊢ e ∷ Id U ℕ ℕ ^ %
             → Γ ⊢ n ∷ ℕ ^ !
             → Γ ⊢ cast ℕ ℕ e (suc n)
                 ⇒ suc (cast ℕ ℕ e n)
                 ∷ ℕ ^ !
  -- Id-U-ΠΠ-alternative : ∀ {A A' rA B B'}
  --           → Γ ⊢ A ∷ (Univ rA) ^ !
  --           → Γ ∙ A ^ rA ⊢ B ∷ U ^ !
  --           → Γ ⊢ A' ∷ (Univ rA) ^ !
  --           → Γ ∙ A ^ rA ⊢ B ∷ U ^ !
  --           → Γ ⊢ (Id U (Π A ^ rA ▹ B) (Π A' ^ rA ▹ B'))
  --                 ⇒ Σ (Id (Univ rA) A A') ▹
  --                   (Π (wk1 A) ^ rA ▹ Id U
  --                     (wk (lift (step id)) B)
  --                     ((wk (lift (step id)) B') [ cast (wk1 (wk1 A)) (wk1 (wk1 A')) (var 1) (var 0) ]↑))
  --               ∷ SProp ^ !
  -- Id-ℕ-S0 : ∀ {n}
  --           → Γ ⊢ n ∷ ℕ ^ !
  --           → Γ ⊢ (Id ℕ (suc n) zero)
  --                 ⇒ Empty
  --                 ∷ SProp ^ !
  -- Id-ℕ-0S : ∀ {n}
  --           → Γ ⊢ n ∷ ℕ ^ !
  --           → Γ ⊢ (Id ℕ zero (suc n))
  --                 ⇒ Empty
  --                 ∷ SProp ^ !
  -- Id-U-ΠΠ%! : ∀ {A A' B B'}
  --             → Γ ⊢ A ∷ SProp ^ !
  --             → Γ ∙ A ^ % ⊢ B ∷ U ^ !
  --             → Γ ⊢ A' ∷ U ^ !
  --             → Γ ∙ A ^ ! ⊢ B ∷ U ^ !
  --             → Γ ⊢ (Id U (Π A ^ % ▹ B) (Π A' ^ ! ▹ B'))
  --                   ⇒ Empty
  --                   ∷ SProp ^ !
  -- Id-U-ΠΠ!% : ∀ {A A' B B'}
  --             → Γ ⊢ A ∷ SProp ^ !
  --             → Γ ∙ A ^ ! ⊢ B ∷ U ^ !
  --             → Γ ⊢ A' ∷ U ^ !
  --             → Γ ∙ A ^ % ⊢ B ∷ U ^ !
  --             → Γ ⊢ (Id U (Π A ^ ! ▹ B) (Π A' ^ % ▹ B'))
  --                   ⇒ Empty
  --                   ∷ SProp ^ !
  -- Id-U-Πℕ : ∀ {A rA B}
  --           → Γ ⊢ A ∷ (Univ rA) ^ !
  --           → Γ ∙ A ^ rA ⊢ B ∷ U ^ !
  --           → Γ ⊢ (Id U (Π A ^ rA ▹ B) ℕ)
  --                 ⇒ Empty
  --                 ∷ SProp ^ !
  -- Id-U-ℕΠ : ∀ {A rA B}
  --           → Γ ⊢ A ∷ (Univ rA) ^ !
  --           → Γ ∙ A ^ rA ⊢ B ∷ U ^ !
  --           → Γ ⊢ (Id U ℕ (Π A ^ rA ▹ B))
  --                 ⇒ Empty
  --                 ∷ SProp ^ !

-- Type reduction
data _⊢_⇒_^_ (Γ : Con Term) : Term → Term → Relevance → Set where
  univ : ∀ {A B r}
       → Γ ⊢ A ⇒ B ∷ (Univ r) ^ !
       → Γ ⊢ A ⇒ B ^ r

-- Term reduction closure
data _⊢_⇒*_∷_^_ (Γ : Con Term) : Term → Term → Term → Relevance → Set where
  id  : ∀ {A t r}
      → Γ ⊢ t ∷ A ^ r
      → Γ ⊢ t ⇒* t ∷ A ^ r
  _⇨_ : ∀ {A t t′ u r}
      → Γ ⊢ t  ⇒  t′ ∷ A ^ r
      → Γ ⊢ t′ ⇒* u  ∷ A ^ r
      → Γ ⊢ t  ⇒* u  ∷ A ^ r

-- Type reduction closure
data _⊢_⇒*_^_ (Γ : Con Term) : Term → Term → Relevance → Set where
  id  : ∀ {A r}
      → Γ ⊢ A ^ r
      → Γ ⊢ A ⇒* A ^ r
  _⇨_ : ∀ {A A′ B r}
      → Γ ⊢ A  ⇒  A′ ^ r
      → Γ ⊢ A′ ⇒* B ^ r
      → Γ ⊢ A  ⇒* B ^ r

-- Type reduction to whnf
_⊢_↘_^_ : (Γ : Con Term) → Term → Term → Relevance → Set
Γ ⊢ A ↘ B ^ r = Γ ⊢ A ⇒* B ^ r × Whnf B

-- Term reduction to whnf
_⊢_↘_∷_^_ : (Γ : Con Term) → Term → Term → Term → Relevance → Set
Γ ⊢ t ↘ u ∷ A ^ r = Γ ⊢ t ⇒* u ∷ A ^ r × Whnf u

-- Type eqaulity with well-formed types
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
record _⊢_:⇒*:_∷_^_ (Γ : Con Term) (t u A : Term) (r : Relevance) : Set where
  constructor [_,_,_]
  field
    ⊢t : Γ ⊢ t ∷ A ^ r
    ⊢u : Γ ⊢ u ∷ A ^ r
    d  : Γ ⊢ t ⇒* u ∷ A ^ r

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


-- Trying to type the reduction lemmas

-- Unitⱼ : {Γ : Con Term}
--         → ⊢ Γ
--         → Γ ⊢ Unit ∷ SProp ^ !
-- Unitⱼ {Γ} Γε = Πⱼ (Emptyⱼ Γε) ▹ Emptyⱼ (Γε ∙ Emptyⱼ Γε)

-- ttⱼ : {Γ : Con Term}
--       → ⊢ Γ
--       → Γ ⊢ tt ∷ Unit ^ %
-- ttⱼ {Γ} Γε = lamⱼ (Emptyⱼ Γε) (Emptyrecⱼ (Emptyⱼ (Γε ∙ Emptyⱼ Γε)) (var (Γε ∙ Emptyⱼ Γε) here))

-- fstⱼ : {Γ : Con Term} {A B t : Term}
--        → ⊢ Γ
--        → Γ ⊢ A ^ %
--        → Γ ∙ A ^ % ⊢ B ^ %
--        → Γ ⊢ t ∷ Σ A ▹ B ^ %
--        → Γ ⊢ fst A B t ∷ A ^ %
-- fstⱼ {Γ} {A} {B} {t} Γε Aε Bε tε
--   = PE.subst (λ (z : Term) → Γ ⊢ fst A B t ∷ z ^ %) (wk[] A t)
--     (sigmarecⱼ {!!}
--       (var (Γε ∙ Aε ∙ Bε)
--       (PE.subst (λ z → 1 ∷ z ^ % ∈ (Γ ∙ A ^ % ∙ B ^ %))
--         (PE.sym (wk[]↑↑ A ⦅ var 0 , var 1 ⦆))
--         (there here)))
--       tε)
--   where
--     wk[] : (A t : Term) → wk1 A [ t ] PE.≡ A
--     wk[] = {!!}

--     wk[]↑↑ : (A t : Term) → wk1 A [ t ]↑↑ PE.≡ wk1 (wk1 A)
--     wk[]↑↑ = {!!}

-- sndⱼ : {Γ : Con Term} {A B t : Term}
--        → ⊢ Γ
--        → Γ ⊢ A ^ %
--        → Γ ∙ A ^ % ⊢ B ^ %
--        → Γ ⊢ t ∷ Σ A ▹ B ^ %
--        → Γ ⊢ snd A B t ∷ (B [ fst A B t ]) ^ %
-- sndⱼ {Γ} {A} {B} {t} Γε Aε Bε tε
--   = PE.subst (λ (z : Term) → Γ ⊢ snd A B t ∷ z ^ %) ([]↑[] t)
--     (sigmarecⱼ {!!} {!!} tε)
--   where
--     []↑[] : (t : Term) → (B [ fst A B (var 0) ]↑) [ t ] PE.≡ B [ fst A B t ]
--     []↑[] = {!!}

-- apⱼ : {Γ : Con Term} {A B f x y e : Term}
--       → ⊢ Γ
--       → Γ ⊢ A ^ !
--       → Γ ⊢ B ^ !
--       → Γ ⊢ x ∷ A ^ !
--       → Γ ⊢ y ∷ A ^ !
--       → Γ ⊢ e ∷ Id A x y ^ %
--       → Γ ⊢ ap A B f x y e ∷ Id B (f ∘ x) (f ∘ y) ^ %
-- apⱼ {Γ} {A} {B} {f} {x} {y} {e} Γε Aε Bε xε yε eε =
--   {!!}
--   where
--     wk[] : (A t : Term) → wk1 A [ t ] PE.≡ A
--     wk[] = {!!}

--     aux : Γ ⊢ ap A B f x y e ∷ Id (wk1 B [ y ]) (wk1 (f ∘ x) [ y ]) (wk1 f [ y ] ∘ y) ^ %
--     aux = transpⱼ (Idⱼ ({!!} ∘ⱼ {!!}) {!? ∘ⱼ ?!}) xε {!!} yε eε
