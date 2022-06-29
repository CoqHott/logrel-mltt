{-# OPTIONS --safe #-}

module Definition.Typed.NonParanoidTyping where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.Inversion
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.RelevanceUnicity

open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.Empty
import Tools.PropositionalEquality as PE

infixl 30 _∙_
infix 30 Πⱼ_▹_▹_▹_

data SimpleCon (A : Set) : Set where
  ε   : SimpleCon A               -- Empty context.
  _∙_ : SimpleCon A → A → SimpleCon A  -- Context extension.

-- Well-typed variables
data _∷_∈∈_ : (x : Nat) (A : Term) (Γ : SimpleCon Term) → Set where
  here  : ∀ {Γ A}                     →         0 ∷ wk1 A ∈∈ (Γ ∙ A )
  there : ∀ {Γ A B x} (h : x ∷ A ∈∈ Γ) → Nat.suc x ∷ wk1 A ∈∈ (Γ ∙ B)

mutual
  -- Well-formed context
  data ⊢⊢_ : SimpleCon Term → Set where
    ε   : ⊢⊢ ε
    _∙_ : ∀ {Γ A}
        → ⊢⊢ Γ
        → Γ ⊢⊢ A 
        → ⊢⊢ Γ ∙ A

  -- Well-formed type
  data _⊢⊢_ (Γ : SimpleCon Term) : Term → Set where
    Uⱼ    : ∀ {r} → ⊢⊢ Γ → Γ ⊢⊢ Univ r ¹ 
    univ : ∀ {A r l}
         → Γ ⊢⊢ A ∷ Univ r l
         → Γ ⊢⊢ A 

  -- Well-formed term of a type
  data _⊢⊢_∷_ (Γ : SimpleCon Term) : Term → Term → Set where
    univ : ∀ {r l l'}
         → l < l'
         → ⊢⊢ Γ
         → Γ ⊢⊢ (Univ r l) ∷ (Univ ! l')
    ℕⱼ      : ⊢⊢ Γ → Γ ⊢⊢ ℕ ∷ U ⁰
    Emptyⱼ : ⊢⊢ Γ → Γ ⊢⊢ sEmpty ∷ SProp
    Πⱼ_▹_▹_▹_ : ∀ {F rF lF G lG r l}
           → (r PE.≡ ! → lF ≤ l × lG ≤ l)
           → (r PE.≡ % → lG PE.≡ ⁰ × l PE.≡ ⁰)
           → Γ     ⊢⊢ F ∷ Univ rF lF
           → Γ ∙ F ⊢⊢ G ∷ Univ r lG
           → Γ     ⊢⊢ Π F ^ rF ° lF ▹ G ° lG ° l ^ r ∷ (Univ r l) 
    ∃ⱼ_▹_ : ∀ {F G}
            → Γ ⊢⊢ F ∷ SProp
            → Γ ∙ F ⊢⊢ G ∷ SProp
            → Γ ⊢⊢ ∃ F ▹ G ∷ SProp
    var    : ∀ {A x}
           → ⊢⊢ Γ
           → x ∷ A ∈∈ Γ
           → Γ ⊢⊢ var x ∷ A
    lamⱼ    : ∀ {F r l rF lF G lG t}
           → (r PE.≡ ! → lF ≤ l × lG ≤ l)
           → (r PE.≡ % → lG PE.≡ ⁰ × l PE.≡ ⁰)
           → Γ ∙ F ⊢⊢ t ∷ G
           → Γ     ⊢⊢ lam F ▹ t ^ l ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ r
    _∘ⱼ_    : ∀ {g a F rF lF G lG r lΠ}
           → Γ ⊢⊢     g ∷ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ r
           → Γ ⊢⊢     a ∷ F 
           → Γ ⊢⊢ g ∘ a ^ lΠ ∷ G [ a ] 
    ⦅_,_,_⦆ⱼ : ∀ {F G t u}
             → Γ ∙ F ⊢⊢ G
             → Γ ⊢⊢ t ∷ F
             → Γ ⊢⊢ u ∷ G [ t ]
             → Γ ⊢⊢ ⦅ G , t , u ⦆ ∷ (∃ F ▹ G)
    fstⱼ : ∀ {F G t}
           → Γ ⊢⊢ t ∷ (∃ F ▹ G)
           → Γ ⊢⊢ fst t ∷ F
    sndⱼ : ∀ {F G t}
           → Γ ⊢⊢ t ∷ (∃ F ▹ G)
           → Γ ⊢⊢ snd t ∷ G [ fst t ]
    zeroⱼ   : ⊢⊢ Γ
           → Γ ⊢⊢ zero ∷ ℕ
    sucⱼ    : ∀ {n}
           → Γ ⊢⊢ n ∷ ℕ
           → Γ ⊢⊢ suc n ∷ ℕ
    natrecⱼ : ∀ {G rG lG s z n}
           → Γ ∙ ℕ ⊢⊢ G
           → Γ       ⊢⊢ z ∷ G [ zero ]
           → Γ       ⊢⊢ s ∷ Π ℕ ^ ! ° ⁰ ▹ (G ^ rG ° lG ▹▹ G [ suc (var Nat.zero) ]↑ ° lG ° lG ^ rG) ° lG ° lG ^ rG
           → Γ       ⊢⊢ n ∷ ℕ
           → Γ       ⊢⊢ natrec lG G z s n ∷ G [ n ]
    Emptyrecⱼ : ∀ {A lA e}
           → Γ ⊢⊢ A → Γ ⊢⊢ e ∷ sEmpty -> Γ ⊢⊢ Emptyrec lA ⁰ A e ∷ A
    Idⱼ : ∀ {A t u}
          → Γ ⊢⊢ t ∷ A
          → Γ ⊢⊢ u ∷ A
          → Γ ⊢⊢ Id A t u ∷ SProp
    Idreflⱼ : ∀ {A t}
              → Γ ⊢⊢ t ∷ A
              → Γ ⊢⊢ Idrefl A t ∷ (Id A t t)
    transpⱼ : ∀ {A P t s u e}
              → Γ ∙ A ⊢⊢ P
              → Γ ⊢⊢ t ∷ A
              → Γ ⊢⊢ s ∷ P [ t ]
              → Γ ⊢⊢ u ∷ A
              → Γ ⊢⊢ e ∷ (Id A t u)
              → Γ ⊢⊢ transp A P t s u e ∷ P [ u ]
    castⱼ : ∀ {A B r e t}
            → Γ ⊢⊢ e ∷ (Id (Univ r ⁰) A B)
            → Γ ⊢⊢ t ∷ A
            → Γ ⊢⊢ cast ⁰ A B e t ∷ B
    castreflⱼ : ∀ {A t}
                 → Γ ⊢⊢ t ∷ A
                 → Γ ⊢⊢ castrefl A t ∷ (Id A t (cast ⁰ A A (Idrefl (U ⁰) A) t))
    conv   : ∀ {t A B}
           → Γ ⊢⊢ t ∷ A
           → Γ ⊢⊢ A ≡ B
           → Γ ⊢⊢ t ∷ B

  -- Type equality
  data _⊢⊢_≡_ (Γ : SimpleCon Term) : Term → Term → Set where
    univ   : ∀ {A B r l}
           → Γ ⊢⊢ A ≡ B ∷ (Univ r l)
           → Γ ⊢⊢ A ≡ B
    refl   : ∀ {A}
           → Γ ⊢⊢ A
           → Γ ⊢⊢ A ≡ A
    sym    : ∀ {A B}
           → Γ ⊢⊢ A ≡ B
           → Γ ⊢⊢ B ≡ A
    trans  : ∀ {A B C}
           → Γ ⊢⊢ A ≡ B
           → Γ ⊢⊢ B ≡ C
           → Γ ⊢⊢ A ≡ C


  -- Term equality
  data _⊢⊢_≡_∷_ (Γ : SimpleCon Term) : Term → Term → Term → Set where
    refl        : ∀ {t A}
                → Γ ⊢⊢ t ∷ A
                → Γ ⊢⊢ t ≡ t ∷ A
    sym         : ∀ {t u A}
                → Γ ⊢⊢ t ≡ u ∷ A
                → Γ ⊢⊢ u ≡ t ∷ A
    trans       : ∀ {t u v A}
                → Γ ⊢⊢ t ≡ u ∷ A
                → Γ ⊢⊢ u ≡ v ∷ A
                → Γ ⊢⊢ t ≡ v ∷ A
    conv        : ∀ {A B t u}
                → Γ ⊢⊢ t ≡ u ∷ A
                → Γ ⊢⊢ A ≡ B
                → Γ ⊢⊢ t ≡ u ∷ B
    Π-cong      : ∀ {E F G H rF lF rG lG l}
                → (rG PE.≡ ! → lF ≤ l × lG ≤ l)
                → (rG PE.≡ % → lG PE.≡ ⁰ × l PE.≡ ⁰)
                → Γ     ⊢⊢ F ≡ H
                → Γ ∙ F ⊢⊢ G ≡ E
                → Γ     ⊢⊢ Π F ^ rF ° lF ▹ G ° lG ° l ^ rG ≡ Π H ^ rF ° lF ▹ E ° lG ° l ^ rG ∷ (Univ rG l)
    ∃-cong      : ∀ {E F G H}
                → Γ     ⊢⊢ F ≡ H       ∷ SProp
                → Γ ∙ F ⊢⊢ G ≡ E       ∷ SProp
                → Γ     ⊢⊢ ∃ F ▹ G ≡ ∃ H ▹ E ∷ SProp
    app-cong    : ∀ {a b f g F G rF lF lG l}
                → Γ ⊢⊢ f ≡ g ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ !
                → Γ ⊢⊢ a ≡ b ∷ F
                → Γ ⊢⊢ f ∘ a ^ l ≡ g ∘ b ^ l ∷ G [ a ]
    β-red       : ∀ {a t F lF G lG l}
                → lF ≤ l
                → lG ≤ l
                → Γ ∙ F ⊢⊢ t ∷ G
                → Γ     ⊢⊢ a ∷ F
                → Γ     ⊢⊢ (lam F ▹ t ^ l) ∘ a ^ l ≡ t [ a ] ∷ G [ a ]
    η-eq        : ∀ {f g F rF lF lG l G}
                → Γ     ⊢⊢ f ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ !
                → Γ     ⊢⊢ g ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ !
                → Γ ∙ F ⊢⊢ wk1 f ∘ var Nat.zero ^ l ≡ wk1 g ∘ var Nat.zero ^ l ∷ G
                → Γ     ⊢⊢ f ≡ g ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ !
    suc-cong    : ∀ {m n}
                → Γ ⊢⊢ m ≡ n ∷ ℕ
                → Γ ⊢⊢ suc m ≡ suc n ∷ ℕ
    natrec-cong : ∀ {z z′ s s′ n n′ F F′ l}
                → Γ ∙ ℕ ⊢⊢ F ≡ F′
                → Γ     ⊢⊢ z ≡ z′ ∷ F [ zero ]
                → Γ     ⊢⊢ s ≡ s′ ∷ Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc (var Nat.zero) ]↑ ° l ° l ^ !) ° l ° l ^ ! 
                → Γ     ⊢⊢ n ≡ n′ ∷ ℕ
                → Γ     ⊢⊢ natrec l F z s n ≡ natrec l F′ z′ s′ n′ ∷ F [ n ]
    natrec-zero : ∀ {z s F l}
                → Γ     ⊢⊢ z ∷ F [ zero ]
                → Γ     ⊢⊢ s ∷ Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc (var Nat.zero) ]↑ ° l ° l ^ !) ° l ° l ^ !
                → Γ     ⊢⊢ natrec l F z s zero ≡ z ∷ F [ zero ]
    natrec-suc  : ∀ {n z s F l}
                → Γ     ⊢⊢ n ∷ ℕ
                → Γ     ⊢⊢ z ∷ F [ zero ]
                → Γ     ⊢⊢ s ∷ Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc (var Nat.zero) ]↑ ° l ° l ^ !) ° l ° l ^ !
                → Γ     ⊢⊢ natrec l F z s (suc n) ≡ (s ∘ n ^ l) ∘ (natrec l F z s n) ^ l
                        ∷ F [ suc n ]
    Emptyrec-cong : ∀ {A A' l e e'}
                → Γ ⊢⊢ A ≡ A'
                → Γ ⊢⊢ e ∷ sEmpty
                → Γ ⊢⊢ e' ∷ sEmpty
                → Γ ⊢⊢ Emptyrec l ⁰  A e ≡ Emptyrec l ⁰  A' e' ∷ A
    proof-irrelevance : ∀ {t u A}
                      → Γ ⊢⊢ t ∷ A
                      → Γ ⊢⊢ u ∷ A
                      → Γ ⊢⊢ t ≡ u ∷ A
    Id-cong : ∀ {A A' t t' u u'}
              → Γ ⊢⊢ A ≡ A'
              → Γ ⊢⊢ t ≡ t' ∷ A
              → Γ ⊢⊢ u ≡ u' ∷ A
              → Γ ⊢⊢ Id A t u ≡ Id A' t' u' ∷ SProp
    Id-Π : ∀ {A rA lA lB l B t u}
           → Γ ⊢⊢ t ∷ (Π A ^ rA ° lA ▹ B ° lB ° l ^ !)
           → Γ ⊢⊢ u ∷ (Π A ^ rA ° lA ▹ B ° lB ° l ^ !)
           → Γ ⊢⊢ (Id (Π A ^ rA ° lA ▹ B ° lB ° l ^ !) t u)
                 ≡ Π A ^ rA ° lA ▹ (Id B ((wk1 t) ∘ (var 0) ^ l) ((wk1 u) ∘ (var 0) ^ l)) ° ⁰ ° ⁰
                  ^ % ∷ SProp
    Id-ℕ-00 : ⊢⊢ Γ
           → Γ ⊢⊢ (Id ℕ zero zero)
                  ≡ sUnit 
                  ∷ SProp
    Id-ℕ-SS : ∀ {m n}
              → Γ ⊢⊢ m ∷ ℕ
              → Γ ⊢⊢ n ∷ ℕ
              → Γ ⊢⊢ (Id ℕ (suc m) (suc n))
                    ≡ (Id ℕ m n)
                    ∷ SProp
    Id-U-ΠΠ : ∀ {A A' rA B B'}
              → Γ ⊢⊢ A ∷ (Univ rA ⁰)
              → Γ ∙ A ⊢⊢ B
              → Γ ⊢⊢ A' ∷ (Univ rA ⁰)
              → Γ ∙ A' ⊢⊢ B'
              → Γ ⊢⊢ (Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ !))
                    ≡ ∃ (Id (Univ rA ⁰) A A') ▹
                      (Π (wk1 A') ^ rA ° ⁰ ▹ Id (U ⁰)
                        ((wk (lift (step id)) B) [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (var 1)) (var 0) ]↑)
                        (wk (lift (step id)) B') ° ⁰ ° ⁰ ^ %)
                  ∷ SProp
    Id-U-ℕℕ : ⊢⊢ Γ
            → Γ ⊢⊢ Id (U ⁰) ℕ ℕ
                  ≡ sUnit 
                  ∷ SProp
    Id-SProp : ∀ {A B}
               → Γ ⊢⊢ A ∷ SProp
               → Γ ⊢⊢ B ∷ SProp
               → Γ ⊢⊢ Id SProp A B
                     ≡ (A ^ % ° ⁰ ▹▹ B ° ⁰ ° ⁰ ^ %) ×× (B ^ % ° ⁰ ▹▹ A ° ⁰ ° ⁰ ^ %)
                     ∷ SProp
    Id-ℕ-0S : ∀ {t}
            → Γ ⊢⊢ t ∷ ℕ
            → Γ ⊢⊢ Id ℕ zero (suc t) ≡ sEmpty ∷ SProp
    Id-ℕ-S0 : ∀ {t}
            → Γ ⊢⊢ t ∷ ℕ
            → Γ ⊢⊢ Id ℕ (suc t) zero ≡ sEmpty ∷ SProp
    Id-U-ℕΠ : ∀ {A rA B}
            → Γ ⊢⊢ A 
            → Γ ∙ A ⊢⊢ B 
            → Γ ⊢⊢ Id (U ⁰) ℕ (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) ≡ sEmpty ∷ SProp
    Id-U-Πℕ : ∀ {A rA B}
            → Γ ⊢⊢ A
            → Γ ∙ A ⊢⊢ B
            → Γ ⊢⊢ Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) ℕ ≡ sEmpty ∷ SProp
    Id-U-ΠΠ!% : ∀ {A rA B A' rA' B' }
            → rA PE.≢ rA'
            → Γ ⊢⊢ A 
            → Γ ∙ A ⊢⊢ B
            → Γ ⊢⊢ A'
            → Γ ∙ A' ⊢⊢ B'
            → Γ ⊢⊢ Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) (Π A' ^ rA' ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ !) ≡ sEmpty ∷ SProp
    cast-cong : ∀ {A A' B B' e e' t t'} → let l = ⁰ in
                  Γ ⊢⊢ A ≡ A'
                → Γ ⊢⊢ B ≡ B'
                → Γ ⊢⊢ t ≡ t' ∷ A
                → Γ ⊢⊢ e ∷ (Id (U ⁰) A B)
                → Γ ⊢⊢ e' ∷ (Id (U ⁰) A' B')
                → Γ ⊢⊢ cast l A B e t ≡ cast l A' B' e' t' ∷ B
    cast-Π : ∀ {A A' rA B B' e f} → let l = ⁰ in let lA = ⁰ in let lB = ⁰ in
               Γ ⊢⊢ e ∷ Id (U l) (Π A ^ rA ° lA ▹ B ° lB ° l ^ !) (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ !)
             → Γ ⊢⊢ f ∷ (Π A ^ rA ° lA ▹ B ° lB ° l ^ !)
             → Γ ⊢⊢ (cast l (Π A ^ rA ° lA ▹ B ° lB ° l ^ !) (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ !) e f)
               ≡ (lam A' ▹
                      (let a = cast l (wk1 A') (wk1 A) (Idsym (Univ rA l) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) in
                      cast l (B [ a ]↑) B' ((snd (wk1 e)) ∘ (var 0) ^ ⁰) ((wk1 f) ∘ a ^ l))
                      ^ l)
                   ∷ Π A' ^ rA ° lA ▹ B' ° lB ° l  ^ !
    cast-ℕ-0 : ∀ {e}
               → Γ ⊢⊢ e ∷ Id (U ⁰) ℕ ℕ
               → Γ ⊢⊢ cast ⁰ ℕ ℕ e zero
                   ≡ zero
                   ∷ ℕ
    cast-ℕ-S : ∀ {e n}
               → Γ ⊢⊢ e ∷ Id (U ⁰) ℕ ℕ
               → Γ ⊢⊢ n ∷ ℕ
               → Γ ⊢⊢ cast ⁰ ℕ ℕ e (suc n)
                   ≡ suc (cast ⁰ ℕ ℕ e n)
                   ∷ ℕ



∥_∥ : {A : Set} → Con A → SimpleCon A
∥ ε ∥ = ε
∥ X ∙ A ^ r ∥ = ∥ X ∥ ∙ A 

∈-∈∈ : ∀ {Γ x A r} → x ∷ A ^ r ∈ Γ → x ∷ A ∈∈ ∥ Γ ∥
∈-∈∈ here = here
∈-∈∈ (there X) = there (∈-∈∈ X)

infixr 30 _∷∷_

data TypeInfos : SimpleCon Term → Set where
  [] : TypeInfos ε
  _∷∷_ : ∀ {Γ A} → TypeInfo → TypeInfos Γ → TypeInfos (Γ ∙ A)

zip : (Γ : SimpleCon Term) → TypeInfos Γ → Con Term
zip .ε [] = ε
zip (._∙_ Γ A) (r ∷∷ rs) = zip Γ rs ∙ A ^ r

find : ∀ {Γ x A} → TypeInfos Γ → (In : x ∷ A ∈∈ Γ) → TypeInfo
find [] ()
find (r ∷∷ rs) here = r
find (r ∷∷ rs) (there Y) = find rs Y

∈∈-∈ : ∀ {Γ x A} → (rs :  TypeInfos Γ) (In : x ∷ A ∈∈ Γ) → x ∷ A ^ find rs In ∈ zip Γ rs
∈∈-∈ (x ∷∷ rs) here = here
∈∈-∈ (x ∷∷ rs) (there X) = there (∈∈-∈ rs X)

-- Escape context extraction

mutual 
  wffTerm : ∀ {Γ A t} → Γ ⊢⊢ t ∷ A → ⊢⊢ Γ
  wffTerm (univ <l ⊢Γ) = ⊢Γ
  wffTerm (ℕⱼ ⊢Γ) = ⊢Γ
  wffTerm (Emptyⱼ ⊢Γ) = ⊢Γ
  wffTerm (Πⱼ <l ▹ <l' ▹ F ▹ G) = wffTerm F
  wffTerm (∃ⱼ F ▹ G) = wffTerm F
  wffTerm (var ⊢Γ x₁) = ⊢Γ
  wffTerm (lamⱼ _ _ t) with wffTerm t
  wffTerm (lamⱼ _ _ t) | ⊢Γ ∙ F′ = ⊢Γ
  wffTerm (g ∘ⱼ a) = wffTerm a
  wffTerm (⦅ G , t , u ⦆ⱼ) = wffTerm t
  wffTerm (fstⱼ t) = wffTerm t
  wffTerm (sndⱼ t) = wffTerm t
  wffTerm (zeroⱼ ⊢Γ) = ⊢Γ
  wffTerm (sucⱼ n) = wffTerm n
  wffTerm (natrecⱼ F z s n) = wffTerm z
  wffTerm (Emptyrecⱼ A e) = wffTerm e
  wffTerm (Idⱼ t u) = wffTerm t
  wffTerm (Idreflⱼ t) = wffTerm t
  wffTerm (transpⱼ P t s u e) = wffTerm t
  wffTerm (castⱼ e t) = wffTerm t
  wffTerm (castreflⱼ t) = wffTerm t
  wffTerm (conv t A≡B) = wffTerm t

  wff : ∀ {Γ A} → Γ ⊢⊢ A → ⊢⊢ Γ
  wff (Uⱼ ⊢Γ) = ⊢Γ
  wff (univ A) = wffTerm A

mutual
  wffEqTerm : ∀ {Γ A t u} → Γ ⊢⊢ t ≡ u ∷ A → ⊢⊢ Γ
  wffEqTerm (refl t) = wffTerm t
  wffEqTerm (sym t≡u) = wffEqTerm t≡u
  wffEqTerm (trans t≡u u≡r) = wffEqTerm t≡u
  wffEqTerm (conv t≡u A≡B) = wffEqTerm t≡u
  wffEqTerm (Π-cong _ _ F≡H G≡E) = wffEq F≡H
  wffEqTerm (∃-cong F≡H G≡E) = wffEqTerm F≡H
  wffEqTerm (app-cong f≡g a≡b) = wffEqTerm f≡g
  wffEqTerm (β-red _ _ t a) = wffTerm a
  wffEqTerm (η-eq f g f0≡g0) = wffTerm f
  wffEqTerm (suc-cong n) = wffEqTerm n
  wffEqTerm (natrec-cong F≡F′ z≡z′ s≡s′ n≡n′) = wffEqTerm z≡z′
  wffEqTerm (natrec-zero z s) = wffTerm z
  wffEqTerm (natrec-suc n z s) = wffTerm n
  wffEqTerm (Emptyrec-cong A≡A' _ _) = wffEq A≡A'
  wffEqTerm (proof-irrelevance t u) = wffTerm t
  wffEqTerm (Id-cong A t u) = wffEqTerm u
  wffEqTerm (Id-Π t u) = wffTerm t
  wffEqTerm (Id-ℕ-00 ⊢Γ) = ⊢Γ
  wffEqTerm (Id-ℕ-SS m n) = wffTerm n
  wffEqTerm (Id-U-ΠΠ A B A' B') = wffTerm A
  wffEqTerm (Id-U-ℕℕ ⊢Γ) = ⊢Γ
  wffEqTerm (Id-SProp A B) = wffTerm A
  wffEqTerm (Id-ℕ-0S n) = wffTerm n
  wffEqTerm (Id-ℕ-S0 n) = wffTerm n
  wffEqTerm (Id-U-ℕΠ A B) = wff A
  wffEqTerm (Id-U-Πℕ A B) = wff A
  wffEqTerm (Id-U-ΠΠ!% eq A B A' B') = wff A
  wffEqTerm (cast-cong A B t _ _) = wffEqTerm t
  wffEqTerm (cast-Π e f) = wffTerm f
  wffEqTerm (cast-ℕ-0 e) = wffTerm e
  wffEqTerm (cast-ℕ-S e n) = wffTerm n

  wffEq : ∀ {Γ A B} → Γ ⊢⊢ A ≡ B → ⊢⊢ Γ
  wffEq (univ A≡B) = wffEqTerm A≡B
  wffEq (refl A) = wff A
  wffEq (sym A≡B) = wffEq A≡B
  wffEq (trans A≡B B≡C) = wffEq A≡B

mutual
  ⊢is⊢⊢ctx : ∀ {Γ} → ⊢ Γ → ⊢⊢ ∥ Γ ∥
  ⊢is⊢⊢ : ∀ {Γ A r} → Γ ⊢ A ^ r → ∥ Γ ∥ ⊢⊢ A
  ⊢is⊢⊢eq : ∀ {Γ A B r} → Γ ⊢ A ≡ B ^ r → ∥ Γ ∥ ⊢⊢ A ≡ B
  ⊢is⊢⊢term : ∀ {Γ A t r} → Γ ⊢ t ∷ A ^ r → ∥ Γ ∥ ⊢⊢ t ∷ A
  ⊢is⊢⊢eqterm : ∀ {Γ A t u r} → Γ ⊢ t ≡ u ∷ A ^ r → ∥ Γ ∥ ⊢⊢ t ≡ u ∷ A
  
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
  ⊢is⊢⊢term (var ⊢Γ x) = var (⊢is⊢⊢ctx ⊢Γ) (∈-∈∈ x)
  ⊢is⊢⊢term (lamⱼ x x₁ x₂ X) = lamⱼ x x₁ (⊢is⊢⊢term X)
  ⊢is⊢⊢term (x ▹ X ▹ X₁ ▹ X₂ ∘ⱼ X₃) = ⊢is⊢⊢term X₂ ∘ⱼ ⊢is⊢⊢term X₃
  ⊢is⊢⊢term (⦅_,_,_,_⦆ⱼ x x₁ X X₁) = ⦅ ⊢is⊢⊢ x₁ , ⊢is⊢⊢term X , ⊢is⊢⊢term X₁ ⦆ⱼ
  ⊢is⊢⊢term (fstⱼ X X₁ X₂) = fstⱼ (⊢is⊢⊢term X₂)
  ⊢is⊢⊢term (sndⱼ X X₁ X₂) = sndⱼ (⊢is⊢⊢term X₂)
  ⊢is⊢⊢term (zeroⱼ x) = zeroⱼ (⊢is⊢⊢ctx x)
  ⊢is⊢⊢term (sucⱼ X) = sucⱼ (⊢is⊢⊢term X)
  ⊢is⊢⊢term (natrecⱼ x x₁ X X₁ X₂) = natrecⱼ (⊢is⊢⊢ x₁) (⊢is⊢⊢term X) (⊢is⊢⊢term X₁) (⊢is⊢⊢term X₂)
  ⊢is⊢⊢term (Emptyrecⱼ x X) = Emptyrecⱼ (⊢is⊢⊢ x) (⊢is⊢⊢term X)
  ⊢is⊢⊢term (Idⱼ X X₁ X₂) = Idⱼ (⊢is⊢⊢term X₁) (⊢is⊢⊢term X₂) 
  ⊢is⊢⊢term (Idreflⱼ X) = Idreflⱼ (⊢is⊢⊢term X)
  ⊢is⊢⊢term (transpⱼ x x₁ X X₁ X₂ X₃) = transpⱼ (⊢is⊢⊢ x₁) (⊢is⊢⊢term X) (⊢is⊢⊢term X₁) (⊢is⊢⊢term X₂) (⊢is⊢⊢term X₃)
  ⊢is⊢⊢term (castⱼ X X₁ X₂ X₃) = castⱼ (⊢is⊢⊢term X₂) (⊢is⊢⊢term X₃) 
  ⊢is⊢⊢term (castreflⱼ X X₁) = castreflⱼ (⊢is⊢⊢term X₁)
  ⊢is⊢⊢term (conv X x) = conv (⊢is⊢⊢term X) (⊢is⊢⊢eq x)

  ⊢is⊢⊢eqterm (refl x) = refl (⊢is⊢⊢term x)
  ⊢is⊢⊢eqterm (sym X) = sym (⊢is⊢⊢eqterm X)
  ⊢is⊢⊢eqterm (trans X X₁) = trans (⊢is⊢⊢eqterm X) (⊢is⊢⊢eqterm X₁)
  ⊢is⊢⊢eqterm (conv X x) = conv (⊢is⊢⊢eqterm X) (⊢is⊢⊢eq x)
  ⊢is⊢⊢eqterm (Π-cong x x₁ x₂ X X₁) = Π-cong x x₁ (univ (⊢is⊢⊢eqterm X)) (univ (⊢is⊢⊢eqterm X₁))
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
  ⊢is⊢⊢eqterm (Id-cong X X₁ X₂) = Id-cong (univ (⊢is⊢⊢eqterm X)) (⊢is⊢⊢eqterm X₁) (⊢is⊢⊢eqterm X₂)
  ⊢is⊢⊢eqterm (Id-Π x x₁ x₂ x₃ x₄ x₅) = Id-Π  (⊢is⊢⊢term x₄) (⊢is⊢⊢term x₅)
  ⊢is⊢⊢eqterm (Id-ℕ-00 x) = Id-ℕ-00 (⊢is⊢⊢ctx x) 
  ⊢is⊢⊢eqterm (Id-ℕ-SS x x₁) = Id-ℕ-SS (⊢is⊢⊢term x) (⊢is⊢⊢term x₁)
  ⊢is⊢⊢eqterm (Id-U-ΠΠ x x₁ x₂ x₃) = Id-U-ΠΠ (⊢is⊢⊢term x) (univ (⊢is⊢⊢term x₁)) (⊢is⊢⊢term x₂) (univ (⊢is⊢⊢term x₃))
  ⊢is⊢⊢eqterm (Id-U-ℕℕ x) = Id-U-ℕℕ (⊢is⊢⊢ctx x)
  ⊢is⊢⊢eqterm (Id-SProp x x₁) = Id-SProp (⊢is⊢⊢term x) (⊢is⊢⊢term x₁)
  ⊢is⊢⊢eqterm (Id-ℕ-0S x) = Id-ℕ-0S (⊢is⊢⊢term x)
  ⊢is⊢⊢eqterm (Id-ℕ-S0 x) = Id-ℕ-S0 (⊢is⊢⊢term x)
  ⊢is⊢⊢eqterm (Id-U-ℕΠ x x₁) = Id-U-ℕΠ (univ (⊢is⊢⊢term x)) (univ (⊢is⊢⊢term x₁))
  ⊢is⊢⊢eqterm (Id-U-Πℕ x x₁) = Id-U-Πℕ (univ (⊢is⊢⊢term x)) (univ (⊢is⊢⊢term x₁))
  ⊢is⊢⊢eqterm (Id-U-ΠΠ!% r x x₁ x₂ x₃) = Id-U-ΠΠ!% r (univ (⊢is⊢⊢term x)) (univ (⊢is⊢⊢term x₁)) (univ (⊢is⊢⊢term x₂)) (univ (⊢is⊢⊢term x₃))
  ⊢is⊢⊢eqterm (cast-cong X X₁ X₂ x x₁) = cast-cong (univ (⊢is⊢⊢eqterm X)) (univ (⊢is⊢⊢eqterm X₁)) (⊢is⊢⊢eqterm X₂) (⊢is⊢⊢term x) (⊢is⊢⊢term x₁)
  ⊢is⊢⊢eqterm (cast-Π x x₁ x₂ x₃ x₄ x₅) = cast-Π (⊢is⊢⊢term x₄) (⊢is⊢⊢term x₅)
  ⊢is⊢⊢eqterm (cast-ℕ-0 x) = cast-ℕ-0 (⊢is⊢⊢term x)
  ⊢is⊢⊢eqterm (cast-ℕ-S x x₁) = cast-ℕ-S (⊢is⊢⊢term x) (⊢is⊢⊢term x₁)

mutual
  ⊢⊢is⊢ctx : ∀ {Γ} → ⊢⊢ Γ → ∃ (λ rs → ⊢ zip Γ rs)
  ⊢⊢is⊢ctx-irr : ∀ {Γ} → (⊢Γ ⊢Γ' : ⊢⊢ Γ) →  proj₁ (⊢⊢is⊢ctx ⊢Γ) PE.≡ proj₁ (⊢⊢is⊢ctx ⊢Γ')
  ⊢⊢is⊢ : ∀ {Γ A} → (X : Γ ⊢⊢ A) → let rs , _ = ⊢⊢is⊢ctx (wff X) in ∃ (λ r → zip Γ rs ⊢ A ^ r)
  ⊢⊢is⊢-irr : ∀ {Γ A} → (⊢A ⊢A' : Γ ⊢⊢ A) →  proj₁ (⊢⊢is⊢ ⊢A) PE.≡ proj₁ (⊢⊢is⊢ ⊢A')
  ⊢⊢is⊢eq : ∀ {Γ A B} → (X : Γ ⊢⊢ A ≡ B) → let rs , _ = ⊢⊢is⊢ctx (wffEq X) in ∃ (λ r → zip Γ rs ⊢ A ≡ B ^ r)
  ⊢⊢is⊢eq-irr : ∀ {Γ A B} → (⊢A≡B ⊢A≡B' : Γ ⊢⊢ A ≡ B) →  proj₁ (⊢⊢is⊢eq ⊢A≡B) PE.≡ proj₁ (⊢⊢is⊢eq ⊢A≡B')
  ⊢⊢is⊢term : ∀ {Γ A t} → (X : Γ ⊢⊢ t ∷ A) → let rs , _ = ⊢⊢is⊢ctx (wffTerm X) in ∃ (λ r → zip Γ rs ⊢ t ∷ A ^ r)
  ⊢⊢is⊢term-irr : ∀ {Γ t A} → (⊢t ⊢t' : Γ ⊢⊢ t ∷ A) →  proj₁ (⊢⊢is⊢term ⊢t) PE.≡ proj₁ (⊢⊢is⊢term ⊢t')
  ⊢⊢is⊢eqterm : ∀ {Γ A t u} → (X : Γ ⊢⊢ t ≡ u ∷ A) → let rs , _ = ⊢⊢is⊢ctx (wffEqTerm X) in ∃ (λ r → zip Γ rs ⊢ t ≡ u ∷ A ^ r)
  ⊢⊢is⊢eqterm-irr : ∀ {Γ A t u} → (⊢t≡u ⊢t≡u' : Γ ⊢⊢ t ≡ u ∷ A) →  proj₁ (⊢⊢is⊢eqterm ⊢t≡u) PE.≡ proj₁ (⊢⊢is⊢eqterm ⊢t≡u')
  
  ⊢⊢is⊢ctx ε = [] , ε
  ⊢⊢is⊢ctx (⊢Γ ∙ x) = let rs , X = ⊢⊢is⊢ctx ⊢Γ
                          r , x' = ⊢⊢is⊢ x
                      in r ∷∷ rs , X ∙ PE.subst (λ rr → zip _ rr ⊢ _ ^ _) (⊢⊢is⊢ctx-irr (wff x) ⊢Γ) x' 

  ⊢⊢is⊢ctx-irr ε ε = PE.refl
  ⊢⊢is⊢ctx-irr (X ∙ x) (Y ∙ y) = PE.cong₂ _∷∷_ (⊢⊢is⊢-irr x y) (⊢⊢is⊢ctx-irr X Y)

  ⊢⊢is⊢ (Uⱼ x) = let _ , ⊢Γ = ⊢⊢is⊢ctx x in [ ! , ∞ ] , Uⱼ ⊢Γ
  ⊢⊢is⊢ {Γ} {A} (univ {A} {rr} {ll} x) =
    let r , ⊢x = ⊢⊢is⊢term x
        rs , _ = ⊢⊢is⊢ctx (wff (univ x))
        ⊢U = syntacticTerm ⊢x
        ⊢U' = Ugenⱼ (wf ⊢U)
        er = relevance-unicity-gen ⊢U ⊢U'
    in _ , univ (PE.subst (λ R → zip Γ rs ⊢ A ∷ Univ rr ll ^ R) er ⊢x) 

  ⊢⊢is⊢eq {Γ} {A} {B} (univ {A} {B} {rr} {ll} x) =
    let r , ⊢x = ⊢⊢is⊢eqterm x
        rs , _ = ⊢⊢is⊢ctx (wffEq (univ x))
        ⊢U = proj₁ (syntacticEqTerm ⊢x)
        ⊢U' = Ugenⱼ (wf ⊢U)
        er = relevance-unicity-gen ⊢U ⊢U'
    in _ , univ (PE.subst (λ R → zip Γ rs ⊢ A ≡ B ∷ Univ rr ll ^ R) er ⊢x)
  ⊢⊢is⊢eq (refl x) = let r , ⊢x = ⊢⊢is⊢ x in r , refl ⊢x
  ⊢⊢is⊢eq (sym X) = let r , ⊢X = ⊢⊢is⊢eq X in r , sym ⊢X
  ⊢⊢is⊢eq (trans X X₁) = let r , ⊢X = ⊢⊢is⊢eq X
                             r₁ , ⊢X₁ = ⊢⊢is⊢eq X₁
                             ⊢B = proj₂ (syntacticEq ⊢X)
                             ⊢B' = proj₁ (syntacticEq ⊢X₁)
                             er = relevance-unicity-gen (PE.subst (λ rs → zip _ rs ⊢ _ ^ _) (⊢⊢is⊢ctx-irr (wffEq X₁) (wffEq X)) ⊢B') ⊢B 
                         in r , trans ⊢X (PE.subst₂ (λ rs rr → zip _ rs ⊢ _ ≡ _ ^ rr) (⊢⊢is⊢ctx-irr (wffEq X₁) (wffEq X)) er ⊢X₁) 

  ⊢⊢is⊢eq-irr X Y = let r , x = ⊢⊢is⊢eq X
                        r' , y = ⊢⊢is⊢eq Y
                        ⊢A = proj₁ (syntacticEq x)
                        ⊢A' = proj₁ (syntacticEq y)
                    in relevance-unicity-gen ⊢A (PE.subst (λ rr → zip _ rr ⊢ _ ^ _) (⊢⊢is⊢ctx-irr (wffEq Y) (wffEq X)) ⊢A')

  ⊢⊢is⊢term-irr X Y = let r , x = ⊢⊢is⊢term X
                          r' , y = ⊢⊢is⊢term Y
                          ⊢A = syntacticTerm x
                          ⊢A' = syntacticTerm y
                      in relevance-unicity-gen ⊢A (PE.subst (λ rr → zip _ rr ⊢ _ ^ _) (⊢⊢is⊢ctx-irr (wffTerm Y) (wffTerm X)) ⊢A')

  ⊢⊢is⊢eqterm-irr X Y = let r , x = ⊢⊢is⊢eqterm X
                            r' , y = ⊢⊢is⊢eqterm Y
                            ⊢A = proj₁ (syntacticEqTerm x)
                            ⊢A' = proj₁ (syntacticEqTerm y)
                        in relevance-unicity-gen ⊢A (PE.subst (λ rr → zip _ rr ⊢ _ ^ _) (⊢⊢is⊢ctx-irr (wffEqTerm Y) (wffEqTerm X)) ⊢A')

  ⊢⊢is⊢-irr X Y = let r , x = ⊢⊢is⊢ X
                      r' , y = ⊢⊢is⊢ Y
                  in relevance-unicity-gen x (PE.subst (λ rr → zip _ rr ⊢ _ ^ _) (⊢⊢is⊢ctx-irr (wff Y) (wff X)) y)



  ⊢⊢is⊢eqterm = {!!} 

  ⊢⊢is⊢term (univ x ⊢⊢Γ) = let rs , ⊢Γ = ⊢⊢is⊢ctx ⊢⊢Γ in _ , univ x ⊢Γ
  ⊢⊢is⊢term (ℕⱼ ⊢⊢Γ) = let rs , ⊢Γ = ⊢⊢is⊢ctx ⊢⊢Γ in  _ , ℕⱼ ⊢Γ
  ⊢⊢is⊢term (Emptyⱼ ⊢⊢Γ) = let rs , ⊢Γ = ⊢⊢is⊢ctx ⊢⊢Γ in  _ , Emptyⱼ ⊢Γ
  ⊢⊢is⊢term {Γ} (Πⱼ x ▹ x₁ ▹ X ▹ X₁) = let rX , ⊢X = ⊢⊢is⊢term X
                                           rX' , ⊢X' = ⊢⊢is⊢term X₁
                                           ⊢U = syntacticTerm ⊢X
                                           ⊢U' = Ugenⱼ (wf ⊢U)
                                           ⊢U'' = syntacticTerm ⊢X'
                                           ⊢U''' = Ugenⱼ (wf ⊢U'')
                                           er = relevance-unicity-gen ⊢U ⊢U'
                                           er' = relevance-unicity-gen ⊢U'' ⊢U'''
                                       in _ , Πⱼ x ▹ x₁ ▹ PE.subst (λ R → zip Γ (proj₁ (⊢⊢is⊢ctx (wffTerm X))) ⊢ _ ∷ _ ^ R) er ⊢X ▹
                                                 PE.subst₂ (λ rs rr → zip _ rs ⊢ _ ∷ _ ^ rr) (⊢⊢is⊢ctx-irr (wffTerm X₁) (wffTerm X ∙ univ X)) er' ⊢X'
  ⊢⊢is⊢term {Γ} (∃ⱼ X ▹ X₁) = let rX , ⊢X = ⊢⊢is⊢term X
                                  rX' , ⊢X' = ⊢⊢is⊢term X₁
                                  ⊢U = syntacticTerm ⊢X
                                  ⊢U' = Ugenⱼ (wf ⊢U)
                                  ⊢U'' = syntacticTerm ⊢X'
                                  ⊢U''' = Ugenⱼ (wf ⊢U'')
                                  er = relevance-unicity-gen ⊢U ⊢U'
                                  er' = relevance-unicity-gen ⊢U'' ⊢U'''
                              in _ , ∃ⱼ PE.subst (λ R → zip Γ (proj₁ (⊢⊢is⊢ctx (wffTerm X))) ⊢ _ ∷ SProp ^ R) er ⊢X ▹
                                        PE.subst₂ (λ rs rr → zip _ rs ⊢ _ ∷ SProp ^ rr) (⊢⊢is⊢ctx-irr (wffTerm X₁) (wffTerm X ∙ univ X)) er' ⊢X'
  ⊢⊢is⊢term (var ⊢⊢Γ x) = let rs , ⊢Γ = ⊢⊢is⊢ctx ⊢⊢Γ in find rs x , var ⊢Γ (∈∈-∈ rs x)
  ⊢⊢is⊢term (lamⱼ x x₁ X) = {!!} -- let XX = ⊢⊢is⊢term X in lamⱼ x x₁ (let ⊢Γ , ⊢F = inversion-ctx (wfTerm XX) in ⊢F) XX
  ⊢⊢is⊢term (X₂ ∘ⱼ X₃) = 
    let rg , ⊢g = ⊢⊢is⊢term X₂ 
        ra , ⊢a = ⊢⊢is⊢term X₃
--        ⊢Π = un-univ (syntacticTerm ⊢g)
 --       rG , _ , l% , _ , ⊢G , _ , req , _ = inversion-Π ⊢Π
    in  {!!} -- PE.subst (λ rr → rr PE.≡ % → _ PE.≡ ⁰ × _ PE.≡ ⁰) req l% ▹ un-univ (syntacticTerm ⊢a) ▹ PE.subst (λ rr → _ ⊢ _ ∷ Univ rr _ ^ [ ! , _ ]) req ⊢G ▹ ⊢g ∘ⱼ ⊢a
  ⊢⊢is⊢term (⦅_,_,_⦆ⱼ x X X₁) =
    let ⊢t = ⊢⊢is⊢term X
        ⊢u = ⊢⊢is⊢term X₁
    in {!!} -- ⦅_,_,_,_⦆ⱼ (syntacticTerm ⊢t) (⊢⊢is⊢ x) ⊢t ⊢u
  ⊢⊢is⊢term (fstⱼ X) =
    let rt , ⊢t = ⊢⊢is⊢term X
--        ⊢A , ⊢G , _ = inversion-∃ (un-univ (syntacticTerm ⊢t))
    in {!!} -- fstⱼ ⊢A ⊢G ⊢t
  ⊢⊢is⊢term (sndⱼ X) =
    let rt , ⊢t = ⊢⊢is⊢term X
        -- ⊢A , ⊢G , _ = inversion-∃ (un-univ (syntacticTerm ⊢t))
    in {!!} -- sndⱼ ⊢A ⊢G ⊢t
  ⊢⊢is⊢term (zeroⱼ x) = {!!} -- zeroⱼ (⊢⊢is⊢ctx x)
  ⊢⊢is⊢term (sucⱼ X) = {!!} -- sucⱼ (⊢⊢is⊢term X)
  ⊢⊢is⊢term (natrecⱼ x₁ X X₁ X₂) =
    let rs , ⊢s = ⊢⊢is⊢term X₁ 
        --⊢Π = un-univ (syntacticTerm ⊢s)
        --rG , _ , l% , _ , ⊢G , _ , req , _ = inversion-Π ⊢Π
        --l% = PE.subst (λ rr → rr PE.≡ % → _ PE.≡ ⁰ × _ PE.≡ ⁰) req l%
    in {!!} -- natrecⱼ (λ req → proj₁ (l% req)) (⊢⊢is⊢ x₁) (⊢⊢is⊢term X) ⊢s (⊢⊢is⊢term X₂)
  ⊢⊢is⊢term (Emptyrecⱼ x X) = {!!} -- Emptyrecⱼ (⊢⊢is⊢ x) (⊢⊢is⊢term X)
  ⊢⊢is⊢term (Idⱼ X₁ X₂) =
    let rt , ⊢t = (⊢⊢is⊢term X₁)
    in {!!} -- Idⱼ (un-univ (syntacticTerm ⊢t)) ⊢t (⊢⊢is⊢term X₂) 
  ⊢⊢is⊢term (Idreflⱼ X) = {!!} -- Idreflⱼ (⊢⊢is⊢term X)
  ⊢⊢is⊢term (transpⱼ x₁ X X₁ X₂ X₃) =
    let rt , ⊢t = (⊢⊢is⊢term X)
    in {!!} -- transpⱼ (syntacticTerm ⊢t) (⊢⊢is⊢ x₁) ⊢t (⊢⊢is⊢term X₁) (⊢⊢is⊢term X₂) (⊢⊢is⊢term X₃)
  ⊢⊢is⊢term (castⱼ X₂ X₃) =
    let ⊢e = ⊢⊢is⊢term X₂
       -- ⊢Id = un-univ (syntacticTerm ⊢e)
        --_ , ⊢U , ⊢A , ⊢B , _ = inversion-Id ⊢Id
        --Ueq , _ = inversion-U ⊢U
        --_ , leq = Uinjectivity Ueq
    in {!!} -- castⱼ (PE.subst (λ l → _ ⊢ _ ∷ _ ^ _ ) leq ⊢A) (PE.subst (λ l → _ ⊢ _ ∷ _ ^ _) leq ⊢B) ⊢e (⊢⊢is⊢term X₃) 
  ⊢⊢is⊢term (castreflⱼ X₁) =
    let rt , ⊢t = (⊢⊢is⊢term X₁)
    in {!!} -- castreflⱼ (un-univ (syntacticTerm ⊢t)) ⊢t
  ⊢⊢is⊢term (conv X x) = let rt , ⊢t = ⊢⊢is⊢term X
                             rA , ⊢A≡A = ⊢⊢is⊢eq x
                             ⊢A = syntacticTerm ⊢t
                             ⊢A' = proj₁ (syntacticEq ⊢A≡A)
                             er = relevance-unicity-gen (PE.subst (λ rr → zip _ rr ⊢ _ ^ _) (⊢⊢is⊢ctx-irr (wffEq x) (wffTerm X)) ⊢A') ⊢A
                         in rt , conv ⊢t (PE.subst₂ (λ rs rr → zip _ rs ⊢ _ ≡ _ ^ rr) (⊢⊢is⊢ctx-irr (wffEq x) (wffTerm X)) er ⊢A≡A)

{-
  ⊢⊢is⊢eqterm (refl x) = refl (⊢⊢is⊢term x)
  ⊢⊢is⊢eqterm (sym X) = sym (⊢⊢is⊢eqterm X)
  ⊢⊢is⊢eqterm (trans X X₁) = trans (⊢⊢is⊢eqterm X) (⊢⊢is⊢eqterm X₁)
  ⊢⊢is⊢eqterm (conv X x) = conv (⊢⊢is⊢eqterm X) (⊢⊢is⊢eq x)
  ⊢⊢is⊢eqterm (Π-cong x x₁ X X₁) =
    let ⊢FH = ⊢⊢is⊢eq X
        ⊢F , _ = syntacticEq ⊢FH
    in Π-cong x x₁ ⊢F (un-univ≡ ⊢FH) (un-univ≡ (⊢⊢is⊢eq X₁))
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
  ⊢⊢is⊢eqterm (Id-cong X X₁ X₂) = Id-cong (un-univ≡ (⊢⊢is⊢eq X)) (⊢⊢is⊢eqterm X₁) (⊢⊢is⊢eqterm X₂)
  ⊢⊢is⊢eqterm (Id-Π x₄ x₅) =
    let ⊢t = ⊢⊢is⊢term x₄
        ⊢Π = un-univ (syntacticTerm ⊢t)
        rG , l! , l% , ⊢F , ⊢G , _ , req , _ = inversion-Π ⊢Π
    in Id-Π (proj₁ (l! req)) (proj₂ (l! req)) ⊢F (PE.subst (λ rr → _ ⊢ _ ∷ Univ rr _ ^ [ ! , _ ]) req ⊢G) ⊢t (⊢⊢is⊢term x₅)
  ⊢⊢is⊢eqterm (Id-ℕ-00 x) = Id-ℕ-00 (⊢⊢is⊢ctx x) 
  ⊢⊢is⊢eqterm (Id-ℕ-SS x x₁) = Id-ℕ-SS (⊢⊢is⊢term x) (⊢⊢is⊢term x₁)
  ⊢⊢is⊢eqterm (Id-U-ΠΠ x x₁ x₂ x₃) = Id-U-ΠΠ (⊢⊢is⊢term x) (un-univ (⊢⊢is⊢ x₁)) (⊢⊢is⊢term x₂) (un-univ (⊢⊢is⊢ x₃))
  ⊢⊢is⊢eqterm (Id-U-ℕℕ x) = Id-U-ℕℕ (⊢⊢is⊢ctx x)
  ⊢⊢is⊢eqterm (Id-SProp x x₁) = Id-SProp (⊢⊢is⊢term x) (⊢⊢is⊢term x₁)
  ⊢⊢is⊢eqterm (Id-ℕ-0S x) = Id-ℕ-0S (⊢⊢is⊢term x)
  ⊢⊢is⊢eqterm (Id-ℕ-S0 x) = Id-ℕ-S0 (⊢⊢is⊢term x)
  ⊢⊢is⊢eqterm (Id-U-ℕΠ x x₁) = Id-U-ℕΠ (un-univ (⊢⊢is⊢ x)) (un-univ (⊢⊢is⊢ x₁))
  ⊢⊢is⊢eqterm (Id-U-Πℕ x x₁) = Id-U-Πℕ (un-univ (⊢⊢is⊢ x)) (un-univ (⊢⊢is⊢ x₁))
  ⊢⊢is⊢eqterm (Id-U-ΠΠ!% r x x₁ x₂ x₃) = Id-U-ΠΠ!% r (un-univ (⊢⊢is⊢ x)) (un-univ (⊢⊢is⊢ x₁)) (un-univ (⊢⊢is⊢ x₂)) (un-univ (⊢⊢is⊢ x₃)) 
  ⊢⊢is⊢eqterm (cast-cong X X₁ X₂ x x₁) = cast-cong (un-univ≡ (⊢⊢is⊢eq X)) (un-univ≡ (⊢⊢is⊢eq X₁)) (⊢⊢is⊢eqterm X₂) (⊢⊢is⊢term x) (⊢⊢is⊢term x₁)
  ⊢⊢is⊢eqterm (cast-Π x₄ x₅) =
    let ⊢e = ⊢⊢is⊢term x₄
        ⊢Id = un-univ (syntacticTerm ⊢e)
        _ , _ , ⊢Π , ⊢Π' , _ = inversion-Id ⊢Id
        _ , _ , _ , ⊢F , ⊢G , _ , req , _ = inversion-Π ⊢Π
        _ , _ , _ , ⊢F' , ⊢G' , _ , req' , _ = inversion-Π ⊢Π'
    in cast-Π ⊢F (PE.subst (λ rr → _ ⊢ _ ∷ Univ rr _ ^ [ ! , _ ]) req ⊢G) ⊢F' (PE.subst (λ rr → _ ⊢ _ ∷ Univ rr _ ^ [ ! , _ ]) req' ⊢G') ⊢e (⊢⊢is⊢term x₅) 
  ⊢⊢is⊢eqterm (cast-ℕ-0 x) = cast-ℕ-0 (⊢⊢is⊢term x)
  ⊢⊢is⊢eqterm (cast-ℕ-S x x₁) = cast-ℕ-S (⊢⊢is⊢term x) (⊢⊢is⊢term x₁)
-}
