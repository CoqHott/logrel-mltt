{-# OPTIONS --safe #-}

module Definition.Typed.NonParanoidTyping where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties as T hiding (wf ; wfTerm)
open import Definition.Typed.Weakening
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.Inversion
open import Definition.Typed.Consequences.Syntactic

open import Tools.Nat using (Nat)
open import Tools.Product
open import Tools.Empty
import Tools.PropositionalEquality as PE

infixl 30 _∙_
infix 30 Πⱼ_▹_▹_

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
    Πⱼ_▹_▹_ : ∀ {F rF lF G lG r l}
           → (r PE.≡ ! → lF ≤ l × lG ≤ l)
           → (r PE.≡ % → lG PE.≡ ⁰ × l PE.≡ ⁰)
           → Γ ∙ F ^ [ rF , ι lF ] ⊢⊢ G ^ [ r , ι lG ]
           → Γ     ⊢⊢ Π F ^ rF ° lF ▹ G ° lG ° l ^ r ∷ (Univ r l) ^ [ ! , next l ]
    var    : ∀ {A rl x}
           → ⊢⊢ Γ
           → x ∷ A ^ rl ∈ Γ
           → Γ ⊢⊢ var x ∷ A ^ rl
    lamⱼ    : ∀ {F r l rF lF G lG t}
           → (r PE.≡ ! → lF ≤ l × lG ≤ l)
           → (r PE.≡ % → lG PE.≡ ⁰ × l PE.≡ ⁰)
           → Γ ∙ F ^ [ rF , ι lF ] ⊢⊢ t ∷ G ^ [ r , ι lG ]
           → Γ     ⊢⊢ lam F ▹ t ^ l ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ r ^ [ r , ι l ]
    _∘ⱼ_    : ∀ {g a F rF lF G lG r lΠ}
           → Γ ⊢⊢     g ∷ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ r ^ [ r , ι lΠ ]
           → Γ ⊢⊢     a ∷ F ^ [ rF , ι lF ]
           → Γ ⊢⊢ g ∘ a ^ lΠ ∷ G [ a ] ^ [ r , ι lG ]
    fstⱼ : ∀ {A A' rA B B' e}
           → Γ ⊢⊢ e ∷ Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ !) ^ [ % , ι ⁰ ]
           → Γ ⊢⊢ fst e ∷ Id (Univ rA ⁰) A A' ^ [ % , ι ⁰ ]
    sndⱼ : ∀ {A A' rA B B' e}
           → Γ ⊢⊢ e ∷ Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ !) ^ [ % , ι ⁰ ]
           → Γ ⊢⊢ snd e ∷ Π A' ^ rA ° ⁰ ▹ Id (U ⁰)
                        (B [ cast ⁰ (wk1 A') (wk1 A) (Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) ]↑)
                        B' ° ⁰ ° ⁰ ^ % ^ [ % , ι ⁰ ]
    zeroⱼ   : ⊢⊢ Γ
           → Γ ⊢⊢ zero ∷ ℕ ^ [ ! ,  ι ⁰ ]
    sucⱼ    : ∀ {n}
           → Γ ⊢⊢ n ∷ ℕ ^ [ ! ,  ι ⁰ ]
           → Γ ⊢⊢ suc n ∷ ℕ ^ [ ! ,  ι ⁰ ]
    natrecⱼ : ∀ {G rG lG s z n}
           → Γ       ⊢⊢ z ∷ G [ zero ] ^ [ rG , ι lG ]
           → Γ       ⊢⊢ s ∷ Π ℕ ^ ! ° ⁰ ▹ (G ^ rG ° lG ▹▹ G [ suc (var Nat.zero) ]↑ ° lG ° lG ^ rG) ° lG ° lG ^ rG ^ [ rG , ι lG ]
           → Γ       ⊢⊢ n ∷ ℕ ^ [ ! ,  ι ⁰ ]
           → Γ       ⊢⊢ natrec lG G z s n ∷ G [ n ] ^ [ rG , ι lG ]
    Emptyrecⱼ : ∀ {A lA rA e}
           → Γ ⊢⊢ A ^ [ rA , ι lA ] → Γ ⊢⊢ e ∷ sEmpty ^ [ % ,  ι ⁰ ] -> Γ ⊢⊢ Emptyrec lA ⁰ A e ∷ A ^ [ rA , ι lA ]
    Idⱼ : ∀ {A l t u}
          → Γ ⊢⊢ t ∷ A ^ [ ! , ι l ]
          → Γ ⊢⊢ u ∷ A ^ [ ! , ι l ]
          → Γ ⊢⊢ Id A t u ∷ SProp ^ [ ! , next ⁰ ]
    Idreflⱼ : ∀ {A l t}
              → Γ ⊢⊢ t ∷ A ^ [ ! , ι l ]
              → Γ ⊢⊢ Idrefl A t ∷ (Id A t t) ^ [ % , ι ⁰ ]
    transpⱼ : ∀ {A l P t s u e}
              → Γ ∙ A ^ [ ! , l ] ⊢⊢ P ^ [ % , ι ⁰ ]
              → Γ ⊢⊢ t ∷ A ^ [ ! , l ]
              → Γ ⊢⊢ s ∷ P [ t ] ^ [ % , ι ⁰ ]
              → Γ ⊢⊢ u ∷ A ^ [ ! , l ]
              → Γ ⊢⊢ e ∷ (Id A t u) ^ [ % , ι ⁰ ]
              → Γ ⊢⊢ transp A P t s u e ∷ P [ u ] ^ [ % , ι ⁰ ]
    castⱼ : ∀ {A B r e t}
            → Γ ⊢⊢ e ∷ (Id (Univ r ⁰) A B) ^ [ % , ι ⁰ ]
            → Γ ⊢⊢ t ∷ A ^ [ r , ι ⁰ ]
            → Γ ⊢⊢ cast ⁰ A B e t ∷ B ^ [ r , ι ⁰ ]
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
                → Γ     ⊢⊢ F ≡ H ^ [ rF , ι lF ]
                → Γ ∙ F ^ [ rF , ι lF ] ⊢⊢ G ≡ E ^ [ rG , ι lG ]
                → Γ     ⊢⊢ Π F ^ rF ° lF ▹ G ° lG ° l ^ rG ≡ Π H ^ rF ° lF ▹ E ° lG ° l ^ rG ∷ (Univ rG l) ^ [ ! , next l ]
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
              → Γ ⊢⊢ A ≡ A' ^ [ ! , ι l ]
              → Γ ⊢⊢ t ≡ t' ∷ A ^ [ ! , ι l ]
              → Γ ⊢⊢ u ≡ u' ∷ A ^ [ ! , ι l ]
              → Γ ⊢⊢ Id A t u ≡ Id A' t' u' ∷ SProp ^ [ ! , next ⁰ ]
    cast-refl : ∀ {A B e t} → let l = ⁰ in
                  Γ ⊢⊢ A ≡ B ^ [ ! , ι l ]
                → Γ ⊢⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ]
                → Γ ⊢⊢ t ∷ A ^ [ ! , ι l ]
                → Γ ⊢⊢ cast l A B e t ≡ t ∷ B ^ [ ! , ι l ]            
    cast-cong : ∀ {A A' B B' e e' t t'} → let l = ⁰ in
                  Γ ⊢⊢ A ≡ A' ^ [ ! , ι l ]
                → Γ ⊢⊢ B ≡ B' ^ [ ! , ι l ]
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

mutual 
  wfTerm : ∀ {Γ A t r} → Γ ⊢⊢ t ∷ A ^ r → ⊢⊢ Γ
  wfTerm (univ <l ⊢⊢Γ) = ⊢⊢Γ
  wfTerm (ℕⱼ ⊢⊢Γ) = ⊢⊢Γ
  wfTerm (Emptyⱼ ⊢⊢Γ) = ⊢⊢Γ
  wfTerm (Πⱼ <l ▹ <l' ▹ G) with wf G
  ... | ⊢Γ ∙ F = ⊢Γ
  wfTerm (var ⊢⊢Γ x₁) = ⊢⊢Γ
  wfTerm (lamⱼ _ _ t) with wfTerm t
  wfTerm (lamⱼ _ _ t) | ⊢⊢Γ ∙ F′ = ⊢⊢Γ
  wfTerm (g ∘ⱼ a) = wfTerm a
  wfTerm (fstⱼ e) = wfTerm e
  wfTerm (sndⱼ e) = wfTerm e
  wfTerm (zeroⱼ ⊢⊢Γ) = ⊢⊢Γ
  wfTerm (sucⱼ n) = wfTerm n
  wfTerm (natrecⱼ z s n) = wfTerm z
  wfTerm (Emptyrecⱼ A e) = wfTerm e
  wfTerm (Idⱼ t u) = wfTerm t
  wfTerm (Idreflⱼ t) = wfTerm t
  wfTerm (transpⱼ P t s u e) = wfTerm t
  wfTerm (castⱼ e t) = wfTerm t
  wfTerm (conv t A≡B) = wfTerm t

  wf : ∀ {Γ A r} → Γ ⊢⊢ A ^ r → ⊢⊢ Γ
  wf (Uⱼ ⊢⊢Γ) = ⊢⊢Γ
  wf (univ A) = wfTerm A

adm-cast-ℕ-0 : ∀ {Γ e}
         → Γ ⊢⊢ e ∷ Id (U ⁰) ℕ ℕ ^ [ % , ι ⁰ ]
         → Γ ⊢⊢ cast ⁰ ℕ ℕ e zero ≡ zero ∷ ℕ ^ [ ! , ι ⁰ ]
adm-cast-ℕ-0 ⊢⊢e = let ⊢⊢Γ = wfTerm ⊢⊢e
                   in cast-refl (refl (univ (ℕⱼ ⊢⊢Γ))) ⊢⊢e (zeroⱼ ⊢⊢Γ)

adm-cast-ℕ-S : ∀ {Γ e n}
               → Γ ⊢⊢ e ∷ Id (U ⁰) ℕ ℕ ^ [ % , ι ⁰ ]
               → Γ ⊢⊢ n ∷ ℕ ^ [ ! , ι ⁰ ]
               → Γ ⊢⊢ cast ⁰ ℕ ℕ e (suc n) ≡ suc (cast ⁰ ℕ ℕ e n) ∷ ℕ ^ [ ! , ι ⁰ ]
adm-cast-ℕ-S ⊢⊢e ⊢⊢n = let ⊢⊢Γ = wfTerm ⊢⊢e
                       in trans (cast-refl (refl (univ (ℕⱼ ⊢⊢Γ))) ⊢⊢e (sucⱼ ⊢⊢n)) (suc-cong (sym (cast-refl (refl (univ (ℕⱼ ⊢⊢Γ))) ⊢⊢e ⊢⊢n)))


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
  ⊢is⊢⊢term (Πⱼ x ▹ x₁ ▹ X ▹ X₁) = Πⱼ x ▹ x₁ ▹ univ (⊢is⊢⊢term X₁)
  ⊢is⊢⊢term (var ⊢Γ x) = var (⊢is⊢⊢ctx ⊢Γ) x
  ⊢is⊢⊢term (lamⱼ x x₁ x₂ X) = lamⱼ x x₁ (⊢is⊢⊢term X)
  ⊢is⊢⊢term (x ▹ X ▹ X₁ ▹ X₂ ∘ⱼ X₃) = ⊢is⊢⊢term X₂ ∘ⱼ ⊢is⊢⊢term X₃
  ⊢is⊢⊢term (fstⱼ X X₁ _ _ X₂) = fstⱼ (⊢is⊢⊢term X₂)
  ⊢is⊢⊢term (sndⱼ X X₁ _ _ X₂) = sndⱼ (⊢is⊢⊢term X₂)
  ⊢is⊢⊢term (zeroⱼ x) = zeroⱼ (⊢is⊢⊢ctx x)
  ⊢is⊢⊢term (sucⱼ X) = sucⱼ (⊢is⊢⊢term X)
  ⊢is⊢⊢term (natrecⱼ x x₁ X X₁ X₂) = natrecⱼ (⊢is⊢⊢term X) (⊢is⊢⊢term X₁) (⊢is⊢⊢term X₂)
  ⊢is⊢⊢term (Emptyrecⱼ x X) = Emptyrecⱼ (⊢is⊢⊢ x) (⊢is⊢⊢term X)
  ⊢is⊢⊢term (Idⱼ X X₁ X₂) = Idⱼ (⊢is⊢⊢term X₁) (⊢is⊢⊢term X₂) 
  ⊢is⊢⊢term (Idreflⱼ X) = Idreflⱼ (⊢is⊢⊢term X)
  ⊢is⊢⊢term (transpⱼ x x₁ X X₁ X₂ X₃) = transpⱼ (⊢is⊢⊢ x₁) (⊢is⊢⊢term X) (⊢is⊢⊢term X₁) (⊢is⊢⊢term X₂) (⊢is⊢⊢term X₃)
  ⊢is⊢⊢term (castⱼ X X₁ X₂ X₃) = castⱼ (⊢is⊢⊢term X₂) (⊢is⊢⊢term X₃) 
  ⊢is⊢⊢term (conv X x) = conv (⊢is⊢⊢term X) (⊢is⊢⊢eq x)

  ⊢is⊢⊢eqterm (refl x) = refl (⊢is⊢⊢term x)
  ⊢is⊢⊢eqterm (sym X) = sym (⊢is⊢⊢eqterm X)
  ⊢is⊢⊢eqterm (trans X X₁) = trans (⊢is⊢⊢eqterm X) (⊢is⊢⊢eqterm X₁)
  ⊢is⊢⊢eqterm (conv X x) = conv (⊢is⊢⊢eqterm X) (⊢is⊢⊢eq x)
  ⊢is⊢⊢eqterm (Π-cong x x₁ x₂ X X₁) = Π-cong x x₁ (univ (⊢is⊢⊢eqterm X)) (univ (⊢is⊢⊢eqterm X₁))
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
  ⊢is⊢⊢eqterm (cast-refl X x x₁) = cast-refl (univ (⊢is⊢⊢eqterm X)) (⊢is⊢⊢term x) (⊢is⊢⊢term x₁)
  ⊢is⊢⊢eqterm (cast-cong X X₁ X₂ x x₁) = cast-cong (univ (⊢is⊢⊢eqterm X)) (univ (⊢is⊢⊢eqterm X₁)) (⊢is⊢⊢eqterm X₂) (⊢is⊢⊢term x) (⊢is⊢⊢term x₁)
  ⊢is⊢⊢eqterm (cast-Π x x₁ x₂ x₃ x₄ x₅) = cast-Π (⊢is⊢⊢term x₄) (⊢is⊢⊢term x₅)
  ⊢is⊢⊢eqterm (cast-ℕ-0 x) = adm-cast-ℕ-0 (⊢is⊢⊢term x)
  ⊢is⊢⊢eqterm (cast-ℕ-S x x₁) = adm-cast-ℕ-S (⊢is⊢⊢term x) (⊢is⊢⊢term x₁)


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
  ⊢⊢is⊢term (Πⱼ x ▹ x₁ ▹ X₁) =
    let ⊢G = ⊢⊢is⊢ X₁
        ⊢Γ , ⊢F = inversion-ctx (T.wf ⊢G)
    in Πⱼ x ▹ x₁ ▹ un-univ ⊢F ▹ un-univ ⊢G
  ⊢⊢is⊢term (var ⊢Γ x) = var (⊢⊢is⊢ctx ⊢Γ) x
  ⊢⊢is⊢term (lamⱼ x x₁ X) = let XX = ⊢⊢is⊢term X in lamⱼ x x₁ (let ⊢Γ , ⊢F = inversion-ctx (T.wfTerm XX) in ⊢F) XX
  ⊢⊢is⊢term (X₂ ∘ⱼ X₃) =
    let ⊢g = ⊢⊢is⊢term X₂ 
        ⊢a = ⊢⊢is⊢term X₃
        ⊢Π = un-univ (syntacticTerm ⊢g)
        rG , _ , l% , _ , ⊢G , _ , req , _ = inversion-Π ⊢Π
    in  PE.subst (λ rr → rr PE.≡ % → _ PE.≡ ⁰ × _ PE.≡ ⁰) req l% ▹ un-univ (syntacticTerm ⊢a) ▹ PE.subst (λ rr → _ ⊢ _ ∷ Univ rr _ ^ [ ! , _ ]) req ⊢G ▹ ⊢g ∘ⱼ ⊢a
  ⊢⊢is⊢term (fstⱼ X) = 
    let ⊢e = ⊢⊢is⊢term X
        l , _ , ⊢Π , ⊢Π' , e , er = inversion-Id (un-univ (syntacticTerm ⊢e))
        rG , _ , _ , ⊢A , ⊢B , _ , req , _ = inversion-Π ⊢Π
        rG' , _ , _ , ⊢A' , ⊢B' , _ , req' , _ = inversion-Π ⊢Π'
    in fstⱼ ⊢A (PE.subst (λ rr → _ ⊢ _ ∷ Univ rr _ ^ [ ! , _ ]) req ⊢B) ⊢A' (PE.subst (λ rr → _ ⊢ _ ∷ Univ rr _ ^ [ ! , _ ]) req' ⊢B') ⊢e
  ⊢⊢is⊢term (sndⱼ X) =
    let ⊢e = ⊢⊢is⊢term X
        l , _ , ⊢Π , ⊢Π' , e , er = inversion-Id (un-univ (syntacticTerm ⊢e))
        rG , _ , _ , ⊢A , ⊢B , _ , req , _ = inversion-Π ⊢Π
        rG' , _ , _ , ⊢A' , ⊢B' , _ , req' , _ = inversion-Π ⊢Π'
    in sndⱼ ⊢A (PE.subst (λ rr → _ ⊢ _ ∷ Univ rr _ ^ [ ! , _ ]) req ⊢B) ⊢A' (PE.subst (λ rr → _ ⊢ _ ∷ Univ rr _ ^ [ ! , _ ]) req' ⊢B') ⊢e
  ⊢⊢is⊢term (zeroⱼ x) = zeroⱼ (⊢⊢is⊢ctx x)
  ⊢⊢is⊢term (sucⱼ X) = sucⱼ (⊢⊢is⊢term X)
  ⊢⊢is⊢term (natrecⱼ X X₁ X₂) =
    let ⊢s = ⊢⊢is⊢term X₁ 
        ⊢Π = un-univ (syntacticTerm ⊢s)
        rG , _ , l% , _ , ⊢GG , _ , req , _ = inversion-Π ⊢Π
        rG , _ , l% , ⊢G , _ , _ , req , _ = inversion-Π ⊢GG
        l% = PE.subst (λ rr → rr PE.≡ % → _ PE.≡ ⁰ × _ PE.≡ ⁰) req l%
    in natrecⱼ (λ req → proj₁ (l% req)) (univ ⊢G) (⊢⊢is⊢term X) ⊢s (⊢⊢is⊢term X₂)
  ⊢⊢is⊢term (Emptyrecⱼ x X) = Emptyrecⱼ (⊢⊢is⊢ x) (⊢⊢is⊢term X)
  ⊢⊢is⊢term (Idⱼ X₁ X₂) =
    let ⊢t = (⊢⊢is⊢term X₁)
    in Idⱼ (un-univ (syntacticTerm ⊢t)) ⊢t (⊢⊢is⊢term X₂) 
  ⊢⊢is⊢term (Idreflⱼ X) = Idreflⱼ (⊢⊢is⊢term X)
  ⊢⊢is⊢term (transpⱼ x₁ X X₁ X₂ X₃) =
    let ⊢t = (⊢⊢is⊢term X)
    in transpⱼ (syntacticTerm ⊢t) (⊢⊢is⊢ x₁) ⊢t (⊢⊢is⊢term X₁) (⊢⊢is⊢term X₂) (⊢⊢is⊢term X₃)
  ⊢⊢is⊢term (castⱼ X₂ X₃) =
    let ⊢e = ⊢⊢is⊢term X₂
        ⊢Id = un-univ (syntacticTerm ⊢e)
        _ , ⊢U , ⊢A , ⊢B , _ = inversion-Id ⊢Id
        Ueq , _ = inversion-U ⊢U
        _ , leq , _ = Uinjectivity Ueq
    in castⱼ (PE.subst (λ l → _ ⊢ _ ∷ _ ^ [ ! , ι l ]) leq ⊢A) (PE.subst (λ l → _ ⊢ _ ∷ _ ^ [ ! , ι l ]) leq ⊢B) ⊢e (⊢⊢is⊢term X₃) 
  ⊢⊢is⊢term (conv X x) = conv (⊢⊢is⊢term X) (⊢⊢is⊢eq x)

  ⊢⊢is⊢eqterm (refl x) = refl (⊢⊢is⊢term x)
  ⊢⊢is⊢eqterm (sym X) = sym (⊢⊢is⊢eqterm X)
  ⊢⊢is⊢eqterm (trans X X₁) = trans (⊢⊢is⊢eqterm X) (⊢⊢is⊢eqterm X₁)
  ⊢⊢is⊢eqterm (conv X x) = conv (⊢⊢is⊢eqterm X) (⊢⊢is⊢eq x)
  ⊢⊢is⊢eqterm (Π-cong x x₁ X X₁) =
    let ⊢FH = ⊢⊢is⊢eq X
        ⊢F , _ = syntacticEq ⊢FH
    in Π-cong x x₁ ⊢F (un-univ≡ ⊢FH) (un-univ≡ (⊢⊢is⊢eq X₁))
  ⊢⊢is⊢eqterm (app-cong X X₁) = app-cong (⊢⊢is⊢eqterm X) (⊢⊢is⊢eqterm X₁)
  ⊢⊢is⊢eqterm (β-red x x₁ x₃ x₄) =
    let ⊢t = ⊢⊢is⊢term x₃
    in β-red x x₁ (let ⊢Γ , ⊢F = inversion-ctx (T.wfTerm ⊢t) in ⊢F) ⊢t (⊢⊢is⊢term x₄)
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
  ⊢⊢is⊢eqterm (cast-refl X x x₁) = cast-refl (un-univ≡ (⊢⊢is⊢eq X)) (⊢⊢is⊢term x) (⊢⊢is⊢term x₁)
  ⊢⊢is⊢eqterm (cast-cong X X₁ X₂ x x₁) = cast-cong (un-univ≡ (⊢⊢is⊢eq X)) (un-univ≡ (⊢⊢is⊢eq X₁)) (⊢⊢is⊢eqterm X₂) (⊢⊢is⊢term x) (⊢⊢is⊢term x₁)
  ⊢⊢is⊢eqterm (cast-Π x₄ x₅) =
    let ⊢e = ⊢⊢is⊢term x₄
        ⊢Id = un-univ (syntacticTerm ⊢e)
        _ , _ , ⊢Π , ⊢Π' , _ = inversion-Id ⊢Id
        _ , _ , _ , ⊢F , ⊢G , _ , req , _ = inversion-Π ⊢Π
        _ , _ , _ , ⊢F' , ⊢G' , _ , req' , _ = inversion-Π ⊢Π'
    in cast-Π ⊢F (PE.subst (λ rr → _ ⊢ _ ∷ Univ rr _ ^ [ ! , _ ]) req ⊢G) ⊢F' (PE.subst (λ rr → _ ⊢ _ ∷ Univ rr _ ^ [ ! , _ ]) req' ⊢G') ⊢e (⊢⊢is⊢term x₅)
