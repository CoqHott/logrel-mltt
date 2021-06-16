{-# OPTIONS --without-K  #-}

module Definition.Typed where

open import Definition.Untyped

open import Tools.Nat using (Nat)
open import Tools.Product


infixl 30 _∙_
infix 30 Πⱼ_▹_

{- Types of constructors and destructors -}
-- All Types `(d : dom) → cod` are assumed to be globally closed

postulate cstr-dom : constructors → Term
postulate cstr-cod : constructors → Term
-- Hypothesis: cstr-cod is a non-neutral whnf
-- postulate cstr-cod-whnf : (k : constructors) → Whnf (cstr-cod k)

postulate cstr-dom-sort : constructors → 𝕊
postulate cstr-cod-sort : constructors → 𝕊


postulate dstr-param : destructors → Term
postulate dstr-dom : destructors → Term
postulate dstr-cod : destructors → Term
-- KM: Shouldn't this constructor target 𝕊 directly ?
postulate dstr-param-sort : destructors → 𝕊
postulate dstr-dom-sort : destructors → 𝕊
postulate dstr-cod-sort : destructors → 𝕊

cstr-𝕊 : constructors → 𝕊
cstr-𝕊 k = cstr-cod-sort k

cstr-dom-ctx : Con Term → constructors → Term
cstr-dom-ctx Γ k = wkAll Γ (cstr-dom k)

cstr-cod-ctx : Con Term → constructors → Term
cstr-cod-ctx Γ k = wk (lift (empty-wk Γ)) (cstr-cod k)

cstr-type : Con Term → constructors → Term → Term
cstr-type Γ k a = (cstr-cod-ctx Γ k) [ a ]
-- cstr-type Γ k = wkAll Γ (Π cstr-dom k ⦂ cstr-dom-sort k ▹ cstr-cod k)

dstr-𝕊 : destructors → 𝕊
dstr-𝕊 o = dstr-cod-sort o

dstr-param-ctx : Con Term → destructors → Term
dstr-param-ctx Γ k = wkAll Γ (dstr-param k)

dstr-dom-ctx : Con Term → destructors → Term
dstr-dom-ctx Γ k = wkAll Γ (dstr-dom k)

dstr-cod-ctx : Con Term → destructors → Term
dstr-cod-ctx Γ k = wk (lift (lift (empty-wk Γ))) (dstr-cod k)

dstr-type : Con Term → destructors → Term → Term → Term
dstr-type Γ o t p = (dstr-cod-ctx Γ o) [ wk1 t ] [ p ]
-- wkAll Γ (Π dstr-dom o ⦂ dstr-dom-sort o ▹ Π dstr-param o ⦂ dstr-param-sort o ▹  dstr-cod o)

{- Rewrite rules -}
postulate Rew⊢_⊚_⊚_⇒_ : destructors → Term → Term → Term → Set

record RewriteRules : Set where
  field
    rew-lhs-head : destructors
    rew-lhs-arg : Term
    rew-lhs-param : Term
    rew-rhs : Term
    rew-rule : Rew⊢ rew-lhs-head ⊚ rew-lhs-arg ⊚ rew-lhs-param ⇒ rew-rhs

open RewriteRules public

rew-𝕊 : RewriteRules → 𝕊
rew-𝕊 r = dstr-𝕊 (rew-lhs-head r)

data _𝕊⊢_⊚_⊚_⇒_⦂_ (Γ : Con Term) (o : destructors) : Term → Term → Term → 𝕊 → Set where
  rew : ∀ {ρ a p t}
        → Rew⊢ o ⊚ a ⊚ p ⇒ t
        → Γ 𝕊⊢ o ⊚ subst ρ a ⊚ subst ρ p ⇒ subst ρ t ⦂ dstr-𝕊 o


-- Well-typed variables
data _∷_⦂_∈_ : (x : Nat) (A : Term) (s : 𝕊) (Γ : Con Term) → Set where
  here  : ∀ {Γ A s}                     →         0 ∷ wk1 A ⦂ s ∈ (Γ ∙ A ⦂ s )
  there : ∀ {Γ A sA B sB x} (h : x ∷ A ⦂ sA ∈ Γ) → Nat.suc x ∷ wk1 A ⦂ sA ∈ (Γ ∙ B ⦂ sB)

mutual
  -- Well-formed context
  data ⊢_ : Con Term → Set where
    ε   : ⊢ ε
    _∙_ : ∀ {Γ A s}
        → ⊢ Γ
        → Γ ⊢ A ⦂ s
        → ⊢ Γ ∙ A ⦂ s

  -- Well-formed type
  data _⊢_⦂_ (Γ : Con Term) : Term → 𝕊 → Set where
    ℕⱼ    : ⊢ Γ → Γ ⊢ ℕ ⦂ 𝕥y
    Emptyⱼ : ⊢ Γ -> Γ ⊢ Empty ⦂ 𝕥y
    Uⱼ    : ∀ {s} → ⊢ Γ → Γ ⊢ (Univ s) ⦂ 𝕥y
    Πⱼ_▹_ : ∀ {F sF G sG}
         → Γ     ⊢ F ⦂ sF
         → Γ ∙ F ⦂ sF ⊢ G ⦂ sG
         → Γ     ⊢ Π F ⦂ sF ▹ G ⦂ sG
    Boxⱼ : ∀ {s A}
         → Γ ⊢ A ⦂ ‼ s
         → Γ ⊢ Box s A ⦂ 𝕥y
    univ : ∀ {A s}
         → Γ ⊢ A ∷ (Univ s) ⦂ 𝕥y
         → Γ ⊢ A ⦂ s

  -- Well-formed term of a type
  data _⊢_∷_⦂_ (Γ : Con Term) : Term → Term → 𝕊 → Set where
    ℕⱼ      : ⊢ Γ → Γ ⊢ ℕ ∷ U ⦂ 𝕥y
    Emptyⱼ :  ⊢ Γ → Γ ⊢ Empty ∷ U ⦂ 𝕥y
    Πⱼ_▹_   : ∀ {F sF G sG}
           → Γ     ⊢ F ∷ (Univ sF) ⦂ 𝕥y
           → Γ ∙ F ⦂ sF ⊢ G ∷ (Univ sG) ⦂ 𝕥y
           → Γ     ⊢ Π F ⦂ sF ▹ G ∷ (Univ sG) ⦂ 𝕥y
    Boxⱼ : ∀ {s A}
         → Γ ⊢ A ∷ 𝕌 s ⦂ 𝕥y
         → Γ ⊢ Box s A ∷ U ⦂ 𝕥y
    var    : ∀ {A s x}
           → ⊢ Γ
           → x ∷ A ⦂ s ∈ Γ
           → Γ ⊢ var x ∷ A ⦂ s
    lamⱼ    : ∀ {F sF G sG t}
           → Γ     ⊢ F ⦂ sF
           → Γ ∙ F ⦂ sF ⊢ t ∷ G ⦂ sG
           → Γ     ⊢ lam F ▹ t ∷ Π F ⦂ sF ▹ G ⦂ sG
    _∘ⱼ_    : ∀ {g a F sF G sG}
           → Γ ⊢     g ∷ Π F ⦂ sF ▹ G ⦂ sG
           → Γ ⊢     a ∷ F ⦂ sF
           → Γ ⊢ g ∘ a ∷ G [ a ] ⦂ sG
    zeroⱼ   : ⊢ Γ
           → Γ ⊢ zero ∷ ℕ ⦂ 𝕥y
    sucⱼ    : ∀ {n}
           → Γ ⊢ n ∷ ℕ ⦂ 𝕥y
           → Γ ⊢ suc n ∷ ℕ ⦂ 𝕥y
    natrecⱼ : ∀ {G sG s z n}
           → Γ ∙ ℕ ⦂ 𝕥y ⊢ G ⦂ sG
           → Γ       ⊢ z ∷ G [ zero ] ⦂ sG
           → Γ       ⊢ s ∷ Π ℕ ⦂ 𝕥y ▹ (G ⦂ sG ▹▹ G [ suc (var Nat.zero) ]↑) ⦂ sG
           → Γ       ⊢ n ∷ ℕ ⦂ 𝕥y
           → Γ       ⊢ natrec G z s n ∷ G [ n ] ⦂ sG
    Emptyrecⱼ : ∀ {A sA e}
           → Γ ⊢ A ⦂ sA → Γ ⊢ e ∷ Empty ⦂ 𝕥y → Γ ⊢ Emptyrec A e ∷ A ⦂ sA
    -- TODO: Do the other boxes
    boxⱼ   : ∀ {t A s}
           → Γ ⊢ t ∷ A ⦂ ‼ s
           → Γ ⊢ box s t ∷ Box s A ⦂ 𝕥y
    Boxrecⱼ   : ∀ {sA sC A C t u}
            → Γ ⊢ A ⦂ ‼ sA
            → Γ ∙ Box sA A ⦂ 𝕥y ⊢ C ⦂ sC
            → Γ ⊢ u ∷ Π A ⦂ ‼ sA ▹ (C [ box sA (var 0) ]↑) ⦂ sC
            → Γ ⊢ t ∷ Box sA A ⦂ 𝕥y
            → Γ ⊢ Boxrec sC A C u t ∷ C [ t ] ⦂ sC
    cstrⱼ  : ∀ {k a}
           → Γ ⊢ cstr-dom-ctx Γ k ⦂ cstr-dom-sort k
           → Γ ∙ cstr-dom-ctx Γ k ⦂ cstr-dom-sort k ⊢ cstr-cod-ctx Γ k ⦂ cstr-cod-sort k
           → (∀ ki → [ k ]-cstr (cstr-cod ki) → Γ ⊢ cstr-dom-ctx Γ ki ⦂ cstr-dom-sort ki)
           -- → (∀ di → [ k ]-cstr (dstr-dom di) → Γ ⊢ dstr-dom-ctx Γ ki ⦂ dstr-dom-sort ki) TODO: negative cstr types
           → Γ ⊢ a ∷ cstr-dom-ctx Γ k ⦂ cstr-dom-sort k
           → Γ ⊢ cstr k ∘ a ∷  (cstr-cod-ctx Γ k) [ a ] ⦂ cstr-𝕊 k
    dstrⱼ  : ∀ {o p a}
           → Γ ⊢ dstr-dom-ctx Γ o ⦂ dstr-dom-sort o
           → Γ ⊢ dstr-param-ctx Γ o ⦂ dstr-param-sort o
           → let Γ' = Γ ∙ dstr-param-ctx Γ o ⦂ dstr-param-sort o in
             Γ' ∙ dstr-dom-ctx Γ' o ⦂ dstr-dom-sort o ⊢ dstr-cod-ctx Γ o ⦂ dstr-cod-sort o
           → Γ ⊢ a ∷ dstr-dom-ctx Γ o ⦂ dstr-dom-sort o
           → Γ ⊢ p ∷ dstr-param-ctx Γ o ⦂ dstr-param-sort o
           → Γ ⊢ dstr′ o a p ∷ dstr-type Γ o a p ⦂ dstr-𝕊 o
    conv   : ∀ {t A B s}
           → Γ ⊢ t ∷ A ⦂ s
           → Γ ⊢ A ≡ B ⦂ s
           → Γ ⊢ t ∷ B ⦂ s

  -- Type equality
  data _⊢_≡_⦂_ (Γ : Con Term) : Term → Term → 𝕊 → Set where
    univ   : ∀ {A B s}
           → Γ ⊢ A ≡ B ∷ (Univ s) ⦂ 𝕥y
           → Γ ⊢ A ≡ B ⦂ s
    refl   : ∀ {A s}
           → Γ ⊢ A ⦂ s
           → Γ ⊢ A ≡ A ⦂ s
    sym    : ∀ {A B s}
           → Γ ⊢ A ≡ B ⦂ s
           → Γ ⊢ B ≡ A ⦂ s
    trans  : ∀ {A B C s}
           → Γ ⊢ A ≡ B ⦂ s
           → Γ ⊢ B ≡ C ⦂ s
           → Γ ⊢ A ≡ C ⦂ s
    Π-cong : ∀ {F H sF G E sG}
           → Γ     ⊢ F ⦂ sF
           → Γ     ⊢ F ≡ H ⦂ sF
           → Γ ∙ F ⦂ sF ⊢ G ≡ E ⦂ sG
           → Γ     ⊢ Π F ⦂ sF ▹ G ≡ Π H ⦂ sF ▹ E ⦂ sG
    Box-cong : ∀ {F H s}
             → Γ ⊢ F ⦂ ‼ s
             → Γ ⊢ F ≡ H ⦂ ‼ s
             → Γ ⊢ Box s F ≡ Box s H ⦂ 𝕥y
  -- Term equality
  data _⊢_≡_∷_⦂_ (Γ : Con Term) : Term → Term → Term → 𝕊 → Set where
    refl        : ∀ {t A s}
                → Γ ⊢ t ∷ A ⦂ s
                → Γ ⊢ t ≡ t ∷ A ⦂ s
    sym         : ∀ {t u A s}
                → Γ ⊢ t ≡ u ∷ A ⦂ s
                → Γ ⊢ u ≡ t ∷ A ⦂ s
    trans       : ∀ {t u v A s}
                → Γ ⊢ t ≡ u ∷ A ⦂ s
                → Γ ⊢ u ≡ v ∷ A ⦂ s
                → Γ ⊢ t ≡ v ∷ A ⦂ s
    conv        : ∀ {A B t u s}
                → Γ ⊢ t ≡ u ∷ A ⦂ s
                → Γ ⊢ A ≡ B ⦂ s
                → Γ ⊢ t ≡ u ∷ B ⦂ s
    Π-cong      : ∀ {E F G H sF sG}
                → Γ     ⊢ F ⦂ sF
                → Γ     ⊢ F ≡ H       ∷ (Univ sF) ⦂ 𝕥y
                → Γ ∙ F ⦂ sF ⊢ G ≡ E       ∷ (Univ sG) ⦂ 𝕥y
                → Γ     ⊢ Π F ⦂ sF ▹ G ≡ Π H ⦂ sF ▹ E ∷ (Univ sG) ⦂ 𝕥y
    app-cong    : ∀ {a b f g F G sF sG}
                → Γ ⊢ f ≡ g ∷ Π F ⦂ sF ▹ G ⦂ sG
                → Γ ⊢ a ≡ b ∷ F ⦂ sF
                → Γ ⊢ f ∘ a ≡ g ∘ b ∷ G [ a ] ⦂ sG
    β-red       : ∀ {a t F sF G sG}
                → Γ     ⊢ F ⦂ sF
                → Γ ∙ F ⦂ sF ⊢ t ∷ G ⦂ sG
                → Γ     ⊢ a ∷ F ⦂ sF
                → Γ     ⊢ (lam F ▹ t) ∘ a ≡ t [ a ] ∷ G [ a ] ⦂ sG
    η-eq        : ∀ {f g F sF G sG}
                → Γ     ⊢ F ⦂ sF
                → Γ     ⊢ f ∷ Π F ⦂ sF ▹ G ⦂ sG
                → Γ     ⊢ g ∷ Π F ⦂ sF ▹ G ⦂ sG
                → Γ ∙ F ⦂ sF ⊢ wk1 f ∘ var Nat.zero ≡ wk1 g ∘ var Nat.zero ∷ G ⦂ sG
                → Γ     ⊢ f ≡ g ∷ Π F ⦂ sF ▹ G ⦂ sG
    suc-cong    : ∀ {m n}
                → Γ ⊢ m ≡ n ∷ ℕ ⦂ 𝕥y
                → Γ ⊢ suc m ≡ suc n ∷ ℕ ⦂ 𝕥y
    natrec-cong : ∀ {z z′ s s′ n n′ F F′ sF}
                → Γ ∙ ℕ ⦂ 𝕥y ⊢ F ≡ F′ ⦂ sF
                → Γ     ⊢ z ≡ z′ ∷ F [ zero ] ⦂ sF
                → Γ     ⊢ s ≡ s′ ∷ Π ℕ ⦂ 𝕥y ▹ (F ⦂ sF ▹▹ F [ suc (var Nat.zero) ]↑) ⦂ sF
                → Γ     ⊢ n ≡ n′ ∷ ℕ ⦂ 𝕥y
                → Γ     ⊢ natrec F z s n ≡ natrec F′ z′ s′ n′ ∷ F [ n ] ⦂ sF
    natrec-zero : ∀ {z s F sF}
                → Γ ∙ ℕ ⦂ 𝕥y ⊢ F ⦂ sF
                → Γ     ⊢ z ∷ F [ zero ] ⦂ sF
                → Γ     ⊢ s ∷ Π ℕ ⦂ 𝕥y ▹ (F ⦂ sF ▹▹ F [ suc (var Nat.zero) ]↑) ⦂ sF
                → Γ     ⊢ natrec F z s zero ≡ z ∷ F [ zero ] ⦂ sF
    natrec-suc  : ∀ {n z s F sF}
                → Γ     ⊢ n ∷ ℕ ⦂ 𝕥y
                → Γ ∙ ℕ ⦂ 𝕥y ⊢ F ⦂ sF
                → Γ     ⊢ z ∷ F [ zero ] ⦂ sF
                → Γ     ⊢ s ∷ Π ℕ ⦂ 𝕥y ▹ (F ⦂ sF ▹▹ F [ suc (var Nat.zero) ]↑) ⦂ sF
                → Γ     ⊢ natrec F z s (suc n) ≡ (s ∘ n) ∘ (natrec F z s n)
                        ∷ F [ suc n ] ⦂ sF
    Emptyrec-cong : ∀ {A A' e e' s}
                → Γ ⊢ A ≡ A' ⦂ s
                → Γ ⊢ e ≡ e' ∷ Empty ⦂ 𝕥y
                → Γ ⊢ Emptyrec A e ≡ Emptyrec A' e' ∷ A ⦂ s
    Box-cong : ∀ {F H s}
             → Γ ⊢ F ∷ 𝕌 s ⦂ 𝕥y
             → Γ ⊢ F ≡ H ∷ 𝕌 s ⦂ 𝕥y
             → Γ ⊢ Box s F ≡ Box s H ∷ 𝕌 s ⦂ 𝕥y
    box-cong : ∀ {a a' F s}
             → Γ ⊢ F ⦂ ‼ s
             → Γ ⊢ a ∷ F ⦂ ‼ s
             → Γ ⊢ a' ∷ F ⦂ ‼ s
             → Γ ⊢ a ≡ a' ∷ F ⦂ ‼ s
             → Γ ⊢ box s a ≡ box s a' ∷ Box s F ⦂ 𝕥y
    Boxrec-cong : ∀ {sF sE E E' F F' t t' u u'}
                → Γ ⊢ F ⦂ ‼ sF
                → Γ ⊢ F ≡ F' ⦂ ‼ sF
                → Γ ∙ Box sF F ⦂ 𝕥y ⊢ E ≡ E' ⦂ sE -- ∷ U𝕤 sF ⦂ 𝕥y ?
                → Γ ⊢ u ≡ u' ∷ Π F ⦂ ‼ sF ▹ (E [ box sF (var 0) ]↑) ⦂ sE
                → Γ ⊢ t ≡ t' ∷ Box sF F ⦂ 𝕥y
                → Γ ⊢ Boxrec sE F E u t ≡ Boxrec sE F' E' u' t' ∷ E [ t ] ⦂ sE
    Boxrec-box : ∀ {sF sE E F a u}
               → Γ ⊢ F ⦂ ‼ sF
               → Γ ∙ Box sF F ⦂ 𝕥y ⊢ E ⦂ sE
               → Γ ⊢ u ∷ Π F ⦂ ‼ sF ▹ (E [ box sF (var 0) ]↑) ⦂ sE
               → Γ ⊢ a ∷ F ⦂ ‼ sF
               → Γ ⊢ Boxrec sE F E u (box sF a) ≡ u ∘ a ∷ E [ box sF a ] ⦂ sE
    cstr-cong  : ∀ {a a' k}
               → Γ ⊢ a ≡ a' ∷ cstr-dom-ctx Γ k ⦂ cstr-dom-sort k
               → Γ ⊢ cstr k ∘ a ≡ cstr k ∘ a' ∷ cstr-type Γ k a ⦂ cstr-𝕊 k
    dstr-cong  : ∀ {a a' p p' k}
               → Γ ⊢ a ≡ a' ∷ dstr-dom-ctx Γ k ⦂ dstr-dom-sort k
               → Γ ⊢ p ≡ p' ∷ dstr-param-ctx Γ k ⦂ dstr-param-sort k
               → Γ ⊢ dstr′ k a p ≡ dstr′ k a' p' ∷ dstr-type Γ k a p ⦂ dstr-𝕊 k
    rew        : ∀ {A s k p a t}
               → Γ 𝕊⊢ k ⊚ a ⊚ p ⇒ t ⦂ s
               → Γ ⊢ dstr′ k a p ∷ A ⦂ s
               → Γ ⊢ dstr′ k a p ≡ t ∷ A ⦂ s

-- Term reduction
data _⊢_⇒_∷_⦂_ (Γ : Con Term) : Term → Term → Term → 𝕊 → Set where
  conv         : ∀ {A B t u s}
               → Γ ⊢ t ⇒ u ∷ A ⦂ s
               → Γ ⊢ A ≡ B ⦂ s
               → Γ ⊢ t ⇒ u ∷ B ⦂ s
  app-subst    : ∀ {A B t u a sA sB}
               → Γ ⊢ t ⇒ u ∷ Π A ⦂ sA ▹ B ⦂ sB
               → Γ ⊢ a ∷ A ⦂ sA
               → Γ ⊢ t ∘ a ⇒ u ∘ a ∷ B [ a ] ⦂ sB
  β-red        : ∀ {A B a t sA sB}
               → Γ     ⊢ A ⦂ sA
               → Γ ∙ A ⦂ sA ⊢ t ∷ B ⦂ sB
               → Γ     ⊢ a ∷ A ⦂ sA
               → Γ     ⊢ (lam A ▹ t) ∘ a ⇒ t [ a ] ∷ B [ a ] ⦂ sB
  natrec-subst : ∀ {z s n n′ F sF}
               → Γ ∙ ℕ ⦂ 𝕥y ⊢ F ⦂ sF
               → Γ     ⊢ z ∷ F [ zero ] ⦂ sF
               → Γ     ⊢ s ∷ Π ℕ ⦂ 𝕥y ▹ (F ⦂ sF ▹▹ F [ suc (var Nat.zero) ]↑) ⦂ sF
               → Γ     ⊢ n ⇒ n′ ∷ ℕ ⦂ 𝕥y
               → Γ     ⊢ natrec F z s n ⇒ natrec F z s n′ ∷ F [ n ] ⦂ sF
  natrec-zero  : ∀ {z s F sF}
               → Γ ∙ ℕ ⦂ 𝕥y ⊢ F ⦂ sF
               → Γ     ⊢ z ∷ F [ zero ] ⦂ sF
               → Γ     ⊢ s ∷ Π ℕ ⦂ 𝕥y ▹ (F ⦂ sF ▹▹ F [ suc (var Nat.zero) ]↑) ⦂ sF
               → Γ     ⊢ natrec F z s zero ⇒ z ∷ F [ zero ] ⦂ sF
  natrec-suc   : ∀ {n z s F sF}
               → Γ     ⊢ n ∷ ℕ ⦂ 𝕥y
               → Γ ∙ ℕ ⦂ 𝕥y ⊢ F ⦂ sF
               → Γ     ⊢ z ∷ F [ zero ] ⦂ sF
               → Γ     ⊢ s ∷ Π ℕ ⦂ 𝕥y ▹ (F ⦂ sF ▹▹ F [ suc (var Nat.zero) ]↑) ⦂ sF
               → Γ     ⊢ natrec F z s (suc n) ⇒ (s ∘ n) ∘ (natrec F z s n)
                       ∷ F [ suc n ] ⦂ sF
  Emptyrec-subst : ∀ {n n′ A s}
               → Γ ⊢ A ⦂ s
               → Γ     ⊢ n ⇒ n′ ∷ Empty ⦂ 𝕥y
               → Γ     ⊢ Emptyrec A n ⇒ Emptyrec A n′ ∷ A ⦂ s
  Boxrec-subst : ∀ {sF sE E F t t' u}
               → Γ ⊢ F ⦂ ‼ sF
               → Γ ∙ Box sF F ⦂ 𝕥y ⊢ E ⦂ sE -- ∷ U𝕤 sF ⦂ 𝕥y ?
               → Γ ⊢ u ∷ Π F ⦂ ‼ sF ▹ (E [ box sF (var 0) ]↑) ⦂ sE
               → Γ ⊢ t ⇒ t' ∷ Box sF F ⦂ 𝕥y
               → Γ ⊢ Boxrec sE F E u t ⇒ Boxrec sE F E u t' ∷ E [ t ] ⦂ sE
  Boxrec-box   : ∀ {sF sE E F a u}
               → Γ ⊢ F ⦂ ‼ sF
               → Γ ∙ Box sF F ⦂ 𝕥y ⊢ E ⦂ sE
               → Γ ⊢ u ∷ Π F ⦂ ‼ sF ▹ (E [ box sF (var 0) ]↑) ⦂ sE
               → Γ ⊢ a ∷ F ⦂ ‼ sF
               → Γ ⊢ Boxrec sE F E u (box sF a) ⇒ u ∘ a ∷ E [ box sF a ] ⦂ sE
  rew          : ∀ {A s k p a t}
               → Γ 𝕊⊢ k ⊚ a ⊚ p ⇒ t ⦂ s
               → Γ ⊢ dstr′ k a p ∷ A ⦂ s
               → Γ ⊢ dstr′ k a p ⇒ t ∷ A ⦂ s

-- pattern dstr-cong d p≡p' t≡t' = app-cong (app-subst d p≡p') t≡t'
-- pattern dstr-subst d ⊢p ⊢t = app-subst (app-subst d ⊢p) ⊢t

-- Type reduction
data _⊢_⇒_⦂_ (Γ : Con Term) : Term → Term → 𝕊 → Set where
  univ : ∀ {A B s}
       → Γ ⊢ A ⇒ B ∷ (Univ s) ⦂ 𝕥y
       → Γ ⊢ A ⇒ B ⦂ s

-- Term reduction closure
data _⊢_⇒*_∷_⦂_ (Γ : Con Term) : Term → Term → Term → 𝕊 → Set where
  id  : ∀ {A t s}
      → Γ ⊢ t ∷ A ⦂ s
      → Γ ⊢ t ⇒* t ∷ A ⦂ s
  _⇨_ : ∀ {A t t′ u s}
      → Γ ⊢ t  ⇒  t′ ∷ A ⦂ s
      → Γ ⊢ t′ ⇒* u  ∷ A ⦂ s
      → Γ ⊢ t  ⇒* u  ∷ A ⦂ s

-- Type reduction closure
data _⊢_⇒*_⦂_ (Γ : Con Term) : Term → Term → 𝕊 → Set where
  id  : ∀ {A s}
      → Γ ⊢ A ⦂ s
      → Γ ⊢ A ⇒* A ⦂ s
  _⇨_ : ∀ {A A′ B s}
      → Γ ⊢ A  ⇒  A′ ⦂ s
      → Γ ⊢ A′ ⇒* B ⦂ s
      → Γ ⊢ A  ⇒* B ⦂ s

-- Type reduction to whnf
_⊢_↘_⦂_ : (Γ : Con Term) → Term → Term → 𝕊 → Set
Γ ⊢ A ↘ B ⦂ s = Γ ⊢ A ⇒* B ⦂ s × Whnf B

-- Term reduction to whnf
_⊢_↘_∷_⦂_ : (Γ : Con Term) → Term → Term → Term → 𝕊 → Set
Γ ⊢ t ↘ u ∷ A ⦂ s = Γ ⊢ t ⇒* u ∷ A ⦂ s × Whnf u

-- Type eqaulity with well-formed types
_⊢_:≡:_⦂_ : (Γ : Con Term) → Term → Term → 𝕊 → Set
Γ ⊢ A :≡: B ⦂ s = Γ ⊢ A ⦂ s × Γ ⊢ B ⦂ s × (Γ ⊢ A ≡ B ⦂ s)

-- Term equality with well-formed terms
_⊢_:≡:_∷_⦂_ : (Γ : Con Term) → Term → Term → Term → 𝕊 → Set
Γ ⊢ t :≡: u ∷ A ⦂ s = Γ ⊢ t ∷ A ⦂ s × Γ ⊢ u ∷ A ⦂ s × (Γ ⊢ t ≡ u ∷ A ⦂ s)

-- Type reduction closure with well-formed types
record _⊢_:⇒*:_⦂_ (Γ : Con Term) (A B : Term) (s : 𝕊) : Set where
  constructor [_,_,_]
  field
    ⊢A : Γ ⊢ A ⦂ s
    ⊢B : Γ ⊢ B ⦂ s
    D  : Γ ⊢ A ⇒* B ⦂ s

open _⊢_:⇒*:_⦂_ using () renaming (D to red) public

-- Term reduction closure with well-formed terms
record _⊢_:⇒*:_∷_⦂_ (Γ : Con Term) (t u A : Term) (s : 𝕊) : Set where
  constructor [_,_,_]
  field
    ⊢t : Γ ⊢ t ∷ A ⦂ s
    ⊢u : Γ ⊢ u ∷ A ⦂ s
    d  : Γ ⊢ t ⇒* u ∷ A ⦂ s

open _⊢_:⇒*:_∷_⦂_ using () renaming (d to redₜ) public

-- Well-formed substitutions.
data _⊢ˢ_∷_ (Δ : Con Term) (σ : Subst) : (Γ : Con Term) → Set where
  id : Δ ⊢ˢ σ ∷ ε
  _,_ : ∀ {Γ A sA}
      → Δ ⊢ˢ tail σ ∷ Γ
      → Δ ⊢ head σ ∷ subst (tail σ) A ⦂ sA
      → Δ ⊢ˢ σ ∷ Γ ∙ A ⦂ sA

-- Conversion of well-formed substitutions.
data _⊢ˢ_≡_∷_ (Δ : Con Term) (σ σ′ : Subst) : (Γ : Con Term) → Set where
  id : Δ ⊢ˢ σ ≡ σ′ ∷ ε
  _,_ : ∀ {Γ A sA}
      → Δ ⊢ˢ tail σ ≡ tail σ′ ∷ Γ
      → Δ ⊢ head σ ≡ head σ′ ∷ subst (tail σ) A ⦂ sA
      → Δ ⊢ˢ σ ≡ σ′ ∷ Γ ∙ A ⦂ sA

-- Note that we cannot use the well-formed substitutions.
-- For that, we need to prove the fundamental theorem for substitutions.

postulate cstr-dom-wty : (k : constructors) → ε ⊢ cstr-dom k ⦂ cstr-dom-sort k

postulate cstr-cod-wty : (k : constructors) → ε ∙ cstr-dom k ⦂ cstr-dom-sort k ⊢ cstr-cod k ⦂ cstr-cod-sort k




