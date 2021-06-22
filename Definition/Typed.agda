{-# OPTIONS --without-K  #-}

module Definition.Typed where

open import Definition.Untyped

open import Tools.Nat using (Nat)
open import Tools.Bool
open import Tools.Product
open import Tools.Sum using (_⊎_)
import Tools.PropositionalEquality as PE


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


cstr-𝕊 : constructors → 𝕊
cstr-𝕊 k = cstr-cod-sort k

cstr-dom-ctx : Con Term → constructors → Term
cstr-dom-ctx Γ k = wkAll Γ (cstr-dom k)

cstr-cod-ctx : Con Term → constructors → Term
cstr-cod-ctx Γ k = wk (lift (empty-wk Γ)) (cstr-cod k)

cstr-type : Con Term → constructors → Term → Term
cstr-type Γ k a = (cstr-cod-ctx Γ k) [ a ]
-- cstr-type Γ k = wkAll Γ (Π cstr-dom k ⦂ cstr-dom-sort k ▹ cstr-cod k)

{- Destructors -}

postulate dstr-param : destructors → Term
postulate dstr-dom : destructors → Term
postulate dstr-cod : destructors → Term

postulate dstr-param-sort : destructors → 𝕊
postulate dstr-dom-sort : destructors → 𝕊
postulate dstr-cod-sort : destructors → 𝕊

dstr-𝕊 : destructors → 𝕊
dstr-𝕊 o = dstr-cod-sort o

module Dstr (Γ : Con Term) (d : destructors) where

  param-ctx : Term
  param-ctx = wkAll Γ (dstr-param d)

  ctx-dom : Con Term
  ctx-dom = Γ ∙ param-ctx ⦂ dstr-param-sort d

  dom-ctx : Term
  dom-ctx = wk (lift (empty-wk Γ)) (dstr-dom d)

  ctx-cod : Con Term
  ctx-cod = ctx-dom ∙ dom-ctx ⦂ dstr-dom-sort d

  cod-ctx : Term
  cod-ctx = wk (lift (lift (empty-wk Γ))) (dstr-cod d)

  param-type : Term
  param-type = param-ctx

  dom-type : (p : Term) → Term
  dom-type p = dom-ctx [ p ]

  cod-type : (p a : Term) → Term
  cod-type p a = (cod-ctx [ wk1 a ]) [ p ]



{- Rewrite rules -}

postulate Rew⊢_⊚_⇒_ : destructors → Term → Term → Set

module Rew {d : destructors} {l r : Term} (rule : Rew⊢ d ⊚ l ⇒ r) where

  postulate binder-type : Term
  postulate binder-sort : 𝕊
  postulate is-recursive : Bool

  binder-type-ctx : (Γ : Con Term) → Term
  binder-type-ctx Γ = wkAll Γ binder-type

  nonrec-ctx : Con Term
  nonrec-ctx =
    ε ∙ dstr-param d ⦂ dstr-param-sort d
      ∙ binder-type ⦂ binder-sort

  nonrec-type : Term
  nonrec-type = Dstr.cod-type ε d (var 1) l

  rec-ctx : Con Term
  rec-ctx = nonrec-ctx ∙ Dstr.cod-type nonrec-ctx d (var 1) (var 0) ⦂ dstr-𝕊 d

  rec-type : Term
  rec-type = wk1 nonrec-type

  ctx : Con Term
  ctx with is-recursive
  ... | false = nonrec-ctx
  ... | true = rec-ctx

  type : Term
  type with is-recursive
  ... | false = nonrec-type
  ... | true = rec-type

  lhs : (p u : Term) → Term
  lhs p u = dstr d p (l [ u ])

  lhs-ctx : (Γ : Con Term) (p u : Term) → Term
  lhs-ctx Γ p u = dstr d p ((wk (lift (empty-wk Γ)) l) [ u ])

  rhs : (p u : Term) → Term
  rhs p u with is-recursive
  ... | false = r [ wk1 u ] [ p ]
  ... | true  = r [ wk1 (wk1 (dstr d p u)) ] [ wk1 u ] [ p ]

  rhs-ctx : (Γ : Con Term) (p u : Term) → Term
  rhs-ctx Γ p u with is-recursive
  ... | false = (wk (lift (lift (empty-wk Γ))) r) [ wk1 u ] [ p ]
  ... | true  = (wk (lift (lift (lift (empty-wk Γ)))) r) [ wk1 (wk1 (dstr d p u)) ] [ wk1 u ] [ p ]

-- record RewriteRules : Set where
--   field
--     rew-lhs-head : destructors
--     rew-lhs-arg : Term
--     -- rew-lhs-param : Term
--     rew-rhs : Term
--     -- rew-rule : Rew⊢ rew-lhs-head ⊚ rew-lhs-arg ⊚ rew-lhs-param ⇒ rew-rhs
--     rew-rule : Rew⊢ rew-lhs-head ⊚ rew-lhs-arg ⇒ rew-rhs

-- open RewriteRules public

-- rew-𝕊 : RewriteRules → 𝕊
-- rew-𝕊 r = dstr-𝕊 (rew-lhs-head r)



-- r : Rew⊢ d ⊚ w ⇒ t
-- Γ ∙ dstr-param-ctx Γ d ⦂ dstr-param-sort d ∙ rew-binder r ⦂ rew-binder-sort r ⊢ w ∷ wk1 (dstr-dom-ctx Γ d) ⦂ dstr-dom-sort d
-- Γ ∙ dstr-param-ctx Γ d ⦂ dstr-param-sort d ∙ rew-binder r ⦂ rew-binder-sort r ⊢ t ∷ dstr-type Γ d (var 1) w

-- Γ ⊢ p ∷ dstr-param-ctx Γ d
-- Γ ⊢ u ∷ rew-binder r [ p ]
-- Γ ⊢ d p (w [ u ]) ⇒ t [ p ] [ u ]

-- data _𝕊⊢_⊚_⊚_⇒_⦂_ (Γ : Con Term) (o : destructors) : Term → Term → Term → 𝕊 → Set where
--   rew : ∀ {ρ a p t}
--         → Rew⊢ o ⊚ a ⊚ p ⇒ t
--         → Γ 𝕊⊢ o ⊚ subst ρ a ⊚ subst ρ p ⇒ subst ρ t ⦂ dstr-𝕊 o


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
           -- If k happens to have elements built out of constructors
           -- we require that the domain of these elements are themselves well-formed
           -- through [ k ]-monomial that provides the opportunity to refer to k in these domains
           -- in a strictly positive fashion.
           → (∀ ki → [ k ]-cstr (cstr-cod ki) → [ k ]-monomial (cstr-dom ki) (cstr-dom-sort ki))
           -- → (∀ di → [ k ]-cstr (dstr-dom di) → Γ ⊢ dstr-cod-ctx Γ di ⦂ dstr-cod-sort di)
           -- TODO: negative cstr types
           → Γ ⊢ a ∷ cstr-dom-ctx Γ k ⦂ cstr-dom-sort k
           → Γ ⊢ cstr k a ∷  (cstr-cod-ctx Γ k) [ a ] ⦂ cstr-𝕊 k
    dstrⱼ  : ∀ {d p a}
           → let open Dstr Γ d in
             Γ ⊢ param-ctx ⦂ dstr-param-sort d
           → ctx-dom ⊢ dom-ctx ⦂ dstr-dom-sort d
           → ctx-cod ⊢ cod-ctx ⦂ dstr-cod-sort d
           → Γ ⊢ p ∷ param-type ⦂ dstr-param-sort d
           → Γ ⊢ a ∷ dom-type p ⦂ dstr-dom-sort d
           → (∀ l r (rule : Rew⊢ d ⊚ l ⇒ r) → Rew.ctx rule ⊢ r ∷ Rew.type rule ⦂ dstr-𝕊 d)
           → Γ ⊢ dstr d p a ∷ cod-type p a ⦂ dstr-𝕊 d
    conv   : ∀ {t A B s}
           → Γ ⊢ t ∷ A ⦂ s
           → Γ ⊢ A ≡ B ⦂ s
           → Γ ⊢ t ∷ B ⦂ s

  data [_]-monomial (K : constructors) (t : Term) (s : 𝕊) : Set where
    cst : ε ⊢ t ⦂ s → [ K ]-monomial t s
    mon : (d : [ K ]-cstr t)
        → s PE.≡ cstr-𝕊 K
        → ε ⊢ [ K ]-cstr-params d ∷ cstr-dom K ⦂ cstr-dom-sort K
        → [ K ]-monomial t s


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
               → Γ ⊢ cstr k a ≡ cstr k a' ∷ cstr-type Γ k a ⦂ cstr-𝕊 k
    dstr-cong  : ∀ {a a' p p' k}
               → let open Dstr Γ k in
                 Γ ⊢ p ≡ p' ∷ param-type ⦂ dstr-param-sort k
               → Γ ⊢ a ≡ a' ∷ dom-type p ⦂ dstr-dom-sort k
               → Γ ⊢ dstr k p a ≡ dstr k p' a' ∷ cod-type  p a ⦂ dstr-𝕊 k
    rew        : ∀ {A s d p u l r}
               → (rule : Rew⊢ d ⊚ l ⇒ r)
               → Γ ⊢ u ∷ Rew.binder-type-ctx rule Γ ⦂ Rew.binder-sort rule
               → Γ ⊢ Rew.lhs-ctx rule Γ p u ∷ A ⦂ s
               → Γ ⊢ Rew.lhs-ctx rule Γ p u ≡ Rew.rhs-ctx rule Γ p u ∷ A ⦂ s

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
  rew          : ∀ {A s d p u l l' r r'}
               → (rule : Rew⊢ d ⊚ l ⇒ r)
               → Γ ⊢ u ∷ Rew.binder-type-ctx rule Γ ⦂ Rew.binder-sort rule
               → Γ ⊢ Rew.lhs-ctx rule Γ p u ∷ A ⦂ s
               → r' PE.≡ Rew.rhs-ctx rule Γ p u
               → l' PE.≡ (wk (lift (empty-wk Γ)) l) [ u ]
               → Γ ⊢ dstr d p l' ⇒ r' ∷ A ⦂ s


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

postulate dstr-dom-wty : (k : destructors) → ε ⊢ dstr-dom k ⦂ dstr-dom-sort k
postulate dstr-param-wty : (k : destructors) → ε ⊢ dstr-param k ⦂ dstr-param-sort k
postulate dstr-cod-wty : (k : destructors) → ε ∙ dstr-param k ⦂ dstr-param-sort k ∙ wk1 (dstr-dom k) ⦂ dstr-dom-sort k ⊢ dstr-cod k ⦂ dstr-cod-sort k



