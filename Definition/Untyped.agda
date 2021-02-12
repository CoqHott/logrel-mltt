-- Raw terms, weakening (renaming) and substitution.

{-# OPTIONS --without-K --safe #-}

module Definition.Untyped where

open import Tools.Nat
open import Tools.Product
open import Tools.List
import Tools.PropositionalEquality as PE


infixl 30 _∙_^_
infix 30 Π_^_▹_
infixr 22 _^_▹▹_
infixl 30 _ₛ•ₛ_ _•ₛ_ _ₛ•_
infix 25 _[_]
infix 25 _[_]↑

data Relevance : Set where
  ! : Relevance
  % : Relevance

!≢% : ! PE.≢ %
!≢% ()

-- two levels of types

data Level : Set where
  ⁰ : Level
  ¹ : Level

⁰≢¹ : ⁰ PE.≢ ¹
⁰≢¹ ()

data _<_ : (i j : Level) → Set where
  0<1 : ⁰ < ¹

-- Typing contexts (snoc-lists, isomorphic to lists).

data Con (A : Set) : Set where
  ε   : Con A               -- Empty context.
  _∙_^_ : Con A → A → Relevance → Con A  -- Context extension.

record GenT (A : Set) : Set where
  inductive
  constructor ⟦_,_⟧
  field
    l : Nat
    t : A


data Kind : Set where
  Ukind : Relevance → Level → Kind
  Pikind : Relevance → Kind
  Natkind : Kind
  Lamkind : Kind
  Appkind : Kind
  Zerokind : Kind
  Suckind : Kind
  Natreckind : Kind
  Emptykind : Kind
  Emptyreckind : Kind
  Idkind : Kind
  Idreflkind : Kind
  Transpkind : Kind
  Castkind : Level → Kind
  Castreflkind : Kind
  Sigmakind : Kind
  Pairkind : Kind
  Fstkind : Kind
  Sndkind : Kind

data Term : Set where
  var : (x : Nat) → Term
  gen : (k : Kind) (c : List (GenT Term)) → Term

-- The Grammar of our language.

-- We represent the expressions of our language as de Bruijn terms.
-- Variables are natural numbers interpreted as de Bruijn indices.
-- Π, lam, and natrec are binders.

-- Type constructors.
U      : Level → Term                     -- Universe.
U l = gen (Ukind ! l) []

SProp : Level → Term
SProp l = gen (Ukind % l) []

pattern Univ r l = gen (Ukind r l) []

Π_^_▹_   : Term → Relevance → Term → Term  -- Dependent function type (B is a binder).
Π A ^ r ▹ B = gen (Pikind r) (⟦ 0 , A ⟧ ∷ ⟦ 1 , B ⟧ ∷ [])

∃_▹_ : Term → Term → Term -- Dependent pairs
∃ A ▹ B = gen Sigmakind (⟦ 0 , A ⟧ ∷ ⟦ 1 , B ⟧ ∷ [])

ℕ      : Term                     -- Type of natural numbers.
ℕ = gen Natkind []

-- Lambda-calculus.
-- var    : (x : Nat)        → Term  -- Variable (de Bruijn index).
-- var = var

lam_▹_    : Term → Term → Term  -- Function abstraction (binder).
lam A ▹ t = gen Lamkind (⟦ 0 , A ⟧ ∷ ⟦ 1 , t ⟧ ∷ [])

_∘_    : (t u : Term)     → Term  -- Application.
t ∘ u = gen Appkind (⟦ 0 , t ⟧ ∷ ⟦ 0 , u ⟧ ∷ [])

⦅_,_⦆ : Term → Term → Term -- Dependent pair formation
⦅ t , u ⦆ = gen Pairkind (⟦ 0 , t ⟧ ∷ ⟦ 0 , u ⟧ ∷ [])

fst : (t : Term) → Term -- Dependent pair elimination
fst t = gen Fstkind (⟦ 0 , t ⟧ ∷ [])

snd : (t : Term) → Term -- Dependent pair elimination
snd t = gen Sndkind (⟦ 0 , t ⟧ ∷ [])

-- Introduction and elimination of natural numbers.
zero   : Term                     -- Natural number zero.
zero = gen Zerokind []

suc    : (t : Term)       → Term  -- Successor.
suc t = gen Suckind (⟦ 0 , t ⟧ ∷ [])

natrec : (A t u v : Term) → Term  -- Recursor (A is a binder).
natrec A t u v = gen Natreckind (⟦ 1 , A ⟧ ∷ ⟦ 0 , t ⟧ ∷ ⟦ 0 , u ⟧ ∷ ⟦ 0 , v ⟧ ∷ [])

Empty : Term
Empty = gen Emptykind []

Emptyrec : (A e : Term) -> Term
Emptyrec A e = gen Emptyreckind (⟦ 0 , A ⟧ ∷ ⟦ 0 , e ⟧ ∷ [])

Id : (A t u : Term) → Term
Id A t u = gen Idkind (⟦ 0 , A ⟧ ∷ ⟦ 0 , t ⟧ ∷ ⟦ 0 , u ⟧ ∷ [])

Idrefl : (A t : Term) → Term
Idrefl A t = gen Idreflkind (⟦ 0 , A ⟧ ∷ ⟦ 0 , t ⟧ ∷ [])

transp : (A P t s u e : Term) → Term
transp A P t s u e = gen Transpkind (⟦ 0 , A ⟧ ∷ ⟦ 1 , P ⟧ ∷ ⟦ 0 , t ⟧ ∷ ⟦ 0 , s ⟧ ∷ ⟦ 0 , u ⟧ ∷ ⟦ 0 , e ⟧ ∷ [])

cast : Level → (A B e t : Term) → Term
cast l A B e t = gen (Castkind l) (⟦ 0 , A ⟧ ∷ ⟦ 0 , B ⟧ ∷ ⟦ 0 , e ⟧ ∷ ⟦ 0 , t ⟧ ∷ [])

castrefl : (A t : Term) → Term
castrefl A t = gen Castreflkind (⟦ 0 , A ⟧ ∷ ⟦ 0 , t ⟧ ∷ [])


-- Injectivity of term constructors w.r.t. propositional equality.

-- If  Π F G = Π H E  then  F = H  and  G = E.

Π-PE-injectivity : ∀ {F rF G H rH E} → Π F ^ rF ▹ G PE.≡ Π H ^ rH ▹ E
  → F PE.≡ H × rF PE.≡ rH × G PE.≡ E
Π-PE-injectivity PE.refl = PE.refl , PE.refl , PE.refl

∃-PE-injectivity : ∀ {F G H E} → ∃ F ▹ G PE.≡ ∃ H ▹ E
  → F PE.≡ H × G PE.≡ E
∃-PE-injectivity PE.refl = PE.refl , PE.refl

-- If  suc n = suc m  then  n = m.

suc-PE-injectivity : ∀ {n m} → suc n PE.≡ suc m → n PE.≡ m
suc-PE-injectivity PE.refl = PE.refl

Univ-PE-injectivity : ∀ {r r' l l'} → Univ r l PE.≡ Univ r' l' → r PE.≡ r' × l PE.≡ l'
Univ-PE-injectivity PE.refl = PE.refl , PE.refl

-- Neutral terms.

-- A term is neutral if it has a variable in head position.
-- The variable blocks reduction of such terms.
-- Emptyrec is always neutral

data Neutral : Term → Set where
  var     : ∀ n                     → Neutral (var n)
  ∘ₙ      : ∀ {k u}     → Neutral k → Neutral (k ∘ u)
  natrecₙ : ∀ {C c g k} → Neutral k → Neutral (natrec C c g k)
  Idₙ : ∀ {A t u} → Neutral A → Neutral (Id A t u)
  Idℕₙ : ∀ {t u} → Neutral t → Neutral (Id ℕ t u)
  Idℕ0ₙ : ∀ {u} → Neutral u → Neutral (Id ℕ zero u)
  IdℕSₙ : ∀ {t u} → Neutral u → Neutral (Id ℕ (suc t) u)
  IdUₙ : ∀ {t u l} → Neutral t → Neutral (Id (U l) t u)
  IdUℕₙ : ∀ {u l} → Neutral u → Neutral (Id (U l) ℕ u)
  IdUΠₙ : ∀ {A rA l B u} → Neutral u → Neutral (Id (U l) (Π A ^ rA ▹ B) u)
  castₙ : ∀ {l A B e t} → Neutral A → Neutral (cast l A B e t)
  castℕₙ : ∀ {l B e t} → Neutral B → Neutral (cast l ℕ B e t)
  castΠₙ : ∀ {l A rA P B e t} → Neutral B → Neutral (cast l (Π A ^ rA ▹ P) B e t)
  castℕℕₙ : ∀ {l e t} → Neutral t → Neutral (cast l ℕ ℕ e t)
  castℕΠₙ : ∀ {l A rA B e t} → Neutral (cast l ℕ (Π A ^ rA ▹ B) e t)
  castΠℕₙ : ∀ {l A rA B e t} → Neutral (cast l (Π A ^ rA ▹ B) ℕ e t)
  Emptyrecₙ : ∀ {A e} -> Neutral (Emptyrec A e)

-- Weak head normal forms (whnfs).
-- These are the (lazy) values of our language.

data Whnf : Term → Set where

  -- Type constructors are whnfs.
  Uₙ    : ∀ {r l} → Whnf (Univ r l)
  Πₙ    : ∀ {A r B} → Whnf (Π A ^ r ▹ B)
  ∃ₙ    : ∀ {A B} → Whnf (∃ A ▹ B)
  ℕₙ    : Whnf ℕ
  Emptyₙ : Whnf Empty

  -- Introductions are whnfs.
  lamₙ  : ∀ {A t} → Whnf (lam A ▹ t)
  zeroₙ : Whnf zero
  sucₙ  : ∀ {t} → Whnf (suc t)

  -- Neutrals are whnfs.
  ne   : ∀ {n} → Neutral n → Whnf n


-- Whnf inequalities.

-- Different whnfs are trivially distinguished by propositional equality.
-- (The following statements are sometimes called "no-confusion theorems".)

U≢ℕ : ∀ {r l} → Univ r l PE.≢ ℕ
U≢ℕ ()

U≢Empty : ∀ {r l} → Univ r l PE.≢ Empty
U≢Empty ()

U≢Π : ∀ {r r' l F G} → Univ r l PE.≢ Π F ^ r' ▹ G
U≢Π ()

U≢∃ : ∀ {r l F G} → Univ r l PE.≢ ∃ F ▹ G
U≢∃ ()

U≢ne : ∀ {r l K} → Neutral K → Univ r l PE.≢ K
U≢ne () PE.refl

ℕ≢Π : ∀ {F r G} → ℕ PE.≢ Π F ^ r ▹ G
ℕ≢Π ()

ℕ≢∃ : ∀ {F G} → ℕ PE.≢ ∃ F ▹ G
ℕ≢∃ ()

ℕ≢Empty : ℕ PE.≢ Empty
ℕ≢Empty ()

Empty≢ℕ : Empty PE.≢ ℕ
Empty≢ℕ ()

ℕ≢ne : ∀ {K} → Neutral K → ℕ PE.≢ K
ℕ≢ne () PE.refl

Empty≢ne : ∀ {K} → Neutral K → Empty PE.≢ K
Empty≢ne () PE.refl

Empty≢Π : ∀ {F r G} → Empty PE.≢ Π F ^ r ▹ G
Empty≢Π ()

Empty≢∃ : ∀ {F G} → Empty PE.≢ ∃ F ▹ G
Empty≢∃ ()

Π≢ne : ∀ {F r G K} → Neutral K → Π F ^ r ▹ G PE.≢ K
Π≢ne () PE.refl

Π≢∃ : ∀ {F r G F' G'} → Π F ^ r ▹ G PE.≢ ∃ F' ▹ G'
Π≢∃ ()

∃≢ne : ∀ {F G K} → Neutral K → ∃ F ▹ G PE.≢ K
∃≢ne () PE.refl

zero≢suc : ∀ {n} → zero PE.≢ suc n
zero≢suc ()

zero≢ne : ∀ {k} → Neutral k → zero PE.≢ k
zero≢ne () PE.refl

suc≢ne : ∀ {n k} → Neutral k → suc n PE.≢ k
suc≢ne () PE.refl


-- Several views on whnfs (note: not recursive).

-- A whnf of type ℕ is either zero, suc t, or neutral.

data Natural : Term → Set where
  zeroₙ :                     Natural zero
  sucₙ  : ∀ {t}             → Natural (suc t)
  ne    : ∀ {n} → Neutral n → Natural n

-- A (small) type in whnf is either Π A B, ℕ, or neutral.
-- Large types could also be U.

data Type : Term → Set where
  Πₙ : ∀ {A r B} → Type (Π A ^ r ▹ B)
  ℕₙ : Type ℕ
  Emptyₙ : Type Empty
  ∃ₙ : ∀ {A B} → Type (∃ A ▹ B)
  ne : ∀{n} → Neutral n → Type n

-- A whnf of type Π A B is either lam t or neutral.

data Function : Term → Set where
  lamₙ : ∀{A t} → Function (lam A ▹ t)
  ne : ∀{n} → Neutral n → Function n

-- These views classify only whnfs.
-- Natural, Type, and Function are a subsets of Whnf.

naturalWhnf : ∀ {n} → Natural n → Whnf n
naturalWhnf sucₙ = sucₙ
naturalWhnf zeroₙ = zeroₙ
naturalWhnf (ne x) = ne x

typeWhnf : ∀ {A} → Type A → Whnf A
typeWhnf Πₙ = Πₙ
typeWhnf ℕₙ = ℕₙ
typeWhnf ∃ₙ = ∃ₙ
typeWhnf Emptyₙ = Emptyₙ
typeWhnf (ne x) = ne x

functionWhnf : ∀ {f} → Function f → Whnf f
functionWhnf lamₙ = lamₙ
functionWhnf (ne x) = ne x

------------------------------------------------------------------------
-- Weakening

-- In the following we define untyped weakenings η : Wk.
-- The typed form could be written η : Γ ≤ Δ with the intention
-- that η transport a term t living in context Δ to a context Γ
-- that can bind additional variables (which cannot appear in t).
-- Thus, if Δ ⊢ t : A and η : Γ ≤ Δ then Γ ⊢ wk η t : wk η A.
--
-- Even though Γ is "larger" than Δ we write Γ ≤ Δ to be conformant
-- with subtyping A ≤ B.  With subtyping, relation Γ ≤ Δ could be defined as
-- ``for all x ∈ dom(Δ) have Γ(x) ≤ Δ(x)'' (in the sense of subtyping)
-- and this would be the natural extension of weakenings.

data Wk : Set where
  id    : Wk        -- η : Γ ≤ Γ.
  step  : Wk  → Wk  -- If η : Γ ≤ Δ then step η : Γ∙A ≤ Δ.
  lift  : Wk  → Wk  -- If η : Γ ≤ Δ then lift η : Γ∙A ≤ Δ∙A.

-- Composition of weakening.
-- If η : Γ ≤ Δ and η′ : Δ ≤ Φ then η • η′ : Γ ≤ Φ.

infixl 30 _•_

_•_                :  Wk → Wk → Wk
id      • η′       =  η′
step η  • η′       =  step  (η • η′)
lift η  • id       =  lift  η
lift η  • step η′  =  step  (η • η′)
lift η  • lift η′  =  lift  (η • η′)

repeat : {A : Set} → (A → A) → A → Nat → A
repeat f a 0 = a
repeat f a (1+ n) = f (repeat f a n)

-- Weakening of variables.
-- If η : Γ ≤ Δ and x ∈ dom(Δ) then wkVar ρ x ∈ dom(Γ).

wkVar : (ρ : Wk) (n : Nat) → Nat
wkVar id       n        = n
wkVar (step ρ) n        = 1+ (wkVar ρ n)
wkVar (lift ρ) 0    = 0
wkVar (lift ρ) (1+ n) = 1+ (wkVar ρ n)

  -- Weakening of terms.
  -- If η : Γ ≤ Δ and Δ ⊢ t : A then Γ ⊢ wk η t : wk η A.

mutual
  wkGen : (ρ : Wk) (g : List (GenT Term)) → List (GenT Term)
  wkGen ρ [] = []
  wkGen ρ (⟦ l , t ⟧ ∷ g) = ⟦ l , (wk (repeat lift ρ l) t) ⟧ ∷ wkGen ρ g

  wk : (ρ : Wk) (t : Term) → Term
  wk ρ (var x) = var (wkVar ρ x)
  wk ρ (gen x c) = gen x (wkGen ρ c)

-- Adding one variable to the context requires wk1.
-- If Γ ⊢ t : B then Γ∙A ⊢ wk1 t : wk1 B.

wk1 : Term → Term
wk1 = wk (step id)

wk1d : Term → Term
wk1d = wk (lift (step id))

-- Weakening of a neutral term.

wkNeutral : ∀ {t} ρ → Neutral t → Neutral (wk ρ t)
wkNeutral ρ (var n)    = var (wkVar ρ n)
wkNeutral ρ (∘ₙ n)    = ∘ₙ (wkNeutral ρ n)
wkNeutral ρ (natrecₙ n) = natrecₙ (wkNeutral ρ n)
wkNeutral ρ Emptyrecₙ = Emptyrecₙ
wkNeutral ρ (Idₙ A) = Idₙ (wkNeutral ρ A)
wkNeutral ρ (Idℕₙ t) = Idℕₙ (wkNeutral ρ t)
wkNeutral ρ (Idℕ0ₙ t) = Idℕ0ₙ (wkNeutral ρ t)
wkNeutral ρ (IdℕSₙ t) = IdℕSₙ (wkNeutral ρ t)
wkNeutral ρ (IdUₙ t) = IdUₙ (wkNeutral ρ t)
wkNeutral ρ (IdUℕₙ t) = IdUℕₙ (wkNeutral ρ t)
wkNeutral ρ (IdUΠₙ t) = IdUΠₙ (wkNeutral ρ t)
wkNeutral ρ (castₙ A) = castₙ (wkNeutral ρ A)
wkNeutral ρ (castℕₙ A) = castℕₙ (wkNeutral ρ A)
wkNeutral ρ (castΠₙ A) = castΠₙ (wkNeutral ρ A)
wkNeutral ρ (castℕℕₙ t) = castℕℕₙ (wkNeutral ρ t)
wkNeutral ρ castℕΠₙ = castℕΠₙ
wkNeutral ρ castΠℕₙ = castΠℕₙ

-- Idℕ0ₙ : ∀ {u} → Neutral u → Neutral (Id ℕ 0 u)
-- IdℕSₙ : ∀ {u} → Neutral u → Neutral (Id ℕ 0 (suc u))
-- IdUₙ : ∀ {t u} → Neutral t → Neutral (Id U t u)
-- IdUℕₙ : ∀ {u} → Neutral u → Neutral (Id U ℕ u)
-- IdUΠₙ : ∀ {A rA B u} → Neutral u → Neutral (Id U (Π A ^ rA ▹ B) u)
-- castₙ : ∀ {A B e t} → Neutral A → Neutral (cast A B e t)
-- castℕₙ : ∀ {B e t} → Neutral B → Neutral (cast ℕ B e t)
-- castΠₙ : ∀ {A rA P B e t} → Neutral B → Neutral (cast (Π A ^ rA ▹ P) B e t)
-- castℕℕₙ : ∀ {e t} → Neutral t → Neutral (cast ℕ ℕ e t)

-- Weakening can be applied to our whnf views.

wkNatural : ∀ {t} ρ → Natural t → Natural (wk ρ t)
wkNatural ρ sucₙ    = sucₙ
wkNatural ρ zeroₙ   = zeroₙ
wkNatural ρ (ne x) = ne (wkNeutral ρ x)

wkType : ∀ {t} ρ → Type t → Type (wk ρ t)
wkType ρ Πₙ      = Πₙ
wkType ρ ℕₙ      = ℕₙ
wkType ρ ∃ₙ      = ∃ₙ
wkType ρ Emptyₙ  = Emptyₙ
wkType ρ (ne x) = ne (wkNeutral ρ x)

wkFunction : ∀ {t} ρ → Function t → Function (wk ρ t)
wkFunction ρ lamₙ    = lamₙ
wkFunction ρ (ne x) = ne (wkNeutral ρ x)

wkWhnf : ∀ {t} ρ → Whnf t → Whnf (wk ρ t)
wkWhnf ρ Uₙ      = Uₙ
wkWhnf ρ Πₙ      = Πₙ
wkWhnf ρ ∃ₙ      = ∃ₙ
wkWhnf ρ ℕₙ      = ℕₙ
wkWhnf ρ Emptyₙ  = Emptyₙ
wkWhnf ρ lamₙ    = lamₙ
wkWhnf ρ zeroₙ   = zeroₙ
wkWhnf ρ sucₙ    = sucₙ
wkWhnf ρ (ne x) = ne (wkNeutral ρ x)

-- Non-dependent version of Π.

_^_▹▹_ : Term → Relevance → Term → Term
A ^ r ▹▹ B = Π A ^ r ▹ wk1 B

------------------------------------------------------------------------
-- Substitution

-- The substitution operation  subst σ t  replaces the free de Bruijn indices
-- of term t by chosen terms as specified by σ.

-- The substitution σ itself is a map from natural numbers to terms.

Subst : Set
Subst = Nat → Term

-- Given closed contexts ⊢ Γ and ⊢ Δ,
-- substitutions may be typed via Γ ⊢ σ : Δ meaning that
-- Γ ⊢ σ(x) : (subst σ Δ)(x) for all x ∈ dom(Δ).
--
-- The substitution operation is then typed as follows:
-- If Γ ⊢ σ : Δ and Δ ⊢ t : A, then Γ ⊢ subst σ t : subst σ A.
--
-- Although substitutions are untyped, typing helps us
-- to understand the operation on substitutions.

-- We may view σ as the infinite stream σ 0, σ 1, ...

-- Extract the substitution of the first variable.
--
-- If Γ ⊢ σ : Δ∙A  then Γ ⊢ head σ : subst σ A.

head : Subst → Term
head σ = σ 0

-- Remove the first variable instance of a substitution
-- and shift the rest to accommodate.
--
-- If Γ ⊢ σ : Δ∙A then Γ ⊢ tail σ : Δ.

tail : Subst → Subst
tail σ n = σ (1+ n)

-- Substitution of a variable.
--
-- If Γ ⊢ σ : Δ then Γ ⊢ substVar σ x : (subst σ Δ)(x).

substVar : (σ : Subst) (x : Nat) → Term
substVar σ x = σ x

-- Identity substitution.
-- Replaces each variable by itself.
--
-- Γ ⊢ idSubst : Γ.

idSubst : Subst
idSubst = var

-- Weaken a substitution by one.
--
-- If Γ ⊢ σ : Δ then Γ∙A ⊢ wk1Subst σ : Δ.

wk1Subst : Subst → Subst
wk1Subst σ x = wk1 (σ x)

-- Lift a substitution.
--
-- If Γ ⊢ σ : Δ then Γ∙A ⊢ liftSubst σ : Δ∙A.

liftSubst : (σ : Subst) → Subst
liftSubst σ 0    = var 0
liftSubst σ (1+ x) = wk1Subst σ x

-- Transform a weakening into a substitution.
--
-- If ρ : Γ ≤ Δ then Γ ⊢ toSubst ρ : Δ.

toSubst : Wk → Subst
toSubst pr x = var (wkVar pr x)

-- Apply a substitution to a term.
--
-- If Γ ⊢ σ : Δ and Δ ⊢ t : A then Γ ⊢ subst σ t : subst σ A.

mutual
  substGen : (σ : Subst) (g : List (GenT Term)) → List (GenT Term)
  substGen σ [] = []
  substGen σ (⟦ l , t ⟧ ∷ g) = ⟦ l , (subst (repeat liftSubst σ l) t) ⟧ ∷ substGen σ g

  subst : (σ : Subst) (t : Term) → Term
  subst σ (var x) = substVar σ x
  subst σ (gen x c) = gen x (substGen σ c)

-- Extend a substitution by adding a term as
-- the first variable substitution and shift the rest.
--
-- If Γ ⊢ σ : Δ and Γ ⊢ t : subst σ A then Γ ⊢ consSubst σ t : Δ∙A.

consSubst : Subst → Term → Subst
consSubst σ t 0    = t
consSubst σ t (1+ n) = σ n

-- Singleton substitution.
--
-- If Γ ⊢ t : A then Γ ⊢ sgSubst t : Γ∙A.

sgSubst : Term → Subst
sgSubst = consSubst idSubst

-- Compose two substitutions.
--
-- If Γ ⊢ σ : Δ and Δ ⊢ σ′ : Φ then Γ ⊢ σ ₛ•ₛ σ′ : Φ.

_ₛ•ₛ_ : Subst → Subst → Subst
_ₛ•ₛ_ σ σ′ x = subst σ (σ′ x)

-- Composition of weakening and substitution.
--
--  If ρ : Γ ≤ Δ and Δ ⊢ σ : Φ then Γ ⊢ ρ •ₛ σ : Φ.

_•ₛ_ : Wk → Subst → Subst
_•ₛ_ ρ σ x = wk ρ (σ x)

--  If Γ ⊢ σ : Δ and ρ : Δ ≤ Φ then Γ ⊢ σ ₛ• ρ : Φ.

_ₛ•_ : Subst → Wk → Subst
_ₛ•_ σ ρ x = σ (wkVar ρ x)

-- Substitute the first variable of a term with an other term.
--
-- If Γ∙A ⊢ t : B and Γ ⊢ s : A then Γ ⊢ t[s] : B[s].

_[_] : (t : Term) (s : Term) → Term
t [ s ] = subst (sgSubst s) t

-- Substitute the first variable of a term with an other term,
-- but let the two terms share the same context.
--
-- If Γ∙A ⊢ t : B and Γ∙A ⊢ s : A then Γ∙A ⊢ t[s]↑ : B[s]↑.

_[_]↑ : (t : Term) (s : Term) → Term
t [ s ]↑ = subst (consSubst (wk1Subst idSubst) s) t

_[_]↑↑ : (t : Term) (s : Term) → Term
t [ s ]↑↑ = subst (consSubst (wk1Subst (wk1Subst idSubst)) s) t
