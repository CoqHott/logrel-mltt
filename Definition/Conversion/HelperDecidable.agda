{-# OPTIONS --safe #-}

module Definition.Conversion.HelperDecidable where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed as T
open import Definition.Typed.Properties
open import Definition.Conversion
open import Definition.Conversion.Whnf
open import Definition.Conversion.Soundness
open import Definition.Conversion.Symmetry
open import Definition.Conversion.Transitivity
open import Definition.Conversion.SymmetrySize
open import Definition.Conversion.Stability
open import Definition.Conversion.Conversion
open import Definition.Conversion.Lift
open import Definition.Conversion.Inversion
open import Definition.Conversion.ConvSize
open import Definition.Conversion.ConversionProp
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.Reduction
open import Definition.Typed.Consequences.Equality
open import Definition.Typed.Consequences.Inequality as IE
open import Definition.Typed.Consequences.NeTypeEq
open import Definition.Typed.Consequences.SucCong
open import Definition.Typed.Consequences.Inversion
open import Definition.Typed.Consequences.TypeUnicity
open import Definition.Conversion.Consequences.Completeness
open import Definition.Conversion.EqRelInstance

open import Tools.Nat
open import Tools.Product
open import Tools.Empty
open import Tools.Nullary
import Tools.PropositionalEquality as PE

dec-relevance : ∀ (r r′ : Relevance) → Dec (r PE.≡ r′)
dec-relevance ! ! = yes PE.refl
dec-relevance ! % = no (λ ())
dec-relevance % ! = no (λ ())
dec-relevance % % = yes PE.refl

dec-level : ∀ (l l′ : Level) → Dec (l PE.≡ l′)
dec-level ⁰ ⁰ = yes PE.refl
dec-level ⁰ ¹ = no (λ ())
dec-level ¹ ⁰ = no (λ ())
dec-level ¹ ¹ = yes PE.refl

neutralconvTerm~↑! : ∀ {t u A Γ l}
                     → Neutral A
                     → Γ ⊢ t [conv↓] u ∷ A ^ l
                     → ∃ λ B → Γ ⊢ t ~ u ↑! B ^ l
neutralconvTerm~↑! neA (ne ([~] A D whnfB k~l)) = _ , k~l
neutralconvTerm~↑! neA (ℕ-ins ([~] A D whnfB k~l)) = _ , k~l
neutralconvTerm~↑! neA (ne-ins x x₁ x₂ ([~] A D whnfB k~l)) = _ , k~l

noNeℕ : Neutral ℕ → ⊥
noNeℕ ()

noNe0 : Neutral zero → ⊥
noNe0 ()

noNeSuc : ∀ {n} → Neutral (suc n) → ⊥
noNeSuc ()


noNeΠ : ∀ {A rA B} → Neutral (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) → ⊥
noNeΠ ()

noNeUniv : ∀ {rA lA} → Neutral (Univ rA lA) → ⊥
noNeUniv ()

⁰-next :  ∀ {l} → ι ⁰ PE.≡ next l → ⊥
⁰-next {⁰} ()
⁰-next {¹} ()

neutralZero : Neutral zero → ⊥
neutralZero ()

neutralSuc : ∀ {n} → Neutral (suc n) → ⊥
neutralSuc ()

noℕ~ℕ : ∀ {Γ X l} → Γ ⊢ ℕ ~ ℕ ↓! X ^ l → ⊥
noℕ~ℕ ()

sizeSubst₂-gen :  ∀ {A B a b a' b'}
              → (P : A → B → Set)
              → (size : ∀ {a b} → P a b → Nat)
              → (ea : a PE.≡ a')
              → (eb : b PE.≡ b')
              → (t : P a b)
              → size (PE.subst₂ P ea eb t) PE.≡ size t
sizeSubst₂-gen _ _ PE.refl PE.refl _ = PE.refl              


abstract -- Agda will do some slow unfolding without abstract
 
  ~atU : ∀ {Γ t u r lU l}
    → Γ ⊢ t ∷ Univ r lU ^ [ ! , l ]
    → (∃ λ A → ∃ λ lA → Γ ⊢ t ~ u ↓! A ^ lA)
    → Γ ⊢ t ~ u ↓! Univ r lU ^ l
  ~atU ⊢t∷U (A , lA , t~u) =
    let whnfA , neT , neU = ne~↓! t~u
        ⊢A , ⊢t , ⊢u = syntacticEqTerm (soundness~↓! t~u)
        l≡l , ⊢U≡A = neTypeEq neT ⊢t∷U ⊢t
        A≡U = U≡A-whnf ⊢U≡A whnfA
    in PE.subst₂ (λ X Y → _ ⊢ _ ~ _ ↓! X ^ Y) A≡U (PE.sym l≡l) t~u

  ~atUsize : ∀ {Γ t u r lU l}
    → (⊢t : Γ ⊢ t ∷ Univ r lU ^ [ ! , l ])
    → (t~u : ∃ λ A → ∃ λ lA → Γ ⊢ t ~ u ↓! A ^ lA)
    → size~↓! (~atU ⊢t t~u) PE.≡ size~↓! (proj₂ (proj₂ t~u))
  ~atUsize ⊢t∷U (A , lA , t~u) =
    let whnfA , neT , neU = ne~↓! t~u
        ⊢A , ⊢t , ⊢u = syntacticEqTerm (soundness~↓! t~u)
        l≡l , ⊢U≡A = neTypeEq neT ⊢t∷U ⊢t
        A≡U = U≡A-whnf ⊢U≡A whnfA
    in sizeSubst₂-gen (λ X Y → _ ⊢ _ ~ _ ↓! X ^ Y) size~↓! A≡U (PE.sym l≡l) t~u


-- Algorithmic equality of variables infers propositional equality.
strongVarEq : ∀ {m n A Γ l} → Γ ⊢ var n ~ var m ↑! A ^ l → n PE.≡ m
strongVarEq (var-refl x x≡y) = x≡y

-- Helper function for decidability of applications.
dec~↑!-app : ∀ {k k₁ l l₁ F F₁ G G₁ rF B Γ Δ lF lG lΠ lK}
          → ⊢ Γ ≡ Δ
          → Γ ⊢ k ∷ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ ! ^ [ ! , ι lΠ ]
          → Δ ⊢ k₁ ∷ Π F₁ ^ rF ° lF ▹ G₁ ° lG ° lΠ ^ ! ^ [ ! , ι lΠ ]
          → Γ ⊢ k ~ k₁ ↓! B ^ lK
          → Dec (Γ ⊢ l [genconv↑] l₁ ∷ F ^ [ rF , ι lF ])
          → Dec (∃ λ A → ∃ λ lA → Γ ⊢ k ∘ l ^ lΠ ~ k₁ ∘ l₁ ^ lΠ ↑! A ^ lA)
dec~↑!-app Γ≡Δ k k₁ k~k₁ (yes p) =
  let
    whnfA , neK , neL = ne~↓! k~k₁
    ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓! k~k₁)
    l≡l , ΠFG₁≡A = neTypeEq neK k ⊢k
    H , E , A≡ΠHE = Π≡A ΠFG₁≡A whnfA
    F≡H , rF≡rH , lF≡lH , lG≡lE , G₁≡E = injectivity (PE.subst (λ x → _ ⊢ _ ≡ x ^ _) A≡ΠHE ΠFG₁≡A)
  in yes (E [ _ ] , _ , app-cong (PE.subst₂ (λ x y → _ ⊢ _ ~ _ ↓! x ^ y) A≡ΠHE (PE.sym l≡l) k~k₁) (convConvTerm%! p F≡H))
dec~↑!-app Γ≡Δ k k₁ k~k₁ (no ¬p) = no (λ { (_ , _ ,  app-cong k~k₁′ p) →
  let
    whnfA , neK , neL = ne~↓! k~k₁′
    ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓! k~k₁′)
    l≡l , Π≡Π = neTypeEq neK k ⊢k
    F≡F , rF≡rF , lF≡lF , lG≡lG , G≡G = injectivity Π≡Π
  in ¬p (convConvTerm%! (PE.subst₂ (λ x y → _ ⊢ _ [genconv↑] _ ∷ _ ^ [ x , ι y ]) (PE.sym rF≡rF) (PE.sym lF≡lF) p) (sym F≡F)) })

Idℕ-elim : ∀ {Γ l A B t u t' u'} → Neutral A → Γ ⊢ Id A t u ~ Id ℕ t' u' ↑! B ^ l → ⊥
Idℕ-elim neA (Id-cong x x₁ x₂) = let _ , _ , neℕ = ne~↓! x in ⊥-elim (noNeℕ neℕ)
Idℕ-elim neA (Id-ℕ x x₁) = ⊥-elim (noNeℕ neA)
Idℕ-elim neA (Id-ℕ0 x) = ⊥-elim (noNeℕ neA)
Idℕ-elim neA (Id-ℕS x x₁) = ⊥-elim (noNeℕ neA)

Idℕ-elim' : ∀ {Γ l A B t u t' u'} → Neutral A → Γ ⊢ Id ℕ t u ~ Id A t' u' ↑! B ^ l → ⊥
Idℕ-elim' neA e = let _ , _ , e' = sym~↑! (reflConEq (wfEqTerm (soundness~↑! e))) e in Idℕ-elim neA e'

conv↑-inversion : ∀ {Γ l A t u} → Whnf A → Whnf t → Whnf u → Γ ⊢ t [conv↑] u ∷ A ^ l → Γ ⊢ t [conv↓] u ∷ A ^ l
conv↑-inversion whnfA whnft whnfu ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) = 
  let et = whnfRed*Term d whnft
      eu = whnfRed*Term d′ whnfu
      eA = whnfRed* D whnfA
  in PE.subst₃ (λ A X Y → _ ⊢ X [conv↓] Y ∷ A ^ _) (PE.sym eA) (PE.sym et) (PE.sym eu) t<>u

Idℕ0-elim-- : ∀ {Γ l t} → Neutral t → Γ ⊢ t ~ zero ↓! ℕ ^ l → ⊥
Idℕ0-elim-- net ([~] A D whnfB (cast-refl x x₃ x₄)) =
    let _ , _ , neA = ne~↓! x
        eqA = whnfRed* D (ne neA)
    in noNeℕ (PE.subst Neutral eqA neA)
Idℕ0-elim-- net ([~] .ℕ D whnfB (castℕ-refl x x₁)) with ne~↓! x
Idℕ0-elim-- net ([~] .ℕ D whnfB (castℕ-refl x x₁)) | _ , _ , ()

Idℕ0-elim- : ∀ {Γ l t} → Neutral t → Γ ⊢ t [conv↓] zero ∷ ℕ ^ l → ⊥
Idℕ0-elim- net (ℕ-ins x) = ⊥-elim (Idℕ0-elim-- net x)

Idℕ0-elim : ∀ {Γ l A t u u'} → Neutral t → Γ ⊢ Id ℕ t u ~ Id ℕ zero u' ↑! A ^ l → ⊥
Idℕ0-elim net (Id-cong x y x₂) =
  let e = conv↑-inversion ℕₙ (ne net) zeroₙ y in Idℕ0-elim- net e
Idℕ0-elim net (Id-ℕ x x₁) = ⊥-elim (Idℕ0-elim-- net x)

Idℕ0-elim' : ∀ {Γ l A t u u'} → Neutral t → Γ ⊢ Id ℕ zero u ~ Id ℕ t u' ↑! A ^ l → ⊥
Idℕ0-elim' net e = let _ , _ , e' = sym~↑! (reflConEq (wfEqTerm (soundness~↑! e))) e in Idℕ0-elim net e'

IdℕS-elim-- : ∀ {Γ l t n} → Neutral t → Γ ⊢ t ~ suc n ↓! ℕ ^ l → ⊥
IdℕS-elim-- net ([~] A D whnfB (cast-refl x x₃ x₄)) = 
    let _ , _ , neA = ne~↓! x
        eqA = whnfRed* D (ne neA)
    in noNeℕ (PE.subst Neutral eqA neA)
IdℕS-elim-- net ([~] .ℕ D whnfB (castℕ-refl x x₁)) with ne~↓! x
IdℕS-elim-- net ([~] .ℕ D whnfB (castℕ-refl x x₁)) | _ , _ , ()

IdℕS-elim- : ∀ {Γ l t n} → Neutral t → Γ ⊢ t [conv↓] suc n ∷ ℕ ^ l → ⊥
IdℕS-elim- net (ℕ-ins x) = ⊥-elim (IdℕS-elim-- net x)

IdℕS-elim : ∀ {Γ l A t n u u'} → Neutral t → Γ ⊢ Id ℕ t u ~ Id ℕ (suc n) u' ↑! A ^ l → ⊥
IdℕS-elim net (Id-cong x y x₂) =
  let e = conv↑-inversion ℕₙ (ne net) sucₙ y in IdℕS-elim- net e
IdℕS-elim net (Id-ℕ x x₁) = ⊥-elim (IdℕS-elim-- net x)

IdℕS-elim' : ∀ {Γ l A t n u u'} → Neutral t → Γ ⊢ Id ℕ (suc n) u ~ Id ℕ t u' ↑! A ^ l → ⊥
IdℕS-elim' net e = let _ , _ , e' = sym~↑! (reflConEq (wfEqTerm (soundness~↑! e))) e in IdℕS-elim net e'

Idℕ0S-elim- : ∀ {Γ l n} → Γ ⊢ zero [conv↓] suc n ∷ ℕ ^ l → ⊥
Idℕ0S-elim- (ℕ-ins ())

Idℕ0S-elim : ∀ {Γ l A u u' n} → Γ ⊢ Id ℕ zero u ~ Id ℕ (suc n) u' ↑! A ^ l → ⊥
Idℕ0S-elim (Id-cong x y x₂) =
  let e = conv↑-inversion ℕₙ zeroₙ sucₙ y in Idℕ0S-elim- e
Idℕ0S-elim (Id-ℕ () _)

Idℕ0S-elim' : ∀ {Γ l A u u' n} → Γ ⊢ Id ℕ (suc n) u ~ Id ℕ zero u' ↑! A ^ l → ⊥
Idℕ0S-elim' e =  let _ , _ , e' = sym~↑! (reflConEq (wfEqTerm (soundness~↑! e))) e in Idℕ0S-elim e'

IdU-elim : ∀ {Γ l A B t u t' u' rU lU} → Neutral A → Γ ⊢ Id A t u ~ Id (Univ rU lU) t' u' ↑! B ^ l → ⊥
IdU-elim neA (Id-cong x x₁ x₂) = let _ , _ , neU = ne~↓! x in ⊥-elim (noNeUniv neU)
IdU-elim neA (Id-U x x₁) = ⊥-elim (noNeUniv neA)
IdU-elim neA (Id-Uℕ x) = ⊥-elim (noNeUniv neA)
IdU-elim neA (Id-UΠ x x₁) = ⊥-elim (noNeUniv neA)

IdU-elim' : ∀ {Γ l A B t u t' u' rU lU} → Neutral A → Γ ⊢ Id (Univ rU lU) t u ~ Id A t' u' ↑! B ^ l → ⊥
IdU-elim' neA e = let _ , _ , e' = sym~↑! (reflConEq (wfEqTerm (soundness~↑! e))) e in IdU-elim neA e'

IdUℕ-elim : ∀ {Γ l A t u t' u' rU lU} → Γ ⊢ Id (Univ rU lU) t u ~ Id ℕ t' u' ↑! A ^ l → ⊥
IdUℕ-elim (Id-cong () x₁ x₂)

IdℕU-elim : ∀ {Γ l A t u t' u' rU lU} → Γ ⊢ Id ℕ t u ~ Id (Univ rU lU) t' u' ↑! A ^ l → ⊥
IdℕU-elim (Id-cong () x₁ x₂)

IdUUℕ-elim : ∀ {Γ l A t u u'} → Neutral t → Γ ⊢ Id (U ⁰) t u ~ Id (U ⁰) ℕ u' ↑! A ^ l → ⊥
IdUUℕ-elim () (Id-Uℕ x)

IdUUℕ-elim' : ∀ {Γ l A t u u'} → Neutral t → Γ ⊢ Id (U ⁰) ℕ u ~ Id (U ⁰) t u' ↑! A ^ l → ⊥
IdUUℕ-elim' () (Id-Uℕ x)

IdUUΠℕ-elim- : ∀ {Γ l A rA B X} → Γ ⊢ Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ ! [conv↓] ℕ ∷ X ^ l → ⊥
IdUUΠℕ-elim- (η-eq x x₁ x₂ x₃ x₄ x₅ (ne ()) x₇)

IdUUΠℕ-elim : ∀ {Γ l A rA B X u u'} → Γ ⊢ Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) u ~ Id (U ⁰) ℕ u' ↑! X ^ l → ⊥
IdUUΠℕ-elim (Id-cong x y x₂) = let e = conv↑-inversion Uₙ Πₙ ℕₙ y in IdUUΠℕ-elim- e
IdUUΠℕ-elim (Id-U () x₁)

IdUUΠℕ-elim' : ∀ {Γ l A rA B X u u'} → Γ ⊢ Id (U ⁰) ℕ u ~ Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) u' ↑! X ^ l → ⊥
IdUUΠℕ-elim' e = let _ , _ , e' = sym~↑! (reflConEq (wfEqTerm (soundness~↑! e))) e in IdUUΠℕ-elim e'

IdUUΠ-elim-- : ∀ {Γ l A rA B t} → Neutral t → Γ ⊢ t ~ Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ ! ↓! Univ ! ⁰ ^ l → ⊥
IdUUΠ-elim-- net ([~] A D whnfB (cast-refl x x₃ x₄)) =
  let _ , _ , neA = ne~↓! x
      eqA = whnfRed* D (ne neA)
  in noNeUniv (PE.subst Neutral eqA neA)
IdUUΠ-elim-- net ([~] A D whnfB (castℕ-refl x x₁)) with ne~↓! x
IdUUΠ-elim-- net ([~] A D whnfB (castℕ-refl x x₁)) | _ , _ , ()

IdUUΠ-elim- : ∀ {Γ l A rA B t} → Neutral t → Γ ⊢ t [conv↓] Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ ! ∷ Univ ! ⁰ ^ l → ⊥
IdUUΠ-elim- net (ne x) = ⊥-elim (IdUUΠ-elim-- net x)
IdUUΠ-elim- net (ne-ins x x₁ () x₃)

IdUUΠ-elim : ∀ {Γ l A rA B X t u u'} → Neutral t → Γ ⊢ Id (U ⁰) t u ~ Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) u' ↑! X ^ l → ⊥
IdUUΠ-elim net (Id-cong x y x₂) = let e = conv↑-inversion Uₙ (ne net) Πₙ y in IdUUΠ-elim- net e
IdUUΠ-elim net (Id-U () x₁)
IdUUΠ-elim () (Id-UΠ x x₁)

IdUUΠ-elim' : ∀ {Γ l A rA B X t u u'} → Neutral t → Γ ⊢ Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) u ~ Id (U ⁰) t u' ↑! X ^ l → ⊥
IdUUΠ-elim' net e = let _ , _ , e' = sym~↑! (reflConEq (wfEqTerm (soundness~↑! e))) e in IdUUΠ-elim net e'

{-
castℕ-elim : ∀ {Γ l A B B' X t e t' e'} → Neutral A → Γ ⊢ cast ⁰ A B e t ~ cast ⁰ ℕ B' e' t' ↑! X ^ l → ⊥
castℕ-elim neA (cast-cong () _ _ x₁ x₂ x₃ x₄)
castℕ-elim () (cast-ℕ x x₁ x₂ x₃)
castℕ-elim () (cast-ℕℕ x x₁ x₂)
castℕ-elim () (cast-ℕΠ x x₁ x₂ x₃)
castℕ-elim x (cast-refl x₁ x₂ x₃ x₄ x₅) =
  let  = inversion-cast x₃
  in {!!}
castℕ-elim x (castℕ-refl' x₁ x₂) = {!!}


castℕ-elim' : ∀ {Γ l A B B' X t e t' e'} → Neutral A → Γ ⊢ cast ⁰ ℕ B e t ~ cast ⁰ A B' e' t' ↑! X ^ l → ⊥
castℕ-elim' neA e = let _ , _ , e' = sym~↑! (reflConEq (wfEqTerm (soundness~↑! e))) e in castℕ-elim neA e'

castΠ-elim : ∀ {Γ l A B B' X t e t' e' r P Q} → Neutral A → Γ ⊢ cast ⁰ A B e t ~ cast ⁰ (Π P ^ r ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ !) B' e' t' ↑! X ^ l → ⊥
castΠ-elim neA (cast-cong () _ _ x₁ x₂ x₃ x₄)
castΠ-elim () (cast-Π x x₁ x₂ x₃ x₄)
castΠ-elim () (cast-Πℕ x x₁ x₂ x₃)
castΠ-elim () (cast-ΠΠ%! x x₁ x₂ x₃ x₄)
castΠ-elim () (cast-ΠΠ!% x x₁ x₂ x₃ x₄)

castΠ-elim' : ∀ {Γ l A B B' X t e t' e' r P Q} → Neutral A → Γ ⊢ cast ⁰ (Π P ^ r ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ !) B e t ~ cast ⁰ A B' e' t' ↑! X ^ l → ⊥
castΠ-elim' neA e = let _ , _ , e' = sym~↑! (reflConEq (wfEqTerm (soundness~↑! e))) e in castΠ-elim neA e'

castℕℕ-elim : ∀ {Γ l A X t e t' e'} → Neutral A → Γ ⊢ cast ⁰ ℕ A e t ~ cast ⁰ ℕ ℕ e' t' ↑! X ^ l → ⊥
castℕℕ-elim neA (cast-cong () _ _ x₁ x₂ x₃ x₄)
castℕℕ-elim (var n) (cast-ℕ () x₁ x₂ x₃)
castℕℕ-elim () (cast-ℕℕ x x₁ x₂)

castℕℕ-elim' : ∀ {Γ l A X t e t' e'} → Neutral A → Γ ⊢ cast ⁰ ℕ ℕ e t ~ cast ⁰ ℕ A e' t' ↑! X ^ l → ⊥
castℕℕ-elim' neA e = let _ , _ , e' = sym~↑! (reflConEq (wfEqTerm (soundness~↑! e))) e in castℕℕ-elim neA e'

castℕΠ-elim : ∀ {Γ l A A' X t e t' e' r P Q} → Γ ⊢ cast ⁰ ℕ A e t ~ cast ⁰ (Π P ^ r ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ !) A' e' t' ↑! X ^ l → ⊥
castℕΠ-elim (cast-cong () _ _ x₁ x₂ x₃ x₄)

castℕΠ-elim' : ∀ {Γ l A A' X t e t' e' r P Q} → Γ ⊢ cast ⁰ (Π P ^ r ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ !) A e t ~ cast ⁰ ℕ A' e' t' ↑! X ^ l → ⊥
castℕΠ-elim' (cast-cong () _ _ x₁ x₂ x₃ x₄) 

castℕneΠ-elim : ∀ {Γ l A X t e t' e' r P Q} → Neutral A → Γ ⊢ cast ⁰ ℕ A e t ~ cast ⁰ ℕ (Π P ^ r ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ !) e' t' ↑! X ^ l → ⊥
castℕneΠ-elim neA (cast-cong () _ _ x₁ x₂ x₃ x₄)
castℕneΠ-elim neA (cast-ℕ () x₁ x₂ x₃)
castℕneΠ-elim () (cast-ℕΠ x x₁ x₂ x₃)

castℕneΠ-elim' : ∀ {Γ l A X t e t' e' r P Q} → Neutral A → Γ ⊢ cast ⁰ ℕ (Π P ^ r ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ !) e t ~ cast ⁰ ℕ A e' t' ↑! X ^ l → ⊥
castℕneΠ-elim' neA e = let _ , _ , e' = sym~↑! (reflConEq (wfEqTerm (soundness~↑! e))) e in castℕneΠ-elim neA e'

castℕℕΠ-elim : ∀ {Γ l X t e t' e' r P Q} → Γ ⊢ cast ⁰ ℕ ℕ e t ~ cast ⁰ ℕ (Π P ^ r ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ !) e' t' ↑! X ^ l → ⊥
castℕℕΠ-elim (cast-cong () _ _ x₁ x₂ x₃ x₄)
castℕℕΠ-elim (cast-ℕ () x₁ x₂ x₃)

castℕℕΠ-elim' : ∀ {Γ l X t e t' e' r P Q} → Γ ⊢ cast ⁰ ℕ (Π P ^ r ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ !) e t ~ cast ⁰ ℕ ℕ e' t' ↑! X ^ l → ⊥
castℕℕΠ-elim' e = let _ , _ , e' = sym~↑! (reflConEq (wfEqTerm (soundness~↑! e))) e in castℕℕΠ-elim e'


castΠneℕ-elim : ∀ {Γ l A X t e t' e' r P Q r' P' Q'} → Neutral A → Γ ⊢ cast ⁰ (Π P ^ r ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ !) A e t ~
                                                                       cast ⁰ (Π P' ^ r' ° ⁰ ▹ Q' ° ⁰ ° ⁰ ^ !) ℕ e' t' ↑! X ^ l → ⊥
castΠneℕ-elim neA (cast-cong () _ _ x₁ x₂ x₃ x₄)
castΠneℕ-elim neA (cast-Π x () x₂ x₃ x₄)
castΠneℕ-elim () (cast-Πℕ x x₁ x₂ x₃)

castΠneℕ-elim' : ∀ {Γ l A X t e t' e' r P Q r' P' Q'} → Neutral A → Γ ⊢ cast ⁰ (Π P ^ r ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ !) ℕ e t ~
                                                                       cast ⁰ (Π P' ^ r' ° ⁰ ▹ Q' ° ⁰ ° ⁰ ^ !) A e' t' ↑! X ^ l → ⊥
castΠneℕ-elim' neA e = let _ , _ , e' = sym~↑! (reflConEq (wfEqTerm (soundness~↑! e))) e in castΠneℕ-elim neA e'

castΠneΠ-elim : ∀ {Γ l A X t e t' e' r P Q r' P' Q' r'' P'' Q''} → Neutral A →
                  Γ ⊢ cast ⁰ (Π P ^ r ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ !) A e t ~ cast ⁰ (Π P' ^ r' ° ⁰ ▹ Q' ° ⁰ ° ⁰ ^ !) (Π P'' ^ r'' ° ⁰ ▹ Q'' ° ⁰ ° ⁰ ^ !) e' t' ↑! X ^ l → ⊥
castΠneΠ-elim neA (cast-cong () _ _ x₁ x₂ x₃ x₄)
castΠneΠ-elim neA (cast-Π x () x₂ x₃ x₄)
castΠneΠ-elim () (cast-ΠΠ%! x x₁ x₂ x₃ x₄)
castΠneΠ-elim () (cast-ΠΠ!% x x₁ x₂ x₃ x₄)

castΠneΠ-elim' : ∀ {Γ l A X t e t' e' r P Q r' P' Q' r'' P'' Q''} → Neutral A →
                  Γ ⊢ cast ⁰ (Π P ^ r ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ !) (Π P'' ^ r'' ° ⁰ ▹ Q'' ° ⁰ ° ⁰ ^ !) e t ~ cast ⁰ (Π P' ^ r' ° ⁰ ▹ Q' ° ⁰ ° ⁰ ^ !) A e' t' ↑! X ^ l → ⊥
castΠneΠ-elim' neA e = let _ , _ , e' = sym~↑! (reflConEq (wfEqTerm (soundness~↑! e))) e in castΠneΠ-elim neA e'

castΠΠℕ-elim : ∀ {Γ l X t e t' e' r P Q r' P' Q' r'' P'' Q''} →
                  Γ ⊢ cast ⁰ (Π P ^ r ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ !) ℕ e t ~ cast ⁰ (Π P' ^ r' ° ⁰ ▹ Q' ° ⁰ ° ⁰ ^ !) (Π P'' ^ r'' ° ⁰ ▹ Q'' ° ⁰ ° ⁰ ^ !) e' t' ↑! X ^ l → ⊥
castΠΠℕ-elim (cast-cong () _ _ x₁ x₂ x₃ x₄)
castΠΠℕ-elim (cast-Π x () x₂ x₃ x₄)

castΠΠℕ-elim' : ∀ {Γ l X t e t' e' r P Q r' P' Q' r'' P'' Q''} →
                  Γ ⊢ cast ⁰ (Π P ^ r ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ !) (Π P'' ^ r'' ° ⁰ ▹ Q'' ° ⁰ ° ⁰ ^ !) e t ~ cast ⁰ (Π P' ^ r' ° ⁰ ▹ Q' ° ⁰ ° ⁰ ^ !) ℕ e' t' ↑! X ^ l → ⊥
castΠΠℕ-elim' e = let _ , _ , e' = sym~↑! (reflConEq (wfEqTerm (soundness~↑! e))) e in castΠΠℕ-elim e'


castΠΠ!%-elim : ∀ {Γ l A A' X t e t' e' P Q P' Q'} → Γ ⊢ cast ⁰ (Π P ^ ! ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ !) A e t ~
                                                         cast ⁰ (Π P' ^ % ° ⁰ ▹ Q' ° ⁰ ° ⁰ ^ !) A' e' t' ↑! X ^ l → ⊥
castΠΠ!%-elim (cast-cong () _ _ x₁ x₂ x₃ x₄)

castΠΠ%!-elim : ∀ {Γ l A A' X t e t' e' P Q P' Q'} → Γ ⊢ cast ⁰ (Π P ^ % ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ !) A e t ~
                                                         cast ⁰ (Π P' ^ ! ° ⁰ ▹ Q' ° ⁰ ° ⁰ ^ !) A' e' t' ↑! X ^ l → ⊥
castΠΠ%!-elim (cast-cong () _ _ x₁ x₂ x₃ x₄)
-}

-- Helper functions for decidability for neutrals
decConv↓Term-ℕ-ins : ∀ {t u v Γ l}
 → Γ ⊢ t [conv↓] u ∷ ℕ ^ l
 → Γ ⊢ t ~ v ↓! ℕ ^ l
 → Γ ⊢ t ~ u ↓! ℕ ^ l
decConv↓Term-ℕ-ins (ℕ-ins x) t~t = x
decConv↓Term-ℕ-ins (ne-ins x x₁ () x₃) t~t
decConv↓Term-ℕ-ins (zero-refl x) ([~] A D whnfB (cast-refl' x₁ x₂ x₃)) =
  let _ , _ , neA = ne~↓! x₁
      e = whnfRed* D (ne neA)
  in ⊥-elim (ℕ≢ne neA (PE.sym e))
decConv↓Term-ℕ-ins (zero-refl x) ([~] .ℕ D whnfB (castℕ-refl' x₁ x₂))
  with ne~↓! x₁
... | _ , () , _
decConv↓Term-ℕ-ins (suc-cong x) ([~] A D whnfB (cast-refl' x₁ x₂ x₃)) =
  let _ , _ , neA = ne~↓! x₁
      e = whnfRed* D (ne neA)
  in ⊥-elim (ℕ≢ne neA (PE.sym e))
decConv↓Term-ℕ-ins (suc-cong x) ([~] .ℕ D whnfB (castℕ-refl' x₁ x₂))
  with ne~↓! x₁
... | _ , () , _

decConv↓Term-U-ins : ∀ {t u v Γ r lU l}
  → Γ ⊢ t [conv↓] u ∷ Univ r lU ^ l
  → Γ ⊢ t ~ v ↓! Univ r lU ^ l
  → Γ ⊢ t ~ u ↓! Univ r lU ^ l
decConv↓Term-U-ins (ne x) t~r = x
decConv↓Term-U-ins (Π-cong x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉) ([~] A D whnfB (cast-refl' x x₁₀ x₁₁)) =
  let _ , _ , neA = ne~↓! x
      e = whnfRed* D (ne neA)
  in ⊥-elim (U≢ne neA (PE.sym e))
                                                                              
decConv↓Term-U-ins (Π-cong x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉) ([~] .ℕ D whnfB (castℕ-refl' x x₁₀)) =
  let e = whnfRed* D ℕₙ in ⊥-elim (U≢ℕ (PE.sym e))

decConv↓Term-ne-ins : ∀ {t u A Γ l}
  → Neutral A
  → Γ ⊢ t [conv↓] u ∷ A ^ l
  → ∃ λ B → ∃ λ lB → Γ ⊢ t ~ u ↓! B ^ lB
decConv↓Term-ne-ins neA (ne-ins x x₁ x₂ x₃) = _ , _ , x₃

-- Helper function for decidability for impossibility of terms not being equal
-- as neutrals when they are equal as terms and the first is a neutral.
decConv↓Term-ℕ : ∀ {t u v Γ l}
  → Γ ⊢ t [conv↓] u ∷ ℕ ^ l
  → Γ ⊢ t ~ v ↓! ℕ ^ l
  → ¬ (Γ ⊢ t ~ u ↓! ℕ ^ l)
  → ⊥
decConv↓Term-ℕ (ℕ-ins x) t~t ¬u~u = ¬u~u x
decConv↓Term-ℕ (ne-ins x x₁ () x₃) t~t ¬u~u
decConv↓Term-ℕ (zero-refl x) ([~] A D whnfB (cast-refl' x₁ x₂ x₃)) ¬u~u =
  let _ , _ , neA = ne~↓! x₁
      e = whnfRed* D (ne neA)
  in ⊥-elim (ℕ≢ne neA (PE.sym e))
decConv↓Term-ℕ (zero-refl x) ([~] .ℕ D whnfB (castℕ-refl' x₁ x₂)) ¬u~u
 with ne~↓! x₁
... | _ , () , _
decConv↓Term-ℕ (suc-cong x) ([~] A D whnfB (cast-refl' x₁ x₂ x₃)) ¬u~u =
  let _ , _ , neA = ne~↓! x₁
      e = whnfRed* D (ne neA)
  in ⊥-elim (ℕ≢ne neA (PE.sym e))
decConv↓Term-ℕ (suc-cong x) ([~] .ℕ D whnfB (castℕ-refl' x₁ x₂)) ¬u~u
 with ne~↓! x₁
... | _ , () , _

decConv↓Term-U : ∀ {t u v Γ r lU l}
  → Γ ⊢ t [conv↓] u ∷ Univ r lU ^ l
  → Γ ⊢ t ~ v ↓! Univ r lU ^ l
  → ¬ (Γ ⊢ t ~ u ↓! Univ r lU ^ l)
  → ⊥
decConv↓Term-U (ne x) t~t ¬u~u = ¬u~u x
decConv↓Term-U (Π-cong x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀) ([~] A D whnfB (cast-refl' x x₁₀' x₁₁)) ¬u~u = 
  let _ , _ , neA = ne~↓! x
      e = whnfRed* D (ne neA)
  in ⊥-elim (U≢ne neA (PE.sym e))
decConv↓Term-U (Π-cong x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀) ([~] .ℕ D whnfB (castℕ-refl' x x₁₀')) ¬u~u =
  let e = whnfRed* D ℕₙ in ⊥-elim (U≢ℕ (PE.sym e))



abstract -- Agda will do some slow unfolding without abstract

  convert~-aux : ∀ {Δ B B' lB}
    → (Δ ⊢ B ~ B' ↓! U lB ^ next lB) 
    → ⊢ Δ ≡ Δ
  convert~-aux B = let ⊢M , ⊢A , ⊢B = syntacticEqTerm (soundness~↓! B) in reflConEq (wfTerm ⊢B)

  convert~-aux' : ∀ {Γ Δ A A' lA B B' lB M lM}
    → ⊢ Γ ≡ Δ
    → (Γ ⊢ A ~ A' ↓! U lA ^ next lA)
    → (Δ ⊢ B ~ B' ↓! U lB ^ next lB)
    → (Γ ⊢ A ~ B ↓! M ^ lM)
    → Δ ⊢ B ≡ A ^ [ ! , ι lA ]
  convert~-aux' Γ≡Δ A B A~B  =
    let
      whnfM , neA , neB = ne~↓! A~B
      ⊢M , ⊢A , ⊢B = syntacticEqTerm (soundness~↓! A~B)
      _ , ⊢A₂ , _ = syntacticEqTerm (soundness~↓! A)
      _ , ⊢B₂ , _ = syntacticEqTerm (soundness~↓! B)
      lA≡lM , ⊢UA≡M = neTypeEq neA ⊢A₂ ⊢A
      lM≡lB , ⊢M≡UA = neTypeEq neB ⊢B (stabilityTerm (symConEq Γ≡Δ) ⊢B₂)
      lA≡lB = next-inj (PE.trans lA≡lM lM≡lB)
      UA≡M = U≡A-whnf ⊢UA≡M whnfM
    in stabilityEq Γ≡Δ (univ (sym (soundness~↓! (PE.subst₂ (λ X Y → _ ⊢ _ ~ _ ↓! X ^ Y) UA≡M (PE.sym lA≡lM) A~B))))

  convert~-aux'' : ∀ {Γ Δ A A' lA B B' lB M lM}
    → ⊢ Γ ≡ Δ
    → (Γ ⊢ A ~ A' ↓! U lA ^ next lA)
    → (Δ ⊢ B ~ B' ↓! U lB ^ next lB)
    → (Γ ⊢ A ~ B ↓! M ^ lM)
    → lA PE.≡ lB
  convert~-aux'' Γ≡Δ A B A~B  =
    let
       whnfM , neA , neB = ne~↓! A~B
       ⊢M , ⊢A , ⊢B = syntacticEqTerm (soundness~↓! A~B)
       _ , ⊢A₂ , _ = syntacticEqTerm (soundness~↓! A)
       _ , ⊢B₂ , _ = syntacticEqTerm (soundness~↓! B)
       lA≡lM , ⊢UA≡M = neTypeEq neA ⊢A₂ ⊢A
       lM≡lB , ⊢M≡UA = neTypeEq neB ⊢B (stabilityTerm (symConEq Γ≡Δ) ⊢B₂)
     in next-inj (PE.trans lA≡lM lM≡lB)

  convert~ : ∀ {Γ Δ A A' lA B B' lB t u M lM}
    → ⊢ Γ ≡ Δ
    → (Γ ⊢ A ~ A' ↓! U lA ^ next lA)
    → (Δ ⊢ B ~ B' ↓! U lB ^ next lB)
    → (Γ ⊢ A ~ B ↓! M ^ lM)
    → (Δ ⊢ t [conv↑] u ∷ B ^ ι lB)
    → (Δ ⊢ t [conv↑] u ∷ A ^ ι lA)
  convert~ Γ≡Δ A B A~B t = convConv↑Term (convert~-aux B) (convert~-aux' Γ≡Δ A B A~B) (PE.subst (λ X → _ ⊢ _ [conv↑] _ ∷ _ ^ ι X) (PE.sym (convert~-aux'' Γ≡Δ A B A~B)) t)
  
  convert~size : ∀ {Γ Δ A A' lA B B' lB t u M lM}
    → (Γ≡Δ : ⊢ Γ ≡ Δ)
    → (A~ : Γ ⊢ A ~ A' ↓! U lA ^ next lA)
    → (B~ : Δ ⊢ B ~ B' ↓! U lB ^ next lB)
    → (A~B : Γ ⊢ A ~ B ↓! M ^ lM)
    → (t : Δ ⊢ t [conv↑] u ∷ B ^ ι lB)
    → sizeConv↑Term (convert~ Γ≡Δ A~ B~ A~B t) PE.≡ sizeConv↑Term t
  convert~size {Γ} {Δ} {A'} {lA} {B'} {lB} {t'} {M} {lM} Γ≡Δ A B A~B t =
      PE.trans (convConv↑TermSize (convert~-aux B) (convert~-aux' Γ≡Δ A B A~B) (PE.subst (λ X → _ ⊢ _ [conv↑] _ ∷ _ ^ ι X) (PE.sym (convert~-aux'' Γ≡Δ A B A~B)) t))
               (sizeSubst-gen (λ X → _ ⊢ _ [conv↑] _ ∷ _ ^ ι X) sizeConv↑Term t (PE.sym (convert~-aux'' Γ≡Δ A B A~B)))

  convert'~ : ∀ {Γ Δ A A' lA B B' lB t u M lM}
    → ⊢ Γ ≡ Δ
    → (Γ ⊢ A ~ A' ↓! U lA ^ next lA)
    → (Δ ⊢ B ~ B' ↓! U lB ^ next lB)
    → (Γ ⊢ A ~ B ↓! M ^ lM)
    → (Δ ⊢ t [conv↓] u ∷ B ^ ι lB)
    → (Δ ⊢ t [conv↓] u ∷ A ^ ι lA)
  convert'~ Γ≡Δ A B A~B t = 
    let whnfM , neA , neB = ne~↓! A~B
    in convConv↓Term (convert~-aux B) (convert~-aux' Γ≡Δ A B A~B) (ne neA) (PE.subst (λ X → _ ⊢ _ [conv↓] _ ∷ _ ^ ι X) (PE.sym (convert~-aux'' Γ≡Δ A B A~B)) t)


  convert'~size : ∀ {Γ Δ A A' lA B B' lB t u M lM}
    → (Γ≡Δ : ⊢ Γ ≡ Δ)
    → (A~ : Γ ⊢ A ~ A' ↓! U lA ^ next lA)
    → (B~ : Δ ⊢ B ~ B' ↓! U lB ^ next lB)
    → (A~B : Γ ⊢ A ~ B ↓! M ^ lM)
    → (t : Δ ⊢ t [conv↓] u ∷ B ^ ι lB)
    → sizeConv↓Term (convert'~ Γ≡Δ A~ B~ A~B t) PE.≡ sizeConv↓Term t
  convert'~size {Γ} {Δ} {A'} {lA} {B'} {lB} {t'} {M} {lM} Γ≡Δ A B A~B t =
    let
      whnfM , neA , neB = ne~↓! A~B
    in PE.trans (convConv↓TermSize (convert~-aux B) (convert~-aux' Γ≡Δ A B A~B) (ne neA) (PE.subst (λ X → _ ⊢ _ [conv↓] _ ∷ _ ^ ι X) (PE.sym (convert~-aux'' Γ≡Δ A B A~B)) t))
                (sizeSubst-gen (λ X → _ ⊢ _ [conv↓] _ ∷ _ ^ ι X) sizeConv↓Term t (PE.sym (convert~-aux'' Γ≡Δ A B A~B)))
                
abstract
  cast-refl-dec : ∀ {Γ A B t e u}
              → Neutral A
              → Neutral B
              → Γ ⊢ A ∷ Univ ! ⁰ ^ [ ! , ι ¹ ]
              → Γ ⊢ t ∷ A ^ [ ! , ι ⁰ ]
              → (⊢e : Γ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ])
              → (decAB : Dec (∃ λ U → ∃ λ lA → Γ ⊢ A ~ B ↓! U ^ lA))
              → (dectu : Dec (∃ λ U → ∃ λ lA → Γ ⊢ t ~ u ↑! U ^ lA))
              → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
              → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ A B e t ~ u ↑! U ^ lA)
  cast-refl-dec neA neB ⊢A ⊢tA ⊢e (yes (_ , _ , A~B)) (yes (_ , _ , p)) _ _ =
    let _ , neA , _ = ne~↓! A~B
        var≡t = soundness~↑! p
        ⊢K , ⊢t , ⊢u = syntacticEqTerm var≡t
        el , eA = type-uniq ⊢t ⊢tA
        _ , whnfD , dd = whNormTerm (un-univ (PE.subst (λ X →  _ ⊢ _ ^ [ ! , X ]) el ⊢K)) 
    in yes ( _ , _ , cast-refl (~atU ⊢A (_ , _ , A~B))
                               (ne-ins ⊢tA (conv (PE.subst (λ X → _ ⊢ _ ∷ _ ^ [ ! , X ]) el ⊢u )
                                               (PE.subst (λ X → _ ⊢ _ ≡ _ ^ [ ! , X ]) el eA))
                                       neA ([~] _ (red (univ:⇒*: dd)) whnfD (PE.subst (λ X → _ ⊢ _ ~ _ ↑! _ ^  X) el p)))
                                                                         ⊢e)
  cast-refl-dec neA neB ⊢A _ ⊢e (yes (_ , _ , A~B)) (no ¬p) noeqNe noeqℕ =
    no (λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ⊥-elim (let _ , _ , neA' = ne~↓! x
                                                            _ , neB' , _ = ne~↓! x₁
                                                        in noeqNe neA' neB' PE.refl) ;
            (_ , _ , cast-refl x x₁ x₂) → ¬p (_ , _ , let _ , neA , _ = ne~↓! A~B
                                                          _ , var~t' , _ = [conv↓]ne neA x₁
                                                          _ , var~t = neutral↓↑ var~t'
                                                      in var~t) ;
            (_ , _ , cast-refl' x x₁ x₂) → ⊥-elim (let _ , neB' , neA' = ne~↓! x
                                                   in noeqNe neA' neB' PE.refl) ;
            (_ , _ , castℕ-refl' x x₁) → ⊥-elim (noeqℕ PE.refl) })
  cast-refl-dec neA neB ⊢A _ ⊢e (no ¬AB) _ noeqNe noeqℕ =
    no (λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ⊥-elim (let _ , _ , neA' = ne~↓! x
                                                            _ , neB' , _ = ne~↓! x₁
                                                        in noeqNe neA' neB' PE.refl) ;
            (_ , _ , cast-refl x x₁ x₂) → ¬AB (_ , _ , x) ;
            (_ , _ , cast-refl' x x₁ x₂) → ⊥-elim (let _ , neB' , neA' = ne~↓! x
                                                   in noeqNe neA' neB' PE.refl) ;
            (_ , _ , castℕ-refl' x x₁) → ⊥-elim (noeqℕ PE.refl) })

abstract
  cast-refl'-dec : ∀ {Γ A B t e u}
                 → Neutral A
                 → Neutral B
                 → Γ ⊢ B ∷ Univ ! ⁰ ^ [ ! , ι ¹ ]
                 → Γ ⊢ t ∷ A ^ [ ! , ι ⁰ ]
                 → (⊢e : Γ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ])
                 → (decAB : Dec (∃ λ U → ∃ λ lA → Γ ⊢ B ~ A ↓! U ^ lA))
                 → (dectu : Dec (∃ λ U → ∃ λ lA → Γ ⊢ u ~ t ↑! U ^ lA))
                 → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
                 → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
                 → Dec (∃ λ U → ∃ λ lA → Γ ⊢ u ~ cast ⁰ A B e t ↑! U ^ lA)
  cast-refl'-dec neA neB ⊢B ⊢tA ⊢e (yes (_ , _ , B~A)) (yes (_ , _ , p)) _ _ =
    let _ , _ , neA = ne~↓! B~A
        var≡t = soundness~↑! p
        ⊢K , ⊢u , ⊢t  = syntacticEqTerm var≡t
        el , eA = type-uniq ⊢t ⊢tA
        _ , whnfD , dd = whNormTerm (un-univ (PE.subst (λ X →  _ ⊢ _ ^ [ ! , X ]) el ⊢K)) 
    in yes ( _ , _ , cast-refl' (~atU ⊢B (_ , _ , B~A))
                                (ne-ins (conv (PE.subst (λ X → _ ⊢ _ ∷ _ ^ [ ! , X ]) el ⊢u )
                                              (PE.subst (λ X → _ ⊢ _ ≡ _ ^ [ ! , X ]) el eA))
                                        ⊢tA
                                        neA ([~] _ (red (univ:⇒*: dd)) whnfD (PE.subst (λ X → _ ⊢ _ ~ _ ↑! _ ^  X) el p)))
                                        ⊢e)
  cast-refl'-dec neA neB _ _ ⊢e (yes (_ , _ , A~B)) (no ¬p) noeqNe noeqℕ =
    no (λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ⊥-elim (let _ , neA' , _ = ne~↓! x
                                                            _ , _ , neB' = ne~↓! x₁
                                                        in noeqNe neA' neB' PE.refl) ;
            (_ , _ , cast-refl' x x₁ x₂) → ¬p (_ , _ , let _ , _ , neA = ne~↓! A~B
                                                           _ , var~t' , _ = [conv↓]ne neA x₁  
                                                           _ , var~t = neutral↓↑ var~t'
                                                       in var~t) ;
            (_ , _ , cast-refl x x₁ x₂) → ⊥-elim (let _ , neA' , neB' = ne~↓! x
                                                  in noeqNe neA' neB' PE.refl) ;
            (_ , _ , castℕ-refl x x₁) → ⊥-elim (noeqℕ PE.refl) })
  cast-refl'-dec neA neB _ _ ⊢e (no ¬AB) _ noeqNe noeqℕ =
    no (λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ⊥-elim (let _ , neA' , _ = ne~↓! x
                                                            _ , _ , neB' = ne~↓! x₁
                                                        in noeqNe neA' neB' PE.refl) ;
            (_ , _ , cast-refl' x x₁ x₂) → ¬AB (_ , _ , x) ;
            (_ , _ , cast-refl x x₁ x₂) → ⊥-elim (let _ , neA' , neB' = ne~↓! x
                                                  in noeqNe neA' neB' PE.refl) ;
            (_ , _ , castℕ-refl x x₁) → ⊥-elim (noeqℕ PE.refl) })

abstract
  castℕ-refl-dec : ∀ {Γ A t e u}
              → Neutral A
              → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
              → (noeqNeℕ : ∀ {A' t' e'} → Neutral A' → u PE.≡ cast ⁰ ℕ A' e' t' → ⊥)
              → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ u ~ cast ⁰ ℕ A e t ↑! U ^ lA)
  castℕ-refl-dec _ noeqNe noeqNeℕ noeqℕ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neA , neB = ne~↓! x in noeqNe neA neB PE.refl ;
                                                  (_ , _ , castℕ-refl x x₁) → noeqℕ PE.refl ;
                                                  (_ , _ , cast-ℕ x x₁ x₂ x₃) → let _ , neA , _ = ne~↓! x in noeqNeℕ neA PE.refl } )

  castℕ-refl'-dec : ∀ {Γ A t e u}
              → Neutral A
              → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
              → (noeqNeℕ : ∀ {A' t' e'} → Neutral A' → u PE.≡ cast ⁰ ℕ A' e' t' → ⊥)
              → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ ℕ A e t ~ u ↑! U ^ lA)
  castℕ-refl'-dec _ noeqNe noeqNeℕ noeqℕ = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neB , neA = ne~↓! x in noeqNe neA neB PE.refl ;
                                                   (_ , _ , castℕ-refl' x x₁) → noeqℕ PE.refl ;
                                                   (_ , _ , cast-ℕ x x₁ x₂ x₃) → let _ , _ , neA = ne~↓! x in noeqNeℕ neA PE.refl } )

abstract
  cast-cast-≡ : ∀ {Γ A A' B B' t t' e e' X lX}
                 → Γ ⊢ cast ⁰ A B e t ~ cast ⁰ A' B' e' t' ↑! X ^ lX
                 → Γ ⊢ B ≡ B' ^ [ ! , ι ⁰ ]
  cast-cast-≡ X =
    let cast≡cast = soundness~↑! X
        _ , ⊢cast , ⊢cast' = syntacticEqTerm cast≡cast
        _ , _ , _ , _ , ⊢t , R≡R , eqR , _ = inversion-cast ⊢cast
        _ , _ , _ , _ , _ , T≡T , eqT , _ = inversion-cast ⊢cast'
        eqR , el = typeinfo-PE-injectivity eqR
        eqT , _ = typeinfo-PE-injectivity eqT
        T≡T' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqT) T≡T
        R≡R' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqR) R≡R
    in T.trans (T.sym R≡R') T≡T'

abstract
  castℕℕ-refl-dec : ∀ {Γ t e u}
              → Γ ⊢ t ∷ ℕ ^ [ ! , ι ⁰ ]
              → (⊢e : Γ ⊢ e ∷ (Id (U ⁰) ℕ ℕ) ^ [ % , ι ⁰ ])
              → (dectu : Dec (∃ λ U → ∃ λ lA → Γ ⊢ t ~ u ↑! U ^ lA))
              → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
              → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ ℕ ℕ e t ~ u ↑! U ^ lA)
  castℕℕ-refl-dec x ⊢e (yes (_ , _ , p)) _ _ =
    let var≡t = soundness~↑! p
        ⊢K , ⊢t , ⊢u = syntacticEqTerm var≡t
        el , eA = type-uniq ⊢t x
        _ , whnfD , dd = whNormTerm (un-univ (PE.subst (λ X →  _ ⊢ _ ^ [ ! , X ]) el ⊢K))
        eA' = ℕ≡A (trans (sym (PE.subst (λ X →  _ ⊢ _ ≡  _ ^ [ ! , X ]) el eA)) (subset* (univ⇒* (redₜ dd)))) whnfD
    in yes ( _ , _ , castℕ-refl ([~] _ (univ⇒* (PE.subst (λ X → _ ⊢ _ ⇒* X ∷ Univ ! ⁰ ^ ι ¹) eA' (redₜ dd))) ℕₙ (PE.subst (λ X → _ ⊢ _ ~ _ ↑! _ ^  X) el p)) ⊢e)
  castℕℕ-refl-dec t~t' ⊢e (no ¬p) noeqNe noeqℕ =
    no (λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ⊥-elim (let _ , _ , neA' = ne~↓! x
                                                            _ , neB' , _ = ne~↓! x₁
                                                        in noeqNe neA' neB' PE.refl) ;
            (_ , _ , cast-refl () x₁ x₂) ;
            (_ , _ , cast-refl' x x₁ x₂) → ⊥-elim (let _ , neB' , neA' = ne~↓! x
                                                   in noeqNe neA' neB' PE.refl) ;
            (_ , _ , castℕ-refl ([~] A D whnfB k~l) x₁) → ¬p (_ , _ , k~l) ;
            (_ , _ , castℕ-refl' x x₁) → ⊥-elim (noeqℕ PE.refl) })

  castℕℕ-refl'-dec : ∀ {Γ t e u}
                 → Γ ⊢ t ∷ ℕ ^ [ ! , ι ⁰ ]
                 → (⊢e : Γ ⊢ e ∷ (Id (U ⁰) ℕ ℕ) ^ [ % , ι ⁰ ])
                 → (dectu : Dec (∃ λ U → ∃ λ lA → Γ ⊢ u ~ t ↑! U ^ lA))
                 → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
                 → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
                 → Dec (∃ λ U → ∃ λ lA → Γ ⊢ u ~ cast ⁰ ℕ ℕ e t ↑! U ^ lA)
  castℕℕ-refl'-dec x ⊢e (yes (_ , _ , p)) _ _ =
    let var≡t = soundness~↑! p
        ⊢K , ⊢u , ⊢t = syntacticEqTerm var≡t
        el , eA = type-uniq ⊢t x
        _ , whnfD , dd = whNormTerm (un-univ (PE.subst (λ X →  _ ⊢ _ ^ [ ! , X ]) el ⊢K))
        eA' = ℕ≡A (trans (sym (PE.subst (λ X →  _ ⊢ _ ≡  _ ^ [ ! , X ]) el eA)) (subset* (univ⇒* (redₜ dd)))) whnfD
    in yes ( _ , _ , castℕ-refl' ([~] _ (univ⇒* (PE.subst (λ X → _ ⊢ _ ⇒* X ∷ Univ ! ⁰ ^ ι ¹) eA' (redₜ dd))) ℕₙ (PE.subst (λ X → _ ⊢ _ ~ _ ↑! _ ^  X) el p)) ⊢e)

  castℕℕ-refl'-dec t~t' ⊢e (no ¬p) noeqNe noeqℕ =
    no (λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ⊥-elim (let _ , neA' , _ = ne~↓! x
                                                            _ , _ , neB' = ne~↓! x₁
                                                        in noeqNe neA' neB' PE.refl) ;
            (_ , _ , cast-refl' () x₁ x₂) ;
            (_ , _ , cast-refl x x₁ x₂) → ⊥-elim (let _ , neA' , neB' = ne~↓! x
                                                  in noeqNe neA' neB' PE.refl) ;
            (_ , _ , castℕ-refl' ([~] A D whnfB k~l) x₁) → ¬p (_ , _ , k~l) ;
            (_ , _ , castℕ-refl x x₁) → ⊥-elim (noeqℕ PE.refl) })



abstract
  ~atU' : ∀ {Γ t v u r lU l}
    → Γ ⊢ t ~ v ↓! Univ r lU ^ l
    → (∃ λ A → ∃ λ lA → Γ ⊢ t ~ u ↓! A ^ lA)
    → Γ ⊢ t ~ u ↓! Univ r lU ^ l
  ~atU' t~v t~u = let _ , ⊢t , _ = syntacticEqTerm (soundness~↓! t~v) in ~atU ⊢t t~u

  sym~↓!U : ∀ {Γ A B r lU l}
    → Γ ⊢ A ~ B ↓! Univ r lU ^ l
    → Γ ⊢ B ~ A ↓! Univ r lU ^ l
  sym~↓!U A~B = let _ , _ , ⊢B = syntacticEqTerm (soundness~↓! A~B)
                    _ , _ , _ , B~A = sym~↓! (reflConEq (wfTerm ⊢B)) A~B
                in ~atU ⊢B (_ , _ , B~A)

  sym~↓!Usize : ∀ {Γ A B r lU l}
    → (A~B : Γ ⊢ A ~ B ↓! Univ r lU ^ l)
    → size~↓! (sym~↓!U A~B) PE.≡ size~↓! A~B
  sym~↓!Usize A~B =
    let _ , _ , ⊢B = syntacticEqTerm (soundness~↓! A~B)
        _ , _ , _ , B~A = sym~↓! (reflConEq (wfTerm ⊢B)) A~B
    in PE.trans (~atUsize ⊢B (_ , _ , B~A)) (size-sym~↓! (reflConEq (wfTerm ⊢B)) A~B)

  reflℕ :  ∀ {Γ t u}
    → Γ ⊢ t ~ u ↓! ℕ ^ ι ⁰
    → Γ ⊢ t ~ t ↓! ℕ ^ ι ⁰
  reflℕ t~u =
    let _ , _ , ⊢u = syntacticEqTerm (soundness~↓! t~u)
        _ , _ , _ , u~t = sym~↓! (reflConEq (wfTerm ⊢u)) t~u
        C , wC , t~t , eqC = trans~↓!-simpl t~u u~t
        eqℕ = ℕ≡A eqC wC        
    in PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ ι ⁰) eqℕ t~t 

  cast-refl'-dec~ : ∀ {Γ A A' B B' t t' e u}
                 → Γ ⊢ A ~ A' ↓! U ⁰ ^ next ⁰
                 → Γ ⊢ B ~ B' ↓! U ⁰ ^ ι ¹
                 → Γ ⊢ t [conv↓] t' ∷ A ^ ι ⁰
                 → (⊢e : Γ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ])
                 → (decAB : Dec (∃ λ U → ∃ λ lA → Γ ⊢ B ~ A ↓! U ^ lA))
                 → (dectu : Dec (∃ λ U → ∃ λ lA → Γ ⊢ u ~ t ↑! U ^ lA))
                 → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
                 → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
                 → Dec (∃ λ U → ∃ λ lA → Γ ⊢ u ~ cast ⁰ A B e t ↑! U ^ lA)
  cast-refl'-dec~ A B t ⊢e decAB dectu noeqNe noeqℕ =
    let _ , neA , _ = ne~↓! A
        _ , neB , _ = ne~↓! B
        _ , ⊢B , _ = syntacticEqTerm (soundness~↓! B)
        _ , ⊢t , _ = syntacticEqTerm (soundnessConv↓Term t)
    in cast-refl'-dec neA neB ⊢B ⊢t ⊢e decAB dectu noeqNe noeqℕ

  cast-refl-dec~ : ∀ {Γ A A' B B' t t' e u}
                 → Γ ⊢ A ~ A' ↓! U ⁰ ^ next ⁰
                 → Γ ⊢ B ~ B' ↓! U ⁰ ^ ι ¹
                 → Γ ⊢ t [conv↓] t' ∷ A ^ ι ⁰
                 → (⊢e : Γ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ])
                 → (decAB : Dec (∃ λ U → ∃ λ lA → Γ ⊢ A ~ B ↓! U ^ lA))
                 → (dectu : Dec (∃ λ U → ∃ λ lA → Γ ⊢ t ~ u ↑! U ^ lA))
                 → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
                 → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
                 → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ A B e t ~ u ↑! U ^ lA)
  cast-refl-dec~ A B t ⊢e decAB dectu noeqNe noeqℕ =
    let _ , neA , _ = ne~↓! A
        _ , neB , _ = ne~↓! B
        _ , ⊢A , _ = syntacticEqTerm (soundness~↓! A)
        _ , ⊢t , _ = syntacticEqTerm (soundnessConv↓Term t)
    in cast-refl-dec neA neB ⊢A ⊢t ⊢e decAB dectu noeqNe noeqℕ

  castℕ-refl-dec~ : ∀ {Γ A A' t e u}
              → Γ ⊢ A ~ A' ↓! U ⁰ ^ next ⁰
              → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
              → (noeqNeℕ : ∀ {A' t' e'} → Neutral A' → u PE.≡ cast ⁰ ℕ A' e' t' → ⊥)
              → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ u ~ cast ⁰ ℕ A e t ↑! U ^ lA)
  castℕ-refl-dec~ A noeqNe noeqNeℕ noeqℕ = let _ , neA , _ = ne~↓! A in castℕ-refl-dec neA noeqNe noeqNeℕ noeqℕ

  castℕ-refl'-dec~ : ∀ {Γ A A' t e u}
              → Γ ⊢ A ~ A' ↓! U ⁰ ^ next ⁰
              → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
              → (noeqNeℕ : ∀ {A' t' e'} → Neutral A' → u PE.≡ cast ⁰ ℕ A' e' t' → ⊥)
              → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ ℕ A e t ~ u ↑! U ^ lA)
  castℕ-refl'-dec~ A noeqNe noeqNeℕ noeqℕ = let _ , neA , _ = ne~↓! A in castℕ-refl'-dec neA noeqNe noeqNeℕ noeqℕ

  castℕℕ-refl-dec~ : ∀ {Γ t t' e u}
              → Γ ⊢ t ~ t' ↓! ℕ ^ ι ⁰
              → (⊢e : Γ ⊢ e ∷ (Id (U ⁰) ℕ ℕ) ^ [ % , ι ⁰ ])
              → (dectu : Dec (∃ λ U → ∃ λ lA → Γ ⊢ t ~ u ↑! U ^ lA))
              → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
              → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ ℕ ℕ e t ~ u ↑! U ^ lA)
  castℕℕ-refl-dec~ X ⊢e dectu noeqNe noeqℕ = let _ , x , _ = syntacticEqTerm (soundness~↓! X) in castℕℕ-refl-dec x ⊢e dectu noeqNe noeqℕ

  castℕℕ-refl'-dec~ : ∀ {Γ t t' e u}
              → Γ ⊢ t ~ t' ↓! ℕ ^ ι ⁰
              → (⊢e : Γ ⊢ e ∷ (Id (U ⁰) ℕ ℕ) ^ [ % , ι ⁰ ])
              → (dectu : Dec (∃ λ U → ∃ λ lA → Γ ⊢ u ~ t ↑! U ^ lA))
              → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
              → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ u ~ cast ⁰ ℕ ℕ e t ↑! U ^ lA)
  castℕℕ-refl'-dec~ X ⊢e dectu noeqNe noeqℕ = let _ , x , _ = syntacticEqTerm (soundness~↓! X) in castℕℕ-refl'-dec x ⊢e dectu noeqNe noeqℕ


  cast-cast-dec : ∀ {Γ Δ A B t e C D u e'}
              → ⊢ Γ ≡ Δ
              → Neutral A
              → Neutral B
              → Neutral C
              → Neutral D
              → Γ ⊢ A ∷ Univ ! ⁰ ^ [ ! , ι ¹ ]
              → Γ ⊢ B ∷ Univ ! ⁰ ^ [ ! , ι ¹ ]
              → Δ ⊢ C ∷ Univ ! ⁰ ^ [ ! , ι ¹ ]
              → Δ ⊢ D ∷ Univ ! ⁰ ^ [ ! , ι ¹ ]
              → Γ ⊢ t ∷ A ^ [ ! , ι ⁰ ]
              → Δ ⊢ u ∷ C ^ [ ! , ι ⁰ ]
              → (⊢e : Γ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ])
              → (⊢e' : Δ ⊢ e' ∷ (Id (U ⁰) C D) ^ [ % , ι ⁰ ])
              → (decAB : Dec (∃ λ U → ∃ λ lA → Γ ⊢ A ~ C ↓! U ^ lA))
              → (decDB : Dec (∃ λ U → ∃ λ lA → Δ ⊢ D ~ B ↓! U ^ lA))
              → (decAC : Dec (∃ λ U → ∃ λ lA → Γ ⊢ A ~ B ↓! U ^ lA))
              → (decCD : Dec (∃ λ U → ∃ λ lA → Δ ⊢ C ~ D ↓! U ^ lA))
              → (dectu : (∃ λ U → ∃ λ lA → Γ ⊢ A ~ C ↓! U ^ lA) → Dec (Γ ⊢ t [conv↓] u ∷ A ^ ι ⁰))
              → (dectcast : Dec (∃ λ U → ∃ λ lA → Γ ⊢ t ~ cast ⁰ C D e' u ↑! U ^ lA))
              → (deccastu : Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ A B e t ~ u ↑! U ^ lA))
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ A B e t ~ cast ⁰ C D e' u ↑! U ^ lA)
  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u ⊢e ⊢e' _ (no ¬BD) _ _ _ _ _ =
    no λ { (_ , _ , X) → ¬BD (U ⁰ , ι ¹ , ~atU ⊢D
                                               let T≡R = sym (cast-cast-≡ X)
                                                   eq = completeEqNeutral neD neB (un-univ≡ (stabilityEq Γ≡Δ T≡R))
                                               in  _ , _ , eq) } 
  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u ⊢e ⊢e' (yes (_ , _ , A~C)) (yes (_ , _ , B~D)) (yes (_ , _ , A~B)) _ dectu _ _
    with dectu (_ , _ , A~C)
  ... | yes p = yes (_ , _ , cast-cong (~atU ⊢A (_ , _ , A~C)) (~atU (stabilityTerm (symConEq Γ≡Δ) ⊢D) (_ , _ , stability~↓! (symConEq Γ≡Δ) B~D)) p ⊢e (stabilityTerm (symConEq Γ≡Δ) ⊢e'))
  ... | no ¬p = no λ { (_ , _ , X) → let whnfcast , whnfcast' = ne~↑! X
                                         cast≡cast = soundness~↑! X
                                         A≡B = soundness~↓! (~atU ⊢A (_ , _ , A~B))
                                         A≡C = soundness~↓! (~atU ⊢A (_ , _ , A~C))
                                         B≡D = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! (~atU ⊢D (_ , _ , B~D))))
                                         C≡D = trans (sym (univ A≡C)) (trans (univ A≡B) (sym B≡D))
                                         _ , ⊢cast , ⊢cast' = syntacticEqTerm cast≡cast
                                         _ , _ , _ , _ , ⊢t , R≡R , eqR , _ = inversion-cast ⊢cast
                                         eqR , el = typeinfo-PE-injectivity eqR
                                         R≡R' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqR) R≡R
                                         cast≡cast' = PE.subst (λ X →  _ ⊢ _ ≡ _ ∷ _ ^ [ ! , X ]) el cast≡cast
                                         ⊢t' = PE.subst (λ X →  _ ⊢ _ ∷ _ ^ [ X , _ ]) (PE.sym eqR) ⊢t
                                         net = castNeutralInv neA neB whnfcast
                                         neu = castNeutralInv neC neD whnfcast'                                        
                                     in ¬p (completeEqTerm↓ (ne neA) (ne net) (ne neu)
                                                            (trans (sym (conv (T.cast-refl A≡B ⊢e ⊢t') (sym (univ A≡B))))
                                                            (trans (conv cast≡cast' (trans R≡R' (sym (univ A≡B))))
                                                            (conv (T.cast-refl (un-univ≡ C≡D) (stabilityTerm (symConEq Γ≡Δ) ⊢e') (stabilityTerm (symConEq Γ≡Δ) ⊢u))
                                                                  (trans B≡D (sym (univ A≡B))))))) }
  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u eAB eCD (no ¬AC) (yes B~D) (yes A~B) (yes C~D) _ _ _ =
    no λ { (_ , _ , X) → ¬AC (let _ , _ , _ , D~B = sym~↓! (reflConEq (wfTerm eCD)) (~atU ⊢D B~D)
                                  _ , _ , A~D , _ = trans~↓!-simpl (~atU ⊢A A~B) (stability~↓! (symConEq Γ≡Δ) D~B)
                                  _ , _ , _ , D~C = sym~↓! (reflConEq (wfTerm eCD)) (~atU ⊢C C~D)
                                  _ , _ , A~C , _ = trans~↓!-simpl A~D (stability~↓! (symConEq Γ≡Δ) D~C)
                              in _ , _ , A~C )}

  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u eAB eCD (yes A~C) (yes B~D) (no ¬AB) (yes C~D) _ _ _ =
    no λ { (_ , _ , X) → ¬AB (let _ , _ , A~D , _ = trans~↓!-simpl (~atU ⊢A A~C) (stability~↓! (symConEq Γ≡Δ) (~atU ⊢C C~D))
                                  _ , _ , A~B , _ = trans~↓!-simpl A~D (stability~↓! (symConEq Γ≡Δ) (~atU ⊢D B~D))
                              in _ , _ , A~B )}

  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u eAB eCD (no ¬AC) (yes B~D) (no ¬AB) (no ¬CD) _ _ _ =
    no λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ¬AC (_ , _ , x) ;
           (_ , _ , cast-refl x x₁ x₂) → ¬AB (_ , _ , x) ;
           (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , _ , D~B = sym~↓! Γ≡Δ (~atU (stabilityTerm (symConEq Γ≡Δ) ⊢D) (_ , _ , x))
                                          in ¬CD (_ , _ , D~B)}

  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u eAB eCD (no ¬AC) (yes B~D) (yes A~B) (no ¬CD) _ (yes (_ , _ , tu)) _ =
    yes (_ , _ , let t≡cast = soundness~↑! tu
                     ⊢K , _ , ⊢cast' = syntacticEqTerm t≡cast
                     _ , ⊢A' , ⊢B' , _ , ⊢t' , T≡T , eqT , _ = inversion-cast ⊢cast'
                     eqT , el = typeinfo-PE-injectivity eqT
                     _ , whnfD , dd = whNormTerm (un-univ (PE.subst (λ X →  _ ⊢ _ ^ [ ! , X ]) el ⊢K)) 
                     A≡B = soundness~↓! (~atU ⊢A A~B)
                     B≡D = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! (~atU ⊢D B~D)))
                  in cast-refl (~atU ⊢A A~B) (ne-ins ⊢t (conv (T.castⱼ (PE.subst (λ X →  _ ⊢ _ ∷ Univ X _ ^ _) (PE.sym eqT) ⊢A')
                                                                                                (PE.subst (λ X →  _ ⊢ _ ∷ Univ X _ ^ _) (PE.sym eqT) ⊢B')
                                                                                                (stabilityTerm (symConEq Γ≡Δ) eCD)
                                                                                                (PE.subst (λ X →  _ ⊢ _ ∷ _ ^ [ X , _ ]) (PE.sym eqT) ⊢t'))
                                                                                       (trans B≡D (sym (univ A≡B))))
                                                                          neA ([~] _ (red (univ:⇒*: dd)) whnfD (PE.subst (λ X →  _ ⊢ _ ~ _ ↑! _ ^ X) el tu)))
                                                     eAB)

  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u eAB eCD (no ¬AC) (yes B~D) (yes A~B) (no ¬CD) _ (no ¬tu) _ =
                 no λ { (_ , _ , X) → let whnfcast , whnfcast' = ne~↑! X
                                          cast≡cast = soundness~↑! X
                                          A≡B = soundness~↓! (~atU ⊢A A~B)
                                          B≡D = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! (~atU ⊢D B~D)))
                                          _ , ⊢cast , ⊢cast' = syntacticEqTerm cast≡cast
                                          _ , _ , _ , _ , ⊢t , R≡R , eqR , _ = inversion-cast ⊢cast
                                          _ , _ , _ , _ , _ , T≡T , eqT , _ = inversion-cast ⊢cast'
                                          eqR , el = typeinfo-PE-injectivity eqR
                                          eqT , _ = typeinfo-PE-injectivity eqT
                                          T≡T' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqT) T≡T
                                          R≡R' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqR) R≡R
                                          cast≡cast' = PE.subst (λ X →  _ ⊢ _ ≡ _ ∷ _ ^ [ ! , X ]) el cast≡cast
                                          ⊢t' = PE.subst (λ X →  _ ⊢ _ ∷ _ ^ [ X , _ ]) (PE.sym eqR) ⊢t
                                          net = castNeutralInv neA neB whnfcast
                                          neu = castNeutralInv neC neD whnfcast'                                        
                                       in ¬tu (let _ , e' , _ = [conv↓]ne neA (completeEqTerm↓ (ne neA) (ne net) (ne (castₙ neC neD neu))
                                                                                               (trans (sym (conv (T.cast-refl A≡B eAB ⊢t') (sym (univ A≡B)) ))
                                                                                                      (conv cast≡cast' (trans R≡R' (sym (univ A≡B))))))
                                                   _ , e = neutral↓↑ e' in _ , _ , e) }

  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u eAB eCD (no ¬AC) (yes B~D) (no ¬AB) (yes C~D) _ _ (yes (_ , _ , tu)) =
                           yes (_ , _ , let t≡cast = soundness~↑! tu
                                            ⊢K , ⊢cast , _ = syntacticEqTerm t≡cast
                                            _ , ⊢A' , ⊢B' , _ , ⊢t' , T≡T , eqT , _ = inversion-cast ⊢cast
                                            eqT , el = typeinfo-PE-injectivity eqT
                                            _ , _ , _ , D~C = sym~↓! (symConEq Γ≡Δ) (~atU ⊢C C~D)
                                            _ , whnfD , dd = whNormTerm (un-univ (PE.subst (λ X →  _ ⊢ _ ^ [ ! , X ]) el ⊢K)) 
                                            C≡D = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! (~atU ⊢C C~D)))
                                            B≡D = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! (~atU ⊢D B~D)))
                                            in cast-refl' (~atU (stabilityTerm (symConEq Γ≡Δ) ⊢D) (_ , _ , D~C))
                                                          (ne-ins (conv (T.castⱼ (PE.subst (λ X →  _ ⊢ _ ∷ Univ X _ ^ _) (PE.sym eqT) ⊢A')
                                                                                 (PE.subst (λ X →  _ ⊢ _ ∷ Univ X _ ^ _) (PE.sym eqT) ⊢B')
                                                                                 eAB
                                                                                 (PE.subst (λ X →  _ ⊢ _ ∷ _ ^ [ X , _ ]) (PE.sym eqT) ⊢t'))
                                                                        (trans (sym B≡D) (sym C≡D)))
                                                                  (stabilityTerm (symConEq Γ≡Δ) ⊢u)
                                                                  neC ([~] _ (red (univ:⇒*: dd)) whnfD (PE.subst (λ X →  _ ⊢ _ ~ _ ↑! _ ^ X) el tu)))
                                                          (stabilityTerm (symConEq Γ≡Δ) eCD))

  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u eAB eCD (no ¬AC) (yes B~D) (no ¬AB) (yes C~D) _ _ (no ¬tu) =
                 no λ { (_ , _ , X) → let whnfcast , whnfcast' = ne~↑! X
                                          cast≡cast = soundness~↑! X
                                          C≡D = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! (~atU ⊢C C~D)))
                                          B≡D = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! (~atU ⊢D B~D)))
                                          _ , ⊢cast , ⊢cast' = syntacticEqTerm cast≡cast
                                          _ , _ , _ , _ , ⊢t , R≡R , eqR , _ = inversion-cast ⊢cast
                                          _ , _ , _ , _ , _ , T≡T , eqT , _ = inversion-cast ⊢cast'
                                          eqR , el = typeinfo-PE-injectivity eqR
                                          eqT , _ = typeinfo-PE-injectivity eqT
                                          T≡T' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqT) T≡T
                                          R≡R' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqR) R≡R
                                          cast≡cast' = PE.subst (λ X →  _ ⊢ _ ≡ _ ∷ _ ^ [ ! , X ]) el cast≡cast
                                          ⊢t' = PE.subst (λ X →  _ ⊢ _ ∷ _ ^ [ X , _ ]) (PE.sym eqR) ⊢t
                                          net = castNeutralInv neA neB whnfcast
                                          neu = castNeutralInv neC neD whnfcast'                                        
                                       in ¬tu (let _ , e' , _ = [conv↓]ne neB (completeEqTerm↓ (ne neB) (ne (castₙ neA neB net)) (ne neu)
                                                                                               (trans (conv cast≡cast' R≡R')
                                                                                                      (conv (T.cast-refl (un-univ≡ C≡D) (stabilityTerm (symConEq Γ≡Δ) eCD)
                                                                                                                         (stabilityTerm (symConEq Γ≡Δ) ⊢u))
                                                                                                            (trans (sym T≡T') R≡R'))))
                                                   _ , e = neutral↓↑ e' in _ , _ , e) } 

  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u ⊢e ⊢e' (yes (_ , _ , A~C)) (yes (_ , _ , B~D)) (no ¬AB) (no ¬CD) dectu _ _
    with dectu (_ , _ , A~C)
  ... | yes p = yes (_ , _ , cast-cong (~atU ⊢A (_ , _ , A~C)) (~atU (stabilityTerm (symConEq Γ≡Δ) ⊢D) (_ , _ , stability~↓! (symConEq Γ≡Δ) B~D)) p ⊢e (stabilityTerm (symConEq Γ≡Δ) ⊢e'))
  ... | no ¬p = no λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ¬p x₂ ;
                       (_ , _ , cast-refl x x₁ x₂) → ¬AB (_ , _ , x) ;
                       (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , _ , D~B = sym~↓! Γ≡Δ (~atU (stabilityTerm (symConEq Γ≡Δ) ⊢D) (_ , _ , x))
                                                      in ¬CD (_ , _ , D~B) }
