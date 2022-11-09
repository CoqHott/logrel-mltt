{-# OPTIONS --safe #-}

module Definition.Conversion.HelperDecidable where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Conversion
open import Definition.Conversion.Whnf
open import Definition.Conversion.Soundness
open import Definition.Conversion.Symmetry
open import Definition.Conversion.Stability
open import Definition.Conversion.Conversion
open import Definition.Conversion.Lift
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.Reduction
open import Definition.Typed.Consequences.Equality
open import Definition.Typed.Consequences.Inequality as IE
open import Definition.Typed.Consequences.NeTypeEq
open import Definition.Typed.Consequences.SucCong
open import Definition.Typed.Consequences.Inversion

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

nonNeutralℕ : Neutral ℕ → ⊥
nonNeutralℕ ()

nonNeutralU : ∀ {r l} → Neutral (Univ r l) → ⊥
nonNeutralU ()

Idℕ-elim : ∀ {Γ l A B t u t' u'} → Neutral A → Γ ⊢ Id A t u ~ Id ℕ t' u' ↑! B ^ l → ⊥
Idℕ-elim neA (Id-cong x x₁ x₂) = let _ , _ , neℕ = ne~↓! x in ⊥-elim (nonNeutralℕ neℕ)
Idℕ-elim neA (Id-ℕ x x₁) = ⊥-elim (nonNeutralℕ neA)
Idℕ-elim neA (Id-ℕ0 x) = ⊥-elim (nonNeutralℕ neA)
Idℕ-elim neA (Id-ℕS x x₁) = ⊥-elim (nonNeutralℕ neA)

Idℕ-elim' : ∀ {Γ l A B t u t' u'} → Neutral A → Γ ⊢ Id ℕ t u ~ Id A t' u' ↑! B ^ l → ⊥
Idℕ-elim' neA e = let _ , _ , e' = sym~↑! (reflConEq (wfEqTerm (soundness~↑! e))) e in Idℕ-elim neA e'

conv↑-inversion : ∀ {Γ l A t u} → Whnf A → Whnf t → Whnf u → Γ ⊢ t [conv↑] u ∷ A ^ l → Γ ⊢ t [conv↓] u ∷ A ^ l
conv↑-inversion whnfA whnft whnfu ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) = 
  let et = whnfRed*Term d whnft
      eu = whnfRed*Term d′ whnfu
      eA = whnfRed* D whnfA
  in PE.subst₃ (λ A X Y → _ ⊢ X [conv↓] Y ∷ A ^ _) (PE.sym eA) (PE.sym et) (PE.sym eu) t<>u

noNeℕ : Neutral ℕ → ⊥
noNeℕ ()

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
IdU-elim neA (Id-cong x x₁ x₂) = let _ , _ , neU = ne~↓! x in ⊥-elim (nonNeutralU neU)
IdU-elim neA (Id-U x x₁) = ⊥-elim (nonNeutralU neA)
IdU-elim neA (Id-Uℕ x) = ⊥-elim (nonNeutralU neA)
IdU-elim neA (Id-UΠ x x₁) = ⊥-elim (nonNeutralU neA)

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
decConv↓Term-ℕ-ins : ∀ {t u Γ l}
 → Γ ⊢ t [conv↓] u ∷ ℕ ^ l
 → Γ ⊢ t ~ t ↓! ℕ ^ l
 → Γ ⊢ t ~ u ↓! ℕ ^ l
decConv↓Term-ℕ-ins (ℕ-ins x) t~t = x
decConv↓Term-ℕ-ins (ne-ins x x₁ () x₃) t~t
decConv↓Term-ℕ-ins (zero-refl x) ([~] A D whnfB ())
decConv↓Term-ℕ-ins (suc-cong x) ([~] A D whnfB ())

decConv↓Term-U-ins : ∀ {t u Γ r lU l}
  → Γ ⊢ t [conv↓] u ∷ Univ r lU ^ l
  → Γ ⊢ t ~ t ↓! Univ r lU ^ l
  → Γ ⊢ t ~ u ↓! Univ r lU ^ l
decConv↓Term-U-ins (ne x) t~r = x

decConv↓Term-ne-ins : ∀ {t u A Γ l}
  → Neutral A
  → Γ ⊢ t [conv↓] u ∷ A ^ l
  → ∃ λ B → ∃ λ lB → Γ ⊢ t ~ u ↓! B ^ lB
decConv↓Term-ne-ins neA (ne-ins x x₁ x₂ x₃) = _ , _ , x₃

-- Helper function for decidability for impossibility of terms not being equal
-- as neutrals when they are equal as terms and the first is a neutral.
decConv↓Term-ℕ : ∀ {t u Γ l}
  → Γ ⊢ t [conv↓] u ∷ ℕ ^ l
  → Γ ⊢ t ~ t ↓! ℕ ^ l
  → ¬ (Γ ⊢ t ~ u ↓! ℕ ^ l)
  → ⊥
decConv↓Term-ℕ (ℕ-ins x) t~t ¬u~u = ¬u~u x
decConv↓Term-ℕ (ne-ins x x₁ () x₃) t~t ¬u~u
decConv↓Term-ℕ (zero-refl x) ([~] A D whnfB ()) ¬u~u
decConv↓Term-ℕ (suc-cong x) ([~] A D whnfB ()) ¬u~u

decConv↓Term-U : ∀ {t u Γ r lU l}
  → Γ ⊢ t [conv↓] u ∷ Univ r lU ^ l
  → Γ ⊢ t ~ t ↓! Univ r lU ^ l
  → ¬ (Γ ⊢ t ~ u ↓! Univ r lU ^ l)
  → ⊥
decConv↓Term-U (ne x) t~t ¬u~u = ¬u~u x


abstract -- Agda will do some slow unfolding without abstract
  ~atℕ : ∀ {Γ t u}
    → Γ ⊢ t ∷ ℕ ^ [ ! , ι ⁰ ]
    → (∃ λ A → ∃ λ lA → Γ ⊢ t ~ u ↓! A ^ lA)
    → Γ ⊢ t ~ u ↓! ℕ ^ ι ⁰
  ~atℕ ⊢t∷ℕ (A , lA , t~u) =
    let whnfA , neT , neU = ne~↓! t~u
        ⊢A , ⊢t , ⊢u = syntacticEqTerm (soundness~↓! t~u)
        l≡l , ⊢ℕ≡A = neTypeEq neT ⊢t∷ℕ ⊢t
        A≡ℕ = ℕ≡A ⊢ℕ≡A whnfA
    in PE.subst₂ (λ X Y → _ ⊢ _ ~ _ ↓! X ^ Y) A≡ℕ (PE.sym l≡l) t~u

  ~atU : ∀ {Γ t u r lU l}
    → Γ ⊢ t ~ t ↓! Univ r lU ^ l
    → (∃ λ A → ∃ λ lA → Γ ⊢ t ~ u ↓! A ^ lA)
    → Γ ⊢ t ~ u ↓! Univ r lU ^ l
  ~atU t (A , lA , t~u) =
    let whnfA , neT , neU = ne~↓! t~u
        ⊢A , ⊢t , ⊢u = syntacticEqTerm (soundness~↓! t~u)
        _ , ⊢t∷U , _ = syntacticEqTerm (soundness~↓! t)
        l≡l , ⊢U≡A = neTypeEq neT ⊢t∷U ⊢t
        A≡U = U≡A-whnf ⊢U≡A whnfA
    in PE.subst₂ (λ X Y → _ ⊢ _ ~ _ ↓! X ^ Y) A≡U (PE.sym l≡l) t~u

  convert~ : ∀ {Γ Δ A lA B lB t M lM}
    → ⊢ Γ ≡ Δ
    → (Γ ⊢ A ~ A ↓! U lA ^ next lA)
    → (Δ ⊢ B ~ B ↓! U lB ^ next lB)
    → (Γ ⊢ A ~ B ↓! M ^ lM)
    → (Δ ⊢ t [conv↑] t ∷ B ^ ι lB)
    → (Δ ⊢ t [conv↑] t ∷ A ^ ι lA)
  convert~ Γ≡Δ A B A~B t =
    let
      whnfM , neA , neB = ne~↓! A~B
      ⊢M , ⊢A , ⊢B = syntacticEqTerm (soundness~↓! A~B)
      _ , ⊢A₂ , _ = syntacticEqTerm (soundness~↓! A)
      _ , ⊢B₂ , _ = syntacticEqTerm (soundness~↓! B)
      lA≡lM , ⊢UA≡M = neTypeEq neA ⊢A₂ ⊢A
      lM≡lB , ⊢M≡UA = neTypeEq neB ⊢B (stabilityTerm (symConEq Γ≡Δ) ⊢B₂)
      lA≡lB = next-inj (PE.trans lA≡lM lM≡lB)
      UA≡M = U≡A-whnf ⊢UA≡M whnfM
      ⊢A≡B = stabilityEq Γ≡Δ (univ (sym (soundness~↓! (PE.subst₂ (λ X Y → _ ⊢ _ ~ _ ↓! X ^ Y) UA≡M (PE.sym lA≡lM) A~B))))
    in convConv↑Term (reflConEq (wfTerm ⊢B₂)) ⊢A≡B (PE.subst (λ X → _ ⊢ _ [conv↑] _ ∷ _ ^ ι X) (PE.sym lA≡lB) t)


  convert'~ : ∀ {Γ Δ A lA B lB t M lM}
    → ⊢ Γ ≡ Δ
    → (Γ ⊢ A ~ A ↓! U lA ^ next lA)
    → (Δ ⊢ B ~ B ↓! U lB ^ next lB)
    → (Γ ⊢ A ~ B ↓! M ^ lM)
    → (Δ ⊢ t [conv↓] t ∷ B ^ ι lB)
    → (Δ ⊢ t [conv↓] t ∷ A ^ ι lA)
  convert'~ Γ≡Δ A B A~B t =
    let
      whnfM , neA , neB = ne~↓! A~B
      ⊢M , ⊢A , ⊢B = syntacticEqTerm (soundness~↓! A~B)
      _ , ⊢A₂ , _ = syntacticEqTerm (soundness~↓! A)
      _ , ⊢B₂ , _ = syntacticEqTerm (soundness~↓! B)
      lA≡lM , ⊢UA≡M = neTypeEq neA ⊢A₂ ⊢A
      lM≡lB , ⊢M≡UA = neTypeEq neB ⊢B (stabilityTerm (symConEq Γ≡Δ) ⊢B₂)
      lA≡lB = next-inj (PE.trans lA≡lM lM≡lB)
      UA≡M = U≡A-whnf ⊢UA≡M whnfM
      ⊢A≡B = stabilityEq Γ≡Δ (univ (sym (soundness~↓! (PE.subst₂ (λ X Y → _ ⊢ _ ~ _ ↓! X ^ Y) UA≡M (PE.sym lA≡lM) A~B))))
      _ , neA , _ = ne~↓! A
    in convConv↓Term (reflConEq (wfTerm ⊢B₂)) ⊢A≡B (ne neA) (PE.subst (λ X → _ ⊢ _ [conv↓] _ ∷ _ ^ ι X) (PE.sym lA≡lB) t)

