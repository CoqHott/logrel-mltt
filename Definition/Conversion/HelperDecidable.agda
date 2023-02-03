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

conv↑-inversion : ∀ {Γ l A t u} → Whnf A → Whnf t → Whnf u → Γ ⊢ t [conv↑] u ∷ A ^ l → Γ ⊢ t [conv↓] u ∷ A ^ l
conv↑-inversion whnfA whnft whnfu ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) = 
  let et = whnfRed*Term d whnft
      eu = whnfRed*Term d′ whnfu
      eA = whnfRed* D whnfA
  in PE.subst₃ (λ A X Y → _ ⊢ X [conv↓] Y ∷ A ^ _) (PE.sym eA) (PE.sym et) (PE.sym eu) t<>u

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

abstract

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

  castℕInv : ∀ {l e t} → Neutral (cast l ℕ ℕ e t) → Neutral t 
  castℕInv (castℕℕₙ net) = net

  cast-t-≡ : ∀ {Γ A B B' t t' e X lX} 
                → Γ ⊢ t' ∷ B' ^ [ ! , ι ⁰ ]
                → Γ ⊢ cast ⁰ A B e t ~ t' ↑! X ^ lX
                → Γ ⊢ B ≡ B' ^ [ ! , ι ⁰ ]
  cast-t-≡ ⊢t X =
    let _ , ⊢cast , ⊢t' = syntacticEqTerm (soundness~↑! X)
        _ , _ , _ , _ , _ , R≡R , eqR , _ = inversion-cast ⊢cast
        eqR , el = typeinfo-PE-injectivity eqR
        _ , eq = type-uniq ⊢t ⊢t'
        R≡R' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqR) R≡R
    in T.trans (T.sym R≡R') (T.sym eq) 
