{-# OPTIONS --safe #-}

module Definition.Conversion.Decidable where

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

-- Algorithmic equality of variables infers propositional equality.
strongVarEq : ∀ {m n A Γ l} → Γ ⊢ var n ~ var m ↑! A ^ l → n PE.≡ m
strongVarEq (var-refl x x≡y) = x≡y

-- Helper function for decidability of applications.
dec~↑!-app : ∀ {k k₁ l l₁ F F₁ G G₁ rF B Γ Δ lF lG lΠ lK}
          → ⊢ Γ ≡ Δ
          → Γ ⊢ k ∷ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ [ ! , ι lΠ ]
          → Δ ⊢ k₁ ∷ Π F₁ ^ rF ° lF ▹ G₁ ° lG ° lΠ ^ [ ! , ι lΠ ]
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

abstract -- Agda will do some slow unfolding without abstract
  ~atℕ : ∀ {Γ t u}
    → Γ ⊢ t ~ t ↓! ℕ ^ ι ⁰
    → (∃ λ A → ∃ λ lA → Γ ⊢ t ~ u ↓! A ^ lA)
    → Γ ⊢ t ~ u ↓! ℕ ^ ι ⁰
  ~atℕ t (A , lA , t~u) =
    let whnfA , neT , neU = ne~↓! t~u
        ⊢A , ⊢t , ⊢u = syntacticEqTerm (soundness~↓! t~u)
        _ , ⊢t∷ℕ , _ = syntacticEqTerm (soundness~↓! t)
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


mutual
  -- Decidability of algorithmic equality of neutrals.
  dec~↑! : ∀ {k l R T Γ Δ lR lT}
        → ⊢ Γ ≡ Δ
        → Γ ⊢ k ~ k ↑! R ^ lR → Δ ⊢ l ~ l ↑! T ^ lT
        → Dec (∃ λ A → ∃ λ lA → Γ ⊢ k ~ l ↑! A ^ lA)

  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (var-refl {m} ⊢y m≡m) with n ≟ m
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (var-refl {m} ⊢y m≡m) | yes PE.refl =
    yes (_ , (_ , var-refl ⊢x n≡n))
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (var-refl {m} ⊢y m≡m) | no ¬p =
    no λ (_ , (_ , eq)) → ¬p (strongVarEq eq)

  dec~↑! Γ≡Δ (app-cong x~x t≡t) (app-cong y~y u≡u) with dec~↓! Γ≡Δ x~x y~y
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (app-cong y~y u≡u) | yes (A , lA , x~y) =
    let
      whnfA , neK , neK₀ = ne~↓! x~y
      ⊢A , ⊢k , ⊢k₀ = syntacticEqTerm (soundness~↓! x~y)
      _ , ⊢k₁ , _ = syntacticEqTerm (soundness~↓! x~x)
      _ , ⊢k₂ , _ = syntacticEqTerm (soundness~↓! y~y)
      l₁≡lA , ΠFG≡A = neTypeEq neK ⊢k₁ ⊢k
      l₂≡lA , ΠF′G′≡A = neTypeEq neK₀ (stabilityTerm (symConEq Γ≡Δ) ⊢k₂) ⊢k₀
      l₂≡l₁ = ιinj (PE.trans l₂≡lA (PE.sym l₁≡lA))
      ΠFG≡ΠF′G′ = trans ΠFG≡A (PE.subst (λ X → _ ⊢ _ ≡ _ ^ [ ! , ι X ]) l₂≡l₁ (sym ΠF′G′≡A))
      F≡F′ , rF≡rF′ , lF≡lF′ , lG≡lG′ , G≡G′ = injectivity ΠFG≡ΠF′G′
      ⊢k₁′ = PE.subst₄ (λ X Y Z T → _ ⊢ _ ∷ Π _ ^ X ° Y ▹ _ ° Z ° T ^ [ ! , ι T ]) rF≡rF′ lF≡lF′ lG≡lG′ (PE.sym l₂≡l₁) ⊢k₁
      F≡F″ = (PE.subst₂ (λ X Y → _ ⊢ _ ≡ _ ^ [ X , ι Y ]) rF≡rF′ lF≡lF′ F≡F′)
    in PE.subst (λ X → Dec (∃ λ A → ∃ λ lA → _ ⊢ _ ∘ _ ^ X ~ _ ∘ _ ^ _ ↑! _ ^ _)) l₂≡l₁
      (dec~↑!-app Γ≡Δ ⊢k₁′ ⊢k₂ x~y (decConv↑TermConv′ Γ≡Δ (PE.sym (PE.cong₂ (λ X Y → [ X , ι Y ]) rF≡rF′ lF≡lF′)) PE.refl F≡F″ t≡t u≡u))
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (app-cong y~y u≡u) | no ¬p =
    no (λ { (_ , (_ , app-cong x′ y′)) → ¬p (_ , (_ , x′)) })

  dec~↑! Γ≡Δ (natrec-cong {lF = l} F a0 aS k) (natrec-cong {lF = l₀} G b0 bS k₀)
    with dec-level l l₀
  dec~↑! Γ≡Δ (natrec-cong {lF = l} F a0 aS k) (natrec-cong {lF = .l} G b0 bS k₀) | yes PE.refl
    with decConv↑ (Γ≡Δ ∙ refl (univ (ℕⱼ (wfEqTerm (soundness~↓! k))))) F G
  dec~↑! Γ≡Δ (natrec-cong {lF = l} F a0 aS k) (natrec-cong {lF = .l} G b0 bS k₀) | yes PE.refl | yes p
    with decConv↑TermConv Γ≡Δ (substTypeEq (soundnessConv↑ p) (refl (zeroⱼ (wfEqTerm (soundness~↓! k))))) a0 b0
           | decConv↑TermConv Γ≡Δ (sucCong (soundnessConv↑ p)) aS bS
           | dec~↓! Γ≡Δ k k₀
  dec~↑! Γ≡Δ (natrec-cong {lF = l} F a0 aS k) (natrec-cong {lF = .l} G b0 bS k₀) | yes PE.refl | yes p | yes p0 | yes pS | yes pK =
    yes (_ , _ , natrec-cong p p0 pS (~atℕ k pK))
  dec~↑! Γ≡Δ (natrec-cong {lF = l} F a0 aS k) (natrec-cong {lF = .l} G b0 bS k₀) | yes PE.refl | yes p | yes p0 | yes pS | no ¬pK =
    no (λ { (_ , _ , natrec-cong x x₁ x₂ x₃) → ¬pK (_ , _ , x₃) })
  dec~↑! Γ≡Δ (natrec-cong {lF = l} F a0 aS k) (natrec-cong {lF = .l} G b0 bS k₀) | yes PE.refl | yes p | yes p0 | no ¬pS | _ =
    no (λ { (_ , _ , natrec-cong x x₁ x₂ x₃) → ¬pS x₂ })
  dec~↑! Γ≡Δ (natrec-cong {lF = l} F a0 aS k) (natrec-cong {lF = .l} G b0 bS k₀) | yes PE.refl | yes p | no ¬p0 | _ | _ =
    no (λ { (_ , _ , natrec-cong x x₁ x₂ x₃) → ¬p0 x₁ })
  dec~↑! Γ≡Δ (natrec-cong {lF = l} F a0 aS k) (natrec-cong {lF = .l} G b0 bS k₀) | yes PE.refl | no ¬p =
    no (λ { (_ , _ , natrec-cong x x₁ x₂ x₃) → ¬p x })
  dec~↑! Γ≡Δ (natrec-cong {lF = l} F a0 aS k) (natrec-cong {lF = l₀} G b0 bS k₀) | no ¬p =
    no (λ { (_ , .(ι l) , natrec-cong x x₁ x₂ x₃) → ¬p PE.refl })

  dec~↑! Γ≡Δ (Emptyrec-cong {ll = l} {lEmpty = ll} F k) (Emptyrec-cong {ll = l₀} {lEmpty = ll₀} G k₀)
    with dec-level l l₀ | dec-level ll ll₀
  dec~↑! Γ≡Δ (Emptyrec-cong {ll = l} {lEmpty = ll} F k) (Emptyrec-cong {ll = .l} {lEmpty = .ll} G k₀) | yes PE.refl | yes PE.refl
    with decConv↑ Γ≡Δ F G
  dec~↑! Γ≡Δ (Emptyrec-cong {ll = l} {lEmpty = ll} F k) (Emptyrec-cong {ll = .l} {lEmpty = .ll} G k₀) | yes PE.refl | yes PE.refl | yes p =
    let _ , ⊢k , _ = soundness~↑% k
        _ , ⊢k₀ , _ = soundness~↑% k₀
        ⊢Γ = wfTerm ⊢k
    in yes (_ , _ , Emptyrec-cong p (%~↑ ⊢k (stabilityTerm (symConEq Γ≡Δ) ⊢k₀)))
  dec~↑! Γ≡Δ (Emptyrec-cong {ll = l} {lEmpty = ll} F k) (Emptyrec-cong {ll = .l} {lEmpty = .ll} G k₀) | yes PE.refl | yes PE.refl | no ¬p =
    no (λ { (_ , .(ι l) , Emptyrec-cong x x₁) → ¬p x })
  dec~↑! Γ≡Δ (Emptyrec-cong {ll = l} {lEmpty = ll} F k) (Emptyrec-cong {ll = .l} {lEmpty = ll₀} G k₀) | yes PE.refl | no ¬p =
    no (λ { (_ , .(ι l) , Emptyrec-cong x x₁) → ¬p PE.refl })
  dec~↑! Γ≡Δ (Emptyrec-cong {ll = l} F k) (Emptyrec-cong {ll = l₀} G k₀) | no ¬p | _ =
    no (λ { (_ , .(ι l) , Emptyrec-cong x x₁) → ¬p PE.refl })

  dec~↑! Γ≡Δ (Id-cong A t u) (Id-cong B v w) with dec~↓! Γ≡Δ A B
  ... | no ¬p = no λ { (.(SProp _) , .(next _) , Id-cong x x₁ x₂) → ¬p (_ , _ , x) }
  ... | yes (M , lM , A~B) with decConv↑Term Γ≡Δ t (convert~ Γ≡Δ A B A~B v) | decConv↑Term Γ≡Δ u (convert~ Γ≡Δ A B A~B w)
  ... | yes tv | yes uw = yes (_ , _ , Id-cong (~atU A (M , lM , A~B)) tv uw)
  ... | yes tv | no ¬uw =
    no λ { (.(SProp _) , .(next _) , Id-cong x x₁ x₂) →
      let
        whnfU , neA , neB = ne~↓! x
        ⊢U , ⊢A , ⊢B = syntacticEqTerm (soundness~↓! x)
        _ , ⊢A₂ , _ = syntacticEqTerm (soundness~↓! A)
        nl≡nl , U≡U = neTypeEq neA ⊢A ⊢A₂
      in ¬uw (PE.subst (λ X → _ ⊢ _ [conv↑] _ ∷ _ ^ ι X) (next-inj nl≡nl) x₂) }
  ... | no ¬tv | _ =
    no λ { (.(SProp _) , .(next _) , Id-cong x x₁ x₂) →
      let
        whnfU , neA , neB = ne~↓! x
        ⊢U , ⊢A , ⊢B = syntacticEqTerm (soundness~↓! x)
        _ , ⊢A₂ , _ = syntacticEqTerm (soundness~↓! A)
        nl≡nl , U≡U = neTypeEq neA ⊢A ⊢A₂
      in ¬tv (PE.subst (λ X → _ ⊢ _ [conv↑] _ ∷ _ ^ ι X) (next-inj nl≡nl) x₁) }

  dec~↑! Γ≡Δ (Id-ℕ t u) (Id-ℕ v w) with dec~↓! Γ≡Δ t v | decConv↑Term Γ≡Δ u w
  ... | yes tv | yes uw = yes (_ , _ , Id-ℕ (~atℕ t tv) uw)
  ... | yes tv | no ¬uw = no λ { (_ , _ , Id-ℕ x x₁) → ¬uw x₁ }
  ... | no ¬tv | _ = no λ { (_ , _ , Id-ℕ x x₁) → ¬tv (_ , _ , x) }

  dec~↑! Γ≡Δ (Id-ℕ0 t) (Id-ℕ0 u) with dec~↓! Γ≡Δ t u
  ... | yes tu = yes (_ , _ , Id-ℕ0 (~atℕ t tu))
  ... | no ¬tu = no λ { (_ , _ , Id-ℕ0 x) → ¬tu (_ , _ , x) }

  dec~↑! Γ≡Δ (Id-ℕS t u) (Id-ℕS v w) with decConv↑Term Γ≡Δ t v | dec~↓! Γ≡Δ u w
  ... | yes tv | yes uw = yes (_ , _ , Id-ℕS tv (~atℕ u uw))
  ... | yes tv | no ¬uw = no λ { (_ , _ , Id-ℕS x x₁) → ¬uw (_ , _ , x₁) }
  ... | no ¬tv | _ = no λ { (_ , _ , Id-ℕS x x₁) → ¬tv x }

  dec~↑! Γ≡Δ (Id-U t u) (Id-U v w) with dec~↓! Γ≡Δ t v | decConv↑Term Γ≡Δ u w
  ... | yes tv | yes uw = yes (_ , _ , Id-U (~atU t tv) uw)
  ... | yes tv | no ¬uw = no λ { (_ , _ , Id-U x x₁) → ¬uw x₁ }
  ... | no ¬tv | _ = no λ { (_ , _ , Id-U x x₁) → ¬tv (_ , _ , x) }

  dec~↑! Γ≡Δ (Id-Uℕ t) (Id-Uℕ u) with dec~↓! Γ≡Δ t u
  ... | yes tu = yes (_ , _ , Id-Uℕ (~atU t tu))
  ... | no ¬tu = no λ { (_ , _ , Id-Uℕ x) → ¬tu (_ , _ , x) }

  dec~↑! Γ≡Δ (Id-UΠ {rA = r} t u) (Id-UΠ {rA = r′} v w) with dec-relevance r r′ | decConv↑Term Γ≡Δ t v | dec~↓! Γ≡Δ u w
  ... | yes PE.refl | yes tv | yes uw = yes (_ , _ , Id-UΠ tv (~atU u uw))
  ... | yes PE.refl | yes tv | no ¬uw = no λ { (_ , _ , Id-UΠ x x₁) → ¬uw (_ , _ , x₁) }
  ... | yes PE.refl | no ¬tv | _ = no λ { (_ , _ , Id-UΠ x x₁) → ¬tv x }
  ... | no ¬p | _ | _ = no λ { (_ , _ , Id-UΠ x x₁) → ¬p PE.refl }

  dec~↑! Γ≡Δ (cast-cong A B t eAB _) (cast-cong C D u eCD _)
    with dec~↓! Γ≡Δ A C | decConv↑Term Γ≡Δ B D
  ... | no ¬AC | _ = no λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ¬AC (_ , _ , x) }
  ... | yes AC | no ¬BD = no λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ¬BD x₁ }
  ... | yes (_ , _ , A~C) | yes BD with decConv↑Term Γ≡Δ t (convert~ Γ≡Δ A C A~C u)
  ... | yes p = yes (_ , _ , cast-cong (~atU A (_ , _ , A~C)) BD p eAB (stabilityTerm (symConEq Γ≡Δ) eCD))
  ... | no ¬p = no λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ¬p x₂ }

  dec~↑! Γ≡Δ (cast-ℕ A t eℕA _) (cast-ℕ B u eℕB _)
    with dec~↓! Γ≡Δ A B | decConv↑Term Γ≡Δ t u
  ... | yes AB | yes tu = yes (_ , _ , cast-ℕ (~atU A AB) tu eℕA (stabilityTerm (symConEq Γ≡Δ) eℕB))
  ... | yes AB | no ¬tu = no λ { (_ , _ , cast-ℕ x x₁ x₂ x₃) → ¬tu x₁ }
  ... | no ¬AB | _ = no λ { (_ , _ , cast-ℕ x x₁ x₂ x₃) → ¬AB (_ , _ , x) }

  dec~↑! Γ≡Δ (cast-ℕℕ t eℕℕ _) (cast-ℕℕ u eℕℕ′ _) with dec~↓! Γ≡Δ t u
  ... | yes tu = yes (_ , _ , cast-ℕℕ (~atℕ t tu) eℕℕ (stabilityTerm (symConEq Γ≡Δ) eℕℕ′))
  ... | no ¬tu = no λ { (_ , _ , cast-ℕℕ x x₁ x₂) → ¬tu (_ , _ , x) }

  dec~↑! Γ≡Δ (cast-Π {rA = r} Π A t eΠA _) (cast-Π {rA = r′} Π′ B u eΠB _)
    with dec-relevance r r′ | decConv↑Term Γ≡Δ Π Π′ | dec~↓! Γ≡Δ A B
  ... | no ¬p | _ | _ = no λ { (_ , _ , cast-Π x x₁ x₂ x₃ x₄) → ¬p PE.refl }
  ... | yes PE.refl | no ¬ΠΠ′ | _ = no λ { (_ , _ , cast-Π x x₁ x₂ x₃ x₄) → ¬ΠΠ′ x }
  ... | yes PE.refl | yes ΠΠ′ | no ¬AB = no λ { (_ , _ , cast-Π x x₁ x₂ x₃ x₄) → ¬AB (_ , _ , x₁) }
  ... | yes PE.refl | yes ΠΠ′ | yes AB with decConv↑TermConv Γ≡Δ (univ (soundnessConv↑Term ΠΠ′)) t u
  ... | yes p = yes (_ , _ , cast-Π ΠΠ′ (~atU A AB) p eΠA (stabilityTerm (symConEq Γ≡Δ) eΠB))
  ... | no ¬p = no λ { (_ , _ , cast-Π x x₁ x₂ x₃ x₄) → ¬p x₂ }

  dec~↑! Γ≡Δ (cast-Πℕ {rA = r} Π t eΠℕ _) (cast-Πℕ {rA = r′} Π′ u eΠℕ′ _)
    with dec-relevance r r′ | decConv↑Term Γ≡Δ Π Π′
  ... | no ¬p | _ = no λ { (_ , _ , cast-Πℕ x x₁ x₂ x₃) → ¬p PE.refl }
  ... | yes PE.refl | no ¬ΠΠ′ = no λ { (_ , _ , cast-Πℕ x x₁ x₂ x₃) → ¬ΠΠ′ x }
  ... | yes PE.refl | yes ΠΠ′ with decConv↑TermConv Γ≡Δ (univ (soundnessConv↑Term ΠΠ′)) t u
  ... | yes p = yes (_ , _ , cast-Πℕ ΠΠ′ p eΠℕ (stabilityTerm (symConEq Γ≡Δ) eΠℕ′))
  ... | no ¬p = no λ { (_ , _ , cast-Πℕ x x₁ x₂ x₃) → ¬p x₁ }

  dec~↑! Γ≡Δ (cast-ℕΠ {rA = r} Π t eΠℕ _) (cast-ℕΠ {rA = r′} Π′ u eΠℕ′ _)
    with dec-relevance r r′ | decConv↑Term Γ≡Δ Π Π′ | decConv↑Term Γ≡Δ t u
  ... | no ¬p | _ | _ = no λ { (_ , _ , cast-ℕΠ x x₁ x₂ x₃) → ¬p PE.refl }
  ... | yes PE.refl | no ¬ΠΠ′ | _ = no λ { (_ , _ , cast-ℕΠ x x₁ x₂ x₃) → ¬ΠΠ′ x }
  ... | yes PE.refl | yes ΠΠ′ | no ¬p = no λ { (_ , _ , cast-ℕΠ x x₁ x₂ x₃) → ¬p x₁ }
  ... | yes PE.refl | yes ΠΠ′ | yes p = yes (_ , _ , cast-ℕΠ ΠΠ′ p eΠℕ (stabilityTerm (symConEq Γ≡Δ) eΠℕ′))

  dec~↑! Γ≡Δ (cast-ΠΠ%! A B t eAB _) (cast-ΠΠ%! C D u eCD _)
    with decConv↑Term Γ≡Δ A C | decConv↑Term Γ≡Δ B D
  ... | no ¬AC | _ = no λ { (_ , _ , cast-ΠΠ%! x x₁ x₂ x₃ x₄) → ¬AC x }
  ... | yes AC | no ¬BD = no λ { (_ , _ , cast-ΠΠ%! x x₁ x₂ x₃ x₄) → ¬BD x₁ }
  ... | yes AC | yes BD with decConv↑TermConv Γ≡Δ (univ (soundnessConv↑Term AC)) t u
  ... | yes p = yes (_ , _ , cast-ΠΠ%! AC BD p eAB (stabilityTerm (symConEq Γ≡Δ) eCD))
  ... | no ¬p = no λ { (_ , _ , cast-ΠΠ%! x x₁ x₂ x₃ x₄) → ¬p x₂ }

  dec~↑! Γ≡Δ (cast-ΠΠ!% A B t eAB _) (cast-ΠΠ!% C D u eCD _)
    with decConv↑Term Γ≡Δ A C | decConv↑Term Γ≡Δ B D
  ... | no ¬AC | _ = no λ { (_ , _ , cast-ΠΠ!% x x₁ x₂ x₃ x₄) → ¬AC x }
  ... | yes AC | no ¬BD = no λ { (_ , _ , cast-ΠΠ!% x x₁ x₂ x₃ x₄) → ¬BD x₁ }
  ... | yes AC | yes BD with decConv↑TermConv Γ≡Δ (univ (soundnessConv↑Term AC)) t u
  ... | yes p = yes (_ , _ , cast-ΠΠ!% AC BD p eAB (stabilityTerm (symConEq Γ≡Δ) eCD))
  ... | no ¬p = no λ { (_ , _ , cast-ΠΠ!% x x₁ x₂ x₃ x₄) → ¬p x₂ }

  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) [l] = no (λ { (_ , _ , var-refl x x₁) → {!!} })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) [l] = {!!}
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) [l] = {!!}
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) [l] = {!!}
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) [l] = {!!}
  dec~↑! Γ≡Δ (Id-ℕ x x₁) [l] = {!!}
  dec~↑! Γ≡Δ (Id-ℕ0 x) [l] = {!!}
  dec~↑! Γ≡Δ (Id-ℕS x x₁) [l] = {!!}
  dec~↑! Γ≡Δ (Id-U x x₁) [l] = {!!}
  dec~↑! Γ≡Δ (Id-Uℕ x) [l] = {!!}
  dec~↑! Γ≡Δ (Id-UΠ x x₁) [l] = {!!}
  dec~↑! Γ≡Δ (cast-cong x x₁ x₂ x₃ x₄) [l] = {!!}
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) [l] = {!!}
  dec~↑! Γ≡Δ (cast-ℕℕ x x₁ x₂) [l] = {!!}
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) [l] = {!!}
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) [l] = {!!}
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) [l] = {!!}
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) [l] = {!!}
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) [l] = {!!}

  -- Decidability of algorithmic equality of neutrals with types in WHNF.
  dec~↓! : ∀ {k l R T Γ Δ lR lT}
        → ⊢ Γ ≡ Δ
        → Γ ⊢ k ~ k ↓! R ^ lR → Δ ⊢ l ~ l ↓! T ^ lT
        → Dec (∃ λ A → ∃ λ lA → Γ ⊢ k ~ l ↓! A ^ lA)
  dec~↓! Γ≡Δ ([~] A D whnfB k~l) ([~] A₁ D₁ whnfB₁ k~l₁)
        with dec~↑! Γ≡Δ k~l k~l₁
  dec~↓! Γ≡Δ ([~] A D whnfB k~l) ([~] A₁ D₁ whnfB₁ k~l₁)
        | yes (B , lB , k~l₂) =
    let ⊢B , _ , _ = syntacticEqTerm (soundness~↑! k~l₂)
        C , whnfC , D′ = whNorm ⊢B
    in  yes (C , _ , [~] B (red D′) whnfC k~l₂)
  dec~↓! Γ≡Δ ([~] A D whnfB k~l) ([~] A₁ D₁ whnfB₁ k~l₁)
        | no ¬p =
    no (λ { (A₂ , _ , [~] A₃ D₂ whnfB₂ k~l₂) → ¬p (A₃ , _ , k~l₂) })

  -- Decidability of algorithmic equality of types.
  decConv↑ : ∀ {A B r Γ Δ}
           → ⊢ Γ ≡ Δ
           → Γ ⊢ A [conv↑] A ^ r → Δ ⊢ B [conv↑] B ^ r
           → Dec (Γ ⊢ A [conv↑] B ^ r)
  decConv↑ Γ≡Δ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′)
               ([↑] A″ B″ D₁ D″ whnfA″ whnfB″ A′<>B″)
           rewrite whrDet* (D , whnfA′) (D′ , whnfB′)
                 | whrDet* (D₁ , whnfA″) (D″ , whnfB″)
           with decConv↓ Γ≡Δ A′<>B′ A′<>B″
  decConv↑ Γ≡Δ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′)
               ([↑] A″ B″ D₁ D″ whnfA″ whnfB″ A′<>B″) | yes p =
    yes ([↑] B′ B″ D′ (stabilityRed* (symConEq Γ≡Δ) D″) whnfB′ whnfB″ p)
  decConv↑ {r = r} Γ≡Δ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′)
               ([↑] A″ B″ D₁ D″ whnfA″ whnfB″ A′<>B″) | no ¬p =
    no (λ { ([↑] A‴ B‴ D₂ D‴ whnfA‴ whnfB‴ A′<>B‴) →
        let A‴≡B′  = whrDet* (D₂ , whnfA‴) (D′ , whnfB′)
            B‴≡B″ = whrDet* (D‴ , whnfB‴)
                                (stabilityRed* (symConEq Γ≡Δ) D″ , whnfB″)
        in  ¬p (PE.subst₂ (λ x y → _ ⊢ x [conv↓] y ^ r) A‴≡B′ B‴≡B″ A′<>B‴) })

  -- Decidability of algorithmic equality of types in WHNF.
  decConv↓ : ∀ {A B r Γ Δ}
           → ⊢ Γ ≡ Δ
           → Γ ⊢ A [conv↓] A ^ r → Δ ⊢ B [conv↓] B ^ r
           → Dec (Γ ⊢ A [conv↓] B ^ r)
  decConv↓ Γ≡Δ (U-refl {r = r} x x₁) (U-refl {r = r′} x₂ x₃) with dec-relevance r r′
  ... | yes p = yes (U-refl p x₁)
  ... | no ¬p = no λ p → ¬p (proj₁ (Uinjectivity (soundnessConv↓ p)))
  decConv↓ Γ≡Δ (univ x) (univ x₁) with decConv↓Term Γ≡Δ x x₁
  ... | yes p = yes (univ p)
  ... | no ¬p = no (λ { (univ x) → ¬p x })

  -- Decidability of algorithmic equality of terms.
  decConv↑Term : ∀ {t u A Γ Δ l}
               → ⊢ Γ ≡ Δ
               → Γ ⊢ t [conv↑] t ∷ A ^ l → Δ ⊢ u [conv↑] u ∷ A ^ l
               → Dec (Γ ⊢ t [conv↑] u ∷ A ^ l)
  decConv↑Term Γ≡Δ ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
                   ([↑]ₜ B₁ t″ u″ D₁ d₁ d″ whnfB₁ whnft″ whnfu″ t<>u₁)
               rewrite whrDet* (D , whnfB) (stabilityRed* (symConEq Γ≡Δ) D₁ , whnfB₁)
                     | whrDet*Term  (d , whnft′) (d′ , whnfu′)
                     | whrDet*Term  (d₁ , whnft″) (d″ , whnfu″)
               with decConv↓Term Γ≡Δ t<>u t<>u₁
  decConv↑Term Γ≡Δ ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
                   ([↑]ₜ B₁ t″ u″ D₁ d₁ d″ whnfB₁ whnft″ whnfu″ t<>u₁)
               | yes p =
    let Δ≡Γ = symConEq Γ≡Δ
    in  yes ([↑]ₜ B₁ u′ u″ (stabilityRed* Δ≡Γ D₁)
                  d′ (stabilityRed*Term Δ≡Γ d″) whnfB₁ whnfu′ whnfu″ p)
  decConv↑Term Γ≡Δ ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
                   ([↑]ₜ B₁ t″ u″ D₁ d₁ d″ whnfB₁ whnft″ whnfu″ t<>u₁)
               | no ¬p =
    no (λ { ([↑]ₜ B₂ t‴ u‴ D₂ d₂ d‴ whnfB₂ whnft‴ whnfu‴ t<>u₂) →
        let B₂≡B₁ = whrDet* (D₂ , whnfB₂)
                             (stabilityRed* (symConEq Γ≡Δ) D₁ , whnfB₁)
            t‴≡u′ = whrDet*Term (d₂ , whnft‴)
                              (PE.subst (λ x → _ ⊢ _ ⇒* _ ∷ x ^ _) (PE.sym B₂≡B₁) d′
                              , whnfu′)
            u‴≡u″ = whrDet*Term (d‴ , whnfu‴)
                               (PE.subst (λ x → _ ⊢ _ ⇒* _ ∷ x ^ _)
                                         (PE.sym B₂≡B₁)
                                         (stabilityRed*Term (symConEq Γ≡Δ) d″)
                               , whnfu″)
        in  ¬p (PE.subst₃ (λ x y z → _ ⊢ x [conv↓] y ∷ z ^ _)
                          t‴≡u′ u‴≡u″ B₂≡B₁ t<>u₂) })

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

  -- Decidability of algorithmic equality of terms in WHNF.
  decConv↓Term : ∀ {t u A Γ Δ l}
               → ⊢ Γ ≡ Δ
               → Γ ⊢ t [conv↓] t ∷ A ^ l → Δ ⊢ u [conv↓] u ∷ A ^ l
               → Dec (Γ ⊢ t [conv↓] u ∷ A ^ l)
--  decConv↓Term = {!!}
  decConv↓Term Γ≡Δ (U-refl {r = r} _ x) (U-refl {r = r′} _ x₁)
    with dec-relevance r r′
  ... | yes p = yes (U-refl p x)
  ... | no ¬p = no λ p → ¬p (proj₁ (Uinjectivity (univ (soundnessConv↓Term p))))

  decConv↓Term Γ≡Δ (ne K) (ne K₁) --TERMINATION ISSUES: should be solved by layering levels
    with dec~↓! Γ≡Δ K K₁
  ... | yes (A , lA , K~K₁) = yes (ne (~atU K (A , lA , K~K₁)))
  ... | no ¬p = no (λ { x → ¬p (Univ _ _ , _ , decConv↓Term-U-ins x K) })

  decConv↓Term Γ≡Δ (ℕ-refl x) (ℕ-refl x₁) = yes (ℕ-refl x)

  decConv↓Term Γ≡Δ (Empty-refl {l = l} x x₁) (Empty-refl {l = l′} x₂ x₃)
    with dec-level l l′
  ... | yes PE.refl = yes (Empty-refl x x₁)
  ... | no ¬p = no (λ { (Empty-refl x x₁) → ¬p PE.refl })

  decConv↓Term Γ≡Δ (Π-cong {rF = rF} {lF = lF} {lG = lG} {lΠ = l} l≡ rF≡rF lF≡lF lG≡lG lF< lG< ⊢F F G)
    (Π-cong {rF = rH} {lF = lH} {lG = lE} {lΠ = l′} l′≡ _ _ _ _ _ ⊢H H E)
    with dec-relevance rF rH | dec-level lF lH | dec-level lG lE | dec-level l l′
  ... | yes PE.refl | yes PE.refl | yes PE.refl | no ¬p = no λ { (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) → ¬p PE.refl }
  ... | yes PE.refl | yes PE.refl | no ¬p | _ = no λ { (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) → ¬p x₃ }
  ... | yes PE.refl | no ¬p | _ | _ = no λ { (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) → ¬p x₂ }
  ... | no ¬p | _ | _ | _ = no λ { (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) → ¬p x₁ }
  ... | yes PE.refl | yes PE.refl | yes PE.refl | yes PE.refl
    with decConv↑Term Γ≡Δ F H
  ... | no ¬p = no λ { (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) → ¬p x₇ }
  ... | yes pFH
    with decConv↑Term (Γ≡Δ ∙ univ (soundnessConv↑Term pFH)) G E
  ... | no ¬p = no λ { (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) → ¬p x₈ }
  ... | yes pGE = yes (Π-cong l≡ rF≡rF lF≡lF lG≡lG lF< lG< ⊢F pFH pGE)

  decConv↓Term Γ≡Δ (∃-cong {l = l} l≡ ⊢F F G) (∃-cong {l = l′} _ ⊢H H E)
    with dec-level l l′
  ... | no ¬p = no λ { (∃-cong x x₁ x₂ x₃) → ¬p PE.refl }
  ... | yes PE.refl
    with decConv↑Term Γ≡Δ F H
  ... | no ¬p = no λ { (∃-cong x x₁ x₂ x₃) → ¬p x₂ }
  ... | yes pFH
    with decConv↑Term (Γ≡Δ ∙ univ (soundnessConv↑Term pFH)) G E
  ... | no ¬p = no λ { (∃-cong x x₁ x₂ x₃) → ¬p x₃ }
  ... | yes pGE = yes (∃-cong l≡ ⊢F pFH pGE)

  decConv↓Term Γ≡Δ (ℕ-ins K) (ℕ-ins K₁)
    with dec~↓! Γ≡Δ K K₁
  ... | yes p = yes (ℕ-ins (~atℕ K p))
  ... | no ¬p = no λ x → ¬p (ℕ , _ , decConv↓Term-ℕ-ins x K)

  decConv↓Term Γ≡Δ (ne-ins ⊢k _ neA k) (ne-ins ⊢k₁ _ _ k₁)
    with dec~↓! Γ≡Δ k k₁
  ... | yes (B , lB , k~k₁) =
    let whnfB , neK , neK₁ = ne~↓! k~k₁
        _ , ⊢k∷B , _ = syntacticEqTerm (soundness~↓! k~k₁)
        l≡l , ⊢A≡B = neTypeEq neK ⊢k∷B ⊢k
    in yes (ne-ins ⊢k (stabilityTerm (symConEq Γ≡Δ) ⊢k₁) neA (PE.subst (λ X → _ ⊢ _ ~ _ ↓! _ ^ X) l≡l k~k₁))
  ... | no ¬p = no λ x → ¬p (decConv↓Term-ne-ins neA x)

  decConv↓Term Γ≡Δ (zero-refl x) (zero-refl x₁) = yes (zero-refl x)

  decConv↓Term Γ≡Δ (suc-cong m) (suc-cong n)
    with decConv↑Term Γ≡Δ m n
  ... | yes p = yes (suc-cong p)
  ... | no ¬p = no λ { (suc-cong x) → ¬p x }

  decConv↓Term Γ≡Δ (η-eq lF< lG< ⊢F ⊢f _ funf _ f) (η-eq _ _ _ ⊢g _ fung _ g)
    with decConv↑Term (Γ≡Δ ∙ refl ⊢F) f g
  ... | yes p = yes (η-eq lF< lG< ⊢F ⊢f (stabilityTerm (symConEq Γ≡Δ) ⊢g) funf fung p)
  ... | no ¬p = no (λ { (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) → ¬p x₇ })

  decConv↓Term Γ≡Δ (U-refl x x₁) (ne x₂) =
    no (λ x₃ → decConv↓Term-U (symConv↓Term Γ≡Δ x₃) x₂ (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (U-refl x x₁) (Π-cong x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀) = no λ { (ne ()) }
  decConv↓Term Γ≡Δ (ne x) (U-refl x₁ x₂) =
    no (λ x₃ → decConv↓Term-U x₃ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (ne x) (ℕ-refl x₁) =
    no (λ x₃ → decConv↓Term-U x₃ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (ne x) (Empty-refl x₁ x₂) =
    no (λ x₃ → decConv↓Term-U x₃ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (ne x) (Π-cong x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉) =
    no (λ x₃ → decConv↓Term-U x₃ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (ne x) (∃-cong x₁ x₂ x₃ x₄) =
    no (λ x₃ → decConv↓Term-U x₃ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (ℕ-refl x) (ne x₁) =
    no (λ x₃ → decConv↓Term-U (symConv↓Term Γ≡Δ x₃) x₁ (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (ℕ-refl x) (Π-cong x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉) = no λ { (ne ()) ; (ne-ins x x₁ () x₃) }
  decConv↓Term Γ≡Δ (Empty-refl x x₁) (ne x₂) =
    no (λ x₃ → decConv↓Term-U (symConv↓Term Γ≡Δ x₃) x₂ (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (Empty-refl x x₁) (Π-cong x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀) = no λ { (ne ()) ; (ne-ins x x₁ () x₃) }
  decConv↓Term Γ≡Δ (Empty-refl x x₁) (∃-cong x₂ x₃ x₄ x₅) = no λ { (ne ()) ; (ne-ins x x₁ () x₃) }
  decConv↓Term Γ≡Δ (Π-cong l x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (U-refl x₈ x₉) = no λ { (ne ()) }
  decConv↓Term Γ≡Δ (Π-cong l x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (ne x₈) =
    no (λ x₉ → decConv↓Term-U (symConv↓Term Γ≡Δ x₉) x₈ (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (Π-cong l x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (ℕ-refl x₈) = no λ { (ne ()) ; (ne-ins x x₁ () x₃) }
  decConv↓Term Γ≡Δ (Π-cong l x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (Empty-refl x₈ x₉) = no λ { (ne ()) ; (ne-ins x x₁ () x₃) }
  decConv↓Term Γ≡Δ (Π-cong l x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (∃-cong x₈ x₉ x₁₀ x₁₁) = no λ { (ne ()) ; (ne-ins x x₁ () x₃) }
  decConv↓Term Γ≡Δ (∃-cong l x x₁ x₂) (ne x₃) =
    no (λ x₉ → decConv↓Term-U (symConv↓Term Γ≡Δ x₉) x₃ (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (∃-cong l x x₁ x₂) (Empty-refl x₃ x₄) = no λ { (ne ()) ; (ne-ins x x₁ () x₃) }
  decConv↓Term Γ≡Δ (∃-cong l x x₁ x₂) (Π-cong x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁) = no λ { (ne ()) ; (ne-ins x x₁ () x₃) }
  decConv↓Term Γ≡Δ (ℕ-ins x) (zero-refl x₁) =
    no (λ x₂ → decConv↓Term-ℕ x₂ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (ℕ-ins x) (suc-cong x₁) =
    no (λ x₂ → decConv↓Term-ℕ x₂ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (ne x₄)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (ℕ-refl x₄)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (Empty-refl x₄ x₅)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (Π-cong x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (∃-cong x₄ x₅ x₆ x₇)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (ℕ-ins x₄)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (zero-refl x₄)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (suc-cong x₄)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (η-eq x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁)
  decConv↓Term Γ≡Δ (zero-refl x) (ℕ-ins x₁) =
    no (λ x₂ → decConv↓Term-ℕ (symConv↓Term Γ≡Δ x₂) x₁ (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (zero-refl x) (suc-cong x₁) = no λ { (ℕ-ins ()) ; (ne-ins x x₁ () x₃) }
  decConv↓Term Γ≡Δ (suc-cong x) (ℕ-ins x₁) =
    no (λ x₂ → decConv↓Term-ℕ (symConv↓Term Γ≡Δ x₂) x₁ (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (suc-cong x) (zero-refl x₁) = no λ { (ℕ-ins ()) ; (ne-ins x x₁ () x₃) }
  decConv↓Term Γ≡Δ (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (ne-ins x₈ x₉ () x₁₁)

  -- Decidability of algorithmic equality of terms of equal types.
  decConv↑TermConv : ∀ {t u A B r Γ Δ}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B ^ r
                → Γ ⊢ t [genconv↑] t ∷ A ^ r
                → Δ ⊢ u [genconv↑] u ∷ B ^ r
                → Dec (Γ ⊢ t [genconv↑] u ∷ A ^ r)
  decConv↑TermConv {r = [ ! , l ]} Γ≡Δ A≡B t u =
    decConv↑Term Γ≡Δ t (convConvTerm u (stabilityEq Γ≡Δ (sym A≡B)))
  decConv↑TermConv {r = [ % , l ]} Γ≡Δ A≡B (%~↑ ⊢t ⊢t') (%~↑ ⊢u ⊢u') =
    yes (%~↑ ⊢t (conv (stabilityTerm (symConEq Γ≡Δ) ⊢u) (sym A≡B)))

  decConv↑TermConv′ : ∀ {t u A B r r₁ r₂ Γ Δ}
                → ⊢ Γ ≡ Δ
                → r PE.≡ r₁
                → r PE.≡ r₂
                → Γ ⊢ A ≡ B ^ r
                → Γ ⊢ t [genconv↑] t ∷ A ^ r₁
                → Δ ⊢ u [genconv↑] u ∷ B ^ r₂
                → Dec (Γ ⊢ t [genconv↑] u ∷ A ^ r)
  decConv↑TermConv′ Γ≡Δ PE.refl PE.refl A≡B t u = decConv↑TermConv Γ≡Δ A≡B t u
