{-# OPTIONS --without-K --safe #-}

module Definition.Conversion.Decidable where

open import Definition.Untyped
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

relevance-discr : ! PE.≡ % → ⊥
relevance-discr ()

-- Algorithmic equality of variables infers propositional equality.
strongVarEq : ∀ {m n A Γ} → Γ ⊢ var n ~ var m ↑! A → n PE.≡ m
strongVarEq (var-refl x x≡y) = x≡y

-- Helper function for decidability of applications.
dec~↑!-app : ∀ {k k₁ l l₁ F F₁ G G₁ rF B Γ Δ}
          → ⊢ Γ ≡ Δ
          → Γ ⊢ k ∷ Π F ^ rF ▹ G ^ !
          → Δ ⊢ k₁ ∷ Π F₁ ^ rF ▹ G₁ ^ !
          → Γ ⊢ k ~ k₁ ↓! B
          → Dec (Γ ⊢ l [genconv↑] l₁ ∷ F ^ rF)
          → Dec (∃ λ A → Γ ⊢ k ∘ l ~ k₁ ∘ l₁ ↑! A)
dec~↑!-app {rF = !} Γ≡Δ k k₁ k~k₁ (yes p) =
  let whnfA , neK , neL = ne~↓! k~k₁
      ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓! k~k₁)
      ΠFG₁≡A = neTypeEq neK k ⊢k
      H , E , A≡ΠHE = Π≡A ΠFG₁≡A whnfA
      F≡H , rF≡rH , G₁≡E = injectivity (PE.subst (λ x → _ ⊢ _ ≡ x ^ _) A≡ΠHE ΠFG₁≡A)
  in  yes (E [ _ ] , app-cong (PE.subst (λ x → _ ⊢ _ ~ _ ↓! x) A≡ΠHE k~k₁) (convConvTerm p F≡H))
dec~↑!-app {rF = %} Γ≡Δ k k₁ k~k₁ (yes p) =
  let whnfA , neK , neL = ne~↓! k~k₁
      ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓! k~k₁)
      ΠFG₁≡A = neTypeEq neK k ⊢k
      H , E , A≡ΠHE = Π≡A ΠFG₁≡A whnfA
      F≡H , rF≡rH , G₁≡E = injectivity (PE.subst (λ x → _ ⊢ _ ≡ x ^ _) A≡ΠHE ΠFG₁≡A)
  in  yes (E [ _ ] , app-cong (PE.subst (λ x → _ ⊢ _ ~ _ ↓! x) A≡ΠHE k~k₁) (conv~↑% p F≡H))
dec~↑!-app {rF = !} Γ≡Δ k₂ k₃ k~k₁ (no ¬p) =
  no (λ { (_ , app-cong {rF = !} x x₁) →
      let whnfA , neK , neL = ne~↓! x
          ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓! x)
          ΠFG≡ΠF₂G₂ = neTypeEq neK k₂ ⊢k
          F≡F₂ , rF≡rF₂ , G≡G₂ = injectivity ΠFG≡ΠF₂G₂
      in  ¬p (convConvTerm x₁ (sym F≡F₂)) ;
      (_ , app-cong {rF = %} x x₁) →
      let whnfA , neK , neL = ne~↓! x
          ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓! x)
          ΠFG≡ΠF₂G₂ = neTypeEq neK k₂ ⊢k
          F≡F₂ , rF≡rF₂ , G≡G₂ = injectivity ΠFG≡ΠF₂G₂
      in  ⊥-elim (relevance-discr rF≡rF₂)})
dec~↑!-app {rF = %} Γ≡Δ k₂ k₃ k~k₁ (no ¬p) =
  no (λ { (_ , app-cong {rF = %} x x₁) →
      let whnfA , neK , neL = ne~↓! x
          ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓! x)
          ΠFG≡ΠF₂G₂ = neTypeEq neK k₂ ⊢k
          F≡F₂ , rF≡rF₂ , G≡G₂ = injectivity ΠFG≡ΠF₂G₂
      in  ¬p (conv~↑% x₁ (sym F≡F₂)) ;
      (_ , app-cong {rF = !} x x₁) →
      let whnfA , neK , neL = ne~↓! x
          ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓! x)
          ΠFG≡ΠF₂G₂ = neTypeEq neK k₂ ⊢k
          F≡F₂ , rF≡rF₂ , G≡G₂ = injectivity ΠFG≡ΠF₂G₂
      in  ⊥-elim (relevance-discr (PE.sym rF≡rF₂))})

mutual
  -- Decidability of algorithmic equality of neutrals.
  dec~↑! : ∀ {k l R T Γ Δ}
        → ⊢ Γ ≡ Δ
        → Γ ⊢ k ~ k ↑! R → Δ ⊢ l ~ l ↑! T
        → Dec (∃ λ A → Γ ⊢ k ~ l ↑! A)
  dec~↑! Γ≡Δ (var-refl {n} x₂ x≡y) (var-refl {m} x₃ x≡y₁) with n ≟ m
  dec~↑! Γ≡Δ (var-refl {n} x₂ x≡y) (var-refl .{n} x₃ x≡y₁) | yes PE.refl = yes (_ , var-refl x₂ x≡y₁)
  dec~↑! Γ≡Δ (var-refl x₂ x≡y) (var-refl x₃ x≡y₁) | no ¬p = no (λ { (A , k~l) → ¬p (strongVarEq k~l) })
  dec~↑! Γ≡Δ (var-refl x₁ x≡y) (app-cong x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl x₁ x≡y) (natrec-cong x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl x₁ x≡y) (Emptyrec-cong x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x₁ x₂) (var-refl x₃ x≡y) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x x₁) (app-cong x₂ x₃)
        with dec~↓! Γ≡Δ x x₂
  dec~↑! Γ≡Δ (app-cong {rF = !} x x₁) (app-cong {rF = !} x₂ x₃) | yes (A , k~l) =
    let whnfA , neK , neL = ne~↓! k~l
        ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓! k~l)
        _ , ⊢l₁ , _ = syntacticEqTerm (soundness~↓! x)
        _ , ⊢l₂ , _ = syntacticEqTerm (soundness~↓! x₂)
        ΠFG≡A = neTypeEq neK ⊢l₁ ⊢k
        ΠF′G′≡A = neTypeEq neL (stabilityTerm (symConEq Γ≡Δ) ⊢l₂) ⊢l
        F≡F′ , rF≡rF′ , G≡G′ = injectivity (trans ΠFG≡A (sym ΠF′G′≡A))
     in dec~↑!-app Γ≡Δ ⊢l₁ ⊢l₂ k~l (decConv↑TermConv Γ≡Δ F≡F′ x₁ x₃)
  dec~↑! Γ≡Δ (app-cong {rF = %} x x₁) (app-cong {rF = %} x₂ x₃) | yes (A , k~l) =
    let whnfA , neK , neL = ne~↓! k~l
        ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓! k~l)
        _ , ⊢l₁ , _ = syntacticEqTerm (soundness~↓! x)
        _ , ⊢l₂ , _ = syntacticEqTerm (soundness~↓! x₂)
        ΠFG≡A = neTypeEq neK ⊢l₁ ⊢k
        ΠF′G′≡A = neTypeEq neL (stabilityTerm (symConEq Γ≡Δ) ⊢l₂) ⊢l
        F≡F′ , rF≡rF′ , G≡G′ = injectivity (trans ΠFG≡A (sym ΠF′G′≡A))
     in dec~↑!-app Γ≡Δ ⊢l₁ ⊢l₂ k~l (decConv↑TermConv Γ≡Δ F≡F′ x₁ x₃)
  dec~↑! Γ≡Δ (app-cong {rF = !} x x₁) (app-cong {rF = %} x₂ x₃) | yes (A , k~l) =
    let whnfA , neK , neL = ne~↓! k~l
        ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓! k~l)
        _ , ⊢l₁ , _ = syntacticEqTerm (soundness~↓! x)
        _ , ⊢l₂ , _ = syntacticEqTerm (soundness~↓! x₂)
        ΠFG≡A = neTypeEq neK ⊢l₁ ⊢k
        ΠF′G′≡A = neTypeEq neL (stabilityTerm (symConEq Γ≡Δ) ⊢l₂) ⊢l
        F≡F′ , rF≡rF′ , G≡G′ = injectivity (trans ΠFG≡A (sym ΠF′G′≡A))
     in ⊥-elim (relevance-discr rF≡rF′)
  dec~↑! Γ≡Δ (app-cong {rF = %} x x₁) (app-cong {rF = !} x₂ x₃) | yes (A , k~l) =
    let whnfA , neK , neL = ne~↓! k~l
        ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓! k~l)
        _ , ⊢l₁ , _ = syntacticEqTerm (soundness~↓! x)
        _ , ⊢l₂ , _ = syntacticEqTerm (soundness~↓! x₂)
        ΠFG≡A = neTypeEq neK ⊢l₁ ⊢k
        ΠF′G′≡A = neTypeEq neL (stabilityTerm (symConEq Γ≡Δ) ⊢l₂) ⊢l
        F≡F′ , rF≡rF′ , G≡G′ = injectivity (trans ΠFG≡A (sym ΠF′G′≡A))
     in ⊥-elim (relevance-discr (PE.sym rF≡rF′))
  dec~↑! Γ≡Δ (app-cong x x₁) (app-cong x₂ x₃) | no ¬p =
    no (λ { (_ , app-cong x₄ x₅) → ¬p (_ , x₄) })
  dec~↑! Γ≡Δ (app-cong x x₁) (natrec-cong x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x x₁) (Emptyrec-cong x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x₁ x₂ x₃ x₄) (var-refl x₅ x≡y) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (app-cong x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x₁ x₂) (var-refl x₅ x≡y) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (app-cong x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (natrec-cong _ _ _ _) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong _ _ _ _) (Emptyrec-cong x x₁) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇)
        with decConv↑ (Γ≡Δ ∙ refl (ℕⱼ (wfEqTerm (soundness~↓! x₃)))) x x₄
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇) | yes p
        with decConv↑TermConv Γ≡Δ
               (substTypeEq (soundnessConv↑ p)
                            (refl (zeroⱼ (wfEqTerm (soundness~↓! x₃)))))
               x₁ x₅
           | decConv↑TermConv Γ≡Δ (sucCong (soundnessConv↑ p)) x₂ x₆
           | dec~↓! Γ≡Δ x₃ x₇
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇)
        | yes p | yes p₁ | yes p₂ | yes (A , k~l) =
    let whnfA , neK , neL = ne~↓! k~l
        ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓! k~l)
        _ , ⊢l∷ℕ , _ = syntacticEqTerm (soundness~↓! x₃)
        ⊢ℕ≡A = neTypeEq neK ⊢l∷ℕ ⊢k
        A≡ℕ = ℕ≡A ⊢ℕ≡A whnfA
        k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x) A≡ℕ k~l
    in  yes (_ , natrec-cong p p₁ p₂ k~l′)
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇)
        | yes p | yes p₁ | yes p₂ | no ¬p =
    no (λ { (_ , natrec-cong x₈ x₉ x₁₀ x₁₁) → ¬p (_ , x₁₁) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇)
        | yes p | yes p₁ | no ¬p | r =
    no (λ { (_ , natrec-cong x₈ x₉ x₁₀ x₁₁) → ¬p x₁₀ })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇)
        | yes p | no ¬p | w | r =
    no (λ { (_ , natrec-cong x₈ x₉ x₁₀ x₁₁) → ¬p x₉ })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇) | no ¬p =
    no (λ { (_ , natrec-cong x₈ x₉ x₁₀ x₁₁) → ¬p x₈ })

  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (Emptyrec-cong x₄ x₅)
        with decConv↑ Γ≡Δ x x₄
  dec~↑! Γ≡Δ (Emptyrec-cong x k~k) (Emptyrec-cong x₄ l~l) | yes p =
    let _ , ⊢k , _ = syntacticEqTerm (soundness~↑% k~k)
        _ , ⊢l , _ = syntacticEqTerm (soundness~↑% l~l)
        ⊢Γ = wfTerm ⊢k
    in  yes (_ , Emptyrec-cong p (%~↑ ⊢k (stabilityTerm (symConEq Γ≡Δ) ⊢l)))
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (Emptyrec-cong x₄ x₅) | no ¬p =
    no (λ { (_ , Emptyrec-cong a b) → ¬p a })

  -- Decidability of algorithmic equality of neutrals with types in WHNF.
  dec~↓! : ∀ {k l R T Γ Δ}
        → ⊢ Γ ≡ Δ
        → Γ ⊢ k ~ k ↓! R → Δ ⊢ l ~ l ↓! T
        → Dec (∃ λ A → Γ ⊢ k ~ l ↓! A)
  dec~↓! Γ≡Δ ([~] A D whnfB k~l) ([~] A₁ D₁ whnfB₁ k~l₁)
        with dec~↑! Γ≡Δ k~l k~l₁
  dec~↓! Γ≡Δ ([~] A D whnfB k~l) ([~] A₁ D₁ whnfB₁ k~l₁)
        | yes (B , k~l₂) =
    let ⊢B , _ , _ = syntacticEqTerm (soundness~↑! k~l₂)
        C , whnfC , D′ = whNorm ⊢B
    in  yes (C , [~] B (red D′) whnfC k~l₂)
  dec~↓! Γ≡Δ ([~] A D whnfB k~l) ([~] A₁ D₁ whnfB₁ k~l₁)
        | no ¬p =
    no (λ { (A₂ , [~] A₃ D₂ whnfB₂ k~l₂) → ¬p (A₃ , k~l₂) })

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
  decConv↓ Γ≡Δ (U-refl {r = r} _ x) (U-refl {r = r′} _ x₁) with dec-relevance r r′
  ... | yes p = yes (U-refl p x)
  ... | no ¬p = no λ p → ¬p (Uinjectivity (soundnessConv↓ p))
  decConv↓ Γ≡Δ (U-refl e x) (ℕ-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
--  decConv↓ Γ≡Δ (U-refl e x) (Empty-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ Γ≡Δ (U-refl e x) (ne x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓! x₁
               in  ⊥-elim (IE.U≢ne! neK (soundnessConv↓ x₂)))
  decConv↓ Γ≡Δ (U-refl e x) (Π-cong e₁ x₁ x₂ x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ Γ≡Δ (ℕ-refl x) (U-refl e x₁) = no (λ { (ne ([~] A D whnfB ())) })
--  decConv↓ Γ≡Δ (Empty-refl x) (U-refl e x₁) = no (λ { (ne ([~] A D whnfB ())) })
--  decConv↓ Γ≡Δ (Empty-refl x) (ℕ-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
--  decConv↓ Γ≡Δ (ℕ-refl x) (Empty-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ Γ≡Δ (ℕ-refl x) (ℕ-refl x₁) = yes (ℕ-refl x)
  decConv↓ Γ≡Δ (Empty-refl x) (Empty-refl x₁) = yes (Empty-refl x)
  decConv↓ Γ≡Δ (ℕ-refl x) (ne x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓! x₁
               in  ⊥-elim (IE.ℕ≢ne! neK (soundnessConv↓ x₂)))
  decConv↓ Γ≡Δ (Empty-refl x) (ne x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓! x₁
               in  ⊥-elim (IE.Empty≢ne% neK (soundnessConv↓ x₂)))
  decConv↓ Γ≡Δ (ℕ-refl x) (Π-cong e x₁ x₂ x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ Γ≡Δ (Empty-refl x) (Π-cong e x₁ x₂ x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ Γ≡Δ (ne x) (U-refl e x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓! x
               in  ⊥-elim (IE.U≢ne! neK (sym (soundnessConv↓ x₂))))
  decConv↓ Γ≡Δ (ne x) (ℕ-refl x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓! x
               in  ⊥-elim (IE.ℕ≢ne! neK (sym (soundnessConv↓ x₂))))
  decConv↓ Γ≡Δ (ne x) (Empty-refl x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓! x
               in  ⊥-elim (IE.Empty≢ne% neK (sym (soundnessConv↓ x₂))))
  decConv↓ Γ≡Δ (ne x) (ne x₁) with dec~↓! Γ≡Δ x x₁
  decConv↓ Γ≡Δ (ne x) (ne x₁) | yes (A , k~l) =
    let whnfA , neK , neL = ne~↓! k~l
        ⊢A , ⊢k , _ = syntacticEqTerm (soundness~↓! k~l)
        _ , ⊢k∷U , _ = syntacticEqTerm (soundness~↓! x)
        ⊢U≡A = neTypeEq neK ⊢k∷U ⊢k
        A≡U = U≡A ⊢U≡A
        k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x) A≡U k~l
    in  yes (ne k~l′)
  decConv↓ {r = r} Γ≡Δ (ne x) (ne x₁) | no ¬p =
    no (λ x₂ → ¬p (Univ r , decConv↓-ne x₂ x))
  decConv↓ Γ≡Δ (ne x) (Π-cong e x₁ x₂ x₃) =
    no (λ x₄ → let whnfA , neK , neL = ne~↓! x
               in  ⊥-elim (IE.Π≢ne neK (sym (soundnessConv↓ x₄))))
  decConv↓ Γ≡Δ (Π-cong e x x₁ x₂) (U-refl e₁ x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ Γ≡Δ (Π-cong e x x₁ x₂) (ℕ-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ Γ≡Δ (Π-cong e x x₁ x₂) (Empty-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ Γ≡Δ (Π-cong e x x₁ x₂) (ne x₃) =
    no (λ x₄ → let whnfA , neK , neL = ne~↓! x₃
               in  ⊥-elim (IE.Π≢ne neK (soundnessConv↓ x₄)))
  decConv↓ Γ≡Δ (Π-cong {rF = rF} _ x x₁ x₂) (Π-cong {rF = rF₁} _ x₃ x₄ x₅) with dec-relevance rF rF₁
  decConv↓ Γ≡Δ (Π-cong _ x x₁ x₂) (Π-cong _ x₃ x₄ x₅) | no rF≢rF₁ = no (λ e → rF≢rF₁ let _ , req , _ = (injectivity (soundnessConv↓ e)) in req)
  decConv↓ Γ≡Δ (Π-cong _ x x₁ x₂) (Π-cong _ x₃ x₄ x₅) | yes PE.refl
           with decConv↑ Γ≡Δ x₁ x₄
  ... | no ¬p =
    no (λ { (ne ([~] A D whnfB ())) ; (Π-cong _ x₆ x₇ x₈) → ¬p x₇ })
  ... | yes p
           with decConv↑ (Γ≡Δ ∙ soundnessConv↑ p) x₂ x₅
  ... | no ¬p =
    no (λ { (ne ([~] A D whnfB ())) ; (Π-cong _ x₆ x₇ x₈) → ¬p x₈ })
  ... | yes p₁ =
    yes (Π-cong PE.refl x p p₁)

  -- Helper function for decidability of neutral types.
  decConv↓-ne : ∀ {A B r Γ}
              → Γ ⊢ A [conv↓] B ^ r
              → Γ ⊢ A ~ A ↓! Univ r
              → Γ ⊢ A ~ B ↓! Univ r
  decConv↓-ne (U-refl PE.refl x) A~A = A~A
  decConv↓-ne (ℕ-refl x) A~A = A~A
  decConv↓-ne (Empty-refl x) A~A = A~A
  decConv↓-ne (ne x) A~A = x
  decConv↓-ne (Π-cong e x x₁ x₂) ([~] A D whnfB ())

  -- Decidability of algorithmic equality of terms.
  decConv↑Term : ∀ {t u A Γ Δ}
               → ⊢ Γ ≡ Δ
               → Γ ⊢ t [conv↑] t ∷ A → Δ ⊢ u [conv↑] u ∷ A
               → Dec (Γ ⊢ t [conv↑] u ∷ A)
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
                              (PE.subst (λ x → _ ⊢ _ ⇒* _ ∷ x ) (PE.sym B₂≡B₁) d′
                              , whnfu′)
            u‴≡u″ = whrDet*Term (d‴ , whnfu‴)
                               (PE.subst (λ x → _ ⊢ _ ⇒* _ ∷ x)
                                         (PE.sym B₂≡B₁)
                                         (stabilityRed*Term (symConEq Γ≡Δ) d″)
                               , whnfu″)
        in  ¬p (PE.subst₃ (λ x y z → _ ⊢ x [conv↓] y ∷ z)
                          t‴≡u′ u‴≡u″ B₂≡B₁ t<>u₂) })

  -- Helper function for decidability for neutrals of natural number type.
  decConv↓Term-ℕ-ins : ∀ {t u Γ}
                     → Γ ⊢ t [conv↓] u ∷ ℕ
                     → Γ ⊢ t ~ t ↓! ℕ
                     → Γ ⊢ t ~ u ↓! ℕ
  decConv↓Term-ℕ-ins (ℕ-ins x) t~t = x
  decConv↓Term-ℕ-ins (ne-ins x x₁ () x₃) t~t
  decConv↓Term-ℕ-ins (zero-refl x) ([~] A D whnfB ())
  decConv↓Term-ℕ-ins (suc-cong x) ([~] A D whnfB ())

  -- Helper function for decidability for neutrals of a neutral type.
  decConv↓Term-ne-ins : ∀ {t u A Γ}
                      → Neutral A
                      → Γ ⊢ t [conv↓] u ∷ A 
                      → ∃ λ B → Γ ⊢ t ~ u ↓! B
  decConv↓Term-ne-ins () (ℕ-ins x)
  decConv↓Term-ne-ins neA (ne-ins x x₁ x₂ x₃) = _ , x₃
  decConv↓Term-ne-ins () (univ x x₁ x₂)
  decConv↓Term-ne-ins () (zero-refl x)
  decConv↓Term-ne-ins () (suc-cong x)
  decConv↓Term-ne-ins () (η-eq x x₁ x₂ x₃ x₄ x₅)

  -- Helper function for decidability for impossibility of terms not being equal
  -- as neutrals when they are equal as terms and the first is a neutral.
  decConv↓Term-ℕ : ∀ {t u Γ}
                 → Γ ⊢ t [conv↓] u ∷ ℕ 
                 → Γ ⊢ t ~ t ↓! ℕ
                 → ¬ (Γ ⊢ t ~ u ↓! ℕ)
                 → ⊥
  decConv↓Term-ℕ (ℕ-ins x) t~t ¬u~u = ¬u~u x
  decConv↓Term-ℕ (ne-ins x x₁ () x₃) t~t ¬u~u
  decConv↓Term-ℕ (zero-refl x) ([~] A D whnfB ()) ¬u~u
  decConv↓Term-ℕ (suc-cong x) ([~] A D whnfB ()) ¬u~u

  -- Decidability of algorithmic equality of terms in WHNF.
  decConv↓Term : ∀ {t u A Γ Δ}
               → ⊢ Γ ≡ Δ
               → Γ ⊢ t [conv↓] t ∷ A → Δ ⊢ u [conv↓] u ∷ A 
               → Dec (Γ ⊢ t [conv↓] u ∷ A)
  decConv↓Term Γ≡Δ (ℕ-ins x) (ℕ-ins x₁) with dec~↓! Γ≡Δ x x₁
  decConv↓Term Γ≡Δ (ℕ-ins x) (ℕ-ins x₁) | yes (A , k~l) =
    let whnfA , neK , neL = ne~↓! k~l
        ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓! k~l)
        _ , ⊢l∷ℕ , _ = syntacticEqTerm (soundness~↓! x)
        ⊢ℕ≡A = neTypeEq neK ⊢l∷ℕ ⊢k
        A≡ℕ = ℕ≡A ⊢ℕ≡A whnfA
        k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x) A≡ℕ k~l
    in  yes (ℕ-ins k~l′)
  decConv↓Term Γ≡Δ (ℕ-ins x) (ℕ-ins x₁) | no ¬p =
    no (λ x₂ → ¬p (ℕ , decConv↓Term-ℕ-ins x₂ x))
  decConv↓Term Γ≡Δ (ℕ-ins x) (ne-ins x₁ x₂ () x₄)
  decConv↓Term Γ≡Δ (ℕ-ins x) (zero-refl x₁) =
    no (λ x₂ → decConv↓Term-ℕ x₂ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (ℕ-ins x) (suc-cong x₁) =
    no (λ x₂ → decConv↓Term-ℕ x₂ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (ℕ-ins x₄)
  decConv↓Term Γ≡Δ (ne-ins x x₁ x₂ x₃) (ne-ins x₄ x₅ x₆ x₇)
               with dec~↓! Γ≡Δ x₃ x₇
  decConv↓Term Γ≡Δ (ne-ins x x₁ x₂ x₃) (ne-ins x₄ x₅ x₆ x₇) | yes (A , k~l) =
    yes (ne-ins x₁ (stabilityTerm (symConEq Γ≡Δ) x₄) x₆ k~l)
  decConv↓Term Γ≡Δ (ne-ins x x₁ x₂ x₃) (ne-ins x₄ x₅ x₆ x₇) | no ¬p =
    no (λ x₈ → ¬p (decConv↓Term-ne-ins x₆ x₈))
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (univ x₄ x₅ x₆)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (zero-refl x₄)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (suc-cong x₄)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (η-eq x₄ x₅ x₆ x₇ x₈ x₉)
  decConv↓Term Γ≡Δ (univ x x₁ x₂) (ne-ins x₃ x₄ () x₆)
  decConv↓Term Γ≡Δ (univ x x₁ x₂) (univ x₃ x₄ x₅)
               with decConv↓ Γ≡Δ x₂ x₅
  decConv↓Term Γ≡Δ (univ x x₁ x₂) (univ x₃ x₄ x₅) | yes p =
    yes (univ x₁ (stabilityTerm (symConEq Γ≡Δ) x₃) p)
  decConv↓Term Γ≡Δ (univ x x₁ x₂) (univ x₃ x₄ x₅) | no ¬p =
    no (λ { (ne-ins x₆ x₇ () x₉)
          ; (univ x₆ x₇ x₈) → ¬p x₈ })
  decConv↓Term Γ≡Δ (zero-refl x) (ℕ-ins x₁) =
    no (λ x₂ → decConv↓Term-ℕ (symConv↓Term Γ≡Δ x₂) x₁ (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (zero-refl x) (ne-ins x₁ x₂ () x₄)
  decConv↓Term Γ≡Δ (zero-refl x) (zero-refl x₁) = yes (zero-refl x)
  decConv↓Term Γ≡Δ (zero-refl x) (suc-cong x₁) =
    no (λ { (ℕ-ins ([~] A D whnfB ())) ; (ne-ins x₂ x₃ () x₅) })
  decConv↓Term Γ≡Δ (suc-cong x) (ℕ-ins x₁) =
    no (λ x₂ → decConv↓Term-ℕ (symConv↓Term Γ≡Δ x₂) x₁ (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (suc-cong x) (ne-ins x₁ x₂ () x₄)
  decConv↓Term Γ≡Δ (suc-cong x) (zero-refl x₁) =
    no (λ { (ℕ-ins ([~] A D whnfB ())) ; (ne-ins x₂ x₃ () x₅) })
  decConv↓Term Γ≡Δ (suc-cong x) (suc-cong x₁) with decConv↑Term Γ≡Δ x x₁
  decConv↓Term Γ≡Δ (suc-cong x) (suc-cong x₁) | yes p =
    yes (suc-cong p)
  decConv↓Term Γ≡Δ (suc-cong x) (suc-cong x₁) | no ¬p =
    no (λ { (ℕ-ins ([~] A D whnfB ()))
          ; (ne-ins x₂ x₃ () x₅)
          ; (suc-cong x₂) → ¬p x₂ })
  decConv↓Term Γ≡Δ (η-eq x x₁ x₂ x₃ x₄ x₅) (ne-ins x₆ x₇ () x₉)
  decConv↓Term Γ≡Δ (η-eq x x₁ x₂ x₃ x₄ x₅) (η-eq x₆ x₇ x₈ x₉ x₁₀ x₁₁)
               with decConv↑Term (Γ≡Δ ∙ refl x) x₅ x₁₁
  decConv↓Term Γ≡Δ (η-eq x x₁ x₂ x₃ x₄ x₅) (η-eq x₆ x₇ x₈ x₉ x₁₀ x₁₁) | yes p =
    yes (η-eq x x₂ (stabilityTerm (symConEq Γ≡Δ) x₇) x₄ x₁₀ p)
  decConv↓Term Γ≡Δ (η-eq x x₁ x₂ x₃ x₄ x₅) (η-eq x₆ x₇ x₈ x₉ x₁₀ x₁₁) | no ¬p =
    no (λ { (ne-ins x₁₂ x₁₃ () x₁₅)
          ; (η-eq x₁₂ x₁₃ x₁₄ x₁₅ x₁₆ x₁₇) → ¬p x₁₇ })

  -- Decidability of algorithmic equality of terms of equal types.
  decConv↑TermConv : ∀ {t u A B rF Γ Δ}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B ^ rF
                → Γ ⊢ t [genconv↑] t ∷ A ^ rF
                → Δ ⊢ u [genconv↑] u ∷ B ^ rF
                → Dec (Γ ⊢ t [genconv↑] u ∷ A ^ rF)
  decConv↑TermConv {rF = !} Γ≡Δ A≡B t u =
    decConv↑Term Γ≡Δ t (convConvTerm u (stabilityEq Γ≡Δ (sym A≡B)))
  decConv↑TermConv {rF = %} Γ≡Δ A≡B (%~↑ ⊢t ⊢t') (%~↑ ⊢u ⊢u') = yes (%~↑ ⊢t (conv (stabilityTerm (symConEq Γ≡Δ) ⊢u) (sym A≡B)))

