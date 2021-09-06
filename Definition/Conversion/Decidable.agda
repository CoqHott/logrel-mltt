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

open import Definition.Conversion.HelperDecidable

open import Tools.Nat
open import Tools.Product
open import Tools.Empty
open import Tools.Nullary
import Tools.PropositionalEquality as PE


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
      r≡r′ = PE.cong₂ (λ X Y → [ X , ι Y ]) rF≡rF′ lF≡lF′ 
    in 
      PE.subst (λ X → Dec (∃ λ A → ∃ λ lA → _ ⊢ _ ∘ _ ^ X ~ _ ∘ _ ^ _ ↑! _ ^ _)) l₂≡l₁
                (dec~↑!-app Γ≡Δ ⊢k₁′ ⊢k₂ x~y (decConv↑TermConv Γ≡Δ r≡r′ F≡F′ t≡t u≡u)) 
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (app-cong y~y u≡u) | no ¬p =
    no (λ { (_ , (_ , app-cong x′ y′)) → ¬p (_ , (_ , x′)) })

  dec~↑! Γ≡Δ (natrec-cong {lF = l} F a0 aS k) (natrec-cong {lF = l₀} G b0 bS k₀)
    with dec-level l l₀
  dec~↑! Γ≡Δ (natrec-cong {lF = l} F a0 aS k) (natrec-cong {lF = .l} G b0 bS k₀) | yes PE.refl
    with decConv↑ (Γ≡Δ ∙ refl (univ (ℕⱼ (wfEqTerm (soundness~↓! k))))) F G
  dec~↑! Γ≡Δ (natrec-cong {lF = l} F a0 aS k) (natrec-cong {lF = .l} G b0 bS k₀) | yes PE.refl | yes p
    with decConv↑TermConv Γ≡Δ PE.refl (substTypeEq (soundnessConv↑ p) (refl (zeroⱼ (wfEqTerm (soundness~↓! k))))) a0 b0
           | decConv↑TermConv Γ≡Δ PE.refl (sucCong (soundnessConv↑ p)) aS bS
           | dec~↓! Γ≡Δ k k₀
  dec~↑! Γ≡Δ (natrec-cong {lF = l} F a0 aS k) (natrec-cong {lF = .l} G b0 bS k₀) | yes PE.refl | yes p | yes p0 | yes pS | yes (_ , _ , pK) =
    let whnfA , neK , neK₀ = ne~↓! pK
        ⊢A , ⊢k , ⊢k₀ = syntacticEqTerm (soundness~↓! pK)
        _ , ⊢k∷ℕ , _ = syntacticEqTerm (soundness~↓! k)
        l≡l , ⊢ℕ≡A = neTypeEq neK ⊢k∷ℕ ⊢k
        A≡ℕ = ℕ≡A ⊢ℕ≡A whnfA
        k~k₀ = PE.subst₂ (λ x y → _ ⊢ _ ~ _ ↓! x ^ y) A≡ℕ (PE.sym l≡l) pK
    in  yes (_ , _ , natrec-cong p p0 pS k~k₀)
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

  dec~↑! Γ≡Δ = {!!}

{-

  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (natrec-cong x x₁ x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (Emptyrec-cong x x₁) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (Id-cong x x₁ x₂) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (Id-ℕ x x₁) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (Id-ℕ0 x) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (Id-ℕS x x₁) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (Id-U x x₁) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (Id-Uℕ x) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (Id-UΠ x x₁) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (cast-cong x x₁ x₂ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (cast-ℕ x x₁ x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (cast-ℕℕ x x₁ x₂) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (cast-Π x x₁ x₂ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (cast-Πℕ x x₁ x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (cast-ℕΠ x x₁ x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (var-refl x x₁) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (natrec-cong x x₁ x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (Emptyrec-cong x x₁) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (Id-cong x x₁ x₂) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (Id-ℕ x x₁) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (Id-ℕ0 x) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (Id-ℕS x x₁) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (Id-U x x₁) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (Id-Uℕ x) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (Id-UΠ x x₁) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-cong x x₁ x₂ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ℕ x x₁ x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ℕℕ x x₁ x₂) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-Π x x₁ x₂ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-Πℕ x x₁ x₂ x₃) =  no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ℕΠ x x₁ x₂ x₃) =  no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) =  no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (var-refl x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (app-cong x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (Emptyrec-cong x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (Id-cong x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (Id-ℕ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (Id-ℕ0 x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (Id-ℕS x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (Id-U x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (Id-Uℕ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (Id-UΠ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (cast-cong x₄ x₅ x₆ x₇ x₈) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (cast-ℕ x₄ x₅ x₆ x₇) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (cast-ℕℕ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (cast-Π x₄ x₅ x₆ x₇ x₈) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (cast-Πℕ x₄ x₅ x₆ x₇) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (cast-ℕΠ x₄ x₅ x₆ x₇) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (cast-ΠΠ%! x₄ x₅ x₆ x₇ x₈) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (cast-ΠΠ!% x₄ x₅ x₆ x₇ x₈) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (var-refl x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (app-cong x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (natrec-cong x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (Id-cong x₂ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (Id-ℕ x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (Id-ℕ0 x₂) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (Id-ℕS x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (Id-U x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (Id-Uℕ x₂) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (Id-UΠ x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (cast-cong x₂ x₃ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (cast-ℕ x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (cast-ℕℕ x₂ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (cast-Π x₂ x₃ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (cast-Πℕ x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (cast-ℕΠ x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (cast-ΠΠ%! x₂ x₃ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (cast-ΠΠ!% x₂ x₃ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (var-refl x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (app-cong x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (natrec-cong x₃ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (Emptyrec-cong x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (Id-ℕ x₃ x₄) =
    let _ , neA , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → Idℕ-elim neA e }
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (Id-ℕ0 x₃) =
    let _ , neA , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → Idℕ-elim neA e }    
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (Id-ℕS x₃ x₄) =
    let _ , neA , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → Idℕ-elim neA e }
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (Id-U x₃ x₄) = 
    let _ , neA , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → IdU-elim neA e }
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (Id-Uℕ x₃) =
    let _ , neA , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → IdU-elim neA e }
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (Id-UΠ x₃ x₄) =
    let _ , neA , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → IdU-elim neA e }
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (cast-cong x₃ x₄ x₅ x₆ x₇) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (cast-ℕ x₃ x₄ x₅ e) = no λ { (_ , _ , ()) }
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (cast-ℕℕ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (cast-Π x₃ x₄ x₅ x₆ x₇) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (cast-Πℕ x₃ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (cast-ℕΠ x₃ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (cast-ΠΠ%! x₃ x₄ x₅ x₆ x₇) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (cast-ΠΠ!% x₃ x₄ x₅ x₆ x₇) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ x x₁) (var-refl x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ x x₁) (app-cong x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ x x₁) (natrec-cong x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ x x₁) (Emptyrec-cong x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ x x₁) (Id-cong x₂ x₃ x₄) =
    let _ , neA , _ = ne~↓! x₂ in no λ { ( _ , ( _ , e )) → Idℕ-elim' neA e }    
  dec~↑! Γ≡Δ (Id-ℕ x x₁) (Id-ℕ0 x₂) =
    let _ , net , _ = ne~↓! x in no (λ { ( _ , ( _ , e )) → Idℕ0-elim net e })
  dec~↑! Γ≡Δ (Id-ℕ x x₁) (Id-ℕS x₂ x₃) =
    let _ , net , _ = ne~↓! x in no (λ { ( _ , ( _ , e )) → IdℕS-elim net e })
  dec~↑! Γ≡Δ (Id-ℕ x x₁) (Id-U x₂ x₃) = no λ { ( _ , ( _ , e )) → IdℕU-elim e }    
  dec~↑! Γ≡Δ (Id-ℕ x x₁) (Id-Uℕ x₂) = no λ { ( _ , ( _ , e )) → IdℕU-elim e }    
  dec~↑! Γ≡Δ (Id-ℕ x x₁) (Id-UΠ x₂ x₃) = no λ { ( _ , ( _ , e )) → IdℕU-elim e }    
  dec~↑! Γ≡Δ (Id-ℕ x x₁) (cast-cong x₂ x₃ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ x x₁) (cast-ℕ x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ x x₁) (cast-ℕℕ x₂ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ x x₁) (cast-Π x₂ x₃ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ x x₁) (cast-Πℕ x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ x x₁) (cast-ℕΠ x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ x x₁) (cast-ΠΠ%! x₂ x₃ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ x x₁) (cast-ΠΠ!% x₂ x₃ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ0 x) (var-refl x₁ x₂) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ0 x) (app-cong x₁ x₂) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ0 x) (natrec-cong x₁ x₂ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ0 x) (Emptyrec-cong x₁ x₂) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ0 x) (Id-cong x₁ x₂ x₃) =
    let _ , neA , _ = ne~↓! x₁ in no λ { ( _ , ( _ , e )) → Idℕ-elim' neA e }    
  dec~↑! Γ≡Δ (Id-ℕ0 x) (Id-ℕ x₁ x₂) = 
    let _ , net , _ = ne~↓! x₁ in no (λ { ( _ , ( _ , e )) → Idℕ0-elim' net e })
  dec~↑! Γ≡Δ (Id-ℕ0 x) (Id-ℕS x₁ x₂) = no λ { ( _ , ( _ , e )) → Idℕ0S-elim e }
  dec~↑! Γ≡Δ (Id-ℕ0 x) (Id-U x₁ x₂) = no λ { ( _ , ( _ , e )) → IdℕU-elim e }    
  dec~↑! Γ≡Δ (Id-ℕ0 x) (Id-Uℕ x₁) = no λ { ( _ , ( _ , e )) → IdℕU-elim e }    
  dec~↑! Γ≡Δ (Id-ℕ0 x) (Id-UΠ x₁ x₂) = no λ { ( _ , ( _ , e )) → IdℕU-elim e }    
  dec~↑! Γ≡Δ (Id-ℕ0 x) (cast-cong x₁ x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ0 x) (cast-ℕ x₁ x₂ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ0 x) (cast-ℕℕ x₁ x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ0 x) (cast-Π x₁ x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ0 x) (cast-Πℕ x₁ x₂ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ0 x) (cast-ℕΠ x₁ x₂ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ0 x) (cast-ΠΠ%! x₁ x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ0 x) (cast-ΠΠ!% x₁ x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕS x x₁) (var-refl x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕS x x₁) (app-cong x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕS x x₁) (natrec-cong x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕS x x₁) (Emptyrec-cong x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕS x x₁) (Id-cong x₂ x₃ x₄) =
    let _ , neA , _ = ne~↓! x₂ in no λ { ( _ , ( _ , e )) → Idℕ-elim' neA e }    
  dec~↑! Γ≡Δ (Id-ℕS x x₁) (Id-ℕ x₂ x₃) =
    let _ , net , _ = ne~↓! x₂ in no (λ { ( _ , ( _ , e )) → IdℕS-elim' net e })  
  dec~↑! Γ≡Δ (Id-ℕS x x₁) (Id-ℕ0 x₂) = no λ { ( _ , ( _ , e )) → Idℕ0S-elim' e }
  dec~↑! Γ≡Δ (Id-ℕS x x₁) (Id-U x₂ x₃) = no λ { ( _ , ( _ , e )) → IdℕU-elim e }
  dec~↑! Γ≡Δ (Id-ℕS x x₁) (Id-Uℕ x₂) = no λ { ( _ , ( _ , e )) → IdℕU-elim e }
  dec~↑! Γ≡Δ (Id-ℕS x x₁) (Id-UΠ x₂ x₃) = no λ { ( _ , ( _ , e )) → IdℕU-elim e }
  dec~↑! Γ≡Δ (Id-ℕS x x₁) (cast-cong x₂ x₃ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕS x x₁) (cast-ℕ x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕS x x₁) (cast-ℕℕ x₂ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕS x x₁) (cast-Π x₂ x₃ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕS x x₁) (cast-Πℕ x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕS x x₁) (cast-ℕΠ x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕS x x₁) (cast-ΠΠ%! x₂ x₃ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕS x x₁) (cast-ΠΠ!% x₂ x₃ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-U x x₁) (var-refl x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-U x x₁) (app-cong x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-U x x₁) (natrec-cong x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-U x x₁) (Emptyrec-cong x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-U x x₁) (Id-cong x₂ x₃ x₄) =
    let _ , neA , _ = ne~↓! x₂ in no λ { ( _ , ( _ , e )) → IdU-elim' neA e }    
  dec~↑! Γ≡Δ (Id-U x x₁) (Id-ℕ x₂ x₃) = no λ { ( _ , ( _ , e )) → IdUℕ-elim e }
  dec~↑! Γ≡Δ (Id-U x x₁) (Id-ℕ0 x₂) = no λ { ( _ , ( _ , e )) → IdUℕ-elim e }
  dec~↑! Γ≡Δ (Id-U x x₁) (Id-ℕS x₂ x₃) = no λ { ( _ , ( _ , e )) → IdUℕ-elim e }
  dec~↑! Γ≡Δ (Id-U x x₁) (Id-Uℕ x₂) = let _ , net , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → IdUUℕ-elim net e }
  dec~↑! Γ≡Δ (Id-U x x₁) (Id-UΠ x₂ x₃) = let _ , net , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → IdUUΠ-elim net e }
  dec~↑! Γ≡Δ (Id-U x x₁) (cast-cong x₂ x₃ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-U x x₁) (cast-ℕ x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-U x x₁) (cast-ℕℕ x₂ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-U x x₁) (cast-Π x₂ x₃ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-U x x₁) (cast-Πℕ x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-U x x₁) (cast-ℕΠ x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-U x x₁) (cast-ΠΠ%! x₂ x₃ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-U x x₁) (cast-ΠΠ!% x₂ x₃ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-Uℕ x) (var-refl x₁ x₂) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-Uℕ x) (app-cong x₁ x₂) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-Uℕ x) (natrec-cong x₁ x₂ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-Uℕ x) (Emptyrec-cong x₁ x₂) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-Uℕ x) (Id-cong x₁ x₂ x₃) = 
    let _ , neA , _ = ne~↓! x₁ in no λ { ( _ , ( _ , e )) → IdU-elim' neA e }    
  dec~↑! Γ≡Δ (Id-Uℕ x) (Id-ℕ x₁ x₂) = no λ { ( _ , ( _ , e )) → IdUℕ-elim e }
  dec~↑! Γ≡Δ (Id-Uℕ x) (Id-ℕ0 x₁) = no λ { ( _ , ( _ , e )) → IdUℕ-elim e }
  dec~↑! Γ≡Δ (Id-Uℕ x) (Id-ℕS x₁ x₂) = no λ { ( _ , ( _ , e )) → IdUℕ-elim e }
  dec~↑! Γ≡Δ (Id-Uℕ x) (Id-U x₁ x₂) = let _ , net , _ = ne~↓! x₁ in no λ { ( _ , ( _ , e )) → IdUUℕ-elim' net e }
  dec~↑! Γ≡Δ (Id-Uℕ x) (Id-UΠ x₁ x₂) = no λ { ( _ , ( _ , e )) → IdUUΠℕ-elim' e }
  dec~↑! Γ≡Δ (Id-Uℕ x) (cast-cong x₁ x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-Uℕ x) (cast-ℕ x₁ x₂ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-Uℕ x) (cast-ℕℕ x₁ x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-Uℕ x) (cast-Π x₁ x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-Uℕ x) (cast-Πℕ x₁ x₂ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-Uℕ x) (cast-ℕΠ x₁ x₂ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-Uℕ x) (cast-ΠΠ%! x₁ x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-Uℕ x) (cast-ΠΠ!% x₁ x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (var-refl x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (app-cong x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (natrec-cong x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (Emptyrec-cong x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (Id-cong x₂ x₃ x₄) =
    let _ , neA , _ = ne~↓! x₂ in no λ { ( _ , ( _ , e )) → IdU-elim' neA e }    
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (Id-ℕ x₂ x₃) = no λ { ( _ , ( _ , e )) → IdUℕ-elim e }
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (Id-ℕ0 x₂) = no λ { ( _ , ( _ , e )) → IdUℕ-elim e }
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (Id-ℕS x₂ x₃) = no λ { ( _ , ( _ , e )) → IdUℕ-elim e }
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (Id-U x₂ x₃) = let _ , net , _ = ne~↓! x₂ in no λ { ( _ , ( _ , e )) → IdUUΠ-elim' net e }
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (Id-Uℕ x₂) = no λ { ( _ , ( _ , e )) → IdUUΠℕ-elim e }
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (cast-cong x₂ x₃ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (cast-ℕ x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (cast-ℕℕ x₂ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (cast-Π x₂ x₃ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (cast-Πℕ x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (cast-ℕΠ x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (cast-ΠΠ%! x₂ x₃ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (cast-ΠΠ!% x₂ x₃ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-cong x x₁ x₂ x₃ x₄) (var-refl x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-cong x x₁ x₂ x₃ x₄) (app-cong x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-cong x x₁ x₂ x₃ x₄) (natrec-cong x₅ x₆ x₇ x₈) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-cong x x₁ x₂ x₃ x₄) (Emptyrec-cong x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-cong x x₁ x₂ x₃ x₄) (Id-cong x₅ x₆ x₇) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-cong x x₁ x₂ x₃ x₄) (Id-ℕ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-cong x x₁ x₂ x₃ x₄) (Id-ℕ0 x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-cong x x₁ x₂ x₃ x₄) (Id-ℕS x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-cong x x₁ x₂ x₃ x₄) (Id-U x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-cong x x₁ x₂ x₃ x₄) (Id-Uℕ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-cong x x₁ x₂ x₃ x₄) (Id-UΠ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-cong x x₁ x₂ x₃ x₄) (cast-ℕ x₅ x₆ x₇ x₈) =
    let _ , neA , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → castℕ-elim neA e }    
  dec~↑! Γ≡Δ (cast-cong x x₁ x₂ x₃ x₄) (cast-ℕℕ x₅ x₆ x₇) =
    let _ , neA , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → castℕ-elim neA e }    
  dec~↑! Γ≡Δ (cast-cong x x₁ x₂ x₃ x₄) (cast-Π x₅ x₆ x₇ x₈ x₉) = 
    let _ , neA , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → castΠ-elim neA e }
  dec~↑! Γ≡Δ (cast-cong x x₁ x₂ x₃ x₄) (cast-Πℕ x₅ x₆ x₇ x₈) = 
    let _ , neA , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → castΠ-elim neA e }
  dec~↑! Γ≡Δ (cast-cong x x₁ x₂ x₃ x₄) (cast-ℕΠ x₅ x₆ x₇ x₈) =
    let _ , neA , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → castℕ-elim neA e }
  dec~↑! Γ≡Δ (cast-cong x x₁ x₂ x₃ x₄) (cast-ΠΠ%! x₅ x₆ x₇ x₈ x₉) =
    let _ , neA , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → castΠ-elim neA e }
  dec~↑! Γ≡Δ (cast-cong x x₁ x₂ x₃ x₄) (cast-ΠΠ!% x₅ x₆ x₇ x₈ x₉) =
    let _ , neA , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → castΠ-elim neA e }
  
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) X = {!!}
  dec~↑! Γ≡Δ (Id-ℕ x x₁) = {!!}
  dec~↑! Γ≡Δ (Id-ℕ0 x) = {!!}
  dec~↑! Γ≡Δ (Id-ℕS x x₁)  = {!!}
  dec~↑! Γ≡Δ (Id-U x x₁) = {!!}
  dec~↑! Γ≡Δ (Id-Uℕ x) = {!!}
  dec~↑! Γ≡Δ (Id-UΠ x x₁) = {!!}
  dec~↑! Γ≡Δ (cast-cong x x₁ x₂ x₃ x₄) = {!!}
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) [l] = {!!}
  dec~↑! Γ≡Δ (cast-ℕℕ x x₁ x₂) [l] = {!!}
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) [l] = {!!}
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) [l] = {!!}
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) [l] = {!!}
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) [l] = {!!}
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) [l] = {!!}
-}

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

  decConv↓Term Γ≡Δ (U-refl {r = r} _ x) (U-refl {r = r′} _ x₁)
    with dec-relevance r r′
  ... | yes p = yes (U-refl p x)
  ... | no ¬p = no λ p → ¬p (proj₁ (Uinjectivity (univ (soundnessConv↓Term p))))

  decConv↓Term Γ≡Δ (ne K) (ne K₁)   --TERMINATION ISSUES: should be solved by layering levels
    with dec~↓! Γ≡Δ K K₁
  ... | yes (A , lA , K~K₁) =
    let whnfA , neK , neK₁ = ne~↓! K~K₁
        ⊢A , ⊢K , ⊢K₁ = syntacticEqTerm (soundness~↓! K~K₁)
        _ , ⊢K∷U , _ = syntacticEqTerm (soundness~↓! K)
        l≡l , ⊢U≡A = neTypeEq neK ⊢K∷U ⊢K
        A≡U = U≡A-whnf ⊢U≡A whnfA
        K~K₁′ = PE.subst₂ (λ x y → _ ⊢ _ ~ _ ↓! x ^ y) A≡U (PE.sym l≡l) K~K₁
    in yes (ne K~K₁′)
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
  ... | yes (A , lA , K~K₁) =
    let whnfA , neK , neK₁ = ne~↓! K~K₁
        ⊢A , ⊢K , ⊢K₁ = syntacticEqTerm (soundness~↓! K~K₁)
        _ , ⊢K∷ℕ , _ = syntacticEqTerm (soundness~↓! K)
        l≡l , ⊢ℕ≡A = neTypeEq neK ⊢K∷ℕ ⊢K
        A≡ℕ = ℕ≡A ⊢ℕ≡A whnfA
        K~K₁′ = PE.subst₂ (λ x y → _ ⊢ _ ~ _ ↓! x ^ y) A≡ℕ (PE.sym l≡l) K~K₁
    in yes (ℕ-ins K~K₁′)
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
  decConv↑TermConv : ∀ {t u A B r r' Γ Δ}
                → ⊢ Γ ≡ Δ
                → r PE.≡ r'
                → Γ ⊢ A ≡ B ^ r
                → Γ ⊢ t [genconv↑] t ∷ A ^ r
                → Δ ⊢ u [genconv↑] u ∷ B ^ r'
                → Dec (Γ ⊢ t [genconv↑] u ∷ A ^ r')
  decConv↑TermConv {r = [ ! , l ]} Γ≡Δ PE.refl A≡B t u =
    decConv↑Term Γ≡Δ t (convConvTerm u (stabilityEq Γ≡Δ (sym A≡B)))
  decConv↑TermConv {r = [ % , l ]} Γ≡Δ PE.refl A≡B (%~↑ ⊢t ⊢t') (%~↑ ⊢u ⊢u') =
    yes (%~↑ ⊢t (conv (stabilityTerm (symConEq Γ≡Δ) ⊢u) (sym A≡B)))
