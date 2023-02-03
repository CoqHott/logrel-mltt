{-# OPTIONS --safe #-}

module Definition.Conversion.DecView where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed as T
open import Definition.Typed.Properties
open import Definition.Conversion

open import Definition.Conversion.Whnf
open import Definition.Conversion.Soundness
open import Definition.Conversion.Symmetry
open import Definition.Conversion.SymmetrySize
open import Definition.Conversion.Stability
open import Definition.Conversion.StabilityProp
open import Definition.Conversion.Conversion
open import Definition.Conversion.ConversionProp
open import Definition.Conversion.ConvSize
open import Definition.Conversion.Lift
open import Definition.Conversion.EqRelInstance
open import Definition.Conversion.Inversion
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

open import Definition.Conversion.HelperDecidable
open import Definition.Conversion.DecidableLemmas

open import Definition.Conversion.Consequences.Completeness
open import Definition.Conversion.TransitivityHelper

open import Tools.Nat
open import Tools.Product
open import Tools.Nullary
import Tools.PropositionalEquality as PE

cast-PE-injectivity : ∀ {A A' B B' e e' t t' l l'} → cast l A B e t PE.≡ cast l' A' B' e' t' → l PE.≡ l' × A PE.≡ A' × B PE.≡ B' × e PE.≡ e' × t PE.≡ t'
cast-PE-injectivity PE.refl = PE.refl , PE.refl , PE.refl , PE.refl , PE.refl

removeSuc : Nat → Nat
removeSuc 0 = 0
removeSuc (1+ n) = n

data Bool : Set where
  true : Bool
  false : Bool

is-diag~↑! : ∀ {k k' l l' R T Γ Δ lR lT}
         → (e : Γ ⊢ k ~ k' ↑! R ^ lR)
         → (e' : Δ ⊢ l ~ l' ↑! T ^ lT)
         → Bool
is-diag~↑! e (cast-refl' _ _ _) = true
is-diag~↑! e (cast-refl _ _ _) = true
is-diag~↑! e (cast-cong _ _ _ _ _) = true
is-diag~↑! e (castℕ-refl _ _) = true
is-diag~↑! e (castℕ-refl' _ _) = true
is-diag~↑! (cast-refl _ _ _) e = true
is-diag~↑! (cast-refl' _ _ _) e = true
is-diag~↑! (castℕ-refl' _ _) e = true
is-diag~↑! (cast-cong _ _ _ _ _) e = true
is-diag~↑! (castℕ-refl _ _) e = true

is-diag~↑! (var-refl x x₁) (var-refl y y₁) = true
is-diag~↑! (var-refl x x₁) e' = false
is-diag~↑! (app-cong x x₁) (app-cong _ _) = true
is-diag~↑! (app-cong x x₁) e' = false
is-diag~↑! (natrec-cong x x₁ x₂ x₃) (natrec-cong  _ _ _ _) = true
is-diag~↑! (natrec-cong x x₁ x₂ x₃) e' = false
is-diag~↑! (Emptyrec-cong x x₁) (Emptyrec-cong _ _) = true
is-diag~↑! (Emptyrec-cong x x₁) e' = false
is-diag~↑! (cast-neℕ x x₁ x₂ x₃) (cast-neℕ _ _ _ _) = true
is-diag~↑! (cast-neℕ x x₁ x₂ x₃) e' = false
is-diag~↑! (cast-ℕ x x₁ x₂ x₃) (cast-ℕ _ _ _ _) = true
is-diag~↑! (cast-ℕ x x₁ x₂ x₃) e' = false
is-diag~↑! (cast-neΠ x x₁ x₂ x₃ x₄) (cast-neΠ _ _ _ _ _) = true
is-diag~↑! (cast-neΠ x x₁ x₂ x₃ x₄) e' = false
is-diag~↑! (cast-Π x x₁ x₂ x₃ x₄) (cast-Π _ _ _ _ _) = true
is-diag~↑! (cast-Π x x₁ x₂ x₃ x₄) e' = false
is-diag~↑! (cast-Πℕ x x₁ x₂ x₃) (cast-Πℕ _ _ _ _) = true
is-diag~↑! (cast-Πℕ x x₁ x₂ x₃) e' = false
is-diag~↑! (cast-ℕΠ x x₁ x₂ x₃) (cast-ℕΠ _ _ _ _) = true
is-diag~↑! (cast-ℕΠ x x₁ x₂ x₃) e' = false
is-diag~↑! (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-ΠΠ%! _ _ _ _ _) = true
is-diag~↑! (cast-ΠΠ%! x x₁ x₂ x₃ x₄) e' = false
is-diag~↑! (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-ΠΠ!% _ _ _ _ _) = true
is-diag~↑! (cast-ΠΠ!% x x₁ x₂ x₃ x₄) e' = false

abstract
  not-diag~↑! : ∀ {k k' l l' R T Γ Δ lR lT}
           → ⊢ Γ ≡ Δ
           → (e : Γ ⊢ k ~ k' ↑! R ^ lR)
           → (e' : Δ ⊢ l ~ l' ↑! T ^ lT)
           → is-diag~↑! e e' PE.≡ false
           → Dec (∃ λ A → ∃ λ lA → Γ ⊢ k ~ l ↑! A ^ lA)
  not-diag~↑! Γ≡Δ (var-refl x x₁) (app-cong x₂ x₃) notdiag = no (λ { (_ , ()) })
  not-diag~↑! Γ≡Δ (var-refl x x₁) (natrec-cong x₂ x₃ x₄ x₅) notdiag = no (λ { (_ , ()) })
  not-diag~↑! Γ≡Δ (var-refl x x₁) (Emptyrec-cong x₂ x₃) notdiag = no (λ { (_ , ()) })
  not-diag~↑! Γ≡Δ (var-refl x x₁) (cast-neℕ x₂ x₃ x₄ x₅) notdiag = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ  ;
                                                                           (_ , _ , castℕ-refl' x x₁) → let _ , neℕ , _ = ne~↓! x₂ in noNeℕ neℕ })
  not-diag~↑! Γ≡Δ (var-refl ⊢x n≡n) (cast-ℕ x X x₂ x₃) notdiag = castℕ-refl-dec~ (stability~↓! (symConEq Γ≡Δ) x) (λ {_ _ ()}) (λ {_ ()}) (λ {()})
  not-diag~↑! Γ≡Δ (var-refl x x₁) (cast-neΠ x₂ x₃ x₄ x₅ x₆) notdiag = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })
  not-diag~↑! Γ≡Δ (var-refl x x₁) (cast-Π x₂ x₃ x₄ x₅ x₆) notdiag = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (var-refl x x₁) (cast-Πℕ x₂ x₃ x₄ x₅) notdiag = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (var-refl x x₁) (cast-ℕΠ x₂ x₃ x₄ x₅) notdiag = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (var-refl x x₁) (cast-ΠΠ%! x₂ x₃ x₄ x₅ x₆) notdiag = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (var-refl x x₁) (cast-ΠΠ!% x₂ x₃ x₄ x₅ x₆) notdiag = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })

  not-diag~↑! Γ≡Δ (app-cong x~x t≡t) (var-refl x x₁) _ = no (λ { (_ , ()) })
  not-diag~↑! Γ≡Δ (app-cong x~x t≡t) (natrec-cong x x₁ x₂ x₃) _ = no (λ { (_ , ()) })
  not-diag~↑! Γ≡Δ (app-cong x~x t≡t) (Emptyrec-cong x x₁) _ = no (λ { (_ , ()) })
  not-diag~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ℕ x x₁ x₂ x₃) _ = castℕ-refl-dec~ (stability~↓! (symConEq Γ≡Δ) x) (λ {_ _ ()}) (λ {_ ()}) (λ {()})
  not-diag~↑! Γ≡Δ (app-cong x~x t≡t) (cast-Π x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (app-cong x~x t≡t) (cast-Πℕ x x₁ x₂ x₃) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ℕΠ x x₁ x₂ x₃) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (app-cong x~x t≡t) (cast-neℕ x₂ x₃ x₄ x₅) _ = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ  ;
                                                                         (_ , _ , castℕ-refl' x x₁) → let _ , neℕ , _ = ne~↓! x₂ in noNeℕ neℕ })
  not-diag~↑! Γ≡Δ (app-cong x~x t≡t) (cast-neΠ x₂ x₃ x₄ x₅ x₆) _ = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })

  not-diag~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (var-refl x₄ x₅) _ = no (λ { (_ , ()) })
  not-diag~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (app-cong x₄ x₅) _ = no (λ { (_ , ()) })
  not-diag~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (Emptyrec-cong x₄ x₅) _ = no (λ { (_ , ()) })
  not-diag~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-ℕ x x₁ x₂ x₃) _ = castℕ-refl-dec~ (stability~↓! (symConEq Γ≡Δ) x) (λ {_ _ ()}) (λ {_ ()}) (λ {()})
  not-diag~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-Π x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-Πℕ x x₁ x₂ x₃) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-ℕΠ x x₁ x₂ x₃) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-neℕ x₂ x₃ x₄ x₅) _ = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ  ;
                                                                                      (_ , _ , castℕ-refl' x x₁) → let _ , neℕ , _ = ne~↓! x₂ in noNeℕ neℕ })
  not-diag~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-neΠ x₂ x₃ x₄ x₅ x₆) _ = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })

  not-diag~↑! Γ≡Δ (Emptyrec-cong x x₁) (var-refl x₂ x₃) _ = no (λ { (_ , ()) })
  not-diag~↑! Γ≡Δ (Emptyrec-cong x x₁) (app-cong x₂ x₃) _ = no (λ { (_ , ()) })
  not-diag~↑! Γ≡Δ (Emptyrec-cong x x₁) (natrec-cong x₂ x₃ x₄ x₅) _ = no (λ { (_ , ()) })
  not-diag~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-ℕ x x₁ x₂ x₃) _ = castℕ-refl-dec~ (stability~↓! (symConEq Γ≡Δ) x) (λ {_ _ ()}) (λ {_ ()}) (λ {()})
  not-diag~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-Π x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-Πℕ x x₁ x₂ x₃) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-ℕΠ x x₁ x₂ x₃) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-neℕ x₂ x₃ x₄ x₅) _ = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ  ;
                                                                                      (_ , _ , castℕ-refl' x x₁) → let _ , neℕ , _ = ne~↓! x₂ in noNeℕ neℕ })
  not-diag~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-neΠ x₂ x₃ x₄ x₅ x₆) _ = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })

  not-diag~↑! Γ≡Δ (cast-neℕ x x₁ x₂ x₃) (var-refl x₄ x₅) _ = castneℕ-refl'-dec~ x (λ {_ _ ()}) (λ {_ ()}) (λ {()})
  not-diag~↑! Γ≡Δ (cast-neℕ x x₁ x₂ x₃) (app-cong x₄ x₅) _ = castneℕ-refl'-dec~ x (λ {_ _ ()}) (λ {_ ()}) (λ {()})
  not-diag~↑! Γ≡Δ (cast-neℕ x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇) _ = castneℕ-refl'-dec~ x (λ {_ _ ()}) (λ {_ ()}) (λ {()})
  not-diag~↑! Γ≡Δ (cast-neℕ x x₁ x₂ x₃) (Emptyrec-cong x₄ x₅) _ = castneℕ-refl'-dec~ x (λ {_ _ ()}) (λ {_ ()}) (λ {()})
  not-diag~↑! Γ≡Δ (cast-neℕ B x₁ x₂ x₃) (cast-ℕΠ x₄ x₅ x₆ x₇) _ =
    no (λ (_ , _ , X) → IE.ℕ≢Π! (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-neℕ B x₁ x₂ x₃) (cast-ΠΠ%! x₄ x₅ x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → IE.ℕ≢Π! (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-neℕ B x₁ x₂ x₃) (cast-ΠΠ!% x₄ x₅ x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → IE.ℕ≢Π! (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-neℕ x₁ x₂ x₃ x₄) (cast-neΠ x₅ x₆ x₇ x₈ x₉) _ = no (λ (_ , _ , X) → IE.ℕ≢Π! (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-neℕ x x₁ x₂ x₃) (cast-Π x₄ x₅ x₆ x₇ x₈) _ =
    castneℕ-refl'-dec~ x
                    (λ neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                   in noNeΠ (PE.subst Neutral (PE.sym eA) neA))
                    (λ neA e → let _ , eA , _ = cast-PE-injectivity e in noNeΠ (PE.subst Neutral (PE.sym eA) neA) )
                    (λ e → let _ , _ , eB , _ = cast-PE-injectivity e
                               _ , neB , _ = ne~↓! x₅
                           in noNeℕ (PE.subst Neutral eB neB))
  not-diag~↑! Γ≡Δ (cast-neℕ x' x₁' x₂' x₃') (cast-ℕ x₂ x₃ x₄ x₅) _ =  no (λ (_ , _ , X) → let _ , neA , _ = ne~↓! x₂ in IE.ℕ≢ne! neA (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-neℕ B x₁ x₂ x₃) (cast-Πℕ x₄ x₅ x₆ x₇) _ =
    no (λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠ ;
            (_ , _ , cast-refl x x₁ x₂) → let _ , _ , neℕ = ne~↓! x in noNeℕ neℕ ;
            (_ , _ , castℕ-refl x x₁) → let _ , neℕ , _ = ne~↓! B in noNeℕ neℕ ;
            (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ ;
            (_ , _ , cast-neℕ x x₁ x₂ x₃) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠ ;
            (_ , _ , cast-Π x x₁ x₂ x₃ x₄) → let _ , neΠ , _ = ne~↓! B in noNeΠ neΠ ;
            (_ , _ , cast-Πℕ x x₁ x₂ x₃) → let _ , neΠ , _ = ne~↓! B in noNeΠ neΠ })

  not-diag~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (var-refl x₄ x₅) _ = castℕ-refl'-dec~ x (λ {_ _ ()}) (λ {_ ()}) (λ {()})
  not-diag~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (app-cong x₄ x₅) _ = castℕ-refl'-dec~ x (λ {_ _ ()}) (λ {_ ()}) (λ {()})
  not-diag~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇) _ = castℕ-refl'-dec~ x (λ {_ _ ()}) (λ {_ ()}) (λ {()})
  not-diag~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (Emptyrec-cong x₄ x₅) _ = castℕ-refl'-dec~ x (λ {_ _ ()}) (λ {_ ()}) (λ {()})
  not-diag~↑! Γ≡Δ (cast-ℕ B x₁ x₂ x₃) (cast-Πℕ x₄ x₅ x₆ x₇) _ =
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in ℕ≢ne! neR (sym (cast-cast-≡ X)))
  not-diag~↑! Γ≡Δ (cast-ℕ B x₁ x₂ x₃) (cast-ℕΠ x₄ x₅ x₆ x₇) _ =
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in IE.Π≢ne neR (sym (cast-cast-≡ X)))
  not-diag~↑! Γ≡Δ (cast-ℕ B x₁ x₂ x₃) (cast-ΠΠ%! x₄ x₅ x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in IE.Π≢ne neR (sym (cast-cast-≡ X)))
  not-diag~↑! Γ≡Δ (cast-ℕ B x₁ x₂ x₃) (cast-ΠΠ!% x₄ x₅ x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in IE.Π≢ne neR (sym (cast-cast-≡ X)))
  not-diag~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (cast-Π x₄ x₅ x₆ x₇ x₈) _ =
    castℕ-refl'-dec~ x
                    (λ neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                   in noNeΠ (PE.subst Neutral (PE.sym eA) neA))
                    (λ neA e → let _ , eA , _ = cast-PE-injectivity e in ℕ≢Π (PE.sym eA))
                    (λ e → let _ , _ , eB , _ = cast-PE-injectivity e
                               _ , neB , _ = ne~↓! x₅
                           in noNeℕ (PE.subst Neutral eB neB))
  not-diag~↑! Γ≡Δ (cast-ℕ x' x₁' x₂' x₃') (cast-neℕ x₂ x₃ x₄ x₅) _ = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ  ;
                                                                                      (_ , _ , castℕ-refl' x x₁) → let _ , neℕ , _ = ne~↓! x₂ in noNeℕ neℕ })
  not-diag~↑! Γ≡Δ (cast-ℕ x' x₁' x₂' x₃') (cast-neΠ x₂ x₃ x₄ x₅ x₆) _ = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })

  not-diag~↑! Γ≡Δ (cast-neΠ _ x x₁ x₂ x₃) (var-refl x₄ x₅) _ = castneΠ-refl'-dec~ x (λ {_ _ ()}) (λ {_ ()}) (λ {()})
  not-diag~↑! Γ≡Δ (cast-neΠ _ x x₁ x₂ x₃) (app-cong x₄ x₅) _ = castneΠ-refl'-dec~ x (λ {_ _ ()}) (λ {_ ()}) (λ {()})
  not-diag~↑! Γ≡Δ (cast-neΠ _ x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇) _ = castneΠ-refl'-dec~ x (λ {_ _ ()}) (λ {_ ()}) (λ {()})
  not-diag~↑! Γ≡Δ (cast-neΠ _ x x₁ x₂ x₃) (Emptyrec-cong x₄ x₅) _ = castneΠ-refl'-dec~ x (λ {_ _ ()}) (λ {_ ()}) (λ {()})
  not-diag~↑! Γ≡Δ (cast-neΠ _ x x₁ x₂ x₃) (cast-Πℕ x₄ x₅ x₆ x₇) _ =
    no (λ (_ , _ , X) → IE.ℕ≢Π! (sym (cast-cast-≡ X)))

  not-diag~↑! Γ≡Δ (cast-neΠ _ x x₁ x₂ x₃) (cast-ΠΠ%! x₄ x₅ x₆ x₇ x₈) _ =
      castneΠ-refl'-dec~ x
                    (λ neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                   in noNeΠ (PE.subst Neutral (PE.sym eA) neA))
                    (λ neA e → let _ , eA , _ = cast-PE-injectivity e in noNeΠ (PE.subst Neutral (PE.sym eA) neA) )
                    (λ e → let _ , _ , eB , _ = cast-PE-injectivity e in ℕ≢Π (PE.sym eB))
  not-diag~↑! Γ≡Δ (cast-neΠ _ x x₁ x₂ x₃) (cast-ΠΠ!% x₄ x₅ x₆ x₇ x₈) _ =
      castneΠ-refl'-dec~ x
                    (λ neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                   in noNeΠ (PE.subst Neutral (PE.sym eA) neA))
                    (λ neA e → let _ , eA , _ = cast-PE-injectivity e in noNeΠ (PE.subst Neutral (PE.sym eA) neA) )
                    (λ e → let _ , _ , eB , _ = cast-PE-injectivity e in ℕ≢Π (PE.sym eB))
  not-diag~↑! Γ≡Δ (cast-neΠ _ x x₁ x₂ x₃) (cast-Π x₄ x₅ x₆ x₇ x₈) _ =  no (λ (_ , _ , X) → let _ , neA , _ = ne~↓! x₅ in IE.Π≢ne neA (cast-cast-≡ X))

  not-diag~↑! Γ≡Δ (cast-neΠ Π x₄ x₅ x₆ x₇) (cast-ℕ x₂ x₃ x₄' x₅') _ = no (λ (_ , _ , X) → let _ , neA , _ = ne~↓! x₂ in IE.Π≢ne neA (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-neΠ Π x₄ x₅ x₆ x₇) (cast-neℕ x₂ x₃ x₄' x₅') _ = no (λ (_ , _ , X) → IE.ℕ≢Π! (sym (cast-cast-≡ X)))

  not-diag~↑! Γ≡Δ (cast-neΠ Π x₄' x₅' x₆' x₇') (cast-ℕΠ x₄ x₅ x₆ x₇) _ =
    no (λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → let _ , _ , neΠ = ne~↓! x in noNeℕ neΠ ;
            (_ , _ , cast-refl x x₁ x₂) → let _ , _ , neℕ = ne~↓! x in noNeΠ neℕ ;
            (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeΠ neℕ ;
            (_ , _ , cast-neΠ _ x x₁ x₂ x₃) → let _ , _ , neΠ = ne~↓! x in noNeℕ neΠ })

  not-diag~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (var-refl x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (app-cong x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (natrec-cong x₅ x₆ x₇ x₈) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (Emptyrec-cong x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (cast-ℕ x₅ x₆ x₇ x₈) _ =
      castℕ-refl-dec~ (stability~↓! (symConEq Γ≡Δ) x₅)
                      (λ neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                     in noNeΠ (PE.subst Neutral (PE.sym eA) neA))
                      (λ neA e → let _ , eA , _ = cast-PE-injectivity e in ℕ≢Π (PE.sym eA))
                      (λ e → let _ , _ , eB , _ = cast-PE-injectivity e
                                 _ , neB , _ = ne~↓! x₁
                             in noNeℕ (PE.subst Neutral eB neB))
  not-diag~↑! Γ≡Δ (cast-Π x B x₂ x₃ x₄) (cast-Πℕ x₅ x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in ℕ≢ne! neR (sym (cast-cast-≡ X)))
  not-diag~↑! Γ≡Δ (cast-Π x B x₂ x₃ x₄) (cast-ℕΠ x₅ x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in IE.Π≢ne neR (sym (cast-cast-≡ X)))
  not-diag~↑! Γ≡Δ (cast-Π x B x₂ x₃ x₄) (cast-ΠΠ%! x₅ x₆ x₇ x₈ x₉) _ =
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in IE.Π≢ne neR (sym (cast-cast-≡ X)))
  not-diag~↑! Γ≡Δ (cast-Π x B x₂ x₃ x₄) (cast-ΠΠ!% x₅ x₆ x₇ x₈ x₉) _ =
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in IE.Π≢ne neR (sym (cast-cast-≡ X)))
  not-diag~↑! Γ≡Δ (cast-Π x' B x₁' x₂' x₃') (cast-neℕ x₂ x₃ x₄ x₅) _ = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ  ;
                                                                                        (_ , _ , castℕ-refl' x x₁) → let _ , neℕ , _ = ne~↓! x₂ in noNeℕ neℕ })
  not-diag~↑! Γ≡Δ (cast-Π x' B x₁' x₂' x₃') (cast-neΠ x₂ x₃ x₄ x₅ x₆) _ = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })

  not-diag~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (var-refl x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (app-cong x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (natrec-cong x₅ x₆ x₇ x₈) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (Emptyrec-cong x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-ℕ B x₅ x₆ x₇) _ =
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B in ℕ≢ne! neR (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-Π x₄ B x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in ℕ≢ne! neR (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-ℕΠ x₄ x₅ x₆ x₇) _ =
    no (λ (_ , _ , X) → ℕ≢Π! (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-ΠΠ%! x₄ x₅ x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → ℕ≢Π! (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-ΠΠ!% x₄ x₅ x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → ℕ≢Π! (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-Πℕ x' x₁' x₂' x₃') (cast-neℕ x₂ x₃ x₄ x₅) _ = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ  ;
                                                                                      (_ , _ , castℕ-refl' x x₁) → let _ , neℕ , _ = ne~↓! x₂ in noNeℕ neℕ })
  not-diag~↑! Γ≡Δ (cast-Πℕ x' x₁' x₂' x₃') (cast-neΠ x₂ x₃ x₄ x₅ x₆) _ = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })

  not-diag~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (var-refl x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ })
  not-diag~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (app-cong x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ })
  not-diag~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (natrec-cong x₅ x₆ x₇ x₈) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ })
  not-diag~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (Emptyrec-cong x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ })
  not-diag~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-ℕ B x₅ x₆ x₇) _ =
      no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                          in IE.Π≢ne neR (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-Π x₄ B x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-Πℕ x₄ x₅ x₆ x₇) _ =
    no (λ (_ , _ , X) → ℕ≢Π! (sym (cast-cast-≡ X)))
  not-diag~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-ΠΠ%! x₄ x₅ x₆ x₇ x₈) _ =
    no (λ { (_ , _ , cast-cong () x₁ x₂ x₃ x₄) ;
            (_ , _ , cast-refl () x₁ x₂) ;
            (_ , _ , cast-refl' () x₁ x₂) ;
            (_ , _ , cast-neΠ x () x₂ x₃ x₄)})
  not-diag~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-ΠΠ!% x₄ x₅ x₆ x₇ x₈) _ =
    no (λ { (_ , _ , cast-cong () x₁ x₂ x₃ x₄) ;
            (_ , _ , cast-refl () x₁ x₂) ;
            (_ , _ , cast-refl' () x₁ x₂) ;
            (_ , _ , cast-neΠ x () x₂ x₃ x₄)})

  not-diag~↑! Γ≡Δ (cast-ℕΠ x' x₁' x₂' x₃') (cast-neℕ x₂ x₃ x₄ x₅) _ = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ  ;
                                                                                      (_ , _ , castℕ-refl' x x₁) → let _ , neℕ , _ = ne~↓! x₂ in noNeℕ neℕ })
  not-diag~↑! Γ≡Δ (cast-ℕΠ x' x₁' x₂' x₃') (cast-neΠ x₂ x₃ x₄ x₅ x₆) _ = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })


  not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (var-refl x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (app-cong x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (natrec-cong x₅ x₆ x₇ x₈) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (Emptyrec-cong x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-ℕ B x₅ x₆ x₇) _ =
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-Π A B x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-Πℕ A x₅ x₆ x₇) _ =
    no (λ (_ , _ , X) → ℕ≢Π! (sym (cast-cast-≡ X)))
  not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-ℕΠ x₅ x₆ x₇ x₈) _ =
    no (λ { (_ , _ , cast-cong () x₁ x₂ x₃ x₄) ;
            (_ , _ , cast-refl () x₁ x₂) ;
            (_ , _ , cast-refl' () x₁ x₂) ;
            (_ , _ , cast-neΠ x () x₂ x₃ x₄)})
  not-diag~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-ΠΠ!% A x₅ x₆ x₇ x₈) _ =
    no (λ { (_ , _ , cast-cong () x₁ x₂ x₃ x₄) ;
            (_ , _ , cast-refl () x₁ x₂) ;
            (_ , _ , cast-refl' () x₁ x₂)})
  not-diag~↑! Γ≡Δ (cast-ΠΠ%! x' x₁' x₂' x₃' x₄') (cast-neℕ x₂ x₃ x₄ x₅) _ = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ  ;
                                                                                      (_ , _ , castℕ-refl' x x₁) → let _ , neℕ , _ = ne~↓! x₂ in noNeℕ neℕ })
  not-diag~↑! Γ≡Δ (cast-ΠΠ%! x' x₁' x₂' x₃' x₄') (cast-neΠ x₂ x₃ x₄ x₅ x₆) _ = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })

  not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (var-refl x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (app-cong x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (natrec-cong x₅ x₆ x₇ x₈) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (Emptyrec-cong x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-ℕ B x₅ x₆ x₇) _ =
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-Π A B x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))
  not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-Πℕ A x₅ x₆ x₇) _ =
    no (λ (_ , _ , X) → ℕ≢Π! (sym (cast-cast-≡ X)))
  not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-ℕΠ x₅ x₆ x₇ x₈) _ =
    no (λ { (_ , _ , cast-cong () x₁ x₂ x₃ x₄) ;
            (_ , _ , cast-refl () x₁ x₂) ;
            (_ , _ , cast-refl' () x₁ x₂) ;
            (_ , _ , cast-neΠ x () x₂ x₃ x₄)})
  not-diag~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-ΠΠ%! A x₅ x₆ x₇ x₈) _ =
    no (λ { (_ , _ , cast-cong () x₁ x₂ x₃ x₄) ;
            (_ , _ , cast-refl () x₁ x₂) ;
            (_ , _ , cast-refl' () x₁ x₂)})
  not-diag~↑! Γ≡Δ (cast-ΠΠ!% x' x₁' x₂' x₃' x₄') (cast-neℕ x₂ x₃ x₄ x₅) _ = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ  ;
                                                                                      (_ , _ , castℕ-refl' x x₁) → let _ , neℕ , _ = ne~↓! x₂ in noNeℕ neℕ })
  not-diag~↑! Γ≡Δ (cast-ΠΠ!% x' x₁' x₂' x₃' x₄') (cast-neΠ x₂ x₃ x₄ x₅ x₆) _ = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })

-- data view~↑! : ∀ {k k' l l' R T Γ Δ lR lT}
--         → (e : Γ ⊢ k ~ k' ↑! R ^ lR)
--         → (e' : Δ ⊢ l ~ l' ↑! T ^ lT)
--         → Set
--   where
--     x-castrefl' : ∀ {Γ k k' R lR Δ A B t u e}
--       (k~k' : Γ ⊢ k ~ k' ↑! R ^ lR)
--       (A~A : Δ ⊢ B ~ A ↓! U ⁰ ^ next ⁰)
--       (t≡u : Δ ⊢ t [conv↓] u ∷ A ^ ι ⁰)
--       (⊢e' : Δ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ])
--       → view~↑! k~k' (cast-refl' A~A t≡u ⊢e')
--     castrefl'-x : ∀ {Γ A B t u e Δ l l' T lT}
--       (A~A : Γ ⊢ B ~ A ↓! U ⁰ ^ next ⁰)
--       (t≡u : Γ ⊢ t [conv↓] u ∷ A ^ ι ⁰)
--       (⊢e' : Γ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ])
--       (l~l' : Δ ⊢ l ~ l' ↑! T ^ lT)
--       → view~↑! (cast-refl' A~A t≡u ⊢e') l~l'
--     x-castℕrefl' : ∀ {Γ k k' R lR Δ t u e}
--       (k~k' : Γ ⊢ k ~ k' ↑! R ^ lR)
--       (t~u : Δ ⊢ t ~ u ↓! ℕ ^ ι ⁰)
--       (⊢e : Δ ⊢ e ∷ (Id (U ⁰) ℕ ℕ) ^ [ % , ι ⁰ ])
--       → view~↑! k~k' (castℕ-refl' t~u ⊢e)
--     castℕrefl'-x : ∀ {Γ t u e Δ l l' T lT}
--       (t~u : Γ ⊢ t ~ u ↓! ℕ ^ ι ⁰)
--       (⊢e : Γ ⊢ e ∷ (Id (U ⁰) ℕ ℕ) ^ [ % , ι ⁰ ])
--       (l~l' : Δ ⊢ l ~ l' ↑! T ^ lT)
--       → view~↑! (castℕ-refl' t~u ⊢e) l~l'
--     varrefl-diag : ∀ {Γ n n' A l Δ m m' B l'}
--       (⊢x : Γ ⊢ var n ∷ A ^ [ ! , l ])
--       (n≡n : n PE.≡ n')
--       (⊢y : Δ ⊢ var m ∷ B ^ [ ! , l' ])
--       (m≡m : m PE.≡ m')
--       → view~↑! (var-refl ⊢x n≡n) (var-refl ⊢y m≡m)
--     appcong-diag : ∀ {Γ k l t v F rF lF lG G lΠ Δ k' l' t' v' F' rF' lF' lG' G' lΠ'}
--       (x~x : Γ ⊢ k ~ l ↓! Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ ! ^ ι lΠ)
--       (t≡t : Γ ⊢ t [genconv↑] v ∷ F ^ [ rF , ι lF ])
--       (y~y : Δ ⊢ k' ~ l' ↓! Π F' ^ rF' ° lF' ▹ G' ° lG' ° lΠ' ^ ! ^ ι lΠ')
--       (u≡u : Δ ⊢ t' [genconv↑] v' ∷ F' ^ [ rF' , ι lF' ])
--       → view~↑! (app-cong x~x t≡t) (app-cong y~y u≡u)
