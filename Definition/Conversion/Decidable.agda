{-# OPTIONS --without-K  #-}

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

dec-relevance : ∀ (s s′ : 𝕊) → Dec (s PE.≡ s′)
dec-relevance 𝕥y 𝕥y = yes PE.refl
dec-relevance 𝕥y 𝕥y = no (λ ())
dec-relevance 𝕥y 𝕥y = no (λ ())
dec-relevance 𝕥y 𝕥y = yes PE.refl

-- Algorithmic equality of variables infers propositional equality.
strongVasEq : ∀ {m n A Γ} → Γ ⊢ var n ~ var m ↑𝕥y A → n PE.≡ m
strongVasEq (var-refl x x≡y) = x≡y

-- Helper function for decidability of applications.
dec~↑𝕥y-app : ∀ {k k₁ l l₁ F F₁ G G₁ sF B Γ Δ}
          → ⊢ Γ ≡ Δ
          → Γ ⊢ k ∷ Π F ⦂ sF ▹ G ⦂ 𝕥y
          → Δ ⊢ k₁ ∷ Π F₁ ⦂ sF ▹ G₁ ⦂ 𝕥y
          → Γ ⊢ k ~ k₁ ↓𝕥y B
          → Dec (Γ ⊢ l [conv↑] l₁ ∷ F ⦂ sF)
          → Dec (∃ λ A → Γ ⊢ k ∘ l ~ k₁ ∘ l₁ ↑𝕥y A)
dec~↑𝕥y-app Γ≡Δ k k₁ k~k₁ (yes p) =
  let whnfA , neK , neL = ne~↓𝕥y k~k₁
      ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓𝕥y k~k₁)
      ΠFG₁≡A = neTypeEq neK k ⊢k
      H , E , A≡ΠHE = Π≡A ΠFG₁≡A whnfA
      F≡H , sF≡sH , G₁≡E = injectivity (PE.subst (λ x → _ ⊢ _ ≡ x ⦂ _) A≡ΠHE ΠFG₁≡A)
  in  yes (E [ _ ] , app-cong (PE.subst (λ x → _ ⊢ _ ~ _ ↓𝕥y x) A≡ΠHE k~k₁)
                              (convConvTerm p F≡H))
dec~↑𝕥y-app Γ≡Δ k₂ k₃ k~k₁ (no ¬p) =
  no (λ { (_ , app-cong x x₁) →
      let whnfA , neK , neL = ne~↓𝕥y x
          ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓𝕥y x)
          ΠFG≡ΠF₂G₂ = neTypeEq neK k₂ ⊢k
          F≡F₂ , sF≡sF₂ , G≡G₂ = injectivity ΠFG≡ΠF₂G₂
          x₁′ = PE.subst (λ rx → _ ⊢ _ [conv↑] _ ∷ _ ⦂ sx) (PE.sym sF≡sF₂) x₁
      in  ¬p (convConvTerm x₁′ (sym F≡F₂)) })

easy~↓𝕥y : ∀ {Γ k l A} → Whnf A → Neutral k → Neutral l
        → Γ ⊢ k ∷ A ⦂ 𝕥y → Γ ⊢ l ∷ A ⦂ 𝕥y → Γ ⊢ k ~ l ↓𝕥y A
easy~↓𝕥y {A = A} whnfA neK neL ⊢k ⊢l = [~] A (id (syntacticTerm ⊢k)) whnfA (𝕥y~↑ neK neL ⊢k ⊢l)

mutual
  -- Decidability of algorithmic equality of neutrals.
  dec~↑𝕥y : ∀ {k l R T Γ Δ}
        → ⊢ Γ ≡ Δ
        → Γ ⊢ k ~ k ↑𝕥y R → Δ ⊢ l ~ l ↑𝕥y T
        → Dec (∃ λ A → Γ ⊢ k ~ l ↑𝕥y A)
  dec~↑𝕥y Γ≡Δ (var-refl {n} x₂ x≡y) (var-refl {m} x₃ x≡y₁) with n ≟ m
  dec~↑𝕥y Γ≡Δ (var-refl {n} x₂ x≡y) (var-refl .{n} x₃ x≡y₁) | yes PE.refl = yes (_ , var-refl x₂ x≡y₁)
  dec~↑𝕥y Γ≡Δ (var-refl x₂ x≡y) (var-refl x₃ x≡y₁) | no ¬p = no (λ { (A , k~l) → ¬p (strongVasEq k~l) })
  dec~↑𝕥y Γ≡Δ (var-refl x₁ x≡y) (app-cong x₂ x₃) = no (λ { (_ , ()) })
  dec~↑𝕥y Γ≡Δ (var-refl x₁ x≡y) (natrec-cong x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑𝕥y Γ≡Δ (var-refl x₁ x≡y) (Emptyrec-cong x₂ x₃) = no (λ { (_ , ()) })
  dec~↑𝕥y Γ≡Δ (app-cong x₁ x₂) (var-refl x₃ x≡y) = no (λ { (_ , ()) })
  dec~↑𝕥y Γ≡Δ (app-cong x x₁) (app-cong x₂ x₃)
        with dec~↓𝕥y Γ≡Δ x x₂
  dec~↑𝕥y Γ≡Δ (app-cong x x₁) (app-cong x₂ x₃) | yes (A , k~l) =
    let whnfA , neK , neL = ne~↓𝕥y k~l
        ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓𝕥y k~l)
        _ , ⊢l₁ , _ = syntacticEqTerm (soundness~↓𝕥y x)
        _ , ⊢l₂ , _ = syntacticEqTerm (soundness~↓𝕥y x₂)
        ΠFG≡A = neTypeEq neK ⊢l₁ ⊢k
        ΠF′G′≡A = neTypeEq neL (stabilityTerm (symConEq Γ≡Δ) ⊢l₂) ⊢l
        F≡F′ , sF≡sF′ , G≡G′ = injectivity (trans ΠFG≡A (sym ΠF′G′≡A))
        ⊢l₂′ = PE.subst (λ rx → _ ⊢ _ ∷ Π _ ⦂ sx ▹ _ ⦂ _) (PE.sym sF≡sF′) ⊢l₂
        x₃′ = PE.subst (λ rx → _ ⊢ _ [conv↑] _ ∷ _ ⦂ sx) (PE.sym sF≡sF′) x₃
    in  dec~↑𝕥y-app Γ≡Δ ⊢l₁ ⊢l₂′ k~l (decConv↑TermConv Γ≡Δ F≡F′ x₁ x₃′)
  dec~↑𝕥y Γ≡Δ (app-cong x x₁) (app-cong x₂ x₃) | no ¬p =
    no (λ { (_ , app-cong x₄ x₅) → ¬p (_ , x₄) })
  dec~↑𝕥y Γ≡Δ (app-cong x x₁) (natrec-cong x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑𝕥y Γ≡Δ (app-cong x x₁) (Emptyrec-cong x₂ x₃) = no (λ { (_ , ()) })
  dec~↑𝕥y Γ≡Δ (natrec-cong x₁ x₂ x₃ x₄) (var-refl x₅ x≡y) = no (λ { (_ , ()) })
  dec~↑𝕥y Γ≡Δ (natrec-cong x x₁ x₂ x₃) (app-cong x₄ x₅) = no (λ { (_ , ()) })
  dec~↑𝕥y Γ≡Δ (Emptyrec-cong x₁ x₂) (var-refl x₅ x≡y) = no (λ { (_ , ()) })
  dec~↑𝕥y Γ≡Δ (Emptyrec-cong x x₁) (app-cong x₄ x₅) = no (λ { (_ , ()) })
  dec~↑𝕥y Γ≡Δ (Emptyrec-cong x x₁) (natrec-cong _ _ _ _) = no (λ { (_ , ()) })
  dec~↑𝕥y Γ≡Δ (natrec-cong _ _ _ _) (Emptyrec-cong x x₁) = no (λ { (_ , ()) })
  dec~↑𝕥y Γ≡Δ (natrec-cong x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇)
        with decConv↑ (Γ≡Δ ∙ refl (ℕⱼ (wfEqTerm (soundness~↓𝕥y x₃)))) x x₄
  dec~↑𝕥y Γ≡Δ (natrec-cong x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇) | yes p
        with decConv↑TermConv Γ≡Δ
               (substTypeEq (soundnessConv↑ p)
                            (refl (zeroⱼ (wfEqTerm (soundness~↓𝕥y x₃)))))
               x₁ x₅
           | decConv↑TermConv Γ≡Δ (sucCong (soundnessConv↑ p)) x₂ x₆
           | dec~↓𝕥y Γ≡Δ x₃ x₇
  dec~↑𝕥y Γ≡Δ (natrec-cong x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇)
        | yes p | yes p₁ | yes p₂ | yes (A , k~l) =
    let whnfA , neK , neL = ne~↓𝕥y k~l
        ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓𝕥y k~l)
        _ , ⊢l∷ℕ , _ = syntacticEqTerm (soundness~↓𝕥y x₃)
        ⊢ℕ≡A = neTypeEq neK ⊢l∷ℕ ⊢k
        A≡ℕ = ℕ≡A ⊢ℕ≡A whnfA
        k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓𝕥y x) A≡ℕ k~l
    in  yes (_ , natrec-cong p p₁ p₂ k~l′)
  dec~↑𝕥y Γ≡Δ (natrec-cong x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇)
        | yes p | yes p₁ | yes p₂ | no ¬p =
    no (λ { (_ , natrec-cong x₈ x₉ x₁₀ x₁₁) → ¬p (_ , x₁₁) })
  dec~↑𝕥y Γ≡Δ (natrec-cong x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇)
        | yes p | yes p₁ | no ¬p | s =
    no (λ { (_ , natrec-cong x₈ x₉ x₁₀ x₁₁) → ¬p x₁₀ })
  dec~↑𝕥y Γ≡Δ (natrec-cong x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇)
        | yes p | no ¬p | w | s =
    no (λ { (_ , natrec-cong x₈ x₉ x₁₀ x₁₁) → ¬p x₉ })
  dec~↑𝕥y Γ≡Δ (natrec-cong x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇) | no ¬p =
    no (λ { (_ , natrec-cong x₈ x₉ x₁₀ x₁₁) → ¬p x₈ })

  dec~↑𝕥y Γ≡Δ (Emptyrec-cong x x₁) (Emptyrec-cong x₄ x₅)
        with decConv↑ Γ≡Δ x x₄
  dec~↑𝕥y Γ≡Δ (Emptyrec-cong x k~k) (Emptyrec-cong x₄ l~l) | yes p =
    let _ , neK , _ = ne~↓𝕥y k~k
        _ , neL , _ = ne~↓𝕥y l~l
        _ , ⊢k , _ = syntacticEqTerm (soundness~↓𝕥y k~k)
        _ , ⊢l , _ = syntacticEqTerm (soundness~↓𝕥y l~l)
        ⊢Γ = wfTerm ⊢k
    in  yes (_ , Emptyrec-cong p ([~] Empty (id (Emptyⱼ ⊢Γ)) Emptyₙ
                               (𝕥y~↑ neK neL ⊢k (stabilityTerm (symConEq Γ≡Δ) ⊢l))))
  dec~↑𝕥y Γ≡Δ (Emptyrec-cong x x₁) (Emptyrec-cong x₄ x₅) | no ¬p =
    no (λ { (_ , Emptyrec-cong a b) → ¬p a })

  -- Decidability of algorithmic equality of neutrals with types in WHNF.
  dec~↓𝕥y : ∀ {k l R T Γ Δ}
        → ⊢ Γ ≡ Δ
        → Γ ⊢ k ~ k ↓𝕥y R → Δ ⊢ l ~ l ↓𝕥y T
        → Dec (∃ λ A → Γ ⊢ k ~ l ↓𝕥y A)
  dec~↓𝕥y Γ≡Δ ([~] A D whnfB k~l) ([~] A₁ D₁ whnfB₁ k~l₁)
        with dec~↑𝕥y Γ≡Δ k~l k~l₁
  dec~↓𝕥y Γ≡Δ ([~] A D whnfB k~l) ([~] A₁ D₁ whnfB₁ k~l₁)
        | yes (B , k~l₂) =
    let ⊢B , _ , _ = syntacticEqTerm (soundness~↑𝕥y k~l₂)
        C , whnfC , D′ = whNorm ⊢B
    in  yes (C , [~] B (red D′) whnfC k~l₂)
  dec~↓𝕥y Γ≡Δ ([~] A D whnfB k~l) ([~] A₁ D₁ whnfB₁ k~l₁)
        | no ¬p =
    no (λ { (A₂ , [~] A₃ D₂ whnfB₂ k~l₂) → ¬p (A₃ , k~l₂) })

  -- Decidability of algorithmic equality of types.
  decConv↑ : ∀ {A B s Γ Δ}
           → ⊢ Γ ≡ Δ
           → Γ ⊢ A [conv↑] A ⦂ s → Δ ⊢ B [conv↑] B ⦂ s
           → Dec (Γ ⊢ A [conv↑] B ⦂ s)
  decConv↑ Γ≡Δ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′)
               ([↑] A″ B″ D₁ D″ whnfA″ whnfB″ A′<>B″)
           rewrite whrDet* (D , whnfA′) (D′ , whnfB′)
                 | whrDet* (D₁ , whnfA″) (D″ , whnfB″)
           with decConv↓ Γ≡Δ A′<>B′ A′<>B″
  decConv↑ Γ≡Δ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′)
               ([↑] A″ B″ D₁ D″ whnfA″ whnfB″ A′<>B″) | yes p =
    yes ([↑] B′ B″ D′ (stabilityRed* (symConEq Γ≡Δ) D″) whnfB′ whnfB″ p)
  decConv↑ {s = s} Γ≡Δ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′)
               ([↑] A″ B″ D₁ D″ whnfA″ whnfB″ A′<>B″) | no ¬p =
    no (λ { ([↑] A‴ B‴ D₂ D‴ whnfA‴ whnfB‴ A′<>B‴) →
        let A‴≡B′  = whrDet* (D₂ , whnfA‴) (D′ , whnfB′)
            B‴≡B″ = whrDet* (D‴ , whnfB‴)
                                (stabilityRed* (symConEq Γ≡Δ) D″ , whnfB″)
        in  ¬p (PE.subst₂ (λ x y → _ ⊢ x [conv↓] y ⦂ s) A‴≡B′ B‴≡B″ A′<>B‴) })

  -- Decidability of algorithmic equality of types in WHNF.
  decConv↓ : ∀ {A B s Γ Δ}
           → ⊢ Γ ≡ Δ
           → Γ ⊢ A [conv↓] A ⦂ s → Δ ⊢ B [conv↓] B ⦂ s
           → Dec (Γ ⊢ A [conv↓] B ⦂ s)
  decConv↓ Γ≡Δ (U-refl {s = s} _ x) (U-refl {s = s′} _ x₁) with dec-relevance s s′
  ... | yes p = yes (U-refl p x)
  ... | no ¬p = no λ p → ¬p (Uinjectivity (soundnessConv↓ p))
  decConv↓ Γ≡Δ (U-refl e x) (ℕ-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
--  decConv↓ Γ≡Δ (U-refl e x) (Empty-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ Γ≡Δ (U-refl e x) (ne x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓𝕥y x₁
               in  ⊥-elim (IE.U≢ne𝕥y neK (soundnessConv↓ x₂)))
  decConv↓ Γ≡Δ (U-refl e x) (Π-cong e₁ x₁ x₂ x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ Γ≡Δ (ℕ-refl x) (U-refl e x₁) = no (λ { (ne ([~] A D whnfB ())) })
--  decConv↓ Γ≡Δ (Empty-refl x) (U-refl e x₁) = no (λ { (ne ([~] A D whnfB ())) })
--  decConv↓ Γ≡Δ (Empty-refl x) (ℕ-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
--  decConv↓ Γ≡Δ (ℕ-refl x) (Empty-refl x₁) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ Γ≡Δ (ℕ-refl x) (ℕ-refl x₁) = yes (ℕ-refl x)
  decConv↓ Γ≡Δ (Empty-refl x) (Empty-refl x₁) = yes (Empty-refl x)
  decConv↓ Γ≡Δ (ℕ-refl x) (ne x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓𝕥y x₁
               in  ⊥-elim (IE.ℕ≢ne𝕥y neK (soundnessConv↓ x₂)))
  decConv↓ Γ≡Δ (Empty-refl x) (ne x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓𝕥y x₁
               in  ⊥-elim (IE.Empty≢ne𝕥y neK (soundnessConv↓ x₂)))
  decConv↓ Γ≡Δ (ℕ-refl x) (Π-cong e x₁ x₂ x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ Γ≡Δ (Empty-refl x) (Π-cong e x₁ x₂ x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ Γ≡Δ (ne x) (U-refl e x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓𝕥y x
               in  ⊥-elim (IE.U≢ne𝕥y neK (sym (soundnessConv↓ x₂))))
  decConv↓ Γ≡Δ (ne x) (ℕ-refl x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓𝕥y x
               in  ⊥-elim (IE.ℕ≢ne𝕥y neK (sym (soundnessConv↓ x₂))))
  decConv↓ Γ≡Δ (ne x) (Empty-refl x₁) =
    no (λ x₂ → let whnfA , neK , neL = ne~↓𝕥y x
               in  ⊥-elim (IE.Empty≢ne𝕥y neK (sym (soundnessConv↓ x₂))))
  decConv↓ Γ≡Δ (ne x) (ne x₁) with dec~↓𝕥y Γ≡Δ x x₁
  decConv↓ Γ≡Δ (ne x) (ne x₁) | yes (A , k~l) =
    let whnfA , neK , neL = ne~↓𝕥y k~l
        ⊢A , ⊢k , _ = syntacticEqTerm (soundness~↓𝕥y k~l)
        _ , ⊢k∷U , _ = syntacticEqTerm (soundness~↓𝕥y x)
        ⊢U≡A = neTypeEq neK ⊢k∷U ⊢k
        A≡U = U≡A ⊢U≡A
        k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓𝕥y x) A≡U k~l
    in  yes (ne k~l′)
  decConv↓ {s = s} Γ≡Δ (ne x) (ne x₁) | no ¬p =
    no (λ x₂ → ¬p (Univ s , decConv↓-ne x₂ x))
  decConv↓ Γ≡Δ (ne x) (Π-cong e x₁ x₂ x₃) =
    no (λ x₄ → let whnfA , neK , neL = ne~↓𝕥y x
               in  ⊥-elim (IE.Π≢ne neK (sym (soundnessConv↓ x₄))))
  decConv↓ Γ≡Δ (Π-cong e x x₁ x₂) (U-refl e₁ x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ Γ≡Δ (Π-cong e x x₁ x₂) (ℕ-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ Γ≡Δ (Π-cong e x x₁ x₂) (Empty-refl x₃) = no (λ { (ne ([~] A D whnfB ())) })
  decConv↓ Γ≡Δ (Π-cong e x x₁ x₂) (ne x₃) =
    no (λ x₄ → let whnfA , neK , neL = ne~↓𝕥y x₃
               in  ⊥-elim (IE.Π≢ne neK (soundnessConv↓ x₄)))
  decConv↓ Γ≡Δ (Π-cong {sF = sF} _ x x₁ x₂) (Π-cong {sF = sF₁} _ x₃ x₄ x₅) with dec-relevance sF sF₁
  decConv↓ Γ≡Δ (Π-cong _ x x₁ x₂) (Π-cong _ x₃ x₄ x₅) | no sF≢sF₁ = no (λ e → sF≢sF₁ let _ , req , _ = (injectivity (soundnessConv↓ e)) in req)
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
  decConv↓-ne : ∀ {A B s Γ}
              → Γ ⊢ A [conv↓] B ⦂ s
              → Γ ⊢ A ~ A ↓𝕥y Univ s
              → Γ ⊢ A ~ B ↓𝕥y Univ s
  decConv↓-ne (U-refl PE.refl x) A~A = A~A
  decConv↓-ne (ℕ-refl x) A~A = A~A
  decConv↓-ne (Empty-refl x) A~A = A~A
  decConv↓-ne (ne x) A~A = x
  decConv↓-ne (Π-cong e x x₁ x₂) ([~] A D whnfB ())

  -- Decidability of algorithmic equality of terms.
  decConv↑Term : ∀ {t u A s Γ Δ}
               → ⊢ Γ ≡ Δ
               → Γ ⊢ t [conv↑] t ∷ A ⦂ s → Δ ⊢ u [conv↑] u ∷ A ⦂ s
               → Dec (Γ ⊢ t [conv↑] u ∷ A ⦂ s)
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
  decConv↑Term {s = s} Γ≡Δ ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
                   ([↑]ₜ B₁ t″ u″ D₁ d₁ d″ whnfB₁ whnft″ whnfu″ t<>u₁)
               | no ¬p =
    no (λ { ([↑]ₜ B₂ t‴ u‴ D₂ d₂ d‴ whnfB₂ whnft‴ whnfu‴ t<>u₂) →
        let B₂≡B₁ = whrDet* (D₂ , whnfB₂)
                             (stabilityRed* (symConEq Γ≡Δ) D₁ , whnfB₁)
            t‴≡u′ = whrDet*Term (d₂ , whnft‴)
                              (PE.subst (λ x → _ ⊢ _ ⇒* _ ∷ x ⦂ _) (PE.sym B₂≡B₁) d′
                              , whnfu′)
            u‴≡u″ = whrDet*Term (d‴ , whnfu‴)
                               (PE.subst (λ x → _ ⊢ _ ⇒* _ ∷ x ⦂ _)
                                         (PE.sym B₂≡B₁)
                                         (stabilityRed*Term (symConEq Γ≡Δ) d″)
                               , whnfu″)
        in  ¬p (PE.subst₃ (λ x y z → _ ⊢ x [conv↓] y ∷ z ⦂ s)
                          t‴≡u′ u‴≡u″ B₂≡B₁ t<>u₂) })

  -- Helper function for decidability for neutrals of natural number type.
  decConv↓Term-ℕ-ins : ∀ {t u Γ}
                     → Γ ⊢ t [conv↓] u ∷ ℕ ⦂ 𝕥y
                     → Γ ⊢ t ~ t ↓𝕥y ℕ
                     → Γ ⊢ t ~ u ↓𝕥y ℕ
  decConv↓Term-ℕ-ins (ℕ-ins x) t~t = x
  decConv↓Term-ℕ-ins (ne-ins x x₁ () x₃) t~t
  decConv↓Term-ℕ-ins (zero-refl x) ([~] A D whnfB ())
  decConv↓Term-ℕ-ins (suc-cong x) ([~] A D whnfB ())

  -- empty neutrals (this will change XD)
  decConv↓Term-Empty-ins : ∀ {t u Γ}
                     → Γ ⊢ t [conv↓] u ∷ Empty ⦂ 𝕥y
                     → Γ ⊢ t ~ t ↓𝕥y Empty
                     → Γ ⊢ t ~ u ↓𝕥y Empty
  decConv↓Term-Empty-ins (Empty-ins x) t~t = x
  decConv↓Term-Empty-ins (ne-ins x x₁ () x₃) t~t

  -- Helper function for decidability for neutrals of a neutral type.
  decConv↓Term-ne-ins : ∀ {t u A Γ}
                      → Neutral A
                      → Γ ⊢ t [conv↓] u ∷ A ⦂ 𝕥y
                      → ∃ λ B → Γ ⊢ t ~ u ↓𝕥y B
  decConv↓Term-ne-ins () (ℕ-ins x)
  decConv↓Term-ne-ins neA (ne-ins x x₁ x₂ (~↓𝕥y x₃)) = _ , x₃
  decConv↓Term-ne-ins () (univ x x₁ x₂)
  decConv↓Term-ne-ins () (zero-refl x)
  decConv↓Term-ne-ins () (suc-cong x)
  decConv↓Term-ne-ins () (η-eq x x₁ x₂ x₃ x₄ x₅)

  -- Helper function for decidability for impossibility of terms not being equal
  -- as neutrals when they are equal as terms and the first is a neutral.
  decConv↓Term-ℕ : ∀ {t u Γ}
                 → Γ ⊢ t [conv↓] u ∷ ℕ ⦂ 𝕥y
                 → Γ ⊢ t ~ t ↓𝕥y ℕ
                 → ¬ (Γ ⊢ t ~ u ↓𝕥y ℕ)
                 → ⊥
  decConv↓Term-ℕ (ℕ-ins x) t~t ¬u~u = ¬u~u x
  decConv↓Term-ℕ (ne-ins x x₁ () x₃) t~t ¬u~u
  decConv↓Term-ℕ (zero-refl x) ([~] A D whnfB ()) ¬u~u
  decConv↓Term-ℕ (suc-cong x) ([~] A D whnfB ()) ¬u~u

  -- Decidability of algorithmic equality of terms in WHNF.
  decConv↓Term : ∀ {t u A s Γ Δ}
               → ⊢ Γ ≡ Δ
               → Γ ⊢ t [conv↓] t ∷ A ⦂ s → Δ ⊢ u [conv↓] u ∷ A ⦂ s
               → Dec (Γ ⊢ t [conv↓] u ∷ A ⦂ s)
  decConv↓Term Γ≡Δ (ℕ-ins x) (ℕ-ins x₁) with dec~↓𝕥y Γ≡Δ x x₁
  decConv↓Term Γ≡Δ (ℕ-ins x) (ℕ-ins x₁) | yes (A , k~l) =
    let whnfA , neK , neL = ne~↓𝕥y k~l
        ⊢A , ⊢k , ⊢l = syntacticEqTerm (soundness~↓𝕥y k~l)
        _ , ⊢l∷ℕ , _ = syntacticEqTerm (soundness~↓𝕥y x)
        ⊢ℕ≡A = neTypeEq neK ⊢l∷ℕ ⊢k
        A≡ℕ = ℕ≡A ⊢ℕ≡A whnfA
        k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓𝕥y x) A≡ℕ k~l
    in  yes (ℕ-ins k~l′)
  decConv↓Term Γ≡Δ (ℕ-ins x) (ℕ-ins x₁) | no ¬p =
    no (λ x₂ → ¬p (ℕ , decConv↓Term-ℕ-ins x₂ x))
  decConv↓Term Γ≡Δ (Empty-ins t~t) (Empty-ins u~u) =
    let _ , neT , _ = ne~↓𝕥y t~t
        _ , neU , _ = ne~↓𝕥y u~u
        _ , ⊢t , _ = syntacticEqTerm (soundness~↓𝕥y t~t)
        _ , ⊢u , _ = syntacticEqTerm (soundness~↓𝕥y u~u)
    in yes (Empty-ins (easy~↓𝕥y Emptyₙ neT neU ⊢t (stabilityTerm (symConEq Γ≡Δ) ⊢u)))
  decConv↓Term Γ≡Δ (ℕ-ins x) (ne-ins x₁ x₂ () x₄)
  decConv↓Term Γ≡Δ (Empty-ins x) (ne-ins x₁ x₂ () x₄)
  decConv↓Term Γ≡Δ (ℕ-ins x) (zero-refl x₁) =
    no (λ x₂ → decConv↓Term-ℕ x₂ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (ℕ-ins x) (suc-cong x₁) =
    no (λ x₂ → decConv↓Term-ℕ x₂ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (ℕ-ins x₄)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (Empty-ins x₄)
  decConv↓Term Γ≡Δ (ne-ins x x₁ x₂ (~↓𝕥y x₃)) (ne-ins x₄ x₅ x₆ (~↓𝕥y x₇))
               with dec~↓𝕥y Γ≡Δ x₃ x₇
  decConv↓Term Γ≡Δ (ne-ins x x₁ x₂ x₃) (ne-ins x₄ x₅ x₆ x₇) | yes (A , k~l) =
    yes (ne-ins x₁ (stabilityTerm (symConEq Γ≡Δ) x₄) x₆ (~↓𝕥y k~l))
  decConv↓Term Γ≡Δ (ne-ins x x₁ x₂ x₃) (ne-ins x₄ x₅ x₆ x₇) | no ¬p =
    no (λ x₈ → ¬p (decConv↓Term-ne-ins x₆ x₈))
  decConv↓Term Γ≡Δ (ne-ins ⊢t _ neA (~↓𝕥y t~t)) (ne-ins ⊢u _ _ (~↓𝕥y u~u)) =
    let whnfM , neT , _ = ne~↓𝕥y t~t
        _ , neU , _ = ne~↓𝕥y u~u
        ⊢M , ⊢t∷M , _ = syntacticEqTerm (soundness~↓𝕥y t~t)
        Γ⊢u = stabilityTerm (symConEq Γ≡Δ) ⊢u
        A≡M = neTypeEq neT ⊢t ⊢t∷M
    in yes (ne-ins ⊢t Γ⊢u neA
                   (~↓𝕥y ([~] _ (id ⊢M) whnfM
                             (𝕥y~↑ neT neU ⊢t∷M (conv Γ⊢u A≡M)))))
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
  decConv↑TermConv : ∀ {t u A B s Γ Δ}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B ⦂ s
                → Γ ⊢ t [conv↑] t ∷ A ⦂ s
                → Δ ⊢ u [conv↑] u ∷ B ⦂ s
                → Dec (Γ ⊢ t [conv↑] u ∷ A ⦂ s)
  decConv↑TermConv Γ≡Δ A≡B t u =
    decConv↑Term Γ≡Δ t (convConvTerm u (stabilityEq Γ≡Δ (sym A≡B)))
