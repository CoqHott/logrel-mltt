{-# OPTIONS --safe #-}

module Definition.Conversion.Symmetry where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Conversion
open import Definition.Conversion.Stability
open import Definition.Conversion.Soundness
open import Definition.Conversion.Conversion
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Equality
open import Definition.Typed.Consequences.Reduction
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.Substitution
open import Definition.Typed.Consequences.SucCong

open import Tools.Product
import Tools.PropositionalEquality as PE


mutual
  -- Symmetry of algorithmic equality of neutrals
  sym~↑! : ∀ {t u A Γ Δ l} → ⊢ Γ ≡ Δ
        → Γ ⊢ t ~ u ↑! A ^ l
        → ∃ λ B → Γ ⊢ A ≡ B ^ [ ! , l ]  × Δ ⊢ u ~ t ↑! B ^ l
  sym~↑! Γ≡Δ (var-refl x x≡y) =
    let ⊢A = syntacticTerm x
    in  _ , refl ⊢A
     ,  var-refl (PE.subst (λ y → _ ⊢ var y ∷ _ ^ _) x≡y (stabilityTerm Γ≡Δ x))
                 (PE.sym x≡y)
  sym~↑! Γ≡Δ (app-cong {rF = !} t~u x) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        B , whnfB , A≡B , u~t = sym~↓! Γ≡Δ t~u
        F′ , G′ , ΠF′G′≡B = Π≡A A≡B whnfB
        F≡F′ , rF≡rF′ , lF≡lF' , lG≡lG' , G≡G′ = injectivity (PE.subst (λ x → _ ⊢ _ ≡ x ^ _) ΠF′G′≡B A≡B)
    in  _ , substTypeEq G≡G′ (soundnessConv↑Term x)
    ,   app-cong (PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) ΠF′G′≡B u~t)
                 (convConvTerm (symConv↑Term Γ≡Δ x) (stabilityEq Γ≡Δ F≡F′))
  sym~↑! Γ≡Δ (app-cong {rF = %} t~u x) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        B , whnfB , A≡B , u~t = sym~↓! Γ≡Δ t~u
        F′ , G′ , ΠF′G′≡B = Π≡A A≡B whnfB
        F≡F′ , rF≡rF′ , lF≡lF' , lG≡lG' , G≡G′ = injectivity (PE.subst (λ x → _ ⊢ _ ≡ x ^ _) ΠF′G′≡B A≡B)
    in  _ , substTypeEq G≡G′ (proj₂ (proj₂ (soundness~↑% x)))
    ,   app-cong (PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) ΠF′G′≡B u~t)
                 (sym~↑% Γ≡Δ (conv~↑% x (stabilityEq (reflConEq ⊢Γ) F≡F′)))
  sym~↑! Γ≡Δ (natrec-cong x x₁ x₂ t~u) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        B , whnfB , A≡B , u~t = sym~↓! Γ≡Δ t~u
        B≡ℕ = ℕ≡A A≡B whnfB
        F≡G = stabilityEq (Γ≡Δ ∙ refl (univ (ℕⱼ ⊢Γ))) (soundnessConv↑ x)
        F[0]≡G[0] = substTypeEq F≡G (refl (zeroⱼ ⊢Δ))
    in  _ , substTypeEq (soundnessConv↑ x) (soundness~↓! t~u)
    ,   natrec-cong (symConv↑ (Γ≡Δ ∙ (refl (univ (ℕⱼ ⊢Γ)))) x)
                    (convConvTerm (symConv↑Term Γ≡Δ x₁) F[0]≡G[0])
                    (convConvTerm (symConv↑Term Γ≡Δ x₂) (sucCong F≡G))
                    (PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) B≡ℕ u~t)
  sym~↑! Γ≡Δ (Emptyrec-cong x t~u) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        u~t = sym~↑% Γ≡Δ t~u
        -- F≡G = stabilityEq Γ≡Δ (soundnessConv↑ x)
    in  _ , soundnessConv↑ x
    , Emptyrec-cong (symConv↑ Γ≡Δ x) u~t
  sym~↑! Γ≡Δ (Id-cong X x x₁) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        B , whnfB , A≡B , u~t = sym~↓! Γ≡Δ X
        U≡B = U≡A-whnf A≡B whnfB
        A'≡A = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) U≡B u~t
    in _ , refl (Ugenⱼ ⊢Γ) , Id-cong A'≡A
                                     (convConvTerm (symConv↑Term Γ≡Δ x) (univ (soundness~↓! (stability~↓! Γ≡Δ X))))
                                     (convConvTerm (symConv↑Term Γ≡Δ x₁) (univ (soundness~↓! (stability~↓! Γ≡Δ X))))
  sym~↑! Γ≡Δ (Id-ℕ X x) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        B , whnfB , A≡B , u~t = sym~↓! Γ≡Δ X
        U≡B = ℕ≡A A≡B whnfB
        A'≡A = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) U≡B u~t
    in _ , refl (Ugenⱼ ⊢Γ) , Id-ℕ A'≡A (symConv↑Term Γ≡Δ x) 
  sym~↑! Γ≡Δ (Id-ℕ0 X) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        B , whnfB , A≡B , u~t = sym~↓! Γ≡Δ X
        U≡B = ℕ≡A A≡B whnfB
        A'≡A = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) U≡B u~t
    in _ , refl (Ugenⱼ ⊢Γ) , Id-ℕ0 A'≡A
  sym~↑! Γ≡Δ (Id-ℕS x X) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        B , whnfB , A≡B , u~t = sym~↓! Γ≡Δ X
        U≡B = ℕ≡A A≡B whnfB
        A'≡A = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) U≡B u~t
    in _ , refl (Ugenⱼ ⊢Γ) , Id-ℕS (symConv↑Term Γ≡Δ x) A'≡A
  sym~↑! Γ≡Δ (Id-U X x) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        B , whnfB , A≡B , u~t = sym~↓! Γ≡Δ X
        U≡B = U≡A-whnf A≡B whnfB
        A'≡A = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) U≡B u~t
    in _ , refl (Ugenⱼ ⊢Γ) , Id-U A'≡A (symConv↑Term Γ≡Δ x)
  sym~↑! Γ≡Δ (Id-Uℕ X) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        B , whnfB , A≡B , u~t = sym~↓! Γ≡Δ X
        U≡B = U≡A-whnf A≡B whnfB
        A'≡A = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) U≡B u~t
    in _ , refl (Ugenⱼ ⊢Γ) , Id-Uℕ A'≡A
  sym~↑! Γ≡Δ (Id-UΠ x X) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        B , whnfB , A≡B , u~t = sym~↓! Γ≡Δ X
        U≡B = U≡A-whnf A≡B whnfB
        A'≡A = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) U≡B u~t
    in _ , refl (Ugenⱼ ⊢Γ) , Id-UΠ (symConv↑Term Γ≡Δ x) A'≡A 
  sym~↑! Γ≡Δ (cast-cong X x x₁ x₂ x₃) =
      let U , whnfU , U≡U' , A'~A = sym~↓! Γ≡Δ X
          B'~B = symConv↑Term Γ≡Δ x
          U≡B = U≡A-whnf U≡U' whnfU
          A'≡A = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) U≡B A'~A
      in
          _ , univ (soundnessConv↑Term x), cast-cong A'≡A B'~B
                                                     (convConvTerm (symConv↑Term Γ≡Δ x₁) (univ (soundness~↓! (stability~↓! Γ≡Δ X))))
                                                     (stabilityTerm Γ≡Δ x₃) (stabilityTerm Γ≡Δ x₂)
  sym~↑! Γ≡Δ (cast-ℕ X x x₁ x₂) =
      let U , whnfU , U≡U' , A'~A = sym~↓! Γ≡Δ X
          B'~B = symConv↑Term Γ≡Δ x
          U≡B = U≡A-whnf U≡U' whnfU
          A'≡A = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) U≡B A'~A
      in _ , univ (soundness~↓! X) , cast-ℕ A'≡A (symConv↑Term Γ≡Δ x) (stabilityTerm Γ≡Δ x₂) (stabilityTerm Γ≡Δ x₁)
  sym~↑! Γ≡Δ (cast-ℕℕ X x x₁) =
      let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
          N , whnfN , N≡N' , t'~t = sym~↓! Γ≡Δ X
          ℕ≡B = ℕ≡A N≡N' whnfN
          t'≡t = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) ℕ≡B t'~t
      in _ , refl (univ (ℕⱼ ⊢Γ)) , cast-ℕℕ t'≡t (stabilityTerm Γ≡Δ x₁) (stabilityTerm Γ≡Δ x)
  sym~↑! Γ≡Δ (cast-Π x X x₁ x₂ x₃) =
      let U , whnfU , U≡U' , A'~A = sym~↓! Γ≡Δ X
          B'~B = symConv↑Term Γ≡Δ x
          U≡B = U≡A-whnf U≡U' whnfU
          A'≡A = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) U≡B A'~A
      in _ , univ (soundness~↓! X) , cast-Π B'~B A'≡A
                                            (convConvTerm (symConv↑Term Γ≡Δ x₁) (univ (soundnessConv↑Term (stabilityConv↑Term Γ≡Δ x))))
                                            (stabilityTerm Γ≡Δ x₃) (stabilityTerm Γ≡Δ x₂)
  sym~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) =
      let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
      in _ , refl (univ (ℕⱼ ⊢Γ)) , cast-Πℕ (symConv↑Term Γ≡Δ x)
                                           (convConvTerm (symConv↑Term Γ≡Δ x₁) (univ (soundnessConv↑Term (stabilityConv↑Term Γ≡Δ x))))
                                           (stabilityTerm Γ≡Δ x₃) (stabilityTerm Γ≡Δ x₂)
  sym~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) = _ , univ (soundnessConv↑Term x) , cast-ℕΠ (symConv↑Term Γ≡Δ x) (symConv↑Term Γ≡Δ x₁)
                                                                              (stabilityTerm Γ≡Δ x₃) (stabilityTerm Γ≡Δ x₂)
  sym~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) = _ , univ (soundnessConv↑Term x₁) ,
                                         cast-ΠΠ%! (symConv↑Term Γ≡Δ x) (symConv↑Term Γ≡Δ x₁)
                                                   (convConvTerm (symConv↑Term Γ≡Δ x₂) (univ (soundnessConv↑Term (stabilityConv↑Term Γ≡Δ x))))
                                                   (stabilityTerm Γ≡Δ x₄) (stabilityTerm Γ≡Δ x₃) 
  sym~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) = _ , univ (soundnessConv↑Term x₁) ,
                                         cast-ΠΠ!% (symConv↑Term Γ≡Δ x) (symConv↑Term Γ≡Δ x₁)
                                                   (convConvTerm (symConv↑Term Γ≡Δ x₂) (univ (soundnessConv↑Term (stabilityConv↑Term Γ≡Δ x))))
                                                   (stabilityTerm Γ≡Δ x₄) (stabilityTerm Γ≡Δ x₃) 

  sym~↑% : ∀ {t u A Γ Δ l} → ⊢ Γ ≡ Δ
         → Γ ⊢ t ~ u ↑% A ^ l
         → Δ ⊢ u ~ t ↑% A ^ l
  sym~↑% Γ≡Δ (%~↑ ⊢k ⊢l) = %~↑ (stabilityTerm Γ≡Δ ⊢l) (stabilityTerm Γ≡Δ ⊢k)

  sym~↑ : ∀ {t u A rA Γ Δ l} → ⊢ Γ ≡ Δ
        → Γ ⊢ t ~ u ↑ A ^ [ rA , l ]
        → ∃ λ B → Γ ⊢ A ≡ B ^ [ rA , l ] × Δ ⊢ u ~ t ↑ B ^ [ rA , l ]
  sym~↑ Γ≡Δ (~↑! x) =
    let B , A≡B , x′ = sym~↑! Γ≡Δ x
    in B , A≡B , ~↑! x′
  sym~↑ {A = A} Γ≡Δ (~↑% x) =
    let x′ = sym~↑% Γ≡Δ x
        ⊢A , _ , _ = syntacticEqTerm (proj₂ (proj₂ (soundness~↑% x)))
    in A , refl ⊢A , ~↑% x′

  -- Symmetry of algorithmic equality of neutrals of types in WHNF.
  sym~↓! : ∀ {t u A Γ Δ l} → ⊢ Γ ≡ Δ → Γ ⊢ t ~ u ↓! A ^ l
         → ∃ λ B → Whnf B × Γ ⊢ A ≡ B ^ [ ! , l ] × Δ ⊢ u ~ t ↓! B ^ l 
  sym~↓! Γ≡Δ ([~] A₁ D whnfA k~l) =
    let B , A≡B , k~l′ = sym~↑! Γ≡Δ k~l
        _ , ⊢B = syntacticEq A≡B
        B′ , whnfB′ , D′ = whNorm ⊢B
        A≡B′ = trans (sym (subset* D)) (trans A≡B (subset* (red D′)))
    in  B′ , whnfB′ , A≡B′ , [~] B (stabilityRed* Γ≡Δ (red D′)) whnfB′ k~l′

  -- Symmetry of algorithmic equality of types.
  symConv↑ : ∀ {A B r Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ A [conv↑] B ^ r → Δ ⊢ B [conv↑] A ^ r
  symConv↑ Γ≡Δ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) =
    [↑] B′ A′ (stabilityRed* Γ≡Δ D′) (stabilityRed* Γ≡Δ D) whnfB′ whnfA′
        (symConv↓ Γ≡Δ A′<>B′)

  -- Symmetry of algorithmic equality of types in WHNF.
  symConv↓ : ∀ {A B r Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ A [conv↓] B ^ r → Δ ⊢ B [conv↓] A ^ r
  symConv↓ Γ≡Δ (U-refl PE.refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  U-refl PE.refl ⊢Δ
  symConv↓ Γ≡Δ (univ x) = univ (symConv↓Term Γ≡Δ x)


  -- Symmetry of algorithmic equality of terms.
  symConv↑Term : ∀ {t u A Γ Δ l} → ⊢ Γ ≡ Δ → Γ ⊢ t [conv↑] u ∷ A ^ l → Δ ⊢ u [conv↑] t ∷ A ^ l
  symConv↑Term Γ≡Δ ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) =
    [↑]ₜ B u′ t′ (stabilityRed* Γ≡Δ D) (stabilityRed*Term Γ≡Δ d′)
         (stabilityRed*Term Γ≡Δ d) whnfB whnfu′ whnft′ (symConv↓Term Γ≡Δ t<>u)

  -- Symmetry of algorithmic equality of terms in WHNF.
  symConv↓Term : ∀ {t u A Γ Δ l} → ⊢ Γ ≡ Δ → Γ ⊢ t [conv↓] u ∷ A ^ l  → Δ ⊢ u [conv↓] t ∷ A ^ l
  symConv↓Term Γ≡Δ (U-refl x x₁) =
      let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ in U-refl (PE.sym x) ⊢Δ 
  symConv↓Term Γ≡Δ (ne t~u) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        B , whnfB , A≡B , u~t = sym~↓! Γ≡Δ t~u
        U≡B = U≡A-whnf A≡B whnfB
    in ne (PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) U≡B (proj₂ (proj₂ (proj₂ (sym~↓! Γ≡Δ t~u)))))
  symConv↓Term Γ≡Δ (ℕ-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  ℕ-refl ⊢Δ
  symConv↓Term Γ≡Δ (Empty-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  Empty-refl ⊢Δ
  symConv↓Term Γ≡Δ (Π-cong PE.refl PE.refl PE.refl l< l<' x A<>B A<>B₁) =
    let F≡H = soundnessConv↑Term A<>B
        _ , ⊢H = syntacticEq (stabilityEq Γ≡Δ (univ F≡H))
    in  Π-cong PE.refl PE.refl PE.refl l< l<' ⊢H (symConv↑Term Γ≡Δ A<>B)
                  (symConv↑Term (Γ≡Δ ∙ univ F≡H) A<>B₁)
  symConv↓Term Γ≡Δ (ℕ-ins t~u) =
    let B , whnfB , A≡B , u~t = sym~↓! Γ≡Δ t~u
        B≡ℕ = ℕ≡A A≡B whnfB
    in  ℕ-ins (PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) B≡ℕ u~t)
  symConv↓Term Γ≡Δ (ne-ins t u x t~u) =
    let B , whnfB , A≡B , u~t = sym~↓! Γ≡Δ t~u
    in  ne-ins (stabilityTerm Γ≡Δ u) (stabilityTerm Γ≡Δ t) x u~t
  symConv↓Term Γ≡Δ (zero-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  zero-refl ⊢Δ
  symConv↓Term Γ≡Δ (suc-cong t<>u) = suc-cong (symConv↑Term Γ≡Δ t<>u)
  symConv↓Term Γ≡Δ (η-eq l< l<' x x₁ x₂ y y₁ t<>u) =
    η-eq l<  l<' (stability Γ≡Δ x) (stabilityTerm Γ≡Δ x₂) (stabilityTerm Γ≡Δ x₁)
         y₁ y (symConv↑Term (Γ≡Δ ∙ refl x) t<>u)

-- Symmetry of algorithmic equality of types with preserved context.
symConv : ∀ {A B r Γ} → Γ ⊢ A [conv↑] B ^ r → Γ ⊢ B [conv↑] A ^ r
symConv A<>B =
  let ⊢Γ = wfEq (soundnessConv↑ A<>B)
  in  symConv↑ (reflConEq ⊢Γ) A<>B

-- Symmetry of algorithmic equality of terms with preserved context.
symConvTerm : ∀ {t u A Γ l} → Γ ⊢ t [conv↑] u ∷ A ^ l → Γ ⊢ u [conv↑] t ∷ A ^ l
symConvTerm t<>u =
  let ⊢Γ = wfEqTerm (soundnessConv↑Term t<>u)
  in  symConv↑Term (reflConEq ⊢Γ) t<>u
