{-# OPTIONS --safe #-}

module Definition.Conversion.Transitivity where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.Conversion
open import Definition.Conversion.Soundness
open import Definition.Conversion.Stability
open import Definition.Conversion.Conversion
open import Definition.Conversion.Whnf
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Injectivity
import Definition.Typed.Consequences.Inequality as WF
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution
open import Definition.Typed.Consequences.NeTypeEq
open import Definition.Typed.Consequences.SucCong

open import Tools.Nat
open import Tools.Product
open import Tools.Empty
import Tools.PropositionalEquality as PE

ιinj : ∀ {l l'} → ι l PE.≡ ι l' → l PE.≡ l'
ιinj {⁰} {⁰} e = PE.refl
ιinj {¹} {¹} e = PE.refl




mutual
  -- Transitivity of algorithmic equality of neutrals.
  trans~↑! : ∀ {t u v A B Γ Δ l l'}
         → l PE.≡ l'
         → ⊢ Γ ≡ Δ
         → Γ ⊢ t ~ u ↑! A ^ l         
         → Δ ⊢ u ~ v ↑! B ^ l'
         → Γ ⊢ t ~ v ↑! A ^ l
         × Γ ⊢ A ≡ B ^ [ ! , l ]
  trans~↑! el Γ≡Δ (var-refl x₁ x≡y) (var-refl x₂ x≡y₁) =
    var-refl x₁ (PE.trans x≡y x≡y₁)
    , neTypeEq (var _) PE.refl x₁
               (PE.subst (λ x → _ ⊢ var x ∷ _ ^ _) (PE.sym x≡y)
                         (stabilityTerm (symConEq Γ≡Δ) (PE.subst (λ lx → _ ⊢ _ ∷ _ ^ [ ! , lx ]) (PE.sym el) x₂))) 
  trans~↑! el Γ≡Δ (app-cong {rF = !} t~u a<>b) (app-cong {rF = !} u~v b<>c) =
    let t~v , ΠFG≡ΠF′G′ = trans~↓! PE.refl Γ≡Δ t~u u~v
        F≡F₁ , rF≡rF₁ , lF≡lF₁ , lG≡lG₁ , G≡G₁ = injectivity ΠFG≡ΠF′G′
        a<>c = transConv↑Term Γ≡Δ F≡F₁ a<>b (PE.subst (λ x → _ ⊢ _ [conv↑] _ ∷ _ ^ ι x) (PE.sym lF≡lF₁) b<>c) 
    in  app-cong t~v a<>c , substTypeEq G≡G₁ (soundnessConv↑Term a<>b)
  trans~↑! el Γ≡Δ (app-cong {rF = %} t~u a<>b) (app-cong {rF = %} u~v b<>c) =
    let t~v , ΠFG≡ΠF′G′ = trans~↓! PE.refl Γ≡Δ t~u u~v
        F≡F₁ , rF≡rF₁ , lF≡lF₁ , lG≡lG₁ , G≡G₁ = injectivity ΠFG≡ΠF′G′
        ⊢Γ = proj₁ (proj₂ (contextConvSubst Γ≡Δ))
        a<>c = trans~↑% Γ≡Δ a<>b (conv~↑% (PE.subst (λ x → _ ⊢ _ ~ _ ↑%  _ ^ ι x) (PE.sym lF≡lF₁) b<>c) (stabilityEq Γ≡Δ (sym F≡F₁)))
        _ , _ , t≡v = soundness~↑% a<>b
    in  app-cong t~v a<>c , substTypeEq G≡G₁ t≡v
  trans~↑! el Γ≡Δ (app-cong {rF = !} t~u a<>b) (app-cong {rF = %} u~v b<>c) = 
   let whnfA , neK , neL = ne~↓! t~u 
       ⊢A , ⊢k , ⊢l₁ = syntacticEqTerm (soundness~↓! t~u)
       ⊢A' , ⊢l₁' , ⊢l = syntacticEqTerm (soundness~↓! u~v)
       ΠFG≡ΠF₂G₂ = neTypeEq neL PE.refl ⊢l₁ (stabilityTerm (symConEq Γ≡Δ) ⊢l₁')
       F≡F₂ , rF≡rF₂ , G≡G₂ = injectivity ΠFG≡ΠF₂G₂
   in ⊥-elim (relevance-discr rF≡rF₂)
  trans~↑! el Γ≡Δ (app-cong {rF = %} t~u a<>b) (app-cong {rF = !} u~v b<>c) =
   let whnfA , neK , neL = ne~↓! t~u 
       ⊢A , ⊢k , ⊢l₁ = syntacticEqTerm (soundness~↓! t~u)
       ⊢A' , ⊢l₁' , ⊢l = syntacticEqTerm (soundness~↓! u~v)
       ΠFG≡ΠF₂G₂ = neTypeEq neL PE.refl ⊢l₁ (stabilityTerm (symConEq Γ≡Δ) ⊢l₁')
       F≡F₂ , rF≡rF₂ , G≡G₂ = injectivity ΠFG≡ΠF₂G₂
   in ⊥-elim (relevance-discr (PE.sym rF≡rF₂))
  trans~↑! PE.refl Γ≡Δ (natrec-cong A<>B a₀<>b₀ aₛ<>bₛ t~u) (natrec-cong B<>C b₀<>c₀ bₛ<>cₛ u~v) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        A≡B = soundnessConv↑ A<>B
        F[0]≡F₁[0] = substTypeEq A≡B (refl (zeroⱼ ⊢Γ))
        ΠℕFs≡ΠℕF₁s = sucCong A≡B
        A<>C = transConv↑ (Γ≡Δ ∙ (refl (univ (ℕⱼ ⊢Γ)))) A<>B B<>C
        a₀<>c₀ = transConv↑Term Γ≡Δ F[0]≡F₁[0] a₀<>b₀ b₀<>c₀
        aₛ<>cₛ = transConv↑Term Γ≡Δ ΠℕFs≡ΠℕF₁s aₛ<>bₛ bₛ<>cₛ
        t~v , _ = trans~↓! PE.refl Γ≡Δ t~u u~v
    in  natrec-cong A<>C a₀<>c₀ aₛ<>cₛ t~v
    ,   substTypeEq A≡B (soundness~↓! t~u)
  trans~↑! PE.refl Γ≡Δ (Emptyrec-cong A<>B t~u) (Emptyrec-cong B<>C u~v) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        A≡B = soundnessConv↑ A<>B
        A<>C = transConv↑ Γ≡Δ A<>B B<>C 
        ⊢t , ⊢u , t≡u = soundness~↑% t~u
        _ , ⊢v , u≡v = soundness~↑% u~v
        t~v = %~↑ ⊢t (stabilityTerm (symConEq Γ≡Δ) ⊢v)
    in  Emptyrec-cong A<>C t~v , A≡B
  trans~↑! el Γ≡Δ (Id-cong X x x₁) (Id-cong Y x₂ x₃) =
    let XY , [U] = trans~↓! el Γ≡Δ X Y
        X≡Y = univ (soundness~↓! XY)
        Y≡Y = PE.subst (λ lx → _ ⊢ _ ≡ _ ^ [ ! , ι lx ]) (PE.sym (next-inj el)) (univ (soundness~↓! Y))
        x₂' = PE.subst (λ lx → _ ⊢ _ [conv↑] _ ∷ _ ^ ι lx) (PE.sym (next-inj el)) x₂
        t~t = transConv↑Term Γ≡Δ X≡Y x (convConvTerm x₂' Y≡Y) 
        x₃' = PE.subst (λ lx → _ ⊢ _ [conv↑] _ ∷ _ ^ ι lx) (PE.sym (next-inj el)) x₃
        u~u = transConv↑Term Γ≡Δ X≡Y x₁ (convConvTerm x₃' Y≡Y)
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
    in Id-cong XY t~t u~u , PE.subst (λ lx → _ ⊢ _ ≡ SProp lx ^ [ ! , _ ]) (next-inj el) (refl (Ugenⱼ ⊢Γ))
  trans~↑! el Γ≡Δ (Id-ℕ X x) (Id-ℕ Y x₁) =
    let t~t , ℕ≡ℕ = trans~↓! PE.refl Γ≡Δ X Y
        u~u = transConv↑Term Γ≡Δ ℕ≡ℕ x x₁ 
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
    in Id-ℕ t~t u~u , refl (Ugenⱼ ⊢Γ)
  trans~↑! el Γ≡Δ (Id-ℕ0 X) (Id-ℕ0 Y) =
    let t~t , ℕ≡ℕ = trans~↓! PE.refl Γ≡Δ X Y
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
    in Id-ℕ0 t~t , refl (Ugenⱼ ⊢Γ)    
  trans~↑! el Γ≡Δ (Id-ℕS x X) (Id-ℕS x₁ Y) =
    let X~X , ℕ≡ℕ = trans~↓! PE.refl Γ≡Δ X Y
        t~t = transConv↑Term Γ≡Δ ℕ≡ℕ x x₁ 
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
    in Id-ℕS t~t X~X , refl (Ugenⱼ ⊢Γ)
  trans~↑! el Γ≡Δ (Id-U X x) (Id-U Y x₁) =
    let t~t , U≡U = trans~↓! PE.refl Γ≡Δ X Y
        u~u = transConv↑Term Γ≡Δ U≡U x x₁ 
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
    in Id-U t~t u~u , refl (Ugenⱼ ⊢Γ)
  trans~↑! el Γ≡Δ (Id-Uℕ X) (Id-Uℕ Y) =
    let t~t , _ = trans~↓! PE.refl Γ≡Δ X Y
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
    in Id-Uℕ t~t , refl (Ugenⱼ ⊢Γ)    
  trans~↑! el Γ≡Δ (Id-UΠ x X) (Id-UΠ x₁ Y) =
    let t~t , U≡U = trans~↓! PE.refl Γ≡Δ X Y
        u~u = transConv↑Term Γ≡Δ U≡U x x₁ 
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
    in Id-UΠ u~u t~t , refl (Ugenⱼ ⊢Γ)
  trans~↑! el Γ≡Δ (cast-cong X x x₁ x₂ x₃) (cast-cong Y x₄ x₅ x₆ x₇) =
    let XY , [U] = trans~↓! PE.refl Γ≡Δ X Y
        X≡Y = univ (soundness~↓! XY)
        Y≡Y = univ (soundness~↓! Y)
        t~t = transConv↑Term Γ≡Δ [U] x x₄
        u~u = transConv↑Term Γ≡Δ X≡Y x₁ (convConvTerm x₅ Y≡Y)
        A₁≡B = trans (soundnessConv↑Term t~t) (sym (soundnessConv↑Term (stabilityConv↑Term (symConEq Γ≡Δ) x₄)))
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
    in cast-cong XY t~t u~u x₂ (stabilityTerm (symConEq Γ≡Δ) x₇) , univ A₁≡B
  trans~↑! el Γ≡Δ (cast-ℕ X x x₁ x₂) (cast-ℕ Y x₃ x₄ x₅) =
    let XY , [U] = trans~↓! PE.refl Γ≡Δ X Y
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        t~t = transConv↑Term Γ≡Δ (refl (univ (ℕⱼ  ⊢Γ))) x x₃
    in cast-ℕ XY t~t x₁ (stabilityTerm (symConEq Γ≡Δ) x₅) , univ (soundness~↓! X) 
  trans~↑! el Γ≡Δ (cast-ℕℕ X x x₁) (cast-ℕℕ Y x₂ x₃) =
    let XY , N = trans~↓! PE.refl Γ≡Δ X Y
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
    in cast-ℕℕ XY x (stabilityTerm (symConEq Γ≡Δ) x₃) , N
  trans~↑! el Γ≡Δ (cast-Π x X x₁ x₂ x₃) (cast-Π x₄ Y x₅ x₆ x₇) =
    let XY , [U] = trans~↓! PE.refl Γ≡Δ X Y
        X≡Y = soundness~↓! XY
        Y≡Y = univ (soundnessConv↑Term x₄)
        t~t = transConv↑Term Γ≡Δ [U] x x₄
        u~u = transConv↑Term Γ≡Δ (univ (soundnessConv↑Term t~t)) x₁ (convConvTerm x₅ Y≡Y)
        A₁≡B = trans X≡Y (sym (soundness~↓! (stability~↓! (symConEq Γ≡Δ) Y)))
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
    in cast-Π t~t XY u~u x₂ (stabilityTerm (symConEq Γ≡Δ) x₇) , univ A₁≡B
  trans~↑! el Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-Πℕ x₄ x₅ x₆ x₇) =
    let Y≡Y = univ (soundnessConv↑Term x₄)
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        t~t = transConv↑Term Γ≡Δ (refl (Ugenⱼ ⊢Γ)) x x₄
        u~u = transConv↑Term Γ≡Δ (univ (soundnessConv↑Term t~t)) x₁ (convConvTerm x₅ Y≡Y)
    in cast-Πℕ t~t u~u x₂ (stabilityTerm (symConEq Γ≡Δ) x₇) , refl (univ (ℕⱼ  ⊢Γ)) 
  trans~↑! el Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-ℕΠ x₄ x₅ x₆ x₇) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        t~t = transConv↑Term Γ≡Δ (refl (Ugenⱼ ⊢Γ)) x x₄
        u~u = transConv↑Term Γ≡Δ (refl (univ (ℕⱼ  ⊢Γ))) x₁ x₅
    in cast-ℕΠ t~t u~u x₂ (stabilityTerm (symConEq Γ≡Δ) x₇) , univ (soundnessConv↑Term x) 
  trans~↑! el Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-ΠΠ%! x₅ x₆ x₇ x₈ x₉) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        A~A = transConv↑Term Γ≡Δ (refl (Ugenⱼ ⊢Γ)) x x₅
        B~B = transConv↑Term Γ≡Δ (refl (Ugenⱼ ⊢Γ)) x₁ x₆
        u~u = transConv↑Term Γ≡Δ (univ (soundnessConv↑Term x)) x₂ x₇
    in cast-ΠΠ%! A~A B~B u~u x₃ (stabilityTerm (symConEq Γ≡Δ) x₉) ,
       trans (univ (soundnessConv↑Term B~B)) (sym (univ (soundnessConv↑Term (stabilityConv↑Term (symConEq Γ≡Δ) x₆))))
  trans~↑! el Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-ΠΠ!% x₅ x₆ x₇ x₈ x₉) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        A~A = transConv↑Term Γ≡Δ (refl (Ugenⱼ ⊢Γ)) x x₅
        B~B = transConv↑Term Γ≡Δ (refl (Ugenⱼ ⊢Γ)) x₁ x₆
        u~u = transConv↑Term Γ≡Δ (univ (soundnessConv↑Term x)) x₂ x₇
    in cast-ΠΠ!% A~A B~B u~u x₃ (stabilityTerm (symConEq Γ≡Δ) x₉) ,
       trans (univ (soundnessConv↑Term B~B)) (sym (univ (soundnessConv↑Term (stabilityConv↑Term (symConEq Γ≡Δ) x₆))))


  trans~↑% : ∀ {t u v A Γ Δ  l}
         → ⊢ Γ ≡ Δ
         → Γ ⊢ t ~ u ↑% A ^ l
         → Δ ⊢ u ~ v ↑% A ^ l
         → Γ ⊢ t ~ v ↑% A ^ l
  trans~↑% Γ≡Δ (%~↑ ⊢t ⊢u) (%~↑ ⊢u′ ⊢v) =
    let ⊢Δu′ = stabilityTerm (symConEq Γ≡Δ) ⊢u′
        ⊢Δv = stabilityTerm (symConEq Γ≡Δ) ⊢v
    in %~↑ ⊢t ⊢Δv

  -- Transitivity of algorithmic equality of neutrals with types in WHNF.
  trans~↓! : ∀ {t u v A B Γ Δ l l'}
          → l PE.≡ l'
          → ⊢ Γ ≡ Δ
          → Γ ⊢ t ~ u ↓! A ^ l
          → Δ ⊢ u ~ v ↓! B ^ l'
          → Γ ⊢ t ~ v ↓! A ^ l
          × Γ ⊢ A ≡ B ^ [ ! , l ] 
  trans~↓! PE.refl Γ≡Δ ([~] A₁ D whnfA k~l) ([~] A₂ D₁ whnfA₁ k~l₁) =
    let t~v , A≡B = trans~↑! PE.refl Γ≡Δ k~l k~l₁
    in  [~] A₁ D whnfA t~v
    ,   trans (sym (subset* D))
              (trans A≡B
                     (subset* (stabilityRed* (symConEq Γ≡Δ) D₁)))

  -- Transitivity of algorithmic equality of types.
  transConv↑ : ∀ {A B C r Γ Δ}
            → ⊢ Γ ≡ Δ
            → Γ ⊢ A [conv↑] B ^ r
            → Δ ⊢ B [conv↑] C ^ r
            → Γ ⊢ A [conv↑] C ^ r
  transConv↑ {r = r} Γ≡Δ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′)
             ([↑] A″ B″ D₁ D″ whnfA″ whnfB″ A′<>B″) =
    [↑] A′ B″ D (stabilityRed* (symConEq Γ≡Δ) D″) whnfA′ whnfB″
        (transConv↓ Γ≡Δ A′<>B′
                    (PE.subst (λ x → _ ⊢ x [conv↓] B″ ^ r)
                              (whrDet* (D₁ , whnfA″)
                                        (stabilityRed* Γ≡Δ D′ , whnfB′))
                              A′<>B″))

  -- Transitivity of algorithmic equality of types in WHNF.
  transConv↓ : ∀ {A B C r Γ Δ}
            → ⊢ Γ ≡ Δ
            → Γ ⊢ A [conv↓] B ^ r
            → Δ ⊢ B [conv↓] C ^ r
            → Γ ⊢ A [conv↓] C ^ r
  transConv↓ Γ≡Δ (U-refl e x) (U-refl e₁ x₁) = U-refl (PE.trans e e₁) x
  transConv↓ Γ≡Δ (univ x) (univ y) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        X = transConv↓Term Γ≡Δ (refl (Ugenⱼ ⊢Γ )) PE.refl x y
    in univ X

  -- Transitivity of algorithmic equality of terms.
  transConv↑Term : ∀ {t u v A B Γ Δ l}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B ^ [ ! , l ]
                → Γ ⊢ t [conv↑] u ∷ A ^ l
                → Δ ⊢ u [conv↑] v ∷ B ^ l
                → Γ ⊢ t [conv↑] v ∷ A ^ l
  transConv↑Term Γ≡Δ A≡B ([↑]ₜ B₁ t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
                 ([↑]ₜ B₂ t″ u″ D₁ d₁ d″ whnfB₁ whnft″ whnfu″ t<>u₁) =
    let B₁≡B₂ = trans (sym (subset* D))
                      (trans A≡B
                             (subset* (stabilityRed* (symConEq Γ≡Δ) D₁)))
        d₁″ = conv* (stabilityRed*Term (symConEq Γ≡Δ) d″) (sym B₁≡B₂)
        d₁′  = stabilityRed*Term Γ≡Δ (conv* d′ B₁≡B₂)
    in  [↑]ₜ B₁ t′ u″ D d d₁″ whnfB whnft′ whnfu″
             (transConv↓Term Γ≡Δ B₁≡B₂ PE.refl t<>u
                             (PE.subst (λ x → _ ⊢ x [conv↓] u″ ∷ B₂ ^ _)
                                       (whrDet*Term (d₁ , whnft″)
                                                (d₁′ , whnfu′))
                                       t<>u₁))

  -- Transitivity of algorithmic equality of terms in WHNF.
  transConv↓Term : ∀ {t u v A B Γ Δ l l'}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B ^ [ ! , l ]
                → l PE.≡ l'
                → Γ ⊢ t [conv↓] u ∷ A ^ l
                → Δ ⊢ u [conv↓] v ∷ B ^ l'
                → Γ ⊢ t [conv↓] v ∷ A ^ l

  transConv↓Term {Δ = Δ} Γ≡Δ A≡B el (ne x) (ne x₁) = ne (proj₁ (trans~↓! PE.refl Γ≡Δ x (PE.subst (λ lx → Δ ⊢ _ ~ _ ↓! Univ _ _ ^ lx) (PE.sym el) x₁)))
  transConv↓Term Γ≡Δ A≡B el (ℕ-ins x) (ℕ-ins x₁) =
    ℕ-ins (proj₁ (trans~↓! PE.refl Γ≡Δ x x₁))
  transConv↓Term {Δ = Δ} Γ≡Δ A≡B el (ne-ins t u x x₁) (ne-ins {k} {l} {M} {N} t′ u′ x₂ x₃) =
    ne-ins t (conv (stabilityTerm (symConEq Γ≡Δ) (PE.subst (λ lx → Δ ⊢ l ∷ N ^ [ ! , lx ]) (PE.sym el) u′))
                   (sym A≡B)) x 
           (proj₁ (trans~↓! PE.refl Γ≡Δ x₁ (PE.subst (λ lx → Δ ⊢ k ~ l ↓! M ^ lx ) (PE.sym el) x₃)))
  transConv↓Term Γ≡Δ A≡B el (zero-refl x) (zero-refl x₁) =
    zero-refl x
  transConv↓Term Γ≡Δ A≡B el (suc-cong x) (suc-cong x₁) =
    suc-cong (transConv↑Term Γ≡Δ A≡B x x₁)
  transConv↓Term {Δ = Δ} Γ≡Δ A≡B el (η-eq {rF = rF₁} l< l<' x x₁ x₂ y y₁ x₃)
                                    (η-eq {u} {v} {F} {G} {rF} {lF} {lG} {l} l<'' l<''' x₄ x₅ x₆ y₂ y₃ x₇) =
    let F₁≡F , rF₁≡rF , lF₁≡lF , lG₁≡lG , G₁≡G = injectivity (PE.subst (λ lx → _ ⊢ _ ≡ Π _ ^ _ ° _ ▹ _ ° _ ° lx ^ _) (ιinj (PE.sym el)) A≡B ) 
    in  η-eq l< l<' x x₁ (conv (stabilityTerm (symConEq Γ≡Δ)
                                           (PE.subst (λ lx → Δ ⊢ v ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ [ ! , lx ]) (PE.sym el) x₆))
                            (sym A≡B))
             y y₃ (transConv↑Term (Γ≡Δ ∙ F₁≡F) G₁≡G x₃
                                  (PE.subst (λ lx → Δ ∙ F ^ [ rF₁ , _ ] ⊢  _ ∘ _ ^ _ [conv↑] wk1 v ∘ var 0 ^ _ ∷ G ^ ι lx)
                                            (PE.sym lG₁≡lG)
                                  (PE.subst (λ lx → Δ ∙ F ^ [ rF₁ , _ ] ⊢  wk1 u ∘ var 0 ^ lx [conv↑] wk1 v ∘ var 0 ^ lx ∷ G ^ ι lG)
                                            (PE.sym (ιinj el))
                                  (PE.subst (λ lx → Δ ∙ F ^ [ rF₁ , lx ] ⊢  wk1 u ∘ var 0 ^ l [conv↑] wk1 v ∘ var 0 ^ l ∷ G ^ ι lG)
                                            (PE.sym (PE.cong ι lF₁≡lF))
                                  (PE.subst (λ rx → Δ ∙ F ^ [ rx , ι lF ] ⊢ _ [conv↑] _ ∷ _ ^ _) (PE.sym rF₁≡rF) x₇)))))
  transConv↓Term Γ≡Δ A≡B el (ℕ-refl x) (ℕ-refl x₁) = ℕ-refl x
  transConv↓Term Γ≡Δ A≡B el (Empty-refl x) (Empty-refl x₁) = Empty-refl x
  transConv↓Term Γ≡Δ A≡B el (U-refl e x) (U-refl e₁ x₁) = U-refl (PE.trans e e₁) x
  transConv↓Term Γ≡Δ A≡B el (Π-cong PE.refl PE.refl PE.refl l< l<' x₅ x₆ x₇) (Π-cong PE.refl PE.refl PE.refl x₁₁ x₁₂ x₁₃ x₁₄ x₁₅) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        rF≡rF₁ , _ = Uinjectivity A≡B
    in Π-cong PE.refl PE.refl PE.refl l< l<' x₅ (transConv↑Term Γ≡Δ (refl (Ugenⱼ ⊢Γ )) x₆ x₁₄)
              (transConv↑Term (Γ≡Δ ∙ univ (soundnessConv↑Term x₆))
                              (PE.subst (λ rx → _ ⊢ _ ≡ Univ rx _ ^ _) rF≡rF₁ (refl (Ugenⱼ (⊢Γ ∙ x₅)) ) ) x₇ x₁₅)

  transConv↓Term Γ≡Δ A≡B PE.refl (ℕ-refl x) (η-eq x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = ⊥-elim (WF.U≢Π! A≡B)
  transConv↓Term Γ≡Δ A≡B el (Empty-refl {l} x) (η-eq x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) =
    let X = PE.subst (λ lx → _ ⊢ SProp l ≡  Π _ ^ _ ° _ ▹ _ ° _ ° _ ^ [ _ , lx ]) el A≡B
    in ⊥-elim (WF.U≢Π! X)
  transConv↓Term Γ≡Δ A≡B el (Π-cong {rΠ = rΠ} {lΠ = lΠ} x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (η-eq x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃ x₁₄ x₁₅) =
    let X = PE.subst (λ lx → _ ⊢ Univ rΠ lΠ ≡  Π _ ^ _ ° _ ▹ _ ° _ ° _ ^ [ _ , lx ]) el A≡B
    in ⊥-elim (WF.U≢Π! X)

  transConv↓Term Γ≡Δ A≡B el (ne x) (ℕ-ins x₁) = ⊥-elim (WF.U≢ℕ! A≡B)
  transConv↓Term Γ≡Δ A≡B PE.refl (ne x) (ne-ins x₁ x₂ x₃ x₄) = ⊥-elim (WF.U≢ne! x₃ A≡B)
  transConv↓Term Γ≡Δ A≡B PE.refl (ne x) (η-eq x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = ⊥-elim (WF.U≢Π! A≡B)
  --transConv↓Term Γ≡Δ A≡B el (zero-refl x) (zero-refl x₁) = {!!}
  transConv↓Term Γ≡Δ A≡B el (ℕ-ins x) (ne-ins t u x₂ x₃) = ⊥-elim (WF.ℕ≢ne! x₂ A≡B)
  transConv↓Term Γ≡Δ A≡B PE.refl (ℕ-ins x) (η-eq _ _ x₂ x₃ x₄ y y₁ x₅) = ⊥-elim (WF.ℕ≢Π! A≡B)
  transConv↓Term Γ≡Δ A≡B el (ℕ-ins x) (ne x₁) = ⊥-elim (WF.U≢ℕ! (sym A≡B))
  transConv↓Term Γ≡Δ A≡B PE.refl (ne-ins x x₁ x₂ x₃) (ne x₄) = ⊥-elim (WF.U≢ne! x₂ (sym A≡B))
  transConv↓Term  Γ≡Δ A≡B PE.refl (ne-ins t u x x₁) (ℕ-ins x₂) =
    ⊥-elim (WF.ℕ≢ne! x (sym A≡B)) 
  transConv↓Term Γ≡Δ A≡B PE.refl (ne-ins x x₁ x₂ x₃) (η-eq x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁) = ⊥-elim (WF.Π≢ne x₂ (sym A≡B))
  transConv↓Term Γ≡Δ A≡B PE.refl (zero-refl x) (η-eq x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) =  ⊥-elim (WF.ℕ≢Π! A≡B)
  transConv↓Term Γ≡Δ A≡B PE.refl (suc-cong x) (η-eq x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) =  ⊥-elim (WF.ℕ≢Π! A≡B)
  transConv↓Term Γ≡Δ A≡B el (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (ne x₈) = ⊥-elim (WF.U≢Π! (sym A≡B))
  transConv↓Term Γ≡Δ A≡B el (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (ℕ-refl x₈) = ⊥-elim (WF.U≢Π! (sym A≡B))
  transConv↓Term Γ≡Δ A≡B el (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (Empty-refl x₈) = ⊥-elim (WF.U≢Π! (sym A≡B))
  transConv↓Term Γ≡Δ A≡B el (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (Π-cong x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃ x₁₄ x₁₅) = ⊥-elim (WF.U≢Π! (sym A≡B))
  transConv↓Term Γ≡Δ A≡B PE.refl (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (ℕ-ins x₈) = ⊥-elim (WF.ℕ≢Π! (sym A≡B))
  transConv↓Term Γ≡Δ A≡B el (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (ne-ins x₈ x₉ x₁₀ x₁₁) = ⊥-elim (WF.Π≢ne x₁₀ A≡B)
  transConv↓Term Γ≡Δ A≡B PE.refl (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (zero-refl x₈) = ⊥-elim (WF.ℕ≢Π! (sym A≡B))
  transConv↓Term Γ≡Δ A≡B PE.refl (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (suc-cong x₈) = ⊥-elim (WF.ℕ≢Π! (sym A≡B))

-- Transitivity of algorithmic equality of types of the same context.
transConv : ∀ {A B C r Γ}
          → Γ ⊢ A [conv↑] B ^ r
          → Γ ⊢ B [conv↑] C ^ r
          → Γ ⊢ A [conv↑] C ^ r
transConv A<>B B<>C =
  let Γ≡Γ = reflConEq (wfEq (soundnessConv↑ A<>B))
  in  transConv↑ Γ≡Γ A<>B B<>C

-- Transitivity of algorithmic equality of terms of the same context.
transConvTerm : ∀ {t u v A Γ l}
              → Γ ⊢ t [conv↑] u ∷ A ^ l
              → Γ ⊢ u [conv↑] v ∷ A ^ l
              → Γ ⊢ t [conv↑] v ∷ A ^ l
transConvTerm t<>u u<>v =
  let t≡u = soundnessConv↑Term t<>u
      Γ≡Γ = reflConEq (wfEqTerm t≡u)
      ⊢A , _ , _ = syntacticEqTerm t≡u
  in  transConv↑Term Γ≡Γ (refl ⊢A) t<>u u<>v

trans~↑!Term : ∀ {t u v A Γ l}
              → Γ ⊢ t ~ u ↑% A ^ l
              → Γ ⊢ u ~ v ↑% A ^ l
              → Γ ⊢ t ~ v ↑% A ^ l
trans~↑!Term t<>u u<>v =
  let _ , _ , t≡u = soundness~↑% t<>u
      Γ≡Γ = reflConEq (wfEqTerm t≡u)
  in  trans~↑% Γ≡Γ t<>u u<>v
