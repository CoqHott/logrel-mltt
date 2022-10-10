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
open import Definition.Conversion.Inversion
open import Definition.Conversion.Whnf
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Reduction
open import Definition.Typed.Consequences.Injectivity
import Definition.Typed.Consequences.Inequality as WF
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution
open import Definition.Typed.Consequences.NeTypeEq
open import Definition.Typed.Consequences.SucCong
open import Definition.Typed.Consequences.RelevanceUnicity
open import Definition.Typed.Consequences.Equality
open import Definition.Typed.Consequences.Inversion

open import Tools.Nat
open import Tools.Product
open import Tools.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Tools.Empty
import Tools.PropositionalEquality as PE


mutual
  -- Transitivity of algorithmic equality of neutrals.
  trans~↑! : ∀ {t u v A B Γ Δ l l'}
         → l PE.≡ l'
         → ⊢ Γ ≡ Δ
         → Γ ⊢ t ~ u ↑! A ^ l
         → Δ ⊢ u ~ v ↑! B ^ l'
         → ∃ λ C → Γ ⊢ t ~ v ↑! C ^ l × Γ ⊢ A ≡ C ^ [ ! , l ] × Γ ⊢ C ≡ B ^ [ ! , l ]
{-
  trans~↑! el Γ≡Δ (var-refl x₁ x≡y) (var-refl x₂ x≡y₁) =
    _ , var-refl x₁ (PE.trans x≡y x≡y₁)
    , refl (syntacticTerm x₁) ,  proj₂ (neTypeEq (var _) x₁
                (PE.subst (λ x → _ ⊢ var x ∷ _ ^ _) (PE.sym x≡y)
                         (stabilityTerm (symConEq Γ≡Δ) (PE.subst (λ lx → _ ⊢ _ ∷ _ ^ [ ! , lx ]) (PE.sym el) x₂))))
  trans~↑! el Γ≡Δ (app-cong {rF = !} t~u a<>b) (app-cong {rF = !} u~v b<>c) =
    let C , wC , t~v , ΠFG≡C , C≡ΠF′G′ = trans~↓! PE.refl Γ≡Δ t~u u~v
        H , E , C≡ΠHE = Π≡A ΠFG≡C wC
        ⊢Γ = proj₁ (contextConvSubst Γ≡Δ)
        ΠFG≡C' = PE.subst (λ X → _ ⊢ _ ≡ X ^ [ ! , ι _ ]) C≡ΠHE ΠFG≡C
        C≡ΠF′G′' = PE.subst (λ X → _ ⊢ X ≡ _ ^ [ ! , ι _ ]) C≡ΠHE C≡ΠF′G′
        F≡F₁ , rF≡rF₁ , _ , lG≡lG₁ , G≡G₁ = injectivity ΠFG≡C'
        F≡F₁' , rF≡rF₁' , lF≡lF₁' , lG≡lG₁' , G≡G₁' = injectivity C≡ΠF′G′'
        t~v' = PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ ι _) C≡ΠHE t~v
        a<>c = transConv↑Term Γ≡Δ (trans F≡F₁ F≡F₁') a<>b (PE.subst (λ x → _ ⊢ _ [conv↑] _ ∷ _ ^ ι x) (PE.sym lF≡lF₁') b<>c)
        t≡v = soundnessConv↑Term a<>b
        _ , ⊢t , _ = syntacticEqTerm t≡v
    in _ , app-cong t~v' (convConv↑Term (reflConEq ⊢Γ) F≡F₁ a<>c) , substTypeEq G≡G₁ (refl ⊢t) , substTypeEq G≡G₁' (conv t≡v F≡F₁)
  trans~↑! el Γ≡Δ (app-cong {rF = %} t~u a<>b) (app-cong {rF = %} u~v b<>c) =
    let C , wC , t~v , ΠFG≡C , C≡ΠF′G′ = trans~↓! PE.refl Γ≡Δ t~u u~v
        H , E , C≡ΠHE = Π≡A ΠFG≡C wC
        ⊢Γ = proj₁ (contextConvSubst Γ≡Δ)
        ΠFG≡C' = PE.subst (λ X → _ ⊢ _ ≡ X ^ [ ! , ι _ ]) C≡ΠHE ΠFG≡C
        C≡ΠF′G′' = PE.subst (λ X → _ ⊢ X ≡ _ ^ [ ! , ι _ ]) C≡ΠHE C≡ΠF′G′
        F≡F₁ , rF≡rF₁ , _ , lG≡lG₁ , G≡G₁ = injectivity ΠFG≡C'
        F≡F₁' , rF≡rF₁' , lF≡lF₁' , lG≡lG₁' , G≡G₁' = injectivity C≡ΠF′G′'
        t~v' = PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ ι _) C≡ΠHE t~v
        a<>c = trans~↑% Γ≡Δ a<>b (conv~↑% (PE.subst (λ x → _ ⊢ _ ~ _ ↑% _ ^ ι x) (PE.sym lF≡lF₁') b<>c) (stabilityEq Γ≡Δ (sym (trans F≡F₁ F≡F₁'))))
        _ , _ , t≡v = soundness~↑% a<>b
        _ , ⊢t , _ = syntacticEqTerm t≡v
    in _ , app-cong t~v' (conv~↑% a<>c F≡F₁) , substTypeEq G≡G₁ (proof-irrelevance ⊢t ⊢t) , substTypeEq G≡G₁' (conv t≡v F≡F₁)
  trans~↑! el Γ≡Δ (app-cong {rF = !} t~u a<>b) (app-cong {rF = %} u~v b<>c) =
   let whnfA , neK , neL = ne~↓! t~u
       ⊢A , ⊢k , ⊢l₁ = syntacticEqTerm (soundness~↓! t~u)
       ⊢A' , ⊢l₁' , ⊢l = syntacticEqTerm (soundness~↓! u~v)
       _ , ΠFG≡ΠF₂G₂ = neTypeEq neL ⊢l₁ (stabilityTerm (symConEq Γ≡Δ) ⊢l₁')
       F≡F₂ , rF≡rF₂ , G≡G₂ = injectivity ΠFG≡ΠF₂G₂
   in ⊥-elim (relevance-discr rF≡rF₂)
  trans~↑! el Γ≡Δ (app-cong {rF = %} t~u a<>b) (app-cong {rF = !} u~v b<>c) =
   let whnfA , neK , neL = ne~↓! t~u
       ⊢A , ⊢k , ⊢l₁ = syntacticEqTerm (soundness~↓! t~u)
       ⊢A' , ⊢l₁' , ⊢l = syntacticEqTerm (soundness~↓! u~v)
       _ , ΠFG≡ΠF₂G₂ = neTypeEq neL ⊢l₁ (stabilityTerm (symConEq Γ≡Δ) ⊢l₁')
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
        C , wC ,  t~v , ℕ≡C , _ = trans~↓! PE.refl Γ≡Δ t~u u~v
        ℕ≡C' = ℕ≡A ℕ≡C wC
    in  _ , natrec-cong A<>C a₀<>c₀ aₛ<>cₛ (PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ ι _) ℕ≡C' t~v)
    , substTypeEq (refl (proj₁ (syntacticEq A≡B))) (refl (proj₁ (proj₂ (syntacticEqTerm (soundness~↓! t~u))))) ,  substTypeEq A≡B (soundness~↓! t~u) 
  trans~↑! PE.refl Γ≡Δ (Emptyrec-cong A<>B t~u) (Emptyrec-cong B<>C u~v) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        A≡B = soundnessConv↑ A<>B
        A<>C = transConv↑ Γ≡Δ A<>B B<>C
        ⊢t , ⊢u , t≡u = soundness~↑% t~u
        _ , ⊢v , u≡v = soundness~↑% u~v
        t~v = %~↑ ⊢t (stabilityTerm (symConEq Γ≡Δ) ⊢v)
    in _ , Emptyrec-cong A<>C t~v , refl (proj₁ (syntacticEq A≡B)) , A≡B
  trans~↑! _ Γ≡Δ (Id-cong X x x₁) (Id-cong Y x₂ x₃) =
    let _ , _ , [A'] = (syntacticEqTerm (soundness~↓! X))
        [A']Δ = stabilityTerm Γ≡Δ [A']
        _ , [A']Δ' , _ = syntacticEqTerm (soundness~↓! Y)
        _ , el' = relevance-unicity (univ [A']Δ) (univ [A']Δ')
        el = PE.cong next (ιinj el')
        K , wK , XY , [U] , [U]' = trans~↓! el Γ≡Δ X Y
        eqU = U≡A-whnf [U] wK
        XY' = PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqU XY
        X≡Y = univ (soundness~↓! XY')
        Y≡Y = PE.subst (λ lx → _ ⊢ _ ≡ _ ^ [ ! , ι lx ]) (PE.sym (next-inj el)) (univ (soundness~↓! Y))
        x₂' = PE.subst (λ lx → _ ⊢ _ [conv↑] _ ∷ _ ^ ι lx) (PE.sym (next-inj el)) x₂
        t~t = transConv↑Term Γ≡Δ X≡Y x (convConvTerm x₂' Y≡Y)
        x₃' = PE.subst (λ lx → _ ⊢ _ [conv↑] _ ∷ _ ^ ι lx) (PE.sym (next-inj el)) x₃
        u~u = transConv↑Term Γ≡Δ X≡Y x₁ (convConvTerm x₃' Y≡Y) 
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ 
    in _ , Id-cong XY' t~t u~u , refl (Ugenⱼ ⊢Γ) , refl (Ugenⱼ ⊢Γ)
  trans~↑! el Γ≡Δ (Id-ℕ X x) (Id-ℕ Y x₁) =
    let X , wX , t~t , ℕ≡X , X≡ℕ = trans~↓! PE.refl Γ≡Δ X Y
        u~u = transConv↑Term Γ≡Δ (trans ℕ≡X X≡ℕ) x x₁
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        eqℕ = ℕ≡A ℕ≡X wX
        t~t' =  PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqℕ t~t
    in _ , Id-ℕ t~t' u~u , refl (Ugenⱼ ⊢Γ) , refl (Ugenⱼ ⊢Γ)
  trans~↑! el Γ≡Δ (Id-ℕ0 X) (Id-ℕ0 Y) =
    let X , wX , t~t , ℕ≡X , X≡ℕ = trans~↓! PE.refl Γ≡Δ X Y
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        eqℕ = ℕ≡A ℕ≡X wX
        t~t' =  PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqℕ t~t
    in _ , Id-ℕ0 t~t' , refl (Ugenⱼ ⊢Γ) , refl (Ugenⱼ ⊢Γ)
  trans~↑! el Γ≡Δ (Id-ℕS x X) (Id-ℕS x₁ Y) =
    let X , wX , t~t , ℕ≡X , X≡ℕ = trans~↓! PE.refl Γ≡Δ X Y
        u~u = transConv↑Term Γ≡Δ (trans ℕ≡X X≡ℕ) x x₁
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        eqℕ = ℕ≡A ℕ≡X wX
        t~t' =  PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqℕ t~t
    in _ , Id-ℕS u~u t~t' , refl (Ugenⱼ ⊢Γ) , refl (Ugenⱼ ⊢Γ)
  trans~↑! el Γ≡Δ (Id-U X x) (Id-U Y x₁) =
    let K , wK , XY , [U] , [U]' = trans~↓! el Γ≡Δ X Y
        eqU = U≡A-whnf [U] wK
        XY' = PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqU XY
        u~u = transConv↑Term Γ≡Δ (trans [U] [U]') x x₁
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
    in _ , Id-U XY' u~u , refl (Ugenⱼ ⊢Γ) , refl (Ugenⱼ ⊢Γ)
  trans~↑! el Γ≡Δ (Id-Uℕ X) (Id-Uℕ Y) =
    let K , wK , XY , [U] , [U]' = trans~↓! el Γ≡Δ X Y
        eqU = U≡A-whnf [U] wK
        XY' = PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqU XY
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
    in _ , Id-Uℕ XY' , refl (Ugenⱼ ⊢Γ)  , refl (Ugenⱼ ⊢Γ)
  trans~↑! el Γ≡Δ (Id-UΠ x X) (Id-UΠ x₁ Y) =
    let K , wK , XY , [U] , [U]' = trans~↓! el Γ≡Δ X Y
        eqU = U≡A-whnf [U] wK
        XY' = PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqU XY
        u~u = transConv↑Term Γ≡Δ (trans [U] [U]') x x₁
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
    in _ , Id-UΠ u~u XY' , refl (Ugenⱼ ⊢Γ) , refl (Ugenⱼ ⊢Γ)
  trans~↑! el Γ≡Δ (cast-cong X x ⊢t ⊢t' x₁ x₂ x₃) (cast-cong Y x₄ ⊢u ⊢u' x₅ x₆ x₇) =
    let K , wK , XY , [U] , _  = trans~↓! PE.refl Γ≡Δ X Y
        eqU = U≡A-whnf [U] wK
        XY' = PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqU XY
        X≡Y = univ (soundness~↓! XY')
        Y≡Y = univ (soundness~↓! Y)
        K' , wK' , t~t , [U]' , _ = trans~↓! PE.refl Γ≡Δ x x₄
        eqU' = U≡A-whnf [U]' wK'
        t~t' = PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqU' t~t
        _ , _ , neA = ne~↓! Y
        u~u = transConv↓Term Γ≡Δ X≡Y PE.refl x₁ (convConv↓Term (reflConEq (wfTerm ⊢u)) Y≡Y (ne neA) x₅)
        A₁≡B = trans (soundness~↓! t~t') (sym (soundness~↓! (stability~↓! (symConEq Γ≡Δ) x₄)))
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
    in _ , cast-cong XY' t~t' ⊢t (stabilityTerm (symConEq Γ≡Δ) ⊢u') u~u x₂ (stabilityTerm (symConEq Γ≡Δ) x₇) , refl (univ (proj₁ (proj₂ (syntacticEqTerm A₁≡B)))) , univ A₁≡B 
  trans~↑! el Γ≡Δ (cast-ℕ X x x₁ x₂) (cast-ℕ Y x₃ x₄ x₅) =
    let K , wK , XY , [U] , _  = trans~↓! PE.refl Γ≡Δ X Y
        eqU = U≡A-whnf [U] wK
        XY' = PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqU XY
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        t~t = transConv↑Term Γ≡Δ (refl (univ (ℕⱼ  ⊢Γ))) x x₃
    in _ , cast-ℕ XY' t~t x₁ (stabilityTerm (symConEq Γ≡Δ) x₅) , refl (proj₁ (syntacticEq (univ (soundness~↓! X)))) , univ (soundness~↓! X)
  trans~↑! el Γ≡Δ (cast-ℕℕ X x x₁) (cast-ℕℕ Y x₂ x₃) =
    let X , wX , t~t , ℕ≡X , X≡ℕ = trans~↓! PE.refl Γ≡Δ X Y
        eqℕ = ℕ≡A ℕ≡X wX
        t~t' =  PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqℕ t~t
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
    in _ , cast-ℕℕ t~t' x (stabilityTerm (symConEq Γ≡Δ) x₃) , refl (univ (ℕⱼ ⊢Γ)) , refl (univ (ℕⱼ ⊢Γ))
  trans~↑! el Γ≡Δ (cast-Π x X x₁ x₂ x₃) (cast-Π x₄ Y x₅ x₆ x₇) =
    let K , wK , XY , [U] , [U]'  = trans~↓! PE.refl Γ≡Δ X Y
        eqU = U≡A-whnf [U] wK
        XY' = PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqU XY
        X≡Y = soundness~↓! XY'
        Y≡Y = univ (soundnessConv↑Term x₄)
        t~t = transConv↑Term Γ≡Δ (trans [U] [U]') x x₄
        u~u = transConv↑Term Γ≡Δ (univ (soundnessConv↑Term t~t)) x₁ (convConvTerm x₅ Y≡Y)
        A₁≡B = trans X≡Y (sym (soundness~↓! (stability~↓! (symConEq Γ≡Δ) Y)))
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
    in _ , cast-Π t~t XY' u~u x₂ (stabilityTerm (symConEq Γ≡Δ) x₇) , refl (univ (proj₁ (proj₂ (syntacticEqTerm A₁≡B)))) , univ A₁≡B
  trans~↑! el Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-Πℕ x₄ x₅ x₆ x₇) =
    let Y≡Y = univ (soundnessConv↑Term x₄)
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        t~t = transConv↑Term Γ≡Δ (refl (Ugenⱼ ⊢Γ)) x x₄
        u~u = transConv↑Term Γ≡Δ (univ (soundnessConv↑Term t~t)) x₁ (convConvTerm x₅ Y≡Y)
    in _ , cast-Πℕ t~t u~u x₂ (stabilityTerm (symConEq Γ≡Δ) x₇) , refl (univ (ℕⱼ  ⊢Γ)) , refl (univ (ℕⱼ  ⊢Γ))
  trans~↑! el Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-ℕΠ x₄ x₅ x₆ x₇) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        t~t = transConv↑Term Γ≡Δ (refl (Ugenⱼ ⊢Γ)) x x₄
        u~u = transConv↑Term Γ≡Δ (refl (univ (ℕⱼ  ⊢Γ))) x₁ x₅
        Π≡Π = univ (soundnessConv↑Term x)
    in _ , cast-ℕΠ t~t u~u x₂ (stabilityTerm (symConEq Γ≡Δ) x₇) , refl (proj₁ (syntacticEq Π≡Π)) , Π≡Π
  trans~↑! el Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-ΠΠ%! x₅ x₆ x₇ x₈ x₉) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        A~A = transConv↑Term Γ≡Δ (refl (Ugenⱼ ⊢Γ)) x x₅
        B~B = transConv↑Term Γ≡Δ (refl (Ugenⱼ ⊢Γ)) x₁ x₆
        u~u = transConv↑Term Γ≡Δ (univ (soundnessConv↑Term x)) x₂ x₇
        Π≡Π = trans (univ (soundnessConv↑Term B~B)) (sym (univ (soundnessConv↑Term (stabilityConv↑Term (symConEq Γ≡Δ) x₆))))
    in _ , cast-ΠΠ%! A~A B~B u~u x₃ (stabilityTerm (symConEq Γ≡Δ) x₉) ,
       refl (proj₁ (syntacticEq Π≡Π)) , Π≡Π
  trans~↑! el Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-ΠΠ!% x₅ x₆ x₇ x₈ x₉) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        A~A = transConv↑Term Γ≡Δ (refl (Ugenⱼ ⊢Γ)) x x₅
        B~B = transConv↑Term Γ≡Δ (refl (Ugenⱼ ⊢Γ)) x₁ x₆
        u~u = transConv↑Term Γ≡Δ (univ (soundnessConv↑Term x)) x₂ x₇
        Π≡Π = trans (univ (soundnessConv↑Term B~B)) (sym (univ (soundnessConv↑Term (stabilityConv↑Term (symConEq Γ≡Δ) x₆))))
    in _ , cast-ΠΠ!% A~A B~B u~u x₃ (stabilityTerm (symConEq Γ≡Δ) x₉) ,
       refl (proj₁ (syntacticEq Π≡Π)) , Π≡Π
  trans~↑! PE.refl Γ≡Δ t~u (cast-refl' A~B ⊢u ⊢v x₃ x₄) =
    let net , neu = ne~↑! t~u
        t≡u = soundness~↑! t~u
        _ , neA , neB = ne~↓! A~B
        ⊢A , ⊢t , ⊢u' = syntacticEqTerm t≡u
        _ , A≡B = neTypeEq neu ⊢u' (stabilityTerm (symConEq Γ≡Δ) ⊢u)
        X , wX , DX = whNorm ⊢A
        _ , ⊢B = syntacticEq A≡B
        t[conv↑]u = ne-ins (conv ⊢t A≡B) (conv ⊢u' A≡B) neA ([~] _ (red DX) wX t~u)
        t~v = transConv↓Term Γ≡Δ (refl ⊢B) PE.refl t[conv↑]u x₃
   in _ , cast-refl' (stability~↓! (symConEq Γ≡Δ) A~B)
                        (conv ⊢t A≡B) 
                        (stabilityTerm (symConEq Γ≡Δ) ⊢v) t~v (stabilityTerm (symConEq Γ≡Δ) x₄) , A≡B , refl ⊢B

  trans~↑! PE.refl Γ≡Δ (cast-refl A~B ⊢t ⊢u x₃ x₄) u~v =
    let neu , nev = ne~↑! u~v
        u≡v = soundness~↑! u~v
        _ , neA , neB = ne~↓! A~B
        ⊢B , ⊢u' , ⊢v = syntacticEqTerm u≡v
        _ , A≡B = neTypeEq neu ⊢u (stabilityTerm (symConEq Γ≡Δ) ⊢u')
        X , wX , DX = whNorm ⊢B
        ⊢A , ⊢B'  = syntacticEq A≡B
        A≡B' = univ (soundness~↓! A~B)
        u[conv↑]v = ne-ins (conv ⊢u' (stabilityEq Γ≡Δ (trans (sym A≡B) A≡B'))) (conv ⊢v (stabilityEq Γ≡Δ (trans (sym A≡B) A≡B'))) neB ([~] _ (red DX) wX u~v)
        t~v = transConv↓Term Γ≡Δ A≡B' PE.refl x₃ u[conv↑]v
        _ , ⊢A' = syntacticEq A≡B'
    in _ , cast-refl A~B ⊢t 
                       (conv (stabilityTerm (symConEq Γ≡Δ) ⊢v) (sym A≡B)) t~v x₄ , refl ⊢A' , trans (sym A≡B') A≡B

  trans~↑! PE.refl Γ≡Δ t~u (castℕ-refl' x₂ x₃) =
    let net , neu = ne~↑! t~u
        t≡u = soundness~↑! t~u
        ⊢A , ⊢t , ⊢u' = syntacticEqTerm t≡u
        X , wX , DX = whNorm ⊢A
        t~↓!u = [~] _ (red DX) wX t~u
        K , wK , t~v , eq , eq' = trans~↓! PE.refl Γ≡Δ t~↓!u x₂
        eqℕ = ℕ≡A (sym eq') wK
        t~v' =  PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqℕ t~v
        u≡v = soundness~↓! x₂
        _ , A≡ℕ = neTypeEq neu ⊢u' (stabilityTerm (symConEq Γ≡Δ) (proj₁ (proj₂ (syntacticEqTerm u≡v))))
    in _ , castℕ-refl' t~v' (stabilityTerm (symConEq Γ≡Δ) x₃)  , A≡ℕ , refl (proj₁ (syntacticEq (sym A≡ℕ)))

  trans~↑! PE.refl Γ≡Δ (castℕ-refl x₂ x₃) u~v =
    let neu , nev = ne~↑! u~v
        u≡v = soundness~↑! u~v
        ⊢B , ⊢u , ⊢v = syntacticEqTerm u≡v
        X , wX , DX = whNorm ⊢B
        u~↓!v = [~] _ (red DX) wX u~v
        K , wK , t~v , eq , eq' = trans~↓! PE.refl Γ≡Δ x₂ u~↓!v
        eqℕ = ℕ≡A eq wK
        t~v' =  PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqℕ t~v
        t≡u = soundness~↓! x₂
        _ , A≡ℕ = neTypeEq neu (proj₂ (proj₂ (syntacticEqTerm t≡u))) (stabilityTerm (symConEq Γ≡Δ) ⊢u)
    in _ , castℕ-refl t~v' x₃  , refl (proj₁ (syntacticEq A≡ℕ)) , A≡ℕ

  trans~↑! el Γ≡Δ (Id-cong x x₁ x₂) (Id-ℕ x₃ x₄) with  ne~↓! x
  trans~↑! el Γ≡Δ (Id-cong x x₁ x₂) (Id-ℕ x₃ x₄) | _ , _ , ()  
  trans~↑! el Γ≡Δ (Id-cong x x₁ x₂) (Id-ℕ0 x₃) with  ne~↓! x
  trans~↑! el Γ≡Δ (Id-cong x x₁ x₂) (Id-ℕ0 x₃) | _ , _ , ()
  trans~↑! el Γ≡Δ (Id-cong x x₁ x₂) (Id-ℕS x₃ x₄) with  ne~↓! x
  trans~↑! el Γ≡Δ (Id-cong x x₁ x₂) (Id-ℕS x₃ x₄) | _ , _ , ()
  trans~↑! el Γ≡Δ (Id-cong x x₁ x₂) (Id-U x₃ x₄) with  ne~↓! x
  trans~↑! el Γ≡Δ (Id-cong x x₁ x₂) (Id-U x₃ x₄) | _ , _ , ()
  trans~↑! el Γ≡Δ (Id-cong x x₁ x₂) (Id-Uℕ x₃) with  ne~↓! x
  trans~↑! el Γ≡Δ (Id-cong x x₁ x₂) (Id-Uℕ x₃) | _ , _ , ()
  trans~↑! el Γ≡Δ (Id-cong x x₁ x₂) (Id-UΠ x₃ x₄) with  ne~↓! x
  trans~↑! el Γ≡Δ (Id-cong x x₁ x₂) (Id-UΠ x₃ x₄) | _ , _ , ()

  trans~↑! el Γ≡Δ (Id-ℕ x₃ x₄) (Id-cong x x₁ x₂) with  ne~↓! x
  trans~↑! el Γ≡Δ (Id-ℕ x₃ x₄) (Id-cong x x₁ x₂) | _ , () , _  
  trans~↑! el Γ≡Δ (Id-ℕ0 x₃) (Id-cong x x₁ x₂) with  ne~↓! x
  trans~↑! el Γ≡Δ (Id-ℕ0 x₃) (Id-cong x x₁ x₂) | _ , () , _
  trans~↑! el Γ≡Δ (Id-ℕS x₃ x₄) (Id-cong x x₁ x₂) with  ne~↓! x
  trans~↑! el Γ≡Δ (Id-ℕS x₃ x₄) (Id-cong x x₁ x₂) | _ , () , _
  trans~↑! el Γ≡Δ (Id-U x₃ x₄) (Id-cong x x₁ x₂) with  ne~↓! x
  trans~↑! el Γ≡Δ (Id-U x₃ x₄) (Id-cong x x₁ x₂) | _ , () , _
  trans~↑! el Γ≡Δ (Id-Uℕ x₃) (Id-cong x x₁ x₂) with  ne~↓! x
  trans~↑! el Γ≡Δ (Id-Uℕ x₃) (Id-cong x x₁ x₂) | _ , () , _
  trans~↑! el Γ≡Δ (Id-UΠ x₃ x₄) (Id-cong x x₁ x₂) with  ne~↓! x
  trans~↑! el Γ≡Δ (Id-UΠ x₃ x₄) (Id-cong x x₁ x₂) | _ , () , _

  trans~↑! el Γ≡Δ (Id-ℕ x x₃) (Id-ℕ0 x₄) with ne~↓! x
  trans~↑! el Γ≡Δ (Id-ℕ x x₃) (Id-ℕ0 x₄) | _ , _ , ()
  trans~↑! el Γ≡Δ (Id-ℕ x x₃) (Id-ℕS x₄ x₅) with ne~↓! x
  trans~↑! el Γ≡Δ (Id-ℕ x x₃) (Id-ℕS x₄ x₅) | _ , _ , ()
  trans~↑! el Γ≡Δ (Id-ℕ0 x₂) (Id-ℕ x x₄) with ne~↓! x
  trans~↑! el Γ≡Δ (Id-ℕ0 x₂) (Id-ℕ x x₄) | _ , () , _
  trans~↑! el Γ≡Δ (Id-ℕS x₂ x₃) (Id-ℕ x x₅)  with ne~↓! x
  trans~↑! el Γ≡Δ (Id-ℕS x₂ x₃) (Id-ℕ x x₅) | _ , () , _
  -}
  trans~↑! el Γ≡Δ (cast-cong x x₁ x₂ x₃ x₄ x₅ x₆) (cast-refl x₇ x₈ x₉ x₁₀ x₁₁) = {!!}
  trans~↑! el Γ≡Δ (cast-refl' x x₁ x₂ x₃ x₄) (cast-cong x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁) = {!!}
  trans~↑! el Γ≡Δ (cast-refl' x x₁ x₂ x₃ x₄) (cast-refl x₅ x₆ x₇ x₈ x₉) =
    let t~v = transConv↓Term Γ≡Δ (refl (syntacticTerm x₁)) PE.refl x₃ x₈
        _ , neA , neB =  ne~↓! x
        X , [~] K D whK t~v' , A≡X = [conv↓]ne neA t~v
    in _ , t~v' , trans A≡X (sym (subset* D)) , trans (subset* D) (trans (sym A≡X) (univ (soundness~↓! x)))
  trans~↑! el Γ≡Δ (castℕ-refl' x x₁) (castℕ-refl x₂ x₃) =
    let X , wX , t~t , ℕ≡X , X≡ℕ = trans~↓! PE.refl Γ≡Δ x x₂
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        eqℕ = ℕ≡A ℕ≡X wX
        t~t' =  PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqℕ t~t
        [~] K D wK t~t'' = t~t'
    in _ , t~t'' , sym (subset* D) , subset* D
  trans~↑! el Γ≡Δ (castℕ-refl' x x₁) (cast-ℕℕ x₂ x₃ x₄) =
    let X , wX , t~t , ℕ≡X , X≡ℕ = trans~↓! PE.refl Γ≡Δ x x₂
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        eqℕ = ℕ≡A ℕ≡X wX
        t~t' =  PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqℕ t~t
    in _ , castℕ-refl' t~t' (stabilityTerm (symConEq Γ≡Δ) x₄) , refl (univ (ℕⱼ ⊢Γ) ) , refl (univ (ℕⱼ ⊢Γ) )
  trans~↑! el Γ≡Δ (cast-neℕ x x₁ x₂ x₃) Y = {!!}
  trans~↑! el Γ≡Δ (cast-ℕ x x₁ x₂ x₃) Y = {!!}
  trans~↑! el Γ≡Δ (cast-ℕℕ x x₁ x₂) Y = {!!}
  trans~↑! el Γ≡Δ (cast-neΠ x x₁ x₂ x₃ x₄) Y = {!!}
  trans~↑! el Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) Y = {!!}
  trans~↑! el Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) Y = {!!}
  trans~↑! el Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) Y = {!!}
  trans~↑! el Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) Y = {!!}
  trans~↑! el Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) Y = {!!}
  trans~↑! el Γ≡Δ X Y = {!!} 

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
          → ∃ λ C → Whnf C × Γ ⊢ t ~ v ↓! C ^ l × Γ ⊢ A ≡ C ^ [ ! , l ] × Γ ⊢ C ≡ B ^ [ ! , l ]
                   
  trans~↓! PE.refl Γ≡Δ ([~] A₁ D whnfA k~l) ([~] A₂ D₁ whnfA₁ k~l₁) =
   let C , t~v , A≡C , C≡B = trans~↑! PE.refl Γ≡Δ k~l k~l₁
       ⊢C , _ = syntacticEq C≡B
       X , wX , DX = whNorm ⊢C
   in X , wX , [~] _ (red DX) wX t~v , trans (sym (subset* D)) (trans A≡C (subset* (red DX))) , trans (trans (sym (subset* (red DX))) C≡B) (subset* (stabilityRed* (symConEq Γ≡Δ) D₁))

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
  transConv↓ = {!!}
{-
  transConv↓ Γ≡Δ (U-refl e x) (U-refl e₁ x₁) = U-refl (PE.trans e e₁) x
  transConv↓ Γ≡Δ (univ x) (univ y) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        X = transConv↓Term Γ≡Δ (refl (Ugenⱼ ⊢Γ )) PE.refl x y
    in univ X
-}
  -- Transitivity of algorithmic equality of terms.
  transConv↑Term : ∀ {t u v A B Γ Δ l}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B ^ [ ! , l ]
                → Γ ⊢ t [conv↑] u ∷ A ^ l
                → Δ ⊢ u [conv↑] v ∷ B ^ l
                → Γ ⊢ t [conv↑] v ∷ A ^ l
  transConv↑Term = {!!}
{-
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
-}

  -- Transitivity of algorithmic equality of terms in WHNF.
  transConv↓Term : ∀ {t u v A B Γ Δ l l'}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B ^ [ ! , l ]
                → l PE.≡ l'
                → Γ ⊢ t [conv↓] u ∷ A ^ l
                → Δ ⊢ u [conv↓] v ∷ B ^ l'
                → Γ ⊢ t [conv↓] v ∷ A ^ l
  transConv↓Term = {!!}
{-  transConv↓Term {Δ = Δ} Γ≡Δ A≡B el (ne x) (ne x₁) = ne (proj₁ (trans~↓! PE.refl Γ≡Δ x (PE.subst (λ lx → Δ ⊢ _ ~ _ ↓! Univ _ _ ^ lx) (PE.sym el) x₁)))
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
    let F₁≡F , rF₁≡rF , lF₁≡lF , lG₁≡lG , G₁≡G = injectivity (PE.subst (λ lx → _ ⊢ _ ≡ Π _ ^ _ ° _ ▹ _ ° _ ° lx ^ _ ^ _) (ιinj (PE.sym el)) A≡B )
    in  η-eq l< l<' x x₁ (conv (stabilityTerm (symConEq Γ≡Δ)
                                           (PE.subst (λ lx → Δ ⊢ v ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ [ ! , lx ]) (PE.sym el) x₆))
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
  transConv↓Term Γ≡Δ A≡B el (Π-cong PE.refl PE.refl PE.refl PE.refl l< l<' x₅ x₆ x₇) (Π-cong PE.refl PE.refl PE.refl PE.refl x₁₁ x₁₂ x₁₃ x₁₄ x₁₅) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        rF≡rF₁ , _ = Uinjectivity A≡B
    in Π-cong PE.refl PE.refl PE.refl PE.refl l< l<' x₅ (transConv↑Term Γ≡Δ (refl (Ugenⱼ ⊢Γ )) x₆ x₁₄)
              (transConv↑Term (Γ≡Δ ∙ univ (soundnessConv↑Term x₆))
                              (refl (Ugenⱼ (⊢Γ ∙ x₅))) x₇ x₁₅)
  transConv↓Term Γ≡Δ A≡B el (∃-cong x₅ x₆ x₇) (∃-cong x₁₃ x₁₄ x₁₅) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        rF≡rF₁ , _ = Uinjectivity A≡B
    in ∃-cong x₅ (transConv↑Term Γ≡Δ (refl (Ugenⱼ ⊢Γ )) x₆ x₁₄)
                 (transConv↑Term (Γ≡Δ ∙ univ (soundnessConv↑Term x₆)) (refl (Ugenⱼ (⊢Γ ∙ x₅))) x₇ x₁₅)

  transConv↓Term Γ≡Δ A≡B PE.refl (ℕ-refl x) (η-eq x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = ⊥-elim (WF.U≢Π! A≡B)
  transConv↓Term {Γ = Γ} Γ≡Δ A≡B el (Empty-refl x) (η-eq {F = F} {G = G} {rF = rF} {lF = lF} {lG = lG} {l = l} x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) =
    let X = PE.subst (λ lx → Γ ⊢ SProp ≡  Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ [ ! , lx ]) el A≡B
    in ⊥-elim (WF.U≢Π! X)
  transConv↓Term Γ≡Δ A≡B el (Π-cong {rΠ = rΠ} {lΠ = lΠ} x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₀) (η-eq x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃ x₁₄ x₁₅) =
    let X = PE.subst (λ lx → _ ⊢ Univ rΠ lΠ ≡ Π _ ^ _ ° _ ▹ _ ° _ ° _ ^ _ ^ [ _ , lx ]) el A≡B
    in ⊥-elim (WF.U≢Π! X)
  transConv↓Term {Γ = Γ} Γ≡Δ A≡B el (∃-cong x₆ x₇ x₀) (η-eq {F = F} {G = G} {rF = rF} {lF = lF} {lG = lG} {l = l} x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃ x₁₄ x₁₅) =
    let X = PE.subst (λ lx → Γ ⊢ SProp ≡ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ [ ! , lx ]) el A≡B
    in ⊥-elim (WF.U≢Π! X)

  transConv↓Term Γ≡Δ A≡B el (ne x) (ℕ-ins x₁) = ⊥-elim (WF.U≢ℕ! A≡B)
  transConv↓Term Γ≡Δ A≡B PE.refl (ne x) (ne-ins x₁ x₂ x₃ x₄) = ⊥-elim (WF.U≢ne! x₃ A≡B)
  transConv↓Term Γ≡Δ A≡B PE.refl (ne x) (η-eq x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) = ⊥-elim (WF.U≢Π! A≡B)
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
  transConv↓Term Γ≡Δ A≡B el (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (Π-cong x₀ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃ x₁₄ x₁₅) = ⊥-elim (WF.U≢Π! (sym A≡B))
  transConv↓Term Γ≡Δ A≡B el (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (∃-cong x₁₃ x₁₄ x₁₅) = ⊥-elim (WF.U≢Π! (sym A≡B))
  transConv↓Term Γ≡Δ A≡B PE.refl (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (ℕ-ins x₈) = ⊥-elim (WF.ℕ≢Π! (sym A≡B))
  transConv↓Term Γ≡Δ A≡B el (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (ne-ins x₈ x₉ x₁₀ x₁₁) = ⊥-elim (WF.Π≢ne x₁₀ A≡B)
  transConv↓Term Γ≡Δ A≡B PE.refl (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (zero-refl x₈) = ⊥-elim (WF.ℕ≢Π! (sym A≡B))
  transConv↓Term Γ≡Δ A≡B PE.refl (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (suc-cong x₈) = ⊥-elim (WF.ℕ≢Π! (sym A≡B))
-}

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
