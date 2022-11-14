-- {-# OPTIONS --safe #-}
{-# OPTIONS --allow-unsolved-metas #-}

module Definition.Conversion.EqRelInstance where

open import Definition.Untyped
open import Definition.Untyped.Properties using (wkSingleSubstId)
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening using (_∷_⊆_; wkEq; step; id)
open import Definition.Conversion
open import Definition.Conversion.Reduction
open import Definition.Conversion.Universe
open import Definition.Conversion.Stability
open import Definition.Conversion.Soundness
open import Definition.Conversion.Lift
open import Definition.Conversion.Conversion
open import Definition.Conversion.Transitivity
open import Definition.Conversion.Weakening
open import Definition.Conversion.Whnf
open import Definition.Typed.EqualityRelation
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.Equality
open import Definition.Typed.Consequences.Reduction
open import Definition.Typed.Consequences.NeTypeEq
open import Definition.Conversion.Symmetry

-- open import Definition.Conversion.HelperDecidable

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Function
open import Tools.Empty using (⊥; ⊥-elim)


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

  
-- Algorithmic equality of neutrals with injected conversion.
data _⊢_~_∷_^_ (Γ : Con Term) (k l A : Term) (r : TypeInfo) : Set where
  ↑ : ∀ {B} → Γ ⊢ A ≡ B ^ r → Γ ⊢ k ~ l ↑ B ^ r → Γ ⊢ k ~ l ∷ A ^ r

-- Properties of algorithmic equality of neutrals with injected conversion.

~-var : ∀ {x A r Γ} → Γ ⊢ var x ∷ A ^ r → Γ ⊢ var x ~ var x ∷ A ^ r
~-var x =
  let ⊢A = syntacticTerm x
  in  ↑ (refl ⊢A) (var-refl′ x)

~-app : ∀ {f g a b F G Γ rF lF lG lΠ}
      → Γ ⊢ f ~ g ∷ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ ! ^ [ ! , ι lΠ ]
      → Γ ⊢ a [genconv↑] b ∷ F ^ [ rF , ι lF ]
      → Γ ⊢ f ∘ a ^ lΠ ~ g ∘ b ^ lΠ ∷ G [ a ] ^ [ ! , ι lG ]
~-app {rF = !} (↑ A≡B (~↑! x)) x₁ =
  let _ , ⊢B = syntacticEq A≡B
      B′ , whnfB′ , D = whNorm ⊢B
      ΠFG≡B′ = trans A≡B (subset* (red D))
      H , E , B≡ΠHE = Π≡A ΠFG≡B′ whnfB′
      F≡H , _ , _ , _ , G≡E = injectivity (PE.subst (λ x → _ ⊢ _ ≡ x ^ _) B≡ΠHE ΠFG≡B′)
      _ , ⊢f , _ = syntacticEqTerm (soundnessConv↑Term x₁)
  in  ↑ (substTypeEq G≡E (refl ⊢f))
        (app-cong′  (PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _)
                       B≡ΠHE ([~] _ (red D) whnfB′ x))
             (convConvTerm x₁ F≡H))
~-app {rF = %} (↑ A≡B (~↑! x)) x₁ =
  let _ , ⊢B = syntacticEq A≡B
      B′ , whnfB′ , D = whNorm ⊢B
      ΠFG≡B′ = trans A≡B (subset* (red D))
      H , E , B≡ΠHE = Π≡A ΠFG≡B′ whnfB′
      F≡H , _ , _ , _ , G≡E = injectivity (PE.subst (λ x → _ ⊢ _ ≡ x ^ _) B≡ΠHE ΠFG≡B′)
      _ , ⊢f , _ = syntacticEqTerm (proj₂ (proj₂ (soundness~↑% x₁)))
  in  ↑ (substTypeEq G≡E (genRefl ⊢f))
        (app-cong′ (PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _)
                       B≡ΠHE ([~] _ (red D) whnfB′ x))
                   (conv~↑% x₁ F≡H))
~-natrec : ∀ {z z′ s s′ n n′ F F′ Γ lF}
         → (Γ ∙ ℕ ^ [ ! , ι ⁰ ]) ⊢ F [conv↑] F′ ^ [ ! , ι lF ]  →
      Γ ⊢ z [conv↑] z′ ∷ (F [ zero ]) ^ ι lF →
      Γ ⊢ s [conv↑] s′ ∷ (Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° lF ▹▹ F [ suc (var 0) ]↑ ° lF ° lF ^ !) ° lF ° lF ^ !) ^ ι lF →
      Γ ⊢ n ~ n′ ∷ ℕ ^ [ ! , ι ⁰ ] →
      Γ ⊢ natrec lF F z s n ~ natrec lF F′ z′ s′ n′ ∷ (F [ n ]) ^ [ ! , ι lF ]
~-natrec {n = n} {n′ = n′} x x₁ x₂ (↑ A≡B (~↑! x₄)) =
  let _ , ⊢B = syntacticEq A≡B
      B′ , whnfB′ , D = whNorm ⊢B
      ℕ≡B′ = trans A≡B (subset* (red D))
      B≡ℕ = ℕ≡A ℕ≡B′ whnfB′
      k~l′ = PE.subst (λ x → _ ⊢ n ~ n′ ↓! x ^ _) B≡ℕ
                      ([~] _ (red D) whnfB′ x₄)
      ⊢F , _ = syntacticEq (soundnessConv↑ x)
      _ , ⊢n , _ = syntacticEqTerm (soundness~↓! k~l′)
  in  ↑ (refl (substType ⊢F ⊢n)) (natrec-cong′ x x₁ x₂ k~l′)


~-Emptyrec : ∀ {e e' F F′ Γ l}
         → Γ ⊢ F [conv↑] F′ ^ [ ! , ι l ] →
         Γ ⊢ e ∷ sEmpty ^ [ % , ι ⁰ ] →
         Γ ⊢ e' ∷ sEmpty ^ [ % , ι ⁰ ] →
         Γ ⊢ Emptyrec l ⁰ F e ~ Emptyrec l ⁰ F′ e' ∷ F ^ [ ! , ι l ]
~-Emptyrec {e = e} {e' = e'} x ⊢e ⊢e' =
  let k~l′ = %~↑ ⊢e ⊢e'
      ⊢F , _ = syntacticEq (soundnessConv↑ x)
  in  ↑ (refl ⊢F) (Emptyrec-cong′ x k~l′)

~-IdCong : ∀ {A A' : Term} {l : Level} {t t' u u' : Term} {Γ : Con Term} →
      Γ ⊢ A ~ A' ∷ Univ ! l ^ [ ! , next l ] →
      Γ ⊢ t [conv↑] t' ∷ A ^ ι l →
      Γ ⊢ u [conv↑] u' ∷ A ^ ι l →
      Γ ⊢ Id A t u ~ Id A' t' u' ∷ SProp ^ [ ! , next ⁰ ]
~-IdCong (↑ A≡B (~↑! x)) t~t' u~u' =
     let ⊢Γ = wfEqTerm (soundnessConv↑Term t~t')
         _ , ⊢B = syntacticEq A≡B
         B′ , whnfB′ , D = whNorm ⊢B
         U≡B′ = trans A≡B (subset* (red D))
         B≡U = U≡A-whnf U≡B′ whnfB′
         A~A′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) B≡U
                      ([~] _ (red D) whnfB′ x)
     in ↑ (refl (Ugenⱼ ⊢Γ)) (~↑! (Id-cong A~A′ t~t' u~u'))

~-Idℕ : ∀ {t t' u u' : Term} {Γ : Con Term} →
    ⊢ Γ →
    Γ ⊢ t ~ t' ∷ ℕ ^ [ ! , ι ⁰ ] →
    Γ ⊢ u [genconv↑] u' ∷ ℕ ^ [ ! , ι ⁰ ] →
    Γ ⊢ Id ℕ t u ~ Id ℕ t' u' ∷ SProp ^ [ ! , next ⁰ ]
~-Idℕ ⊢Γ (↑ A≡B (~↑! x)) u~u' =
     let _ , ⊢B = syntacticEq A≡B
         B′ , whnfB′ , D = whNorm ⊢B
         ℕ≡B′ = trans A≡B (subset* (red D))
         B≡ℕ = ℕ≡A ℕ≡B′ whnfB′
         t~t′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) B≡ℕ
                      ([~] _ (red D) whnfB′ x)
     in ↑ (refl (Ugenⱼ ⊢Γ)) (~↑! (Id-ℕ t~t′ u~u'))

~-Idℕ0 : ∀ {u u' : Term} {Γ : Con Term} →
    ⊢ Γ →
    Γ ⊢ u ~ u' ∷ ℕ ^ [ ! , ι ⁰ ] →
    Γ ⊢ Id ℕ zero u ~ Id ℕ zero u' ∷ SProp ^ [ ! , next ⁰ ]
~-Idℕ0 ⊢Γ (↑ A≡B (~↑! x)) =
     let _ , ⊢B = syntacticEq A≡B
         B′ , whnfB′ , D = whNorm ⊢B
         ℕ≡B′ = trans A≡B (subset* (red D))
         B≡ℕ = ℕ≡A ℕ≡B′ whnfB′
         t~t′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) B≡ℕ
                      ([~] _ (red D) whnfB′ x)
     in ↑ (refl (Ugenⱼ ⊢Γ)) (~↑! (Id-ℕ0 t~t′))

~-IdℕS : ∀ {t t' u u' : Term} {Γ : Con Term} →
    ⊢ Γ →
    Γ ⊢ t [genconv↑] t' ∷ ℕ ^ [ ! , ι ⁰ ] →
    Γ ⊢ u ~ u' ∷ ℕ ^ [ ! , ι ⁰ ] →
    Γ ⊢ Id ℕ (suc t) u ~ Id ℕ (suc t') u' ∷ SProp ^ [ ! , next ⁰ ]
~-IdℕS ⊢Γ X (↑ A≡B (~↑! x)) =
     let _ , ⊢B = syntacticEq A≡B
         B′ , whnfB′ , D = whNorm ⊢B
         ℕ≡B′ = trans A≡B (subset* (red D))
         B≡ℕ = ℕ≡A ℕ≡B′ whnfB′
         t~t′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) B≡ℕ
                      ([~] _ (red D) whnfB′ x)
     in ↑ (refl (Ugenⱼ ⊢Γ)) (~↑! (Id-ℕS X t~t′))

~-IdU : ∀ {t t' u u' : Term} {Γ : Con Term} →
    ⊢ Γ →
    Γ ⊢ t ~ t' ∷ U ⁰ ^ [ ! , next ⁰ ] →
    Γ ⊢ u [genconv↑] u' ∷ U ⁰ ^ [ ! , next ⁰ ] →
    Γ ⊢ Id (U ⁰) t u ~ Id (U ⁰) t' u' ∷ SProp ^ [ ! , next ⁰ ]
~-IdU ⊢Γ (↑ A≡B (~↑! x)) X =
     let _ , ⊢B = syntacticEq A≡B
         B′ , whnfB′ , D = whNorm ⊢B
         U≡B′ = trans A≡B (subset* (red D))
         B≡U = U≡A-whnf U≡B′ whnfB′
         t~t′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) B≡U
                      ([~] _ (red D) whnfB′ x)
     in ↑ (refl (Ugenⱼ ⊢Γ)) (~↑! (Id-U t~t′ X))

~-IdUℕ : ∀ {u u' : Term} {Γ : Con Term} →
    ⊢ Γ →
    Γ ⊢ u ~ u' ∷ U ⁰ ^ [ ! , next ⁰ ] →
    Γ ⊢ Id (U ⁰) ℕ u ~ Id (U ⁰) ℕ u' ∷ SProp ^ [ ! , next ⁰ ]
~-IdUℕ ⊢Γ (↑ A≡B (~↑! x)) =
     let _ , ⊢B = syntacticEq A≡B
         B′ , whnfB′ , D = whNorm ⊢B
         U≡B′ = trans A≡B (subset* (red D))
         B≡U = U≡A-whnf U≡B′ whnfB′
         t~t′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) B≡U
                      ([~] _ (red D) whnfB′ x)
     in ↑ (refl (Ugenⱼ ⊢Γ)) (~↑! (Id-Uℕ t~t′))

~-IdUΠ : ∀ {A : Term} {rA : Relevance} {B A' B' u u' : Term}
    {Γ : Con Term} →
    Γ ⊢ Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ ! [genconv↑] Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ [ ! , next ⁰ ] →
    Γ ⊢ u ~ u' ∷ U ⁰ ^ [ ! , next ⁰ ] →
    Γ ⊢ Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) u ~
    Id (U ⁰) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ !) u' ∷ SProp ^ [ ! , next ⁰ ]
~-IdUΠ X (↑ A≡B (~↑! x)) =
     let ⊢Γ =  wfEqTerm (soundnessConv↑Term X)
         _ , ⊢B = syntacticEq A≡B
         B′ , whnfB′ , D = whNorm ⊢B
         U≡B′ = trans A≡B (subset* (red D))
         B≡U = U≡A-whnf U≡B′ whnfB′
         t~t′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) B≡U
                      ([~] _ (red D) whnfB′ x)
     in ↑ (refl (Ugenⱼ ⊢Γ)) (~↑! (Id-UΠ X t~t′))

~-castcong : ∀ {A A' B B' e e' t t' : Term} {Γ : Con Term} →
    Γ ⊢ A ~ A' ∷ U ⁰ ^ [ ! , next ⁰ ] →
    Γ ⊢ B ~ B' ∷ U ⁰ ^ [ ! , next ⁰ ] →
    Γ ⊢ t ~ t' ∷ A ^ [ ! , ι ⁰ ] → 
    Γ ⊢ e ∷ Id (U ⁰) A B ^ [ % , ι ⁰ ] →
    Γ ⊢ e' ∷ Id (U ⁰) A' B' ^ [ % , ι ⁰ ] →
    Γ ⊢ cast ⁰ A B e t ~ cast ⁰ A' B' e' t' ∷ B ^ [ ! , ι ⁰ ]
~-castcong (↑ A≡B (~↑! x)) (↑ A≡B' (~↑! x')) (↑ T≡U (~↑! t<>u)) ⊢e ⊢e' =
     let _ , ⊢B' = syntacticEq A≡B
         X , eqX , x'' = sym~↑! (reflConEq (wf ⊢B')) x'
         ⊢BU , _ , ⊢B   = syntacticEqTerm (soundness~↑! x'')
         B′ , whnfB′ , D = whNorm ⊢B'
         U≡B′ = trans A≡B (subset* (red D))
         B≡U = U≡A-whnf U≡B′ whnfB′
         A≡B'' = trans A≡B' eqX
         t~t′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) B≡U
                      ([~] _ (red D) whnfB′ x)
         BU′ , whnfBU′ , D' = whNorm ⊢BU
         U≡B' = trans A≡B'' (subset* (red D'))
         B≡U' = U≡A-whnf U≡B' whnfBU′
         u~u = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) B≡U'
                        ([~] _ (red D') whnfBU′ x'')
         ⊢Bt , ⊢t , ⊢u = syntacticEqTerm (soundness~↑! t<>u)
         neA , _ = ne~↑! x
         Bt , whnfBt , Dt = whNorm ⊢Bt
     in ↑ (refl (univ (conv ⊢B (sym A≡B''))))
          (~↑! (cast-cong t~t′ u~u
                          (ne-ins (conv ⊢t (sym T≡U)) (conv ⊢u (sym T≡U)) neA ([~] _ (red Dt) whnfBt t<>u)) ⊢e ⊢e'))

~-castneℕ : ∀ {A A' e e' t t' : Term} {Γ : Con Term} →
    Γ ⊢ A ~ A' ∷ U ⁰ ^ [ ! , next ⁰ ] →
    Γ ⊢ t [genconv↑] t' ∷ A ^ [ ! , ι ⁰ ] →
    Γ ⊢ e ∷ Id (U ⁰) A ℕ ^ [ % , ι ⁰ ] →
    Γ ⊢ e' ∷ Id (U ⁰) A' ℕ ^ [ % , ι ⁰ ] →
    Γ ⊢ cast ⁰ A ℕ e t ~ cast ⁰ A' ℕ e' t' ∷ ℕ ^ [ ! , ι ⁰ ]
~-castneℕ (↑ A≡B (~↑! x)) t<>u ⊢e ⊢e' = 
     let _ , ⊢B' = syntacticEq A≡B
         B′ , whnfB′ , D = whNorm ⊢B'
         U≡B′ = trans A≡B (subset* (red D))
         B≡U = U≡A-whnf U≡B′ whnfB′
         t~t′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) B≡U
                      ([~] _ (red D) whnfB′ x)
     in ↑ (refl (univ (ℕⱼ (wf ⊢B')))) (~↑! (cast-neℕ t~t′ t<>u ⊢e ⊢e'))

~-castneΠ : ∀ {A A' P P' B B' : Term} {rB : Relevance} {e e' t t' : Term}
    {Γ : Con Term} →
    Γ ⊢ A ~ A' ∷ U ⁰ ^ [ ! , next ⁰ ] →
    Γ ⊢ Π B ^ rB ° ⁰ ▹ P ° ⁰ ° ⁰ ^ ! [genconv↑] Π B' ^ rB ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ [ ! , next ⁰ ] →
    Γ ⊢ t [genconv↑] t' ∷ A ^ [ ! , ι ⁰ ] →
    Γ ⊢ e ∷ Id (U ⁰) A (Π B ^ rB ° ⁰ ▹ P ° ⁰ ° ⁰ ^ !) ^ [ % , ι ⁰ ] →
    Γ ⊢ e' ∷ Id (U ⁰) A' (Π B' ^ rB ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ !) ^
    [ % , ι ⁰ ] →
    Γ ⊢ cast ⁰ A (Π B ^ rB ° ⁰ ▹ P ° ⁰ ° ⁰ ^ !) e t ~
    cast ⁰ A' (Π B' ^ rB ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ !) e' t' ∷
    Π B ^ rB ° ⁰ ▹ P ° ⁰ ° ⁰ ^ ! ^ [ ! , ι ⁰ ]
~-castneΠ (↑ A≡B (~↑! x)) Π<>Π t<>u ⊢e ⊢e' = 
     let _ , ⊢B' = syntacticEq A≡B
         B′ , whnfB′ , D = whNorm ⊢B'
         U≡B′ = trans A≡B (subset* (red D))
         B≡U = U≡A-whnf U≡B′ whnfB′
         t~t′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) B≡U
                      ([~] _ (red D) whnfB′ x)
         _ , ⊢Π , _ = syntacticEqTerm (soundnessConv↑Term Π<>Π)
     in ↑ (refl (univ ⊢Π))
          (~↑! (cast-neΠ Π<>Π t~t′ t<>u ⊢e ⊢e'))

~-cast-refl : ∀ {A B e t u : Term} {Γ : Con Term} →
    Γ ⊢ A ~ B ∷ U ⁰ ^ [ ! , next ⁰ ] →
    Γ ⊢ t ~ u ∷ A ^ [ ! , ι ⁰ ] →
    Γ ⊢ t ∷ A ^ [ ! , ι ⁰ ] →
    Γ ⊢ e ∷ Id (U ⁰) A B ^ [ % , ι ⁰ ] →
    Γ ⊢ cast ⁰ A B e t ~ u ∷ B ^ [ ! , ι ⁰ ]
~-cast-refl (↑ A≡B (~↑! x)) (↑ T≡U (~↑! t<>u)) ⊢t ⊢e =
     let _ , ⊢B' = syntacticEq A≡B
         B′ , whnfB′ , D = whNorm ⊢B'
         U≡B′ = trans A≡B (subset* (red D))
         B≡U = U≡A-whnf U≡B′ whnfB′
         t~t′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) B≡U
                      ([~] _ (red D) whnfB′ x)
         _ , _ , ⊢B   = syntacticEqTerm (soundness~↑! x)
         ⊢Bt , ⊢t , ⊢u = syntacticEqTerm (soundness~↑! t<>u)
         neA , _ = ne~↑! x
         Bt , whnfBt , Dt = whNorm ⊢Bt
     in ↑ (refl (univ (conv ⊢B (sym A≡B))))
          (~↑! (cast-refl t~t′ (ne-ins (conv ⊢t (sym T≡U)) (conv ⊢u (sym T≡U)) neA ([~] _ (red Dt) whnfBt t<>u)) ⊢e))

~-castℕ-refl : ∀ {e t u : Term} {Γ : Con Term} →
    Γ ⊢ t ~ u ∷ ℕ ^ [ ! , ι ⁰ ] →
    Γ ⊢ t ∷ ℕ ^ [ ! , ι ⁰ ] →
    Γ ⊢ e ∷ Id (U ⁰) ℕ ℕ ^ [ % , ι ⁰ ] →
    Γ ⊢ cast ⁰ ℕ ℕ e t ~ u ∷ ℕ ^ [ ! , ι ⁰ ]
~-castℕ-refl (↑ T≡U (~↑! t<>u)) ⊢t ⊢e =
     let ⊢Bt , ⊢t , ⊢u = syntacticEqTerm (soundness~↑! t<>u)
         Bt , whnfBt , Dt = whNorm ⊢Bt
     in ↑ (refl (univ (ℕⱼ (wfTerm ⊢t))))
          (~↑! (castℕ-refl (~atℕ (conv ⊢t (sym T≡U)) (_ , _ , [~] _ (red Dt) whnfBt t<>u)) ⊢e)) 

~-castℕ : ∀ {B B' e e' t t' : Term} {Γ : Con Term} →
    ⊢ Γ →
    Γ ⊢ B ~ B' ∷ U ⁰ ^ [ ! , next ⁰ ] →
    Γ ⊢ t [genconv↑] t' ∷ ℕ ^ [ ! , ι ⁰ ] →
    Γ ⊢ e ∷ Id (U ⁰) ℕ B ^ [ % , ι ⁰ ] →
    Γ ⊢ e' ∷ Id (U ⁰) ℕ B' ^ [ % , ι ⁰ ] →
    Γ ⊢ cast ⁰ ℕ B e t ~ cast ⁰ ℕ B' e' t' ∷ B ^ [ ! , ι ⁰ ]
~-castℕ ⊢Γ (↑ A≡B (~↑! x)) X ⊢e ⊢e' =
     let _ , ⊢B' = syntacticEq A≡B
         B′ , whnfB′ , D = whNorm ⊢B'
         U≡B′ = trans A≡B (subset* (red D))
         B≡U = U≡A-whnf U≡B′ whnfB′
         t~t′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) B≡U
                      ([~] _ (red D) whnfB′ x)
         _ , ⊢B , _ = syntacticEqTerm (soundness~↓! t~t′)
     in ↑ (refl (univ ⊢B)) (~↑! (cast-ℕ t~t′ X ⊢e ⊢e'))

~-castℕℕ : ∀ {e e' t t' : Term} {Γ : Con Term} →
    ⊢ Γ →
    Γ ⊢ t ~ t' ∷ ℕ ^ [ ! , ι ⁰ ] →
    Γ ⊢ e ∷ Id (U ⁰) ℕ ℕ ^ [ % , ι ⁰ ] →
    Γ ⊢ e' ∷ Id (U ⁰) ℕ ℕ ^ [ % , ι ⁰ ] →
    Γ ⊢ cast ⁰ ℕ ℕ e t ~ cast ⁰ ℕ ℕ e' t' ∷ ℕ ^ [ ! , ι ⁰ ]
~-castℕℕ ⊢Γ (↑ A≡B (~↑! x)) ⊢e ⊢e' =
     let _ , ⊢B' = syntacticEq A≡B
         B′ , whnfB′ , D = whNorm ⊢B'
         ℕ≡B′ = trans A≡B (subset* (red D))
         B≡ℕ = ℕ≡A ℕ≡B′ whnfB′
         t~t′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) B≡ℕ
                      ([~] _ (red D) whnfB′ x)
         _ , ⊢B , _ = syntacticEqTerm (soundness~↓! t~t′)
     in ↑ (refl (univ (ℕⱼ ⊢Γ))) (~↑! (cast-ℕℕ t~t′ ⊢e ⊢e'))

~-castΠ : ∀ {A A' : Term} {rA : Relevance} {P P' B B' e e' t t' : Term}
    {Γ : Con Term} →
    Γ ⊢ Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰ ^ ! [genconv↑] Π A' ^ rA ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ [ ! , next ⁰ ] →
    Γ ⊢ B ~ B' ∷ U ⁰ ^ [ ! , next ⁰ ] →
    Γ ⊢ t [genconv↑] t' ∷ Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰  ^ ! ^ [ ! , ι ⁰ ] →
    Γ ⊢ e ∷ Id (U ⁰) (Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰ ^ !) B ^ [ % , ι ⁰ ] →
    Γ ⊢ e' ∷ Id (U ⁰) (Π A' ^ rA ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ !) B' ^ [ % , ι ⁰ ] →
    Γ ⊢ cast ⁰ (Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰ ^ !) B e t ~ cast ⁰ (Π A' ^ rA ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ !) B' e' t' ∷ B ^ [ ! , ι ⁰ ]
~-castΠ X (↑ A≡B (~↑! x)) Y ⊢e ⊢e' =
     let _ , ⊢B' = syntacticEq A≡B
         B′ , whnfB′ , D = whNorm ⊢B'
         U≡B′ = trans A≡B (subset* (red D))
         B≡U = U≡A-whnf U≡B′ whnfB′
         t~t′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓! x ^ _) B≡U
                      ([~] _ (red D) whnfB′ x)
         _ , ⊢B , _ = syntacticEqTerm (soundness~↓! t~t′)
     in ↑ (refl (univ ⊢B)) (~↑! (cast-Π X t~t′ Y ⊢e ⊢e'))

~-castℕΠ : ∀ {A A' : Term} {rA : Relevance} {P P' e e' t t' : Term}
    {Γ : Con Term} →
    Γ ⊢ A ∷ Univ rA ⁰ ^ [ ! , next ⁰ ] →
    (Γ ∙ A ^ [ rA , ι ⁰ ]) ⊢ P ∷ U ⁰ ^ [ ! , next ⁰ ] →
    Γ ⊢ Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰ ^ ! [genconv↑] Π A' ^ rA ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ [ ! , next ⁰ ] →
    Γ ⊢ t [genconv↑] t' ∷ ℕ ^ [ ! , ι ⁰ ] →
    Γ ⊢ e ∷ Id (U ⁰) ℕ (Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰ ^ !) ^ [ % , ι ⁰ ] →
    Γ ⊢ e' ∷ Id (U ⁰) ℕ (Π A' ^ rA ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ !) ^ [ % , ι ⁰ ] →
    Γ ⊢ cast ⁰ ℕ (Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰ ^ !) e t ~ cast ⁰ ℕ (Π A' ^ rA ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ !) e' t' ∷
    Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰ ^ ! ^ [ ! , ι ⁰ ]
~-castℕΠ ⊢A ⊢P X Y ⊢e ⊢e' = ↑ (refl (univ (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ ⊢A ▹ ⊢P))) (~↑! (cast-ℕΠ X Y ⊢e ⊢e'))

~-castΠℕ : ∀ {A A' : Term} {rA : Relevance} {P P' e e' t t' : Term}
    {Γ : Con Term} →
    Γ ⊢ A ∷ Univ rA ⁰ ^ [ ! , next ⁰ ] →
    (Γ ∙ A ^ [ rA , ι ⁰ ]) ⊢ P ∷ U ⁰ ^ [ ! , next ⁰ ] →
    Γ ⊢ Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰ ^ ! [genconv↑] Π A' ^ rA ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ !
    ∷ U ⁰ ^ [ ! , next ⁰ ] →
    Γ ⊢ t [genconv↑] t' ∷ Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰ ^ ! ^ [ ! , ι ⁰ ] →
    Γ ⊢ e ∷ Id (U ⁰) (Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰ ^ !) ℕ ^ [ % , ι ⁰ ] →
    Γ ⊢ e' ∷ Id (U ⁰) (Π A' ^ rA ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ !) ℕ ^ [ % , ι ⁰ ] →
    Γ ⊢ cast ⁰ (Π A ^ rA ° ⁰ ▹ P ° ⁰ ° ⁰ ^ !) ℕ e t ~
    cast ⁰ (Π A' ^ rA ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ !) ℕ e' t' ∷ ℕ ^ [ ! , ι ⁰ ]
~-castΠℕ ⊢A ⊢P X Y ⊢e ⊢e' = ↑ (refl (univ (ℕⱼ (wfTerm ⊢A)))) (~↑! (cast-Πℕ X Y ⊢e ⊢e'))

~-castΠΠ%! : ∀ {A A' P P' B B' Q Q' e e' t t' : Term} {Γ : Con Term} →
    Γ ⊢ A ∷ Univ % ⁰ ^ [ ! , next ⁰ ] →
    (Γ ∙ A ^ [ % , ι ⁰ ]) ⊢ P ∷ U ⁰ ^ [ ! , next ⁰ ] →
    Γ ⊢ Π A ^ % ° ⁰ ▹ P ° ⁰ ° ⁰ ^ ! [genconv↑] Π A' ^ % ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ [ ! , next ⁰ ] →
    Γ ⊢ B ∷ Univ ! ⁰ ^ [ ! , next ⁰ ] →
    (Γ ∙ B ^ [ ! , ι ⁰ ]) ⊢ Q ∷ U ⁰ ^ [ ! , next ⁰ ] →
    Γ ⊢ Π B ^ ! ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ ! [genconv↑] Π B' ^ ! ° ⁰ ▹ Q' ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ [ ! , next ⁰ ] →
    Γ ⊢ t [genconv↑] t' ∷ Π A ^ % ° ⁰ ▹ P ° ⁰ ° ⁰ ^ ! ^ [ ! , ι ⁰ ] →
    Γ ⊢ e  ∷ Id (U ⁰) (Π A ^ % ° ⁰ ▹ P ° ⁰ ° ⁰ ^ !) (Π B ^ ! ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ !) ^ [ % , ι ⁰ ] →
    Γ ⊢ e' ∷ Id (U ⁰) (Π A' ^ % ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ !) (Π B' ^ ! ° ⁰ ▹ Q' ° ⁰ ° ⁰ ^ !) ^ [ % , ι ⁰ ] →
    Γ ⊢ cast ⁰ (Π A ^ % ° ⁰ ▹ P ° ⁰ ° ⁰ ^ !) (Π B ^ ! ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ !) e t ~
        cast ⁰ (Π A' ^ % ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ !) (Π B' ^ ! ° ⁰ ▹ Q' ° ⁰ ° ⁰ ^ !) e' t' ∷ Π B ^ ! ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ ! ^ [ ! , ι ⁰ ]
~-castΠΠ%! ⊢A ⊢P X ⊢B ⊢Q Y t~t' ⊢e ⊢e' = ↑ (refl (univ (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ ⊢B ▹ ⊢Q)))
                                           (~↑! (cast-ΠΠ%! X Y t~t' ⊢e ⊢e'))

~-castΠΠ!% : ∀ {A A' P P' B B' Q Q' e e' t t' : Term} {Γ : Con Term} →
    Γ ⊢ A ∷ Univ ! ⁰ ^ [ ! , next ⁰ ] →
    (Γ ∙ A ^ [ ! , ι ⁰ ]) ⊢ P ∷ U ⁰ ^ [ ! , next ⁰ ] →
    Γ ⊢ Π A ^ ! ° ⁰ ▹ P ° ⁰ ° ⁰ ^ ! [genconv↑] Π A' ^ ! ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ [ ! , next ⁰ ] →
    Γ ⊢ B ∷ Univ % ⁰ ^ [ ! , next ⁰ ] →
    (Γ ∙ B ^ [ % , ι ⁰ ]) ⊢ Q ∷ U ⁰ ^ [ ! , next ⁰ ] →
    Γ ⊢ Π B ^ % ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ ! [genconv↑] Π B' ^ % ° ⁰ ▹ Q' ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ [ ! , next ⁰ ] →
    Γ ⊢ t [genconv↑] t' ∷ Π A ^ ! ° ⁰ ▹ P ° ⁰ ° ⁰ ^ ! ^ [ ! , ι ⁰ ] →
    Γ ⊢ e  ∷ Id (U ⁰) (Π A ^ ! ° ⁰ ▹ P ° ⁰ ° ⁰ ^ !) (Π B ^ % ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ !) ^ [ % , ι ⁰ ] →
    Γ ⊢ e' ∷ Id (U ⁰) (Π A' ^ ! ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ !) (Π B' ^ % ° ⁰ ▹ Q' ° ⁰ ° ⁰ ^ !) ^ [ % , ι ⁰ ] →
    Γ ⊢ cast ⁰ (Π A ^ ! ° ⁰ ▹ P ° ⁰ ° ⁰ ^ !) (Π B ^ % ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ !) e t ~
        cast ⁰ (Π A' ^ ! ° ⁰ ▹ P' ° ⁰ ° ⁰ ^ !) (Π B' ^ % ° ⁰ ▹ Q' ° ⁰ ° ⁰ ^ !) e' t' ∷ Π B ^ % ° ⁰ ▹ Q ° ⁰ ° ⁰ ^ ! ^ [ ! , ι ⁰ ]
~-castΠΠ!% ⊢A ⊢P X ⊢B ⊢Q Y t~t' ⊢e ⊢e' = ↑ (refl (univ (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ ⊢B ▹ ⊢Q)))
                                           (~↑! (cast-ΠΠ!% X Y t~t' ⊢e ⊢e'))

~-sym : {k l A : Term} {r : TypeInfo} {Γ : Con Term} → Γ ⊢ k ~ l ∷ A ^ r → Γ ⊢ l ~ k ∷ A ^ r
~-sym (↑ A≡B x) =
  let ⊢Γ = wfEq A≡B
      B , A≡B′ , l~k = sym~↑ (reflConEq ⊢Γ) x
  in  ↑ (trans A≡B A≡B′) l~k

~-trans : {k l m A : Term} {r : TypeInfo} {Γ : Con Term}
        → Γ ⊢ k ~ l ∷ A ^ r → Γ ⊢ l ~ m ∷ A ^ r
        → Γ ⊢ k ~ m ∷ A ^ r
~-trans (↑ x (~↑! x₁)) (↑ x₂ (~↑! x₃)) =
  let ⊢Γ = wfEq x
      C , k~m , eAC = trans~↑!-simpl x₁ x₃
  in  ↑ (trans x eAC) (~↑! k~m)
~-trans (↑ x (~↑% x₁)) (↑ x₂ (~↑% x₃)) =
  let ⊢Γ = wfEq x
      k~m = trans~↑% (reflConEq ⊢Γ) x₁ (conv~↑% x₃ (trans (sym x₂) x))
  in  ↑ x (~↑% k~m)

~-wk : {k l A : Term} {r : TypeInfo} {ρ : Wk} {Γ Δ : Con Term} →
      ρ ∷ Δ ⊆ Γ →
      ⊢ Δ → Γ ⊢ k ~ l ∷ A ^ r → Δ ⊢ wk ρ k ~ wk ρ l ∷ wk ρ A ^ r
~-wk x x₁ (↑ x₂ x₃) = ↑ (wkEq x x₁ x₂) (wk~↑ x x₁ x₃)


~-conv : {k l A B : Term} {r : TypeInfo} {Γ : Con Term} →
      Γ ⊢ k ~ l ∷ A ^ r → Γ ⊢ A ≡ B ^ r → Γ ⊢ k ~ l ∷ B ^ r
~-conv (↑ x x₁) x₂ = ↑ (trans (sym x₂) x) x₁

~-to-conv : {k l A : Term} {Γ : Con Term} {r : TypeInfo} →
      Γ ⊢ k ~ l ∷ A ^ r →  Γ ⊢ k [genconv↑] l ∷ A ^ r
~-to-conv {r = [ ! , ll ]} (↑ x x₁) = convConvTerm (lift~toConv↑ x₁) (sym x)
~-to-conv {r = [ % , ll ]} (↑ x (~↑% x₁)) = conv~↑% x₁ (sym x)

un-univConv : ∀ {A B : Term} {r : Relevance} {l : Level} {Γ : Con Term} →
                Γ ⊢ A [conv↑] B ^ [ r , ι l ] →
                Γ ⊢ A [conv↑] B ∷ Univ r l ^ next l
un-univConv {A} {B} {r} {l} ([↑] A′ B′ D D′ whnfA′ whnfB′ (univ x)) =
            let ⊢Γ = wfEqTerm (soundnessConv↓Term x)
            in [↑]ₜ (Univ r l) A′ B′ (id (Ugenⱼ ⊢Γ)) (un-univ⇒* D) (un-univ⇒* D′) Uₙ whnfA′ whnfB′ x


Πₜ-cong : ∀ {F G H E rF rG lF lG lΠ Γ}
        → (rG PE.≡ ! → lF ≤ lΠ × lG ≤ lΠ)
        → (rG PE.≡ % → lG PE.≡ ⁰ × lΠ PE.≡ ⁰)
        → Γ ⊢ F ^ [ rF , ι lF ]
        → Γ ⊢ F [conv↑] H ∷ Univ rF lF ^ next lF
        → Γ ∙ F ^ [ rF , ι lF ] ⊢ G [conv↑] E ∷ Univ rG lG ^ next lG
        → Γ ⊢ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ rG [conv↑] Π H ^ rF ° lF ▹ E ° lG ° lΠ ^ rG ∷ Univ rG lΠ ^ next lΠ
Πₜ-cong lF< lG< x x₁ x₂ = liftConvTerm (Π-cong PE.refl PE.refl PE.refl PE.refl lF< lG< x x₁ x₂)

~-irrelevance : {k l A : Term} {Γ : Con Term} {ll : TypeLevel}
               → Γ ⊢ k ∷ A ^ [ % , ll ]
               → Γ ⊢ l ∷ A ^ [ % , ll ]
               → Γ ⊢ k ~ l ∷ A ^ [ % , ll ]
~-irrelevance ⊢k ⊢l =
  let X = ~↑% (%~↑ ⊢k ⊢l)
      ⊢A  = syntacticTerm ⊢k
  in ↑ (refl ⊢A) X

soundnessgenConv : ∀ {a b A r Γ} → Γ ⊢ a [genconv↑] b ∷ A ^ r → Γ ⊢ a ≡ b ∷ A ^ r
soundnessgenConv {r = [ ! , l ]} = soundnessConv↑Term
soundnessgenConv {r = [ % , l ]} x = proj₂ (proj₂ (soundness~↑% x))

symgenConv : ∀ {t u A r Γ} → Γ ⊢ t [genconv↑] u ∷ A ^ r → Γ ⊢ u [genconv↑] t ∷ A ^ r
symgenConv {r = [ ! , l ]} = symConvTerm
symgenConv {r = [ % , l ]} t<>u = let ⊢Γ = wfEqTerm (proj₂ (proj₂ (soundness~↑% t<>u)))
                          in  sym~↑% (reflConEq ⊢Γ) t<>u

wkgenConv↑Term : ∀ {ρ t u A Γ r Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) → ⊢ Δ
             → Γ ⊢ t [genconv↑] u ∷ A ^ r
             → Δ ⊢ wk ρ t [genconv↑] wk ρ u ∷ wk ρ A ^ r
wkgenConv↑Term {r = [ ! , l ]} = wkConv↑Term
wkgenConv↑Term {r = [ % , l ]} = wk~↑%

convgenconv : ∀ {t u A B : Term} {r : TypeInfo} {Γ : Con Term} →
      Γ ⊢ t [genconv↑] u ∷ A ^ r →
      Γ ⊢ A ≡ B ^ r → Γ ⊢ t [genconv↑] u ∷ B ^ r
convgenconv {r = [ ! , l ]} = convConvTerm
convgenconv {r = [ % , l ]} = conv~↑%

transgenConv : ∀ {t u v A : Term} {r : TypeInfo} {Γ : Con Term} →
      Γ ⊢ t [genconv↑] u ∷ A ^ r →
      Γ ⊢ u [genconv↑] v ∷ A ^ r → Γ ⊢ t [genconv↑] v ∷ A ^ r
transgenConv {r = [ ! , l ]} = transConvTerm
transgenConv {r = [ % , l ]} = trans~↑!Term


-- Algorithmic equality instance of the generic equality relation.
instance eqRelInstance : EqRelSet
eqRelInstance = eqRel _⊢_[conv↑]_^_ _⊢_[genconv↑]_∷_^_ _⊢_~_∷_^_
                      ~-to-conv soundnessConv↑ soundnessgenConv
                      univConv↑ un-univConv
                      symConv symgenConv ~-sym
                      transConv transgenConv ~-trans
                      convgenconv ~-conv
                      wkConv↑ wkgenConv↑Term ~-wk
                      reductionConv↑ reductionConv↑Term
                      (liftConv ∘ᶠ (U-refl PE.refl)) ( liftConvTerm ∘ᶠ  (U-refl PE.refl))
                      (liftConvTerm ∘ᶠ ℕ-refl)
                      (liftConvTerm ∘ᶠ Empty-refl)
                      Πₜ-cong
                      (λ x x₁ x₂ → liftConvTerm (∃-cong x x₁ x₂))
                      (liftConvTerm ∘ᶠ zero-refl)
                      (liftConvTerm ∘ᶠ suc-cong)
                      (λ l< l<' x x₁ x₂ x₃ x₄ x₅ → liftConvTerm (η-eq l< l<' x x₁ x₂ x₃ x₄ x₅))
                      ~-var ~-app ~-natrec ~-Emptyrec
                      ~-IdCong ~-Idℕ ~-Idℕ0 ~-IdℕS ~-IdU ~-IdUℕ ~-IdUΠ
                      ~-castcong ~-castneℕ ~-castneΠ ~-cast-refl ~-castℕ-refl
                      ~-castℕ ~-castℕℕ ~-castΠ ~-castℕΠ ~-castΠℕ ~-castΠΠ%! ~-castΠΠ!%
                      ~-irrelevance
