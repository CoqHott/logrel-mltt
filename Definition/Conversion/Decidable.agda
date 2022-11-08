-- {-# OPTIONS --safe #-}
{-# OPTIONS --allow-unsolved-metas #-}

module Definition.Conversion.Decidable where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed as T
open import Definition.Typed.Properties
open import Definition.Conversion
open import Definition.Conversion.Whnf
open import Definition.Conversion.Soundness
open import Definition.Conversion.Symmetry
open import Definition.Conversion.Stability
open import Definition.Conversion.Conversion
open import Definition.Conversion.ConvSize
open import Definition.Conversion.Lift
open import Definition.Conversion.Transitivity
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
open import Definition.Conversion.Consequences.Completeness
open import Definition.Conversion.TransitivityHelper

open import Tools.Nat
open import Tools.Product
open import Tools.Empty
open import Tools.Nullary
import Tools.PropositionalEquality as PE


mutual
  -- Decidability of algorithmic equality of neutrals.
  dec~↑! : ∀ {n k l R T Γ Δ lR lT}
        → ⊢ Γ ≡ Δ
        → (e : Γ ⊢ k ~ k ↑! R ^ lR)
        → (e' : Δ ⊢ l ~ l ↑! T ^ lT)
        → (size~↑! e + size~↑! e') << n
        → Dec (∃ λ A → ∃ λ lA → Γ ⊢ k ~ l ↑! A ^ lA)

{-
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
      ⊢k₁′ = PE.subst₄ (λ X Y Z T → _ ⊢ _ ∷ Π _ ^ X ° Y ▹ _ ° Z ° T ^ ! ^ [ ! , ι T ]) rF≡rF′ lF≡lF′ lG≡lG′ (PE.sym l₂≡l₁) ⊢k₁
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

  dec~↑! Γ≡Δ (Emptyrec-cong {ll = l} F k) (Emptyrec-cong {ll = l₀} G k₀)
    with dec-level l l₀ 
  dec~↑! Γ≡Δ (Emptyrec-cong {ll = l} F k) (Emptyrec-cong {ll = .l} G k₀) | yes PE.refl 
    with decConv↑ Γ≡Δ F G
  dec~↑! Γ≡Δ (Emptyrec-cong {ll = l} F k) (Emptyrec-cong {ll = .l} G k₀) | yes PE.refl | yes p =
    let _ , ⊢k , _ = soundness~↑% k
        _ , ⊢k₀ , _ = soundness~↑% k₀
        ⊢Γ = wfTerm ⊢k
    in yes (_ , _ , Emptyrec-cong p (%~↑ ⊢k (stabilityTerm (symConEq Γ≡Δ) ⊢k₀)))
  dec~↑! Γ≡Δ (Emptyrec-cong {ll = l} F k) (Emptyrec-cong {ll = .l} G k₀) | yes PE.refl | no ¬p =
    no (λ { (_ , .(ι l) , Emptyrec-cong x x₁) → ¬p x })
  dec~↑! Γ≡Δ (Emptyrec-cong {ll = l} F k) (Emptyrec-cong {ll = l₀} G k₀) | no ¬p =
    no (λ { (_ , .(ι l) , Emptyrec-cong x x₁) → ¬p PE.refl })

  dec~↑! Γ≡Δ (Id-cong A t u) (Id-cong B v w) with dec~↓! Γ≡Δ A B
  ... | no ¬p = no λ { (.(SProp) , .(next _) , Id-cong x x₁ x₂) → ¬p (_ , _ , x) }
  ... | yes (M , lM , A~B) with decConv↑Term Γ≡Δ t (convert~ Γ≡Δ A B A~B v) | decConv↑Term Γ≡Δ u (convert~ Γ≡Δ A B A~B w)
  ... | yes tv | yes uw = yes (_ , _ , Id-cong (~atU A (M , lM , A~B)) tv uw)
  ... | yes tv | no ¬uw =
    no λ { (.(SProp) , .(next _) , Id-cong x x₁ x₂) →
      let
        whnfU , neA , neB = ne~↓! x
        ⊢U , ⊢A , ⊢B = syntacticEqTerm (soundness~↓! x)
        _ , ⊢A₂ , _ = syntacticEqTerm (soundness~↓! A)
        nl≡nl , U≡U = neTypeEq neA ⊢A ⊢A₂
      in ¬uw (PE.subst (λ X → _ ⊢ _ [conv↑] _ ∷ _ ^ ι X) (next-inj nl≡nl) x₂) }
  ... | no ¬tv | _ =
    no λ { (.(SProp) , .(next _) , Id-cong x x₁ x₂) →
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
-}

  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) eAB _) (cast-cong C D (ne-ins x₃ x₄ x₅ ([~] A₂ D₂ whnfB₁ k~l₁)) eCD _) (leS size)
             with dec~↓! Γ≡Δ A C (<<-trans (<=-help-id-cong {a = size~↓! A} {b = size~↓! C}) size) |
                  dec~↓! (symConEq Γ≡Δ) D B (<<-trans (<=-trans (≡-to-<= (+-sym (size~↓! D) (size~↓! B))) (<=-help-b'c' {a = size~↓! A} {b = size~↓! C})) size) |
                  dec~↓! (reflConEq (wfTerm eAB)) A B (<<-trans {!!} size) |
                  dec~↓! (reflConEq (wfTerm eCD)) C D (<<-trans {!!} size) 
  ... | _ | no ¬BD | _ | _ = no λ { (_ , _ , X) → ¬BD (U ⁰ , ι ¹ , ~atU D let _ , ⊢cast , ⊢cast' = syntacticEqTerm (soundness~↑! X)
                                                                              _ , _ , _ , _ , _ , R≡R , eqR , _ = inversion-cast ⊢cast
                                                                              _ , _ , _ , _ , _ , T≡T , eqT , _ = inversion-cast ⊢cast'
                                                                              eqR , _ = typeinfo-PE-injectivity eqR
                                                                              eqT , _ = typeinfo-PE-injectivity eqT
                                                                              T≡R = trans (sym (PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqT) T≡T))
                                                                                          (PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqR) R≡R)
                                                                              eq = completeEqNeutral (proj₁ (proj₂ (ne~↓! D))) (proj₁ (proj₂ (ne~↓! B)))
                                                                                                     (un-univ≡ (stabilityEq Γ≡Δ T≡R))
                                                                          in  _ , _ , eq) } 
  ... | yes (_ , _ , A~C) | yes (_ , _ , B~D) | yes (_ , _ , A~B) | _
        with decConv↓Term Γ≡Δ (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) (convert'~ Γ≡Δ A C A~C (ne-ins x₃ x₄ x₅ ([~] A₂ D₂ whnfB₁ k~l₁))) 
  ... | yes p = yes (_ , _ , cast-cong (~atU A (_ , _ , A~C)) (~atU (stability~↓! (symConEq Γ≡Δ) D) (_ , _ , stability~↓! (symConEq Γ≡Δ) B~D))
                                       p eAB (stabilityTerm (symConEq Γ≡Δ) eCD))
  ... | no ¬p = no λ { (_ , _ , X) → let whnfcast , whnfcast' = ne~↑! X
                                         cast≡cast = soundness~↑! X
                                         A≡B = soundness~↓! (~atU A (_ , _ , A~B))
                                         A≡C = soundness~↓! (~atU A (_ , _ , A~C))
                                         B≡D = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! (~atU D (_ , _ , B~D))))
                                         C≡D = trans (sym (univ A≡C)) (trans (univ A≡B) (sym B≡D))
                                         _ , ⊢cast , ⊢cast' = syntacticEqTerm cast≡cast
                                         _ , _ , _ , _ , ⊢t , R≡R , eqR , _ = inversion-cast ⊢cast
                                         _ , _ , _ , _ , _ , T≡T , eqT , _ = inversion-cast ⊢cast'
                                         eqR , el = typeinfo-PE-injectivity eqR
                                         eqT , _ = typeinfo-PE-injectivity eqT
                                         T≡T' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqT) T≡T
                                         R≡R' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqR) R≡R
                                         cast≡cast' = PE.subst (λ X →  _ ⊢ _ ≡ _ ∷ _ ^ [ ! , X ]) el cast≡cast
                                         ⊢t' = PE.subst (λ X →  _ ⊢ _ ∷ _ ^ [ X , _ ]) (PE.sym eqR) ⊢t
                                         neA = proj₁ (proj₂ (ne~↓! A))
                                         neB = proj₁ (proj₂ (ne~↓! B))
                                         neC = proj₁ (proj₂ (ne~↓! C))
                                         neD = proj₁ (proj₂ (ne~↓! D))
                                         net = castNeutralInv neA neB whnfcast
                                         neu = castNeutralInv neC neD whnfcast'                                        
                                     in ¬p (completeEqTerm↓ (ne neA) (ne net) (ne neu)
                                                            (trans (sym (conv (T.cast-refl A≡B eAB ⊢t') (sym (univ A≡B))))
                                                            (trans (conv cast≡cast' (trans R≡R' (sym (univ A≡B))))
                                                            (conv (T.cast-refl (un-univ≡ C≡D) (stabilityTerm (symConEq Γ≡Δ) eCD) (stabilityTerm (symConEq Γ≡Δ) x₃))
                                                                  (trans B≡D (sym (univ A≡B))))))) }
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) eAB _) (cast-cong C D (ne-ins x₃ x₄ x₅ ([~] A₂ D₂ whnfB₁ k~l₁)) eCD _) (leS size)
    | no ¬AC | yes B~D | yes A~B | yes C~D = no λ { (_ , _ , X) → ¬AC (let _ , _ , _ , D~B = sym~↓! (reflConEq (wfTerm eCD)) (~atU D B~D)
                                                                           _ , _ , A~D , _ = trans~↓!-simpl (~atU A A~B) (stability~↓! (symConEq Γ≡Δ) D~B)
                                                                           _ , _ , _ , D~C = sym~↓! (reflConEq (wfTerm eCD)) (~atU C C~D)
                                                                           _ , _ , A~C , _ = trans~↓!-simpl A~D (stability~↓! (symConEq Γ≡Δ) D~C)
                                                                       in _ , _ , A~C )}
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) eAB _) (cast-cong C D (ne-ins x₃ x₄ x₅ ([~] A₂ D₂ whnfB₁ k~l₁)) eCD _) (leS size)
    | yes A~C | yes B~D | no ¬AB | yes C~D = no λ { (_ , _ , X) → ¬AB (let _ , _ , A~D , _ = trans~↓!-simpl (~atU A A~C) (stability~↓! (symConEq Γ≡Δ) (~atU C C~D))
                                                                           _ , _ , A~B , _ = trans~↓!-simpl A~D (stability~↓! (symConEq Γ≡Δ) (~atU D B~D))
                                                                       in _ , _ , A~B )}
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) eAB _) (cast-cong C D (ne-ins x₃ x₄ x₅ ([~] A₂ D₂ whnfB₁ k~l₁)) eCD _) (leS size)
    | no ¬AC | yes (_ , _ , B~D) | no ¬AB | no ¬CD = no λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ¬AC (_ , _ , x) ;
                                                            (_ , _ , cast-refl x x₁ x₂) → ¬AB (_ , _ , x) ;
                                                            (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , _ , D~B = sym~↓! Γ≡Δ (~atU (stability~↓! (symConEq Γ≡Δ) D) (_ , _ , x))
                                                                                           in ¬CD (_ , _ , D~B)}
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) eAB _) (cast-cong C D (ne-ins x₃ x₄ x₅ ([~] A₂ D₂ whnfB₁ k~l₁)) eCD eCD') (leS size)
    | no ¬AC | yes B~D | yes A~B | no ¬CD
    with dec~↑! Γ≡Δ k~l (cast-cong C D (ne-ins x₃ x₄ x₅ ([~] A₂ D₂ whnfB₁ k~l₁)) eCD eCD') (<<-trans {!!} size)
  ... | yes (_ , _ , tu) = yes (_ , _ , let _ , _ , ⊢A , ⊢T , _  = inversion-Id (un-univ (syntacticTerm eCD))
                                            t≡cast = soundness~↑! tu
                                            ⊢K , _ , ⊢cast' = syntacticEqTerm t≡cast
                                            _ , ⊢A , ⊢B , _ , ⊢t , T≡T , eqT , _ = inversion-cast ⊢cast'
                                            eqT , el = typeinfo-PE-injectivity eqT
                                            neA = proj₁ (proj₂ (ne~↓! A))
                                            neB = proj₁ (proj₂ (ne~↓! B))
                                            neC = proj₁ (proj₂ (ne~↓! C))
                                            neD = proj₁ (proj₂ (ne~↓! D))
                                            _ , whnfD , dd = whNormTerm (un-univ (PE.subst (λ X →  _ ⊢ _ ^ [ ! , X ]) el ⊢K)) 
                                            A≡B = soundness~↓! (~atU A A~B)
                                            B≡D = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! (~atU D B~D)))
                                            in cast-refl (~atU A A~B) (ne-ins x₁ (conv (T.castⱼ (PE.subst (λ X →  _ ⊢ _ ∷ Univ X _ ^ _) (PE.sym eqT) ⊢A)
                                                                                                (PE.subst (λ X →  _ ⊢ _ ∷ Univ X _ ^ _) (PE.sym eqT) ⊢B)
                                                                                                (stabilityTerm (symConEq Γ≡Δ) eCD)
                                                                                                (PE.subst (λ X →  _ ⊢ _ ∷ _ ^ [ X , _ ]) (PE.sym eqT) ⊢t))
                                                                                       (trans B≡D (sym (univ A≡B))))
                                                                          neA ([~] _ (red (univ:⇒*: dd)) whnfD (PE.subst (λ X →  _ ⊢ _ ~ _ ↑! _ ^ X) el tu)))
                                                     eAB)
  ... | no ¬tu = no λ { (_ , _ , X) → let whnfcast , whnfcast' = ne~↑! X
                                          cast≡cast = soundness~↑! X
                                          A≡B = soundness~↓! (~atU A A~B)
                                          B≡D = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! (~atU D B~D)))
                                          _ , ⊢cast , ⊢cast' = syntacticEqTerm cast≡cast
                                          _ , _ , _ , _ , ⊢t , R≡R , eqR , _ = inversion-cast ⊢cast
                                          _ , _ , _ , _ , _ , T≡T , eqT , _ = inversion-cast ⊢cast'
                                          eqR , el = typeinfo-PE-injectivity eqR
                                          eqT , _ = typeinfo-PE-injectivity eqT
                                          T≡T' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqT) T≡T
                                          R≡R' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqR) R≡R
                                          cast≡cast' = PE.subst (λ X →  _ ⊢ _ ≡ _ ∷ _ ^ [ ! , X ]) el cast≡cast
                                          ⊢t' = PE.subst (λ X →  _ ⊢ _ ∷ _ ^ [ X , _ ]) (PE.sym eqR) ⊢t
                                          neA = proj₁ (proj₂ (ne~↓! A))
                                          neB = proj₁ (proj₂ (ne~↓! B))
                                          neC = proj₁ (proj₂ (ne~↓! C))
                                          neD = proj₁ (proj₂ (ne~↓! D))
                                          net = castNeutralInv neA neB whnfcast
                                          neu = castNeutralInv neC neD whnfcast'                                        
                                       in ¬tu (let _ , e' , _ = [conv↓]ne neA (completeEqTerm↓ (ne neA) (ne net) (ne (castₙ neC neD neu))
                                                                                               (trans (sym (conv (T.cast-refl A≡B eAB ⊢t') (sym (univ A≡B)) ))
                                                                                                      (conv cast≡cast' (trans R≡R' (sym (univ A≡B))))))
                                                   _ , e = neutral↓↑ e' in _ , _ , e) } 
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) eAB eAB') (cast-cong C D (ne-ins x₃ x₄ x₅ ([~] A₂ D₂ whnfB₁ k~l₁)) eCD _) (leS size)
    | no ¬AC | yes B~D | no ¬AB | yes C~D 
    with dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) eAB eAB') k~l₁ (<<-trans {!!} size)
  ... | yes (_ , _ , tu) = yes (_ , _ , let _ , _ , ⊢A , ⊢T , _  = inversion-Id (un-univ (syntacticTerm eCD))
                                            t≡cast = soundness~↑! tu
                                            ⊢K , ⊢cast , _ = syntacticEqTerm t≡cast
                                            _ , ⊢A , ⊢B , _ , ⊢t , T≡T , eqT , _ = inversion-cast ⊢cast
                                            eqT , el = typeinfo-PE-injectivity eqT
                                            neA = proj₁ (proj₂ (ne~↓! A))
                                            neB = proj₁ (proj₂ (ne~↓! B))
                                            neC = proj₁ (proj₂ (ne~↓! C))
                                            neD = proj₁ (proj₂ (ne~↓! D))
                                            _ , _ , _ , D~C = sym~↓! (symConEq Γ≡Δ) (~atU C C~D)
                                            _ , whnfD , dd = whNormTerm (un-univ (PE.subst (λ X →  _ ⊢ _ ^ [ ! , X ]) el ⊢K)) 
                                            C≡D = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! (~atU C C~D)))
                                            B≡D = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! (~atU D B~D)))
                                            in cast-refl' (~atU (stability~↓! (symConEq Γ≡Δ) D) (_ , _ , D~C))
                                                          (ne-ins (conv (T.castⱼ (PE.subst (λ X →  _ ⊢ _ ∷ Univ X _ ^ _) (PE.sym eqT) ⊢A)
                                                                                 (PE.subst (λ X →  _ ⊢ _ ∷ Univ X _ ^ _) (PE.sym eqT) ⊢B)
                                                                                 eAB
                                                                                 (PE.subst (λ X →  _ ⊢ _ ∷ _ ^ [ X , _ ]) (PE.sym eqT) ⊢t))
                                                                        (trans (sym B≡D) (sym C≡D)))
                                                                  (stabilityTerm (symConEq Γ≡Δ) x₃)
                                                                  neC ([~] _ (red (univ:⇒*: dd)) whnfD (PE.subst (λ X →  _ ⊢ _ ~ _ ↑! _ ^ X) el tu)))
                                                          (stabilityTerm (symConEq Γ≡Δ) eCD))
  ... | no ¬tu = no λ { (_ , _ , X) → let whnfcast , whnfcast' = ne~↑! X
                                          cast≡cast = soundness~↑! X
                                          C≡D = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! (~atU C C~D)))
                                          B≡D = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! (~atU D B~D)))
                                          _ , ⊢cast , ⊢cast' = syntacticEqTerm cast≡cast
                                          _ , _ , _ , _ , ⊢t , R≡R , eqR , _ = inversion-cast ⊢cast
                                          _ , _ , _ , _ , _ , T≡T , eqT , _ = inversion-cast ⊢cast'
                                          eqR , el = typeinfo-PE-injectivity eqR
                                          eqT , _ = typeinfo-PE-injectivity eqT
                                          T≡T' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqT) T≡T
                                          R≡R' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqR) R≡R
                                          cast≡cast' = PE.subst (λ X →  _ ⊢ _ ≡ _ ∷ _ ^ [ ! , X ]) el cast≡cast
                                          ⊢t' = PE.subst (λ X →  _ ⊢ _ ∷ _ ^ [ X , _ ]) (PE.sym eqR) ⊢t
                                          neA = proj₁ (proj₂ (ne~↓! A))
                                          neB = proj₁ (proj₂ (ne~↓! B))
                                          neC = proj₁ (proj₂ (ne~↓! C))
                                          neD = proj₁ (proj₂ (ne~↓! D))
                                          net = castNeutralInv neA neB whnfcast
                                          neu = castNeutralInv neC neD whnfcast'                                        
                                       in ¬tu (let _ , e' , _ = [conv↓]ne neB (completeEqTerm↓ (ne neB) (ne (castₙ neA neB net)) (ne neu)
                                                                                               (trans (conv cast≡cast' R≡R')
                                                                                                      (conv (T.cast-refl (un-univ≡ C≡D) (stabilityTerm (symConEq Γ≡Δ) eCD)
                                                                                                                         (stabilityTerm (symConEq Γ≡Δ) x₃))
                                                                                                            (trans (sym T≡T') R≡R'))))
                                                   _ , e = neutral↓↑ e' in _ , _ , e) } 
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) eAB _) (cast-cong C D (ne-ins x₃ x₄ x₅ ([~] A₂ D₂ whnfB₁ k~l₁)) eCD _) (leS size)
    | yes (_ , _ , A~C) | yes (_ , _ , B~D) | no ¬AB | no ¬CD
    with decConv↓Term Γ≡Δ (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) (convert'~ Γ≡Δ A C A~C (ne-ins x₃ x₄ x₅ ([~] A₂ D₂ whnfB₁ k~l₁))) 
  ... | yes p = yes (_ , _ , cast-cong (~atU A (_ , _ , A~C)) (~atU (stability~↓! (symConEq Γ≡Δ) D) (_ , _ , stability~↓! (symConEq Γ≡Δ) B~D))
                                       p eAB (stabilityTerm (symConEq Γ≡Δ) eCD))
  ... | no ¬p = no λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ¬p x₂ ;
                       (_ , _ , cast-refl x x₁ x₂) → ¬AB (_ , _ , x) ;
                       (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , _ , D~B = sym~↓! Γ≡Δ (~atU (stability~↓! (symConEq Γ≡Δ) D) (_ , _ , x))
                                                      in ¬CD (_ , _ , D~B) }

{- old version of cast-cong vs cast-cong

dec~↑! Γ≡Δ (cast-cong A B t eAB _) (cast-cong C D u eCD _)
    with dec~↓! Γ≡Δ A C | decConv↑Term Γ≡Δ B D
  ... | no ¬AC | _ = no λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ¬AC (_ , _ , x) }
  ... | yes AC | no ¬BD = no λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ¬BD x₁ }
  ... | yes (_ , _ , A~C) | yes BD with decConv↑Term Γ≡Δ t (convert~ Γ≡Δ A C A~C u)
  ... | yes p = yes (_ , _ , cast-cong (~atU A (_ , _ , A~C)) BD p eAB (stabilityTerm (symConEq Γ≡Δ) eCD))
  ... | no ¬p = no λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ¬p x₂ }
  
-}

{-

  dec~↑! Γ≡Δ (cast-ℕ A t eℕA _) (cast-ℕ B u eℕB _)
    with dec~↓! Γ≡Δ A B | decConv↑Term Γ≡Δ t u
  ... | yes AB | yes tu = yes (_ , _ , cast-ℕ (~atU A AB) tu eℕA (stabilityTerm (symConEq Γ≡Δ) eℕB))
  ... | yes AB | no ¬tu = no λ { (_ , _ , cast-ℕ x x₁ x₂ x₃) → ¬tu x₁ }
  ... | no ¬AB | _ = no λ { (_ , _ , cast-ℕ x x₁ x₂ x₃) → ¬AB (_ , _ , x) }


  dec~↑! Γ≡Δ (cast-ℕℕ t eℕℕ _) (cast-ℕℕ u eℕℕ′ _) with dec~↓! Γ≡Δ t u
  ... | yes tu = yes (_ , _ , cast-ℕℕ (~atℕ t tu) eℕℕ (stabilityTerm (symConEq Γ≡Δ) eℕℕ′))
  ... | no ¬tu = no λ { (_ , _ , cast-ℕℕ x x₁ x₂) → ¬tu (_ , _ , x) ;
                        (_ , _ , castℕ-refl x x₁) → let C , wC , tu , eqC = trans~↓!-simpl x ([~] ℕ (id (univ (ℕⱼ (wfTerm x₁)))) ℕₙ
                                                                                                  (castℕ-refl (stability~↓! (symConEq Γ≡Δ) u) (stabilityTerm (symConEq Γ≡Δ) eℕℕ′)))
                                                        eqℕ = ℕ≡A eqC wC
                                                    in ¬tu (_ , _ , PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ ι ⁰) eqℕ tu) ;
                        (_ , _ , castℕ-refl' x x₁) → let C , wC , tu , eqC = trans~↓!-simpl ([~] ℕ (id (univ (ℕⱼ (wfTerm x₁)))) ℕₙ (castℕ-refl' t eℕℕ)) x
                                                         eqℕ = ℕ≡A eqC wC
                                                     in ¬tu (_ , _ , PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ ι ⁰) eqℕ tu) }  
-}
{-
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

  -- antidiagonal cases
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (app-cong x~x t≡t) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (natrec-cong x x₁ x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (Emptyrec-cong x x₁) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (Id-cong x x₁ x₂) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (Id-ℕ x x₁) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (Id-ℕ0 x) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (Id-ℕS x x₁) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (Id-U x x₁) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (Id-Uℕ x) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (Id-UΠ x x₁) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (cast-cong x x₁ _ _ x₂ x₃ x₄) = {!!} -- no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (cast-ℕ x x₁ x₂ x₃) = {!!} -- no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (cast-ℕℕ x x₁ x₂) = {!!} -- no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (cast-Π x x₁ x₂ x₃ x₄) = {!!} -- no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (cast-Πℕ x x₁ x₂ x₃) = {!!} -- no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (cast-ℕΠ x x₁ x₂ x₃) = {!!} -- no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) = {!!} -- no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) = {!!} -- no (λ { (_ , ()) })
-}
  dec~↑! Γ≡Δ X Y = {!!} 

{-
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
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-cong x x₁ _ _ x₂ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ℕ x x₁ x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ℕℕ x x₁ x₂) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-Π x x₁ x₂ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-Πℕ x x₁ x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ℕΠ x x₁ x₂ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) = no (λ { (_ , ()) })

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
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (cast-cong x₄ x₅ _ _ x₆ x₇ x₈) = no (λ { (_ , ()) })
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
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (cast-cong x₂ x₃ _ _ x₄ x₅ x₆) = no (λ { (_ , ()) })
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
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (cast-cong x₃ x₄ _ _ x₅ x₆ x₇) = no (λ { (_ , ()) })
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
  dec~↑! Γ≡Δ (Id-ℕ x x₁) (cast-cong x₂ x₃ _ _ x₄ x₅ x₆) = no (λ { (_ , ()) })
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
  dec~↑! Γ≡Δ (Id-ℕ0 x) (cast-cong x₁ x₂ _ _ x₃ x₄ x₅) = no (λ { (_ , ()) })
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
  dec~↑! Γ≡Δ (Id-ℕS x x₁) (cast-cong x₂ x₃ _ _ x₄ x₅ x₆) = no (λ { (_ , ()) })
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
  dec~↑! Γ≡Δ (Id-U x x₁) (cast-cong x₂ x₃ _ _ x₄ x₅ x₆) = no (λ { (_ , ()) })
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
  dec~↑! Γ≡Δ (Id-Uℕ x) (cast-cong x₁ x₂ _ _ x₃ x₄ x₅) = no (λ { (_ , ()) })
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
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (cast-cong x₂ x₃ _ _ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (cast-ℕ x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (cast-ℕℕ x₂ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (cast-Π x₂ x₃ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (cast-Πℕ x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (cast-ℕΠ x₂ x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (cast-ΠΠ%! x₂ x₃ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (cast-ΠΠ!% x₂ x₃ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-cong x x₁ _ _ x₂ x₃ x₄) (var-refl x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-cong x x₁ _ _ x₂ x₃ x₄) (app-cong x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-cong x x₁ _ _ x₂ x₃ x₄) (natrec-cong x₅ x₆ x₇ x₈) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-cong x x₁ _ _ x₂ x₃ x₄) (Emptyrec-cong x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-cong x x₁ _ _ x₂ x₃ x₄) (Id-cong x₅ x₆ x₇) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-cong x x₁ _ _ x₂ x₃ x₄) (Id-ℕ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-cong x x₁ _ _ x₂ x₃ x₄) (Id-ℕ0 x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-cong x x₁ _ _ x₂ x₃ x₄) (Id-ℕS x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-cong x x₁ _ _ x₂ x₃ x₄) (Id-U x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-cong x x₁ _ _ x₂ x₃ x₄) (Id-Uℕ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-cong x x₁ _ _ x₂ x₃ x₄) (Id-UΠ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-cong x x₁ _ _ x₂ x₃ x₄) (cast-ℕ x₅ x₆ x₇ x₈) = ?
--    let _ , neA , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → castℕ-elim neA e }
  dec~↑! Γ≡Δ (cast-cong x x₁ _ _ x₂ x₃ x₄) (cast-ℕℕ x₅ x₆ x₇) = ?
--   let _ , neA , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → castℕ-elim neA e }
  dec~↑! Γ≡Δ (cast-cong x x₁ _ _ x₂ x₃ x₄) (cast-Π x₅ x₆ x₇ x₈ x₉) = ?
--    let _ , neA , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → castΠ-elim neA e }
  dec~↑! Γ≡Δ (cast-cong x x₁ _ _ x₂ x₃ x₄) (cast-Πℕ x₅ x₆ x₇ x₈) = ?
--    let _ , neA , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → castΠ-elim neA e }
  dec~↑! Γ≡Δ (cast-cong x x₁ _ _ x₂ x₃ x₄) (cast-ℕΠ x₅ x₆ x₇ x₈) = ? 
--    let _ , neA , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → castℕ-elim neA e }
  dec~↑! Γ≡Δ (cast-cong x x₁ _ _ x₂ x₃ x₄) (cast-ΠΠ%! x₅ x₆ x₇ x₈ x₉) = ?
--    let _ , neA , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → castΠ-elim neA e }
  dec~↑! Γ≡Δ (cast-cong x x₁ _ _ x₂ x₃ x₄) (cast-ΠΠ!% x₅ x₆ x₇ x₈ x₉) = ?
--    let _ , neA , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → castΠ-elim neA e }
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (var-refl x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (app-cong x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (Emptyrec-cong x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (Id-cong x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (Id-ℕ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (Id-ℕ0 x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (Id-ℕS x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (Id-U x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (Id-Uℕ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (Id-UΠ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (cast-cong x₄ x₅ _ _ x₆ x₇ x₈) = ?
--    let _ , neA , _ = ne~↓! x₄ in no λ { ( _ , ( _ , e )) → castℕ-elim' neA e }
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (cast-ℕℕ x₄ x₅ x₆) = ?
--    let _ , neA , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → castℕℕ-elim neA e }
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (cast-Π x₄ x₅ x₆ x₇ x₈) = ? -- no λ { ( _ , ( _ , e )) → castℕΠ-elim e }
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (cast-Πℕ x₄ x₅ x₆ x₇) = ? -- no λ { ( _ , ( _ , e )) → castℕΠ-elim e }
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (cast-ℕΠ x₄ x₅ x₆ x₇) = ?
--    let _ , neA , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → castℕneΠ-elim neA e }
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (cast-ΠΠ%! x₄ x₅ x₆ x₇ x₈) = ? -- no λ { ( _ , ( _ , e )) → castℕΠ-elim e }
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (cast-ΠΠ!% x₄ x₅ x₆ x₇ x₈) = ? -- no λ { ( _ , ( _ , e )) → castℕΠ-elim e }
  dec~↑! Γ≡Δ (cast-ℕℕ x x₁ x₂) (var-refl x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕℕ x x₁ x₂) (app-cong x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕℕ x x₁ x₂) (natrec-cong x₃ x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕℕ x x₁ x₂) (Emptyrec-cong x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕℕ x x₁ x₂) (Id-cong x₃ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕℕ x x₁ x₂) (Id-ℕ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕℕ x x₁ x₂) (Id-ℕ0 x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕℕ x x₁ x₂) (Id-ℕS x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕℕ x x₁ x₂) (Id-U x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕℕ x x₁ x₂) (Id-Uℕ x₃) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕℕ x x₁ x₂) (Id-UΠ x₃ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕℕ x x₁ x₂) (cast-cong x₃ x₄ _ _ x₅ x₆ x₇) = ? 
--    let _ , neA , _ = ne~↓! x₃ in no λ { ( _ , ( _ , e )) → castℕ-elim' neA e }
  dec~↑! Γ≡Δ (cast-ℕℕ x x₁ x₂) (cast-ℕ x₃ x₄ x₅ x₆) = ?
--    let _ , neA , _ = ne~↓! x₃ in no λ { ( _ , ( _ , e )) → castℕℕ-elim' neA e }
  dec~↑! Γ≡Δ (cast-ℕℕ x x₁ x₂) (cast-Π x₃ x₄ x₅ x₆ x₇) = ? -- no λ { ( _ , ( _ , e )) → castℕΠ-elim e }
  dec~↑! Γ≡Δ (cast-ℕℕ x x₁ x₂) (cast-Πℕ x₃ x₄ x₅ x₆) = ? -- no λ { ( _ , ( _ , e )) → castℕΠ-elim e }
  dec~↑! Γ≡Δ (cast-ℕℕ x x₁ x₂) (cast-ℕΠ x₃ x₄ x₅ x₆) = ? -- no λ { ( _ , ( _ , e )) → castℕℕΠ-elim e }
  dec~↑! Γ≡Δ (cast-ℕℕ x x₁ x₂) (cast-ΠΠ%! x₃ x₄ x₅ x₆ x₇) = ? -- no λ { ( _ , ( _ , e )) → castℕΠ-elim e }
  dec~↑! Γ≡Δ (cast-ℕℕ x x₁ x₂) (cast-ΠΠ!% x₃ x₄ x₅ x₆ x₇) = ? -- no λ { ( _ , ( _ , e )) → castℕΠ-elim e }
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (var-refl x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (app-cong x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (natrec-cong x₅ x₆ x₇ x₈) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (Emptyrec-cong x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (Id-cong x₅ x₆ x₇) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (Id-ℕ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (Id-ℕ0 x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (Id-ℕS x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (Id-U x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (Id-Uℕ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (Id-UΠ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (cast-cong x₅ x₆ _ _ x₇ x₈ x₉) =
    ? -- let _ , neA , _ = ne~↓! x₅ in no λ { ( _ , ( _ , e )) → castΠ-elim' neA e }
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (cast-ℕ x₅ x₆ x₇ x₈) = ? -- no λ { ( _ , ( _ , e )) → castℕΠ-elim' e }
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (cast-ℕℕ x₅ x₆ x₇) = ? -- no λ { ( _ , ( _ , e )) → castℕΠ-elim' e }
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (cast-Πℕ x₅ x₆ x₇ x₈) =
    ? -- let _ , neA , _ = ne~↓! x₁ in no λ { ( _ , ( _ , e )) → castΠneℕ-elim neA e }
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (cast-ℕΠ x₅ x₆ x₇ x₈) = ? -- no λ { ( _ , ( _ , e )) → castℕΠ-elim' e }
  dec~↑! Γ≡Δ (cast-Π {rA = rA} x x₁ x₂ x₃ x₄) (cast-ΠΠ%! x₅ x₆ x₇ x₈ x₉) =
    ? -- let _ , neA , _ = ne~↓! x₁ in no λ { ( _ , ( _ , e )) → castΠneΠ-elim neA e }
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (cast-ΠΠ!% x₅ x₆ x₇ x₈ x₉) =
    ? -- let _ , neA , _ = ne~↓! x₁ in no λ { ( _ , ( _ , e )) → castΠneΠ-elim neA e }

  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (var-refl x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (app-cong x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (Emptyrec-cong x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (Id-cong x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (Id-ℕ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (Id-ℕ0 x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (Id-ℕS x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (Id-U x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (Id-Uℕ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (Id-UΠ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-cong x₄ x₅ _ _ x₆ x₇ x₈) =
    ? -- let _ , neA , _ = ne~↓! x₄ in no λ { ( _ , ( _ , e )) → castΠ-elim' neA e }
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-ℕ x₄ x₅ x₆ x₇) = ? -- no λ { ( _ , ( _ , e )) → castℕΠ-elim' e }
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-ℕℕ x₄ x₅ x₆) = ? -- no λ { ( _ , ( _ , e )) → castℕΠ-elim' e }
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-Π x₄ x₅ x₆ x₇ x₈) =
    ? -- let _ , neA , _ = ne~↓! x₅ in no λ { ( _ , ( _ , e )) → castΠneℕ-elim' neA e }
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-ℕΠ x₄ x₅ x₆ x₇) = ? -- no λ { ( _ , ( _ , e )) → castℕΠ-elim' e }
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-ΠΠ%! x₄ x₅ x₆ x₇ x₈) = ? -- no λ { ( _ , ( _ , e )) → castΠΠℕ-elim e }
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-ΠΠ!% x₄ x₅ x₆ x₇ x₈) = ? -- no λ { ( _ , ( _ , e )) → castΠΠℕ-elim e }

  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (var-refl x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (app-cong x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (Emptyrec-cong x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (Id-cong x₄ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (Id-ℕ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (Id-ℕ0 x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (Id-ℕS x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (Id-U x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (Id-Uℕ x₄) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (Id-UΠ x₄ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-cong x₄ x₅ _ _ x₆ x₇ x₈) =
    ? -- let _ , neA , _ = ne~↓! x₄ in no λ { ( _ , ( _ , e )) → castℕ-elim' neA e }
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-ℕ x₄ x₅ x₆ x₇) =
    ? -- let _ , neA , _ = ne~↓! x₄ in no λ { ( _ , ( _ , e )) → castℕneΠ-elim' neA e }
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-ℕℕ x₄ x₅ x₆) = ? -- no λ { ( _ , ( _ , e )) → castℕℕΠ-elim' e }
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-Π x₄ x₅ x₆ x₇ x₈) = ? -- no λ { ( _ , ( _ , e )) → castℕΠ-elim e }
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-Πℕ x₄ x₅ x₆ x₇) = ? -- no λ { ( _ , ( _ , e )) → castℕΠ-elim e }
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-ΠΠ%! x₄ x₅ x₆ x₇ x₈) = ? -- no λ { ( _ , ( _ , e )) → castℕΠ-elim e }
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-ΠΠ!% x₄ x₅ x₆ x₇ x₈) = ? -- no λ { ( _ , ( _ , e )) → castℕΠ-elim e }

  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (var-refl x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (app-cong x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (natrec-cong x₅ x₆ x₇ x₈) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (Emptyrec-cong x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (Id-cong x₅ x₆ x₇) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (Id-ℕ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (Id-ℕ0 x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (Id-ℕS x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (Id-U x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (Id-Uℕ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (Id-UΠ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-cong x₅ x₆ _ _ x₇ x₈ x₉) =
    ? -- let _ , neA , _ = ne~↓! x₅ in no λ { ( _ , ( _ , e )) → castΠ-elim' neA e }
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-ℕ x₅ x₆ x₇ x₈) = ? -- no λ { ( _ , ( _ , e )) → castℕΠ-elim' e }
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-ℕℕ x₅ x₆ x₇) = ? -- no λ { ( _ , ( _ , e )) → castℕΠ-elim' e }
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-Π x₅ x₆ x₇ x₈ x₉) =
    ? -- let _ , neA , _ = ne~↓! x₆ in no λ { ( _ , ( _ , e )) → castΠneΠ-elim' neA e }
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-Πℕ x₅ x₆ x₇ x₈) = ? -- no λ { ( _ , ( _ , e )) → castΠΠℕ-elim' e }
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-ℕΠ x₅ x₆ x₇ x₈) = ? -- no λ { ( _ , ( _ , e )) → castℕΠ-elim' e }
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-ΠΠ!% x₅ x₆ x₇ x₈ x₉) = ? -- no λ { ( _ , ( _ , e )) → castΠΠ%!-elim e }

  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (var-refl x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (app-cong x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (natrec-cong x₅ x₆ x₇ x₈) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (Emptyrec-cong x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (Id-cong x₅ x₆ x₇) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (Id-ℕ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (Id-ℕ0 x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (Id-ℕS x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (Id-U x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (Id-Uℕ x₅) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (Id-UΠ x₅ x₆) = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-cong x₅ x₆ _ _ x₇ x₈ x₉) =
    ? -- let _ , neA , _ = ne~↓! x₅ in no λ { ( _ , ( _ , e )) → castΠ-elim' neA e }
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-ℕ x₅ x₆ x₇ x₈) = ? -- no λ { ( _ , ( _ , e )) → castℕΠ-elim' e }
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-ℕℕ x₅ x₆ x₇) = ? -- no λ { ( _ , ( _ , e )) → castℕΠ-elim' e }
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-Π x₅ x₆ x₇ x₈ x₉) =
    ? -- let _ , neA , _ = ne~↓! x₆ in no λ { ( _ , ( _ , e )) → castΠneΠ-elim' neA e }
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-Πℕ x₅ x₆ x₇ x₈) = ? -- no λ { ( _ , ( _ , e )) → castΠΠℕ-elim' e }
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-ℕΠ x₅ x₆ x₇ x₈) = ? -- no λ { ( _ , ( _ , e )) → castℕΠ-elim' e }
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-ΠΠ%! x₅ x₆ x₇ x₈ x₉) = ? -- no λ { ( _ , ( _ , e )) → castΠΠ!%-elim e }
-}

  -- Decidability of algorithmic equality of neutrals with types in WHNF.
  dec~↓! : ∀ {n k l R T Γ Δ lR lT}
        → ⊢ Γ ≡ Δ
        → (e : Γ ⊢ k ~ k ↓! R ^ lR)
        → (e' : Δ ⊢ l ~ l ↓! T ^ lT)
        → (size~↓! e + size~↓! e') << n
        → Dec (∃ λ A → ∃ λ lA → Γ ⊢ k ~ l ↓! A ^ lA)
  dec~↓! Γ≡Δ ([~] A D whnfB k~l) ([~] A₁ D₁ whnfB₁ k~l₁) (leS size)
        with dec~↑! Γ≡Δ k~l k~l₁ (<<-trans <=-help-ab1' size)
  ... | yes (B , lB , k~l₂) =
    let ⊢B , _ , _ = syntacticEqTerm (soundness~↑! k~l₂)
        C , whnfC , D′ = whNorm ⊢B
    in  yes (C , _ , [~] B (red D′) whnfC k~l₂)
  ... | no ¬p =
    no (λ { (A₂ , _ , [~] A₃ D₂ whnfB₂ k~l₂) → ¬p (A₃ , _ , k~l₂) })

  -- Decidability of algorithmic equality of types.
  decConv↑ : ∀ {A B r Γ Δ}
           → ⊢ Γ ≡ Δ
           → Γ ⊢ A [conv↑] A ^ r → Δ ⊢ B [conv↑] B ^ r
           → Dec (Γ ⊢ A [conv↑] B ^ r)
{-
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
-}
  decConv↑ = {!!}
  
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

--  decConv↑Term = {!!}

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

{-

  decConv↑Term Γ≡Δ ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
                   ([↑]ₜ B₁ t″ u″ D₁ d₁ d″ whnfB₁ whnft″ whnfu″ t<>u₁)
               rewrite whrDet*Term  (d , whnft′) (d′ , whnfu′)
                     | whrDet*Term  (d₁ , whnft″) (d″ , whnfu″)
               with decConv↓Term Γ≡Δ t<>u t<>u₁
  decConv↑Term Γ≡Δ ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
                   ([↑]ₜ B₁ t″ u″ D₁ d₁ d″ whnfB₁ whnft″ whnfu″ t<>u₁)
               | yes p =
    let Δ≡Γ = symConEq Γ≡Δ
        B≡B' = soundnessConv↓Term p
        _ , _ , ⊢u″ = syntacticEqTerm B≡B'
        _ , _ , ⊢u″' = syntacticEqTerm (subset*Term d″)
        _ , B≡B = type-uniq ⊢u″' (stabilityTerm Γ≡Δ ⊢u″)
    in  yes ([↑]ₜ B u′ u″ D d′ (stabilityRed*Term Δ≡Γ (conv⇒* d″ B≡B )) whnfB whnfu′ whnfu″ p)
  decConv↑Term Γ≡Δ ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
                   ([↑]ₜ B₁ t″ u″ D₁ d₁ d″ whnfB₁ whnft″ whnfu″ t<>u₁)
               | no ¬p =
    no (λ { ([↑]ₜ B₂ t‴ u‴ D₂ d₂ d‴ whnfB₂ whnft‴ whnfu‴ t<>u₂) →
        let _ , ⊢t , ⊢u″ = syntacticEqTerm (subset*Term d′)
            _ , ⊢t' , _ = syntacticEqTerm (soundnessConv↓Term t<>u₂)
            t‴≡u′ = whrDet*Term (d₂ , whnft‴) (d′ , whnfu′)
            u‴≡u″ = whrDet*Term (d‴ , whnfu‴) (stabilityRed*Term (symConEq Γ≡Δ) d″ , whnfu″)
            _ , B₂≡B = type-uniq (PE.subst (λ x → _ ⊢ x ∷ _ ^ _) t‴≡u′ ⊢t') ⊢u″
            t~u = PE.subst₂ (λ x y → _ ⊢ x [conv↓] y ∷ _ ^ _) t‴≡u′ u‴≡u″ t<>u₂
        in  ¬p (convConv↓Term (reflConEq (wfTerm ⊢t)) B₂≡B whnfB t~u) })
-}

  -- Decidability of algorithmic equality of terms in WHNF.
  decConv↓Term : ∀ {t u A Γ Δ l}
               → ⊢ Γ ≡ Δ
               → Γ ⊢ t [conv↓] t ∷ A ^ l → Δ ⊢ u [conv↓] u ∷ A ^ l
               → Dec (Γ ⊢ t [conv↓] u ∷ A ^ l)

{-

  decConv↓Term Γ≡Δ (U-refl {r = r} _ x) (U-refl {r = r′} _ x₁)
    with dec-relevance r r′
  ... | yes p = yes (U-refl p x)
  ... | no ¬p = no λ p → ¬p (proj₁ (Uinjectivity (univ (soundnessConv↓Term p))))

  decConv↓Term Γ≡Δ (ne K) (ne K₁)
    with dec~↓! Γ≡Δ K K₁
  ... | yes (A , lA , K~K₁) = yes (ne (~atU K (A , lA , K~K₁)))
  ... | no ¬p = no (λ { x → ¬p (Univ _ _ , _ , decConv↓Term-U-ins x K) })

  decConv↓Term Γ≡Δ (ℕ-refl x) (ℕ-refl x₁) = yes (ℕ-refl x)

  decConv↓Term Γ≡Δ (Empty-refl x₁) (Empty-refl x₃) = yes (Empty-refl x₁)

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

  decConv↓Term Γ≡Δ (∃-cong ⊢F F G) (∃-cong ⊢H H E)
    with decConv↑Term Γ≡Δ F H
  ... | no ¬p = no λ { (∃-cong x₁ x₂ x₃) → ¬p x₂ }
  ... | yes pFH
    with decConv↑Term (Γ≡Δ ∙ univ (soundnessConv↑Term pFH)) G E
  ... | no ¬p = no λ { (∃-cong x₁ x₂ x₃) → ¬p x₃ }
  ... | yes pGE = yes (∃-cong ⊢F pFH pGE)

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
  decConv↓Term Γ≡Δ (ne x) (Empty-refl x₂) =
    no (λ x₃ → decConv↓Term-U x₃ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (ne x) (Π-cong x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉) =
    no (λ x₃ → decConv↓Term-U x₃ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (ne x) (∃-cong x₂ x₃ x₄) =
    no (λ x₃ → decConv↓Term-U x₃ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (ℕ-refl x) (ne x₁) =
    no (λ x₃ → decConv↓Term-U (symConv↓Term Γ≡Δ x₃) x₁ (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (ℕ-refl x) (Π-cong x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉) = no λ { (ne ()) ; (ne-ins _ x₁ () x₃) }
  decConv↓Term Γ≡Δ (Empty-refl x₁) (ne x₂) =
    no (λ x₃ → decConv↓Term-U (symConv↓Term Γ≡Δ x₃) x₂ (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (Empty-refl x₁) (Π-cong x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀) = no λ { (ne ()) ; (ne-ins _ x₁ () x₃) }
  decConv↓Term Γ≡Δ (Empty-refl x₁) (∃-cong x₃ x₄ x₅) = no λ { (ne ()) ; (ne-ins _ x₁ () x₃) }
  decConv↓Term Γ≡Δ (Π-cong l x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (U-refl x₈ x₉) = no λ { (ne ()) }
  decConv↓Term Γ≡Δ (Π-cong l x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (ne x₈) =
    no (λ x₉ → decConv↓Term-U (symConv↓Term Γ≡Δ x₉) x₈ (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (Π-cong l x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (ℕ-refl x₈) = no λ { (ne ()) ; (ne-ins x x₁ () x₃) }
  decConv↓Term Γ≡Δ (Π-cong l x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (Empty-refl x₉) = no λ { (ne ()) ; (ne-ins x x₁ () x₃) }
  decConv↓Term Γ≡Δ (Π-cong l x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (∃-cong x₉ x₁₀ x₁₁) = no λ { (ne ()) ; (ne-ins x x₁ () x₃) }
  decConv↓Term Γ≡Δ (∃-cong x x₁ x₂) (ne x₃) =
    no (λ x₉ → decConv↓Term-U (symConv↓Term Γ≡Δ x₉) x₃ (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (∃-cong x x₁ x₂) (Empty-refl x₄) = no λ { (ne ()) ; (ne-ins x x₁ () _) }
  decConv↓Term Γ≡Δ (∃-cong x x₁ x₂) (Π-cong x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁) = no λ { (ne ()) ; (ne-ins x x₁ () x₃) }
  decConv↓Term Γ≡Δ (ℕ-ins x) (zero-refl x₁) =
    no (λ x₂ → decConv↓Term-ℕ x₂ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (ℕ-ins x) (suc-cong x₁) =
    no (λ x₂ → decConv↓Term-ℕ x₂ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (ne x₄)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (ℕ-refl x₄)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (Empty-refl x₅)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (Π-cong x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (∃-cong x₅ x₆ x₇)
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
-}

  decConv↓Term Γ≡Δ X Y = {!!}

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
