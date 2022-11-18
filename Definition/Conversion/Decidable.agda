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
open import Definition.Conversion.SymmetrySize
open import Definition.Conversion.Stability
open import Definition.Conversion.StabilityProp
open import Definition.Conversion.Conversion
open import Definition.Conversion.ConversionProp
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

cast-PE-injectivity : ∀ {A A' B B' e e' t t' l l'} → cast l A B e t PE.≡ cast l' A' B' e' t' → l PE.≡ l' × A PE.≡ A' × B PE.≡ B' × e PE.≡ e' × t PE.≡ t'
cast-PE-injectivity PE.refl = PE.refl , PE.refl , PE.refl , PE.refl , PE.refl

removeSuc : Nat → Nat
removeSuc 0 = 0
removeSuc (1+ n) = n

<=-help-b'b-c'' :  ∀ {a b b' b'' c' : Nat} → (b' + b) <= (a + b' + b'' + 1+ (b + c'))
<=-help-b'b-c'' = {!!}

<=-help-b''-c'' :  ∀ {a b b' b'' c' : Nat} → (b'' + c') <= (a + b' + b'' + 1+ (b + c'))
<=-help-b''-c'' = {!!}

<=-help-ab'b''c'' :  ∀ {a b b' b'' c' : Nat} → 1+ (a + b' + b'' + c') <= (a + b' + b'' + 1+ (b + (2 + c')))
<=-help-ab'b''c'' = {!!}

<=-help-b''x :  ∀ {a b b'' x : Nat} → (b'' + x) <= (a + b + (2 +  b'') + x)
<=-help-b''x = {!!}

<=-help-ab-c'' :  ∀ {a b b' c' c'' : Nat} → (a + b) <= (a + b' + 1+ (b + c' + c''))
<=-help-ab-c'' = {!!}

<=-help-ac'-c'' :  ∀ {a b b' c' c'' : Nat} → (a + c') <= (a + b' + 1+ (b + c' + c''))
<=-help-ac'-c'' = {!!}

<=-help-bc'-c'' :  ∀ {a b b' c' c'' : Nat} → (b + c') <= (a + b' + 1+ (b + c' + c''))
<=-help-bc'-c'' = {!!}

<=-help-b'c'' :  ∀ {a b b' c' c'' : Nat} → (b' + c'') <= (a + b' + 1+ (b + c' + c''))
<=-help-b'c'' = {!!}

<=-help-ab'c'' :  ∀ {a b b' c' c'' : Nat} → 1+ (a + b' + c'') <= (a + b' + 1+ (b + c' + (2 + c'')))
<=-help-ab'c'' = {!!}


abstract
  cast-t-≡ : ∀ {Γ A B B' t t' e X lX} 
                → Γ ⊢ t' ∷ B' ^ [ ! , ι ⁰ ]
                → Γ ⊢ cast ⁰ A B e t ~ t' ↑! X ^ lX
                → Γ ⊢ B ≡ B' ^ [ ! , ι ⁰ ]
  cast-t-≡ ⊢t X =
    let _ , ⊢cast , ⊢t' = syntacticEqTerm (soundness~↑! X)
        _ , _ , _ , _ , _ , R≡R , eqR , _ = inversion-cast ⊢cast
        eqR , el = typeinfo-PE-injectivity eqR
        _ , eq = type-uniq ⊢t ⊢t'
        R≡R' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqR) R≡R
    in T.trans (T.sym R≡R') (T.sym eq) 

castℕInv : ∀ {l e t} → Neutral (cast l ℕ ℕ e t) → Neutral t 
castℕInv (castℕℕₙ net) = net


mutual
  -- Decidability of algorithmic equality of neutrals.
  dec~↑! : ∀ {n k k' l l' R T Γ Δ lR lT}
        → ⊢ Γ ≡ Δ
        → (e : Γ ⊢ k ~ k' ↑! R ^ lR)
        → (e' : Δ ⊢ l ~ l' ↑! T ^ lT)
        → (size~↑! e + size~↑! e') << n
        → Dec (∃ λ A → ∃ λ lA → Γ ⊢ k ~ l ↑! A ^ lA)

  dec~↑! {n = 0} _ _ _ ()

{-
  dec~↑! Γ≡Δ (var-refl {n} ⊢x PE.refl) (var-refl {m} ⊢y m≡m) _ with n ≟ m
  ... | yes PE.refl =  yes (_ , (_ , var-refl ⊢x PE.refl))
  ... | no ¬p = no λ (_ , (_ , eq)) → ¬p (strongVarEq eq)

  dec~↑! Γ≡Δ (app-cong x~x t≡t) (app-cong y~y u≡u) (leS size) with dec~↓! Γ≡Δ x~x y~y (<=-trans (leS (<=-help-ab' {a = size~↓! x~x})) size)
  ... | yes (A , lA , x~y) =
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
      (dec~↑!-app Γ≡Δ ⊢k₁′ ⊢k₂ x~y (decConv↑TermConv′ Γ≡Δ (PE.sym (PE.cong₂ (λ X Y → [ X , ι Y ]) rF≡rF′ lF≡lF′)) PE.refl F≡F″ t≡t u≡u (<<-trans (<=-help-ab'' {a = size~↓! x~x}) size)))
  ... | no ¬p = no (λ { (_ , (_ , app-cong x′ y′)) → ¬p (_ , (_ , x′)) })

  dec~↑! Γ≡Δ (natrec-cong {lF = l} F a0 aS k) (natrec-cong {lF = l₀} G b0 bS k₀) (leS size)
    with dec-level l l₀
  dec~↑! Γ≡Δ (natrec-cong {lF = l} F a0 aS k) (natrec-cong {lF = .l} G b0 bS k₀) (leS size) | yes PE.refl
    with decConv↑ (Γ≡Δ ∙ refl (univ (ℕⱼ (wfEqTerm (soundness~↓! k))))) F G (<<-trans (<=-help-nat-cong-ab {a = sizeConv↑ F}) size)
  dec~↑! Γ≡Δ (natrec-cong {lF = l} F a0 aS k) (natrec-cong {lF = .l} G b0 bS k₀) (leS size)| yes PE.refl | yes p
    with decConv↑TermConv Γ≡Δ (substTypeEq (soundnessConv↑ p) (refl (zeroⱼ (wfEqTerm (soundness~↓! k))))) a0 b0 (<<-trans (<=-help-nat-congb'c' {a = sizeConv↑ F} {b = sizeConv↑ G}) size)
           | decConv↑TermConv Γ≡Δ (sucCong (soundnessConv↑ p)) aS bS (<<-trans (<=-help-nat-congb''c'' {a = sizeConv↑ F} {b = sizeConv↑ G}) size)
           | dec~↓! Γ≡Δ k k₀ (<<-trans (<=-help-nat-congb'''c''' {a = sizeConv↑ F} {b = sizeConv↑ G}) size)
  dec~↑! Γ≡Δ (natrec-cong {lF = l} F a0 aS k) (natrec-cong {lF = .l} G b0 bS k₀) (leS size) | yes PE.refl | yes p | yes p0 | yes pS | yes pK =
    yes (_ , _ , let _ , ⊢k , _ = syntacticEqTerm (soundness~↓! k) in natrec-cong p p0 pS (~atℕ ⊢k pK))
  dec~↑! Γ≡Δ (natrec-cong {lF = l} F a0 aS k) (natrec-cong {lF = .l} G b0 bS k₀) (leS size) | yes PE.refl | yes p | yes p0 | yes pS | no ¬pK =
    no (λ { (_ , _ , natrec-cong x x₁ x₂ x₃) → ¬pK (_ , _ , x₃) })
  dec~↑! Γ≡Δ (natrec-cong {lF = l} F a0 aS k) (natrec-cong {lF = .l} G b0 bS k₀) (leS size) | yes PE.refl | yes p | yes p0 | no ¬pS | _ =
    no (λ { (_ , _ , natrec-cong x x₁ x₂ x₃) → ¬pS x₂ })
  dec~↑! Γ≡Δ (natrec-cong {lF = l} F a0 aS k) (natrec-cong {lF = .l} G b0 bS k₀) (leS size) | yes PE.refl | yes p | no ¬p0 | _ | _ =
    no (λ { (_ , _ , natrec-cong x x₁ x₂ x₃) → ¬p0 x₁ })
  dec~↑! Γ≡Δ (natrec-cong {lF = l} F a0 aS k) (natrec-cong {lF = .l} G b0 bS k₀) (leS size) | yes PE.refl | no ¬p =
    no (λ { (_ , _ , natrec-cong x x₁ x₂ x₃) → ¬p x })
  dec~↑! Γ≡Δ (natrec-cong {lF = l} F a0 aS k) (natrec-cong {lF = l₀} G b0 bS k₀) (leS size) | no ¬p =
    no (λ { (_ , .(ι l) , natrec-cong x x₁ x₂ x₃) → ¬p PE.refl })

  dec~↑! Γ≡Δ (Emptyrec-cong {ll = l} F k) (Emptyrec-cong {ll = l₀} G k₀) (leS size)
    with dec-level l l₀ 
  dec~↑! Γ≡Δ (Emptyrec-cong {ll = l} F k) (Emptyrec-cong {ll = .l} G k₀) (leS size) | yes PE.refl 
    with decConv↑ Γ≡Δ F G (<<-trans (<=-help-ab1' {a = sizeConv↑ F}) size)
  dec~↑! Γ≡Δ (Emptyrec-cong {ll = l} F k) (Emptyrec-cong {ll = .l} G k₀) (leS size) | yes PE.refl | yes p =
    let ⊢k , _  = soundness~↑% k
        ⊢k₀ , _ = soundness~↑% k₀
        ⊢Γ = wfTerm ⊢k
    in yes (_ , _ , Emptyrec-cong p (%~↑ ⊢k (stabilityTerm (symConEq Γ≡Δ) ⊢k₀)))
  dec~↑! Γ≡Δ (Emptyrec-cong {ll = l} F k) (Emptyrec-cong {ll = .l} G k₀) (leS size) | yes PE.refl | no ¬p =
    no (λ { (_ , .(ι l) , Emptyrec-cong x x₁) → ¬p x })
  dec~↑! Γ≡Δ (Emptyrec-cong {ll = l} F k) (Emptyrec-cong {ll = l₀} G k₀) (leS size) | no ¬p =
    no (λ { (_ , .(ι l) , Emptyrec-cong x x₁) → ¬p PE.refl })

  dec~↑! Γ≡Δ (Id-cong A t u) (Id-cong B v w) (leS size) with dec~↓! Γ≡Δ A B (<<-trans (<=-help-id-cong {a =  size~↓! A}) size)
  ... | no ¬p = no λ { (_ , _ , Id-cong x x₁ x₂) → ¬p (_ , _ , x) ;
                       (_ , _ , Id-ℕ x x₁) → let _ , neℕ , _ = ne~↓! A in noNeℕ neℕ ;
                       (_ , _ , Id-ℕ0 x) → let _ , neℕ , _ = ne~↓! A in noNeℕ neℕ ;
                       (_ , _ , Id-ℕS x x₁) → let _ , neℕ , _ = ne~↓! A in noNeℕ neℕ ;
                       (_ , _ , Id-U x x₁) → let _ , neU , _ = ne~↓! A in noNeUniv neU ;
                       (_ , _ , Id-Uℕ x) → let _ , neU , _ = ne~↓! A in noNeUniv neU ;
                       (_ , _ , Id-UΠ x x₁) → let _ , neU , _ = ne~↓! A in noNeUniv neU }
  ... | yes (M , lM , A~B) with decConv↑Term Γ≡Δ t (convert~ Γ≡Δ A B A~B v)
                                             (<<-trans (<=-trans (<=-cong-+ (le-refl (sizeConv↑Term t))
                                                       (≡-to-<= (convert~size Γ≡Δ A B A~B v)))
                                                       (<=-help-b'c' {a = size~↓! A} {b = size~↓! B})) size)
                              | decConv↑Term Γ≡Δ u (convert~ Γ≡Δ A B A~B w)
                                             (<<-trans (<=-trans (<=-cong-+ (le-refl (sizeConv↑Term u))
                                                       (≡-to-<= (convert~size Γ≡Δ A B A~B w)))
                                                       (<=-help-b''c'' {a = size~↓! A} {b = size~↓! B})) size)
  ... | yes tv | yes uw = yes (_ , _ , Id-cong (~atU' A (M  , lM , A~B)) tv uw)
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

  dec~↑! Γ≡Δ (Id-ℕ t u) (Id-ℕ v w) (leS size)
    with dec~↓! Γ≡Δ t v (<<-trans (<=-help-ab' {a = size~↓! t}) size) |
         decConv↑Term Γ≡Δ u w (<<-trans (<=-help-ab'' {a = size~↓! t} {c = size~↓! v}) size) 
  ... | yes tv | yes uw = yes (_ , _ , let _ , ⊢t , _ = syntacticEqTerm (soundness~↓! t) in Id-ℕ (~atℕ ⊢t tv) uw)
  ... | yes tv | no ¬uw = no λ { (_ , _ , Id-ℕ x x₁) → ¬uw x₁ }
  ... | no ¬tv | _ = no λ { (_ , _ , Id-ℕ x x₁) → ¬tv (_ , _ , x) ;
                            (_ , _ , Id-ℕ0 x) → let _ , ne0 , _ = ne~↓! v in noNe0 ne0 ;
                            (_ , _ , Id-ℕS x x₁) → let _ , neS , _ = ne~↓! v in noNeSuc neS }

  dec~↑! Γ≡Δ (Id-ℕ0 t) (Id-ℕ0 u) (leS size) with dec~↓! Γ≡Δ t u (<<-trans (<=-help-ab1' {a = size~↓! t}) size)
  ... | yes tu = yes (_ , _ , let _ , ⊢t , _ = syntacticEqTerm (soundness~↓! t) in Id-ℕ0 (~atℕ ⊢t tu))
  ... | no ¬tu = no λ { (_ , _ , Id-ℕ0 x) → ¬tu (_ , _ , x) }

  dec~↑! Γ≡Δ (Id-ℕS t u) (Id-ℕS v w) (leS size) with decConv↑Term Γ≡Δ t v (<<-trans (<=-help-ab' {a = sizeConv↑Term t}) size) | dec~↓! Γ≡Δ u w (<<-trans (<=-help-ab'' {a = sizeConv↑Term t} {c = sizeConv↑Term v}) size)
  ... | yes tv | yes uw = yes (_ , _ , let _ , ⊢u , _ = syntacticEqTerm (soundness~↓! u) in Id-ℕS tv (~atℕ ⊢u uw))
  ... | yes tv | no ¬uw = no λ { (_ , _ , Id-ℕS x x₁) → ¬uw (_ , _ , x₁) }
  ... | no ¬tv | _ = no λ { (_ , _ , Id-ℕS x x₁) → ¬tv x }

  dec~↑! Γ≡Δ (Id-U t u) (Id-U v w) (leS size) with dec~↓! Γ≡Δ t v (<<-trans (<=-help-ab' {a = size~↓! t}) size) | decConv↑Term Γ≡Δ u w (<<-trans (<=-help-ab'' {a = size~↓! t} {c = size~↓! v}) size)
  ... | yes tv | yes uw = yes (_ , _ , Id-U (~atU' t tv) uw)
  ... | yes tv | no ¬uw = no λ { (_ , _ , Id-U x x₁) → ¬uw x₁ }
  ... | no ¬tv | _ = no λ { (_ , _ , Id-U x x₁) → ¬tv (_ , _ , x) }

  dec~↑! Γ≡Δ (Id-Uℕ t) (Id-Uℕ u) (leS size) with dec~↓! Γ≡Δ t u (<<-trans (<=-help-ab1' {a = size~↓! t}) size)
  ... | yes tu = yes (_ , _ , Id-Uℕ (~atU' t tu))
  ... | no ¬tu = no λ { (_ , _ , Id-Uℕ x) → ¬tu (_ , _ , x) }

  dec~↑! Γ≡Δ (Id-UΠ {rA = r} t u) (Id-UΠ {rA = r′} v w) (leS size) with dec-relevance r r′ | decConv↑Term Γ≡Δ t v (<<-trans (<=-help-ab' {a = sizeConv↑Term t}) size) | dec~↓! Γ≡Δ u w (<<-trans (<=-help-ab'' {a = sizeConv↑Term t} {c = sizeConv↑Term v}) size)
  ... | yes PE.refl | yes tv | yes uw = yes (_ , _ , Id-UΠ tv (~atU' u uw))
  ... | yes PE.refl | yes tv | no ¬uw = no λ { (_ , _ , Id-UΠ x x₁) → ¬uw (_ , _ , x₁) }
  ... | yes PE.refl | no ¬tv | _ = no λ { (_ , _ , Id-UΠ x x₁) → ¬tv x }
  ... | no ¬p | _ | _ = no λ { (_ , _ , Id-UΠ x x₁) → ¬p PE.refl }

  dec~↑! Γ≡Δ (cast-cong A B (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) eAB eAB') (cast-cong C D (ne-ins ⊢u x₄ x₅ ([~] A₂ D₂ whnfB₁ k~l₁)) eCD eCD') (leS size) =
    let neA = proj₁ (proj₂ (ne~↓! A))
        neB = proj₁ (proj₂ (ne~↓! (sym~↓!U B)))
        neC = proj₁ (proj₂ (ne~↓! C))
        neD = proj₁ (proj₂ (ne~↓! (sym~↓!U D)))
        _ , ⊢A , _ = syntacticEqTerm (soundness~↓! A)
        _ , _ , ⊢B = syntacticEqTerm (soundness~↓! B)
        _ , ⊢C , _ = syntacticEqTerm (soundness~↓! C)
        _ , _ , ⊢D = syntacticEqTerm (soundness~↓! D)
    in cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u eAB eCD
                     (dec~↓! Γ≡Δ A C (<<-trans (<=-help-id-cong {a = size~↓! A} {b = size~↓! C}) size))
                     (dec~↓! (symConEq Γ≡Δ) (sym~↓!U D) (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.trans (PE.cong₂ _+_ (sym~↓!Usize D) (sym~↓!Usize B))
                                                                      (+-sym (size~↓! D) (size~↓! B))) ) (<=-help-b'c' {a = size~↓! A} {b = size~↓! C})) size) )
                     (dec~↓! (reflConEq (wfTerm eAB)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B)))
                                                                              (<=-help-id-cong-ab' {a = size~↓! A} {b = size~↓! C} {b' = size~↓! B})) size))
                     (dec~↓! (reflConEq (wfTerm eCD)) C (sym~↓!U D) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! C)) (sym~↓!Usize D)))
                                                                              (<=-help-id-cong-bc' {a = size~↓! A} {b = size~↓! C} {b' = size~↓! B})) size))
                     (λ (_ , _ , A~C) →
                       decConv↓Term Γ≡Δ (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) (convert'~ Γ≡Δ A C A~C (ne-ins ⊢u x₄ x₅ ([~] A₂ D₂ whnfB₁ k~l₁)))
                          (<<-trans (PE.subst ( λ X →  (sizeConv↓Term (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) + X) <= _)
                                    (PE.sym (convert'~size Γ≡Δ A C A~C (ne-ins ⊢u x₄ x₅ ([~] A₂ D₂ whnfB₁ k~l₁))))
                                              (<=-help-b''c'' {a = size~↓! A } {b = size~↓! C} {b'' = 1+ (size~↓! ([~] A₁ D₁ whnfB k~l))})) 
                                    size))
                     (dec~↑! Γ≡Δ k~l (cast-cong C D (ne-ins ⊢u x₄ x₅ ([~] A₂ D₂ whnfB₁ k~l₁)) eCD eCD')
                                     (<<-trans (<=-help-cast {a = size~↓! A} {b = size~↓! B}) size))
                     (dec~↑! Γ≡Δ (cast-cong A B (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) eAB eAB') k~l₁
                                 (<<-trans (<=-help-cast' {a = size~↓! A} {b = size~↓! C} {b' = size~↓! B} {c' = size~↓! D}) size))
                                                    
  dec~↑! Γ≡Δ (cast-ℕ A t eℕA _) (cast-ℕ B u eℕB _) (leS size)
    with dec~↓! Γ≡Δ A B (<<-trans (<=-help-ab' {a = size~↓! A} {b = size~↓! B}) size) | decConv↑Term Γ≡Δ t u (<<-trans (<=-help-ab'' {a = size~↓! A} {c = size~↓! B}) size)
  ... | yes AB | yes tu = yes (_ , _ , cast-ℕ (~atU' A AB) tu eℕA (stabilityTerm (symConEq Γ≡Δ) eℕB))
  ... | yes AB | no ¬tu = no λ { (_ , _ , cast-ℕ x x₁ x₂ x₃) → ¬tu x₁ }
  ... | no ¬AB | _ = no λ { (_ , _ , cast-ℕ x x₁ x₂ x₃) → ¬AB (_ , _ , x) }

  dec~↑! Γ≡Δ (cast-Π {rA = r} Π A t eΠA _) (cast-Π {rA = r′} Π′ B u eΠB _) (leS size)
    with dec-relevance r r′ | decConv↑Term Γ≡Δ Π Π′ (<<-trans (<=-help-id-cong {a = sizeConv↑Term Π}) size) | dec~↓! Γ≡Δ A B (<<-trans (<=-help-b'c' {a = sizeConv↑Term Π} {b = sizeConv↑Term Π′}) size)
  ... | no ¬p | _ | _ = no λ { (_ , _ , cast-Π x x₁ x₂ x₃ x₄) → ¬p PE.refl }
  ... | yes PE.refl | no ¬ΠΠ′ | _ = no λ { (_ , _ , cast-Π x x₁ x₂ x₃ x₄) → ¬ΠΠ′ x }
  ... | yes PE.refl | yes ΠΠ′ | no ¬AB = no λ { (_ , _ , cast-Π x x₁ x₂ x₃ x₄) → ¬AB (_ , _ , x₁) }
  ... | yes PE.refl | yes ΠΠ′ | yes AB with decConv↑TermConv Γ≡Δ (univ (soundnessConv↑Term ΠΠ′)) t u (<<-trans (<=-help-b''c'' {a = sizeConv↑Term Π} {b = sizeConv↑Term Π′}) size)
  ... | yes p = yes (_ , _ , cast-Π ΠΠ′ (~atU' A AB) p eΠA (stabilityTerm (symConEq Γ≡Δ) eΠB))
  ... | no ¬p = no λ { (_ , _ , cast-Π x x₁ x₂ x₃ x₄) → ¬p x₂ }

  dec~↑! Γ≡Δ (cast-Πℕ {rA = r} Π t eΠℕ _) (cast-Πℕ {rA = r′} Π′ u eΠℕ′ _) (leS size)
    with dec-relevance r r′ | decConv↑Term Γ≡Δ Π Π′ (<<-trans (<=-help-ab' {a = sizeConv↑Term Π}) size)
  ... | no ¬p | _ = no λ { (_ , _ , cast-Πℕ x x₁ x₂ x₃) → ¬p PE.refl }
  ... | yes PE.refl | no ¬ΠΠ′ = no λ { (_ , _ , cast-Πℕ x x₁ x₂ x₃) → ¬ΠΠ′ x }
  ... | yes PE.refl | yes ΠΠ′ with decConv↑TermConv Γ≡Δ (univ (soundnessConv↑Term ΠΠ′)) t u (<<-trans (<=-help-ab'' {a = sizeConv↑Term Π} {c = sizeConv↑Term Π′}) size)
  ... | yes p = yes (_ , _ , cast-Πℕ ΠΠ′ p eΠℕ (stabilityTerm (symConEq Γ≡Δ) eΠℕ′))
  ... | no ¬p = no λ { (_ , _ , cast-Πℕ x x₁ x₂ x₃) → ¬p x₁ }

  dec~↑! Γ≡Δ (cast-ℕΠ {rA = r} Π t eΠℕ _) (cast-ℕΠ {rA = r′} Π′ u eΠℕ′ _) (leS size)
    with dec-relevance r r′ | decConv↑Term Γ≡Δ Π Π′ (<<-trans (<=-help-ab' {a = sizeConv↑Term Π}) size) | decConv↑Term Γ≡Δ t u (<<-trans (<=-help-ab'' {a = sizeConv↑Term Π} {c = sizeConv↑Term Π′}) size)
  ... | no ¬p | _ | _ = no λ { (_ , _ , cast-ℕΠ x x₁ x₂ x₃) → ¬p PE.refl }
  ... | yes PE.refl | no ¬ΠΠ′ | _ = no λ { (_ , _ , cast-ℕΠ x x₁ x₂ x₃) → ¬ΠΠ′ x }
  ... | yes PE.refl | yes ΠΠ′ | no ¬p = no λ { (_ , _ , cast-ℕΠ x x₁ x₂ x₃) → ¬p x₁ }
  ... | yes PE.refl | yes ΠΠ′ | yes p = yes (_ , _ , cast-ℕΠ ΠΠ′ p eΠℕ (stabilityTerm (symConEq Γ≡Δ) eΠℕ′))

  dec~↑! Γ≡Δ (cast-ΠΠ%! A B t eAB _) (cast-ΠΠ%! C D u eCD _) (leS size)
    with decConv↑Term Γ≡Δ A C (<<-trans (<=-help-id-cong {a = sizeConv↑Term A}) size) | decConv↑Term Γ≡Δ B D (<<-trans (<=-help-b'c' {a = sizeConv↑Term A} {b = sizeConv↑Term C}) size)
  ... | no ¬AC | _ = no λ { (_ , _ , cast-ΠΠ%! x x₁ x₂ x₃ x₄) → ¬AC x }
  ... | yes AC | no ¬BD = no λ { (_ , _ , cast-ΠΠ%! x x₁ x₂ x₃ x₄) → ¬BD x₁ }
  ... | yes AC | yes BD with decConv↑TermConv Γ≡Δ (univ (soundnessConv↑Term AC)) t u (<<-trans (<=-help-b''c'' {a = sizeConv↑Term A} {b = sizeConv↑Term C}) size)
  ... | yes p = yes (_ , _ , cast-ΠΠ%! AC BD p eAB (stabilityTerm (symConEq Γ≡Δ) eCD))
  ... | no ¬p = no λ { (_ , _ , cast-ΠΠ%! x x₁ x₂ x₃ x₄) → ¬p x₂ }

  dec~↑! Γ≡Δ (cast-ΠΠ!% A B t eAB _) (cast-ΠΠ!% C D u eCD _) (leS size)
    with decConv↑Term Γ≡Δ A C (<<-trans (<=-help-id-cong {a = sizeConv↑Term A}) size) | decConv↑Term Γ≡Δ B D (<<-trans (<=-help-b'c' {a = sizeConv↑Term A} {b = sizeConv↑Term C}) size)
  ... | no ¬AC | _ = no λ { (_ , _ , cast-ΠΠ!% x x₁ x₂ x₃ x₄) → ¬AC x }
  ... | yes AC | no ¬BD = no λ { (_ , _ , cast-ΠΠ!% x x₁ x₂ x₃ x₄) → ¬BD x₁ }
  ... | yes AC | yes BD with decConv↑TermConv Γ≡Δ (univ (soundnessConv↑Term AC)) t u (<<-trans (<=-help-b''c'' {a = sizeConv↑Term A} {b = sizeConv↑Term C}) size)
  ... | yes p = yes (_ , _ , cast-ΠΠ!% AC BD p eAB (stabilityTerm (symConEq Γ≡Δ) eCD))
  ... | no ¬p = no λ { (_ , _ , cast-ΠΠ!% x x₁ x₂ x₃ x₄) → ¬p x₂ }

  -- antidiagonal cases

  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (app-cong x~x t≡t) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (natrec-cong x x₁ x₂ x₃) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (Emptyrec-cong x x₁) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (Id-cong x x₁ x₂) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (Id-ℕ x x₁) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (Id-ℕ0 x) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (Id-ℕS x x₁) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (Id-U x x₁) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (Id-Uℕ x) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (Id-UΠ x x₁) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e _) (leS size) =
    cast-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) A) (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B))
                    (stabilityConv↓Term (symConEq Γ≡Δ) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)))
                    (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                    (dec~↓! Γ≡Δ (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B)) A (<<-trans (<=-trans (<=-trans (≡-to-<= (PE.trans (PE.cong (λ X → X + size~↓! A) (sym~↓!Usize _))
                                                                                                (+-sym (size~↓! (stability~↓! (symConEq Γ≡Δ) B)) (size~↓! A))))
                                                                                                (<=-cong-+ (le-refl (size~↓! A)) (≡-to-<= (stabilitySize~↓! _ B))))
                                                                  (<=-help-abrem {x = 0} {a = size~↓! A + size~↓! B} {b = 2 + size~↑! k~l}) ) size))
                    (dec~↑! Γ≡Δ (var-refl ⊢x n≡n) k~l (<<-trans (<=-help-abrem' {x = 1} {a = size~↓! A + size~↓! B} {b = 1 + size~↑! k~l}) size))
                    (λ { _ _ () }) (λ { () })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (cast-ℕ x X x₂ x₃) (leS size) = castℕ-refl-dec~ (stability~↓! (symConEq Γ≡Δ) x) (λ {_ _ ()}) (λ {_ ()}) (λ {()})
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (cast-Π x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (cast-Πℕ x x₁ x₂ x₃) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (cast-ℕΠ x x₁ x₂ x₃) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (var-refl {n} ⊢x n≡n) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (var-refl ⊢x n≡n) (cast-refl A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let _ , neA , neB = ne~↓! A~A
        _ , _ , eqU , A~A' = sym~↓! (symConEq Γ≡Δ) A~A
        _ , _ , ⊢B  = syntacticEqTerm (soundness~↓! A~A)
    in cast-refl'-dec neA neB (stabilityTerm (symConEq Γ≡Δ) ⊢B) (stabilityTerm (symConEq Γ≡Δ) x) (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                      (yes (_ , _ , A~A'))
                      (dec~↑! Γ≡Δ (var-refl ⊢x n≡n) k~l (<<-trans (<=-help-abrem' {x = 1} {a = size~↓! A~A} {b = 1 + size~↑! k~l}) size))
                      (λ { _ _ () }) λ { () }
  dec~↑! Γ≡Δ (var-refl ⊢x n≡n) (castℕ-refl ([~] A D whnfB k~l) ⊢e) (leS size) =
      castℕℕ-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) ([~] A D whnfB k~l))
                     (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                     (dec~↑! Γ≡Δ (var-refl ⊢x n≡n) k~l (<<-trans (le-suc (le-refl _)) size))
                     (λ { _ _ () }) (λ { () })
  dec~↑! Γ≡Δ (var-refl ⊢x n≡n) (cast-refl' A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    dec~↑! Γ≡Δ (var-refl ⊢x n≡n) k~l (<<-trans (<=-help-abrem' {x = 1} {a = size~↓! A~A} {b = 1 + size~↑! k~l}) size)
  dec~↑! Γ≡Δ (var-refl ⊢x n≡n) (castℕ-refl' ([~] A D whnfB k~l) ⊢e) (leS size) =
    dec~↑! Γ≡Δ (var-refl ⊢x n≡n) k~l (<<-trans (le-suc (le-refl _)) size)
  dec~↑! Γ≡Δ (var-refl x x₁) (cast-neℕ x₂ x₃ x₄ x₅) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ  ;
                                                                         (_ , _ , castℕ-refl' x x₁) → let _ , neℕ , _ = ne~↓! x₂ in noNeℕ neℕ })
  dec~↑! Γ≡Δ (var-refl x x₁) (cast-neΠ x₂ x₃ x₄ x₅ x₆) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })

  dec~↑! Γ≡Δ (app-cong x~x t≡t) (var-refl x x₁) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (natrec-cong x x₁ x₂ x₃) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (Emptyrec-cong x x₁) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (Id-cong x x₁ x₂) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (Id-ℕ x x₁) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (Id-ℕ0 x) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (Id-ℕS x x₁) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (Id-U x x₁) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (Id-Uℕ x) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (Id-UΠ x x₁) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e _) (leS size) =
    let X = app-cong x~x t≡t
    in cast-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) A) (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B))
                       (stabilityConv↓Term (symConEq Γ≡Δ) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)))
                       (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                       (dec~↓! Γ≡Δ (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B)) A (<<-trans (<=-trans (<=-trans (≡-to-<= (PE.trans (PE.cong (λ X → X + size~↓! A) (sym~↓!Usize _))
                                                                                                (+-sym (size~↓! (stability~↓! (symConEq Γ≡Δ) B)) (size~↓! A))))
                                                                                                (<=-cong-+ (le-refl (size~↓! A)) (≡-to-<= (stabilitySize~↓! _ B))))
                                                                   (<=-help-abrem {x = removeSuc (size~↑! X)}
                                                                                  {a = size~↓! A + size~↓! B} {b = 2 + size~↑! k~l}) ) size))
                       (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A + size~↓! B} {c = size~↑! k~l}) size))
                       (λ { _ _ () }) (λ { () })    
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ℕ x x₁ x₂ x₃) _ = castℕ-refl-dec~ (stability~↓! (symConEq Γ≡Δ) x) (λ {_ _ ()}) (λ {_ ()}) (λ {()}) 
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-Π x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-Πℕ x x₁ x₂ x₃) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ℕΠ x x₁ x₂ x₃) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-refl A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = app-cong x~x t≡t
        _ , neA , neB = ne~↓! A~A
        _ , _ , eqU , A~A' = sym~↓! (symConEq Γ≡Δ) A~A
        _ , _ , ⊢B  = syntacticEqTerm (soundness~↓! A~A)
    in cast-refl'-dec neA neB (stabilityTerm (symConEq Γ≡Δ) ⊢B) (stabilityTerm (symConEq Γ≡Δ) x) (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                      (yes (_ , _ , A~A'))
                      (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size))
                      (λ { _ _ () }) λ { () }
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (castℕ-refl ([~] A D whnfB k~l) ⊢e) (leS size) =
      let X = app-cong x~x t≡t
      in castℕℕ-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) ([~] A D whnfB k~l))
                           (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                           (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size))
                           (λ { _ _ () }) (λ { () })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-refl' A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = app-cong x~x t≡t
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size)
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (castℕ-refl' ([~] A D whnfB k~l) ⊢e) (leS size) =
    let X = app-cong x~x t≡t
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size)
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-neℕ x₂ x₃ x₄ x₅) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ  ;
                                                                         (_ , _ , castℕ-refl' x x₁) → let _ , neℕ , _ = ne~↓! x₂ in noNeℕ neℕ })
  dec~↑! Γ≡Δ (app-cong x~x t≡t) (cast-neΠ x₂ x₃ x₄ x₅ x₆) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })

  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (var-refl x₄ x₅) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (app-cong x₄ x₅) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (Emptyrec-cong x₄ x₅) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (Id-cong x₄ x₅ x₆) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (Id-ℕ x₄ x₅) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (Id-ℕ0 x₄) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (Id-ℕS x₄ x₅) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (Id-U x₄ x₅) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (Id-Uℕ x₄) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) (Id-UΠ x₄ x₅) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e _) (leS size) =
    let X = natrec-cong x' x'₁ x'₂ x'₃
    in cast-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) A) (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B))
                       (stabilityConv↓Term (symConEq Γ≡Δ) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)))
                       (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                       (dec~↓! Γ≡Δ (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B)) A (<<-trans (<=-trans (<=-trans (≡-to-<= (PE.trans (PE.cong (λ X → X + size~↓! A) (sym~↓!Usize _))
                                                                                                (+-sym (size~↓! (stability~↓! (symConEq Γ≡Δ) B)) (size~↓! A))))
                                                                                                (<=-cong-+ (le-refl (size~↓! A)) (≡-to-<= (stabilitySize~↓! _ B))))
                                                                   (<=-help-abrem {x = removeSuc (size~↑! X)}
                                                                                  {a = size~↓! A + size~↓! B} {b = 2 + size~↑! k~l}) ) size))
                       (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A + size~↓! B} {c = size~↑! k~l}) size))
                       (λ { _ _ () }) (λ { () })    
  dec~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-ℕ x x₁ x₂ x₃) _ = castℕ-refl-dec~ (stability~↓! (symConEq Γ≡Δ) x) (λ {_ _ ()}) (λ {_ ()}) (λ {()}) 
  dec~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-Π x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-Πℕ x x₁ x₂ x₃) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-ℕΠ x x₁ x₂ x₃) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-refl A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (natrec-cong x' x'₁ x'₂ x'₃)
        _ , neA , neB = ne~↓! A~A
        _ , _ , eqU , A~A' = sym~↓! (symConEq Γ≡Δ) A~A
        _ , _ , ⊢B  = syntacticEqTerm (soundness~↓! A~A)
    in cast-refl'-dec neA neB (stabilityTerm (symConEq Γ≡Δ) ⊢B) (stabilityTerm (symConEq Γ≡Δ) x) (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                      (yes (_ , _ , A~A'))
                      (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size))
                      (λ { _ _ () }) λ { () }
  dec~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (castℕ-refl ([~] A D whnfB k~l) ⊢e) (leS size) =
      let X = (natrec-cong x' x'₁ x'₂ x'₃)
      in castℕℕ-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) ([~] A D whnfB k~l))
                           (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                           (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size))
                           (λ { _ _ () }) (λ { () })
  dec~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-refl' A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (natrec-cong x' x'₁ x'₂ x'₃)
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size)
  dec~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (castℕ-refl' ([~] A D whnfB k~l) ⊢e) (leS size) =
    let X = (natrec-cong x' x'₁ x'₂ x'₃)
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size)
  dec~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-neℕ x₂ x₃ x₄ x₅) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ  ;
                                                                                      (_ , _ , castℕ-refl' x x₁) → let _ , neℕ , _ = ne~↓! x₂ in noNeℕ neℕ })
  dec~↑! Γ≡Δ (natrec-cong x' x'₁ x'₂ x'₃) (cast-neΠ x₂ x₃ x₄ x₅ x₆) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })

  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (var-refl x₂ x₃) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (app-cong x₂ x₃) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (natrec-cong x₂ x₃ x₄ x₅) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (Id-cong x₂ x₃ x₄) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (Id-ℕ x₂ x₃) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (Id-ℕ0 x₂) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (Id-ℕS x₂ x₃) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (Id-U x₂ x₃) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (Id-Uℕ x₂) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x x₁) (Id-UΠ x₂ x₃) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e _) (leS size) =
    let X = Emptyrec-cong x' x'₁
    in cast-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) A) (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B))
                       (stabilityConv↓Term (symConEq Γ≡Δ) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)))
                       (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                       (dec~↓! Γ≡Δ (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B)) A (<<-trans (<=-trans (<=-trans (≡-to-<= (PE.trans (PE.cong (λ X → X + size~↓! A) (sym~↓!Usize _))
                                                                                                (+-sym (size~↓! (stability~↓! (symConEq Γ≡Δ) B)) (size~↓! A))))
                                                                                                (<=-cong-+ (le-refl (size~↓! A)) (≡-to-<= (stabilitySize~↓! _ B))))
                                                                   (<=-help-abrem {x = removeSuc (size~↑! X)}
                                                                                  {a = size~↓! A + size~↓! B} {b = 2 + size~↑! k~l}) ) size))
                       (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A + size~↓! B} {c = size~↑! k~l}) size))
                       (λ { _ _ () }) (λ { () })    
  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-ℕ x x₁ x₂ x₃) _ = castℕ-refl-dec~ (stability~↓! (symConEq Γ≡Δ) x) (λ {_ _ ()}) (λ {_ ()}) (λ {()}) 
  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-Π x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-Πℕ x x₁ x₂ x₃) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-ℕΠ x x₁ x₂ x₃) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-refl A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (Emptyrec-cong x' x'₁)
        _ , neA , neB = ne~↓! A~A
        _ , _ , eqU , A~A' = sym~↓! (symConEq Γ≡Δ) A~A
        _ , _ , ⊢B  = syntacticEqTerm (soundness~↓! A~A)
    in cast-refl'-dec neA neB (stabilityTerm (symConEq Γ≡Δ) ⊢B) (stabilityTerm (symConEq Γ≡Δ) x) (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                      (yes (_ , _ , A~A'))
                      (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size))
                      (λ { _ _ () }) λ { () }
  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (castℕ-refl ([~] A D whnfB k~l) ⊢e) (leS size) =
      let X = (Emptyrec-cong x' x'₁)
      in castℕℕ-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) ([~] A D whnfB k~l))
                           (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                           (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size))
                           (λ { _ _ () }) (λ { () })
  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-refl' A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (Emptyrec-cong x' x'₁)
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size)
  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (castℕ-refl' ([~] A D whnfB k~l) ⊢e) (leS size) =
    let X = (Emptyrec-cong x' x'₁)
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size)
  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-neℕ x₂ x₃ x₄ x₅) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ  ;
                                                                                      (_ , _ , castℕ-refl' x x₁) → let _ , neℕ , _ = ne~↓! x₂ in noNeℕ neℕ })
  dec~↑! Γ≡Δ (Emptyrec-cong x' x'₁) (cast-neΠ x₂ x₃ x₄ x₅ x₆) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })

  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (var-refl x₃ x₄) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (app-cong x₃ x₄) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (natrec-cong x₃ x₄ x₅ x₆) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (Emptyrec-cong x₃ x₄) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (Id-ℕ x₃ x₄) _ =
    let _ , neA , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → Idℕ-elim neA e }
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (Id-ℕ0 x₃) _ =
    let _ , neA , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → Idℕ-elim neA e }
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (Id-ℕS x₃ x₄) _ =
    let _ , neA , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → Idℕ-elim neA e }
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (Id-U x₃ x₄) _ =
    let _ , neA , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → IdU-elim neA e }
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (Id-Uℕ x₃) _ =
    let _ , neA , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → IdU-elim neA e }
  dec~↑! Γ≡Δ (Id-cong x x₁ x₂) (Id-UΠ x₃ x₄) _ =
    let _ , neA , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → IdU-elim neA e }
  dec~↑! Γ≡Δ (Id-cong x' x'₁ x'₂) (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e _) (leS size) =
    let X = Id-cong x' x'₁ x'₂
    in cast-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) A) (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B))
                       (stabilityConv↓Term (symConEq Γ≡Δ) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)))
                       (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                       (dec~↓! Γ≡Δ (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B)) A (<<-trans (<=-trans (<=-trans (≡-to-<= (PE.trans (PE.cong (λ X → X + size~↓! A) (sym~↓!Usize _))
                                                                                                (+-sym (size~↓! (stability~↓! (symConEq Γ≡Δ) B)) (size~↓! A))))
                                                                                                (<=-cong-+ (le-refl (size~↓! A)) (≡-to-<= (stabilitySize~↓! _ B))))
                                                                   (<=-help-abrem {x = removeSuc (size~↑! X)}
                                                                                  {a = size~↓! A + size~↓! B} {b = 2 + size~↑! k~l}) ) size))
                       (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A + size~↓! B} {c = size~↑! k~l}) size))
                       (λ { _ _ () }) (λ { () })    
  dec~↑! Γ≡Δ (Id-cong x' x'₁ x'₂) (cast-ℕ x x₁ x₂ x₃) _ = castℕ-refl-dec~ (stability~↓! (symConEq Γ≡Δ) x) (λ {_ _ ()}) (λ {_ ()}) (λ {()}) 
  dec~↑! Γ≡Δ (Id-cong x' x'₁ x'₂) (cast-Π x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-cong x' x'₁ x'₂) (cast-Πℕ x x₁ x₂ x₃) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-cong x' x'₁ x'₂) (cast-ℕΠ x x₁ x₂ x₃) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-cong x' x'₁ x'₂) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-cong x' x'₁ x'₂) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-cong x' x'₁ x'₂) (cast-refl A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (Id-cong x' x'₁ x'₂)
        _ , neA , neB = ne~↓! A~A
        _ , _ , eqU , A~A' = sym~↓! (symConEq Γ≡Δ) A~A
        _ , _ , ⊢B  = syntacticEqTerm (soundness~↓! A~A)
    in cast-refl'-dec neA neB (stabilityTerm (symConEq Γ≡Δ) ⊢B) (stabilityTerm (symConEq Γ≡Δ) x) (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                      (yes (_ , _ , A~A'))
                      (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size))
                      (λ { _ _ () }) λ { () }
  dec~↑! Γ≡Δ (Id-cong x' x'₁ x'₂) (castℕ-refl ([~] A D whnfB k~l) ⊢e) (leS size) =
      let X = (Id-cong x' x'₁ x'₂)
      in castℕℕ-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) ([~] A D whnfB k~l))
                           (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                           (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size))
                           (λ { _ _ () }) (λ { () })
  dec~↑! Γ≡Δ (Id-cong x' x'₁ x'₂) (cast-refl' A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (Id-cong x' x'₁ x'₂)
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size)
  dec~↑! Γ≡Δ (Id-cong x' x'₁ x'₂) (castℕ-refl' ([~] A D whnfB k~l) ⊢e) (leS size) =
    let X = (Id-cong x' x'₁ x'₂)
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size)
  dec~↑! Γ≡Δ (Id-cong x' x'₁ x'₂) (cast-neℕ x₂ x₃ x₄ x₅) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ  ;
                                                                                      (_ , _ , castℕ-refl' x x₁) → let _ , neℕ , _ = ne~↓! x₂ in noNeℕ neℕ })
  dec~↑! Γ≡Δ (Id-cong x' x'₁ x'₂) (cast-neΠ x₂ x₃ x₄ x₅ x₆) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })

  dec~↑! Γ≡Δ (Id-ℕ x x₁) (var-refl x₂ x₃) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ x x₁) (app-cong x₂ x₃) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ x x₁) (natrec-cong x₂ x₃ x₄ x₅) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ x x₁) (Emptyrec-cong x₂ x₃) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ x x₁) (Id-cong x₂ x₃ x₄) _ =
    let _ , neA , _ = ne~↓! x₂ in no λ { ( _ , ( _ , e )) → Idℕ-elim' neA e }
  dec~↑! Γ≡Δ (Id-ℕ x x₁) (Id-ℕ0 x₂) _ =
    let _ , net , _ = ne~↓! x in no (λ { ( _ , ( _ , e )) → Idℕ0-elim net e })
  dec~↑! Γ≡Δ (Id-ℕ x x₁) (Id-ℕS x₂ x₃) _ =
    let _ , net , _ = ne~↓! x in no (λ { ( _ , ( _ , e )) → IdℕS-elim net e })
  dec~↑! Γ≡Δ (Id-ℕ x x₁) (Id-U x₂ x₃) _ = no λ { ( _ , ( _ , e )) → IdℕU-elim e }
  dec~↑! Γ≡Δ (Id-ℕ x x₁) (Id-Uℕ x₂) _ = no λ { ( _ , ( _ , e )) → IdℕU-elim e }
  dec~↑! Γ≡Δ (Id-ℕ x x₁) (Id-UΠ x₂ x₃) _ = no λ { ( _ , ( _ , e )) → IdℕU-elim e }
  dec~↑! Γ≡Δ (Id-ℕ x' x'₁) (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e _) (leS size) =
    let X = (Id-ℕ x' x'₁)
    in cast-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) A) (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B))
                       (stabilityConv↓Term (symConEq Γ≡Δ) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)))
                       (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                       (dec~↓! Γ≡Δ (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B)) A (<<-trans (<=-trans (<=-trans (≡-to-<= (PE.trans (PE.cong (λ X → X + size~↓! A) (sym~↓!Usize _))
                                                                                                (+-sym (size~↓! (stability~↓! (symConEq Γ≡Δ) B)) (size~↓! A))))
                                                                                                (<=-cong-+ (le-refl (size~↓! A)) (≡-to-<= (stabilitySize~↓! _ B))))
                                                                   (<=-help-abrem {x = removeSuc (size~↑! X)}
                                                                                  {a = size~↓! A + size~↓! B} {b = 2 + size~↑! k~l}) ) size))
                       (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A + size~↓! B} {c = size~↑! k~l}) size))
                       (λ { _ _ () }) (λ { () })    
  dec~↑! Γ≡Δ (Id-ℕ x' x'₁) (cast-ℕ x x₁ x₂ x₃) _ = castℕ-refl-dec~ (stability~↓! (symConEq Γ≡Δ) x) (λ {_ _ ()}) (λ {_ ()}) (λ {()}) 
  dec~↑! Γ≡Δ (Id-ℕ x' x'₁) (cast-Π x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-ℕ x' x'₁) (cast-Πℕ x x₁ x₂ x₃) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-ℕ x' x'₁) (cast-ℕΠ x x₁ x₂ x₃) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-ℕ x' x'₁) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-ℕ x' x'₁) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-ℕ x' x'₁) (cast-refl A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (Id-ℕ x' x'₁)
        _ , neA , neB = ne~↓! A~A
        _ , _ , eqU , A~A' = sym~↓! (symConEq Γ≡Δ) A~A
        _ , _ , ⊢B  = syntacticEqTerm (soundness~↓! A~A)
    in cast-refl'-dec neA neB (stabilityTerm (symConEq Γ≡Δ) ⊢B) (stabilityTerm (symConEq Γ≡Δ) x) (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                      (yes (_ , _ , A~A'))
                      (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size))
                      (λ { _ _ () }) λ { () }
  dec~↑! Γ≡Δ (Id-ℕ x' x'₁) (castℕ-refl ([~] A D whnfB k~l) ⊢e) (leS size) =
      let X = (Id-ℕ x' x'₁)
      in castℕℕ-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) ([~] A D whnfB k~l))
                           (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                           (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size))
                           (λ { _ _ () }) (λ { () })
  dec~↑! Γ≡Δ (Id-ℕ x' x'₁) (cast-refl' A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (Id-ℕ x' x'₁)
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size)
  dec~↑! Γ≡Δ (Id-ℕ x' x'₁) (castℕ-refl' ([~] A D whnfB k~l) ⊢e) (leS size) =
    let X = (Id-ℕ x' x'₁)
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size)
  dec~↑! Γ≡Δ (Id-ℕ x' x'₁) (cast-neℕ x₂ x₃ x₄ x₅) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ  ;
                                                                                      (_ , _ , castℕ-refl' x x₁) → let _ , neℕ , _ = ne~↓! x₂ in noNeℕ neℕ })
  dec~↑! Γ≡Δ (Id-ℕ x' x'₁) (cast-neΠ x₂ x₃ x₄ x₅ x₆) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })

  dec~↑! Γ≡Δ (Id-ℕ0 x) (var-refl x₁ x₂) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ0 x) (app-cong x₁ x₂) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ0 x) (natrec-cong x₁ x₂ x₃ x₄) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ0 x) (Emptyrec-cong x₁ x₂) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕ0 x) (Id-cong x₁ x₂ x₃) _ =
    let _ , neA , _ = ne~↓! x₁ in no λ { ( _ , ( _ , e )) → Idℕ-elim' neA e }
  dec~↑! Γ≡Δ (Id-ℕ0 x) (Id-ℕ x₁ x₂) _ =
    let _ , net , _ = ne~↓! x₁ in no (λ { ( _ , ( _ , e )) → Idℕ0-elim' net e })
  dec~↑! Γ≡Δ (Id-ℕ0 x) (Id-ℕS x₁ x₂) _ = no λ { ( _ , ( _ , e )) → Idℕ0S-elim e }
  dec~↑! Γ≡Δ (Id-ℕ0 x) (Id-U x₁ x₂) _ = no λ { ( _ , ( _ , e )) → IdℕU-elim e }
  dec~↑! Γ≡Δ (Id-ℕ0 x) (Id-Uℕ x₁) _ = no λ { ( _ , ( _ , e )) → IdℕU-elim e }
  dec~↑! Γ≡Δ (Id-ℕ0 x) (Id-UΠ x₁ x₂) _ = no λ { ( _ , ( _ , e )) → IdℕU-elim e }
  dec~↑! Γ≡Δ (Id-ℕ0 x') (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e _) (leS size) =
    let X = (Id-ℕ0 x')
    in cast-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) A) (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B))
                       (stabilityConv↓Term (symConEq Γ≡Δ) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)))
                       (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                       (dec~↓! Γ≡Δ (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B)) A (<<-trans (<=-trans (<=-trans (≡-to-<= (PE.trans (PE.cong (λ X → X + size~↓! A) (sym~↓!Usize _))
                                                                                                (+-sym (size~↓! (stability~↓! (symConEq Γ≡Δ) B)) (size~↓! A))))
                                                                                                (<=-cong-+ (le-refl (size~↓! A)) (≡-to-<= (stabilitySize~↓! _ B))))
                                                                   (<=-help-abrem {x = removeSuc (size~↑! X)}
                                                                                  {a = size~↓! A + size~↓! B} {b = 2 + size~↑! k~l}) ) size))
                       (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A + size~↓! B} {c = size~↑! k~l}) size))
                       (λ { _ _ () }) (λ { () })    
  dec~↑! Γ≡Δ (Id-ℕ0 x') (cast-ℕ x x₁ x₂ x₃) _ = castℕ-refl-dec~ (stability~↓! (symConEq Γ≡Δ) x) (λ {_ _ ()}) (λ {_ ()}) (λ {()}) 
  dec~↑! Γ≡Δ (Id-ℕ0 x') (cast-Π x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-ℕ0 x') (cast-Πℕ x x₁ x₂ x₃) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-ℕ0 x') (cast-ℕΠ x x₁ x₂ x₃) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-ℕ0 x') (cast-ΠΠ%! x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-ℕ0 x') (cast-ΠΠ!% x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-ℕ0 x') (cast-refl A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (Id-ℕ0 x')
        _ , neA , neB = ne~↓! A~A
        _ , _ , eqU , A~A' = sym~↓! (symConEq Γ≡Δ) A~A
        _ , _ , ⊢B  = syntacticEqTerm (soundness~↓! A~A)
    in cast-refl'-dec neA neB (stabilityTerm (symConEq Γ≡Δ) ⊢B) (stabilityTerm (symConEq Γ≡Δ) x) (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                      (yes (_ , _ , A~A'))
                      (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size))
                      (λ { _ _ () }) λ { () }
  dec~↑! Γ≡Δ (Id-ℕ0 x') (castℕ-refl ([~] A D whnfB k~l) ⊢e) (leS size) =
      let X = (Id-ℕ0 x')
      in castℕℕ-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) ([~] A D whnfB k~l))
                           (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                           (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size))
                           (λ { _ _ () }) (λ { () })
  dec~↑! Γ≡Δ (Id-ℕ0 x') (cast-refl' A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (Id-ℕ0 x')
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size)
  dec~↑! Γ≡Δ (Id-ℕ0 x') (castℕ-refl' ([~] A D whnfB k~l) ⊢e) (leS size) =
    let X = (Id-ℕ0 x')
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size)
  dec~↑! Γ≡Δ (Id-ℕ0 x') (cast-neℕ x₂ x₃ x₄ x₅) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ  ;
                                                                                      (_ , _ , castℕ-refl' x x₁) → let _ , neℕ , _ = ne~↓! x₂ in noNeℕ neℕ })
  dec~↑! Γ≡Δ (Id-ℕ0 x') (cast-neΠ x₂ x₃ x₄ x₅ x₆) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })

  dec~↑! Γ≡Δ (Id-ℕS x x₁) (var-refl x₂ x₃) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕS x x₁) (app-cong x₂ x₃) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕS x x₁) (natrec-cong x₂ x₃ x₄ x₅) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕS x x₁) (Emptyrec-cong x₂ x₃) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-ℕS x x₁) (Id-cong x₂ x₃ x₄) _ =
    let _ , neA , _ = ne~↓! x₂ in no λ { ( _ , ( _ , e )) → Idℕ-elim' neA e }
  dec~↑! Γ≡Δ (Id-ℕS x x₁) (Id-ℕ x₂ x₃) _ =
    let _ , net , _ = ne~↓! x₂ in no (λ { ( _ , ( _ , e )) → IdℕS-elim' net e })
  dec~↑! Γ≡Δ (Id-ℕS x x₁) (Id-ℕ0 x₂) _ = no λ { ( _ , ( _ , e )) → Idℕ0S-elim' e }
  dec~↑! Γ≡Δ (Id-ℕS x x₁) (Id-U x₂ x₃) _ = no λ { ( _ , ( _ , e )) → IdℕU-elim e }
  dec~↑! Γ≡Δ (Id-ℕS x x₁) (Id-Uℕ x₂) _ = no λ { ( _ , ( _ , e )) → IdℕU-elim e }
  dec~↑! Γ≡Δ (Id-ℕS x x₁) (Id-UΠ x₂ x₃) _ = no λ { ( _ , ( _ , e )) → IdℕU-elim e }
  dec~↑! Γ≡Δ (Id-ℕS x' x'₁) (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e _) (leS size) =
    let X = (Id-ℕS x' x'₁)
    in cast-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) A) (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B))
                       (stabilityConv↓Term (symConEq Γ≡Δ) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)))
                       (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                       (dec~↓! Γ≡Δ (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B)) A (<<-trans (<=-trans (<=-trans (≡-to-<= (PE.trans (PE.cong (λ X → X + size~↓! A) (sym~↓!Usize _))
                                                                                                (+-sym (size~↓! (stability~↓! (symConEq Γ≡Δ) B)) (size~↓! A))))
                                                                                                (<=-cong-+ (le-refl (size~↓! A)) (≡-to-<= (stabilitySize~↓! _ B))))
                                                                   (<=-help-abrem {x = removeSuc (size~↑! X)}
                                                                                  {a = size~↓! A + size~↓! B} {b = 2 + size~↑! k~l}) ) size))
                       (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A + size~↓! B} {c = size~↑! k~l}) size))
                       (λ { _ _ () }) (λ { () })    
  dec~↑! Γ≡Δ (Id-ℕS x' x'₁) (cast-ℕ x x₁ x₂ x₃) _ = castℕ-refl-dec~ (stability~↓! (symConEq Γ≡Δ) x) (λ {_ _ ()}) (λ {_ ()}) (λ {()}) 
  dec~↑! Γ≡Δ (Id-ℕS x' x'₁) (cast-Π x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-ℕS x' x'₁) (cast-ℕΠ x x₁ x₂ x₃) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-ℕS x' x'₁) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-ℕS x' x'₁) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-ℕS x' x'₁) (cast-refl A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (Id-ℕS x' x'₁)
        _ , neA , neB = ne~↓! A~A
        _ , _ , eqU , A~A' = sym~↓! (symConEq Γ≡Δ) A~A
        _ , _ , ⊢B  = syntacticEqTerm (soundness~↓! A~A)
    in cast-refl'-dec neA neB (stabilityTerm (symConEq Γ≡Δ) ⊢B) (stabilityTerm (symConEq Γ≡Δ) x) (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                      (yes (_ , _ , A~A'))
                      (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size))
                      (λ { _ _ () }) λ { () }
  dec~↑! Γ≡Δ (Id-ℕS x' x'₁) (castℕ-refl ([~] A D whnfB k~l) ⊢e) (leS size) =
      let X = (Id-ℕS x' x'₁)
      in castℕℕ-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) ([~] A D whnfB k~l))
                           (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                           (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size))
                           (λ { _ _ () }) (λ { () })
  dec~↑! Γ≡Δ (Id-ℕS x' x'₁) (cast-refl' A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (Id-ℕS x' x'₁)
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size)
  dec~↑! Γ≡Δ (Id-ℕS x' x'₁) (castℕ-refl' ([~] A D whnfB k~l) ⊢e) (leS size) =
    let X = (Id-ℕS x' x'₁)
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size)
  dec~↑! Γ≡Δ (Id-ℕS x' x'₁) (cast-neℕ x₂ x₃ x₄ x₅) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ  ;
                                                                                      (_ , _ , castℕ-refl' x x₁) → let _ , neℕ , _ = ne~↓! x₂ in noNeℕ neℕ })
  dec~↑! Γ≡Δ (Id-ℕS x' x'₁) (cast-neΠ x₂ x₃ x₄ x₅ x₆) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })

  dec~↑! Γ≡Δ (Id-U x x₁) (var-refl x₂ x₃) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-U x x₁) (app-cong x₂ x₃) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-U x x₁) (natrec-cong x₂ x₃ x₄ x₅) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-U x x₁) (Emptyrec-cong x₂ x₃) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-U x x₁) (Id-cong x₂ x₃ x₄) _ =
    let _ , neA , _ = ne~↓! x₂ in no λ { ( _ , ( _ , e )) → IdU-elim' neA e }
  dec~↑! Γ≡Δ (Id-U x x₁) (Id-ℕ x₂ x₃) _ = no λ { ( _ , ( _ , e )) → IdUℕ-elim e }
  dec~↑! Γ≡Δ (Id-U x x₁) (Id-ℕ0 x₂) _ = no λ { ( _ , ( _ , e )) → IdUℕ-elim e }
  dec~↑! Γ≡Δ (Id-U x x₁) (Id-ℕS x₂ x₃) _ = no λ { ( _ , ( _ , e )) → IdUℕ-elim e }
  dec~↑! Γ≡Δ (Id-U x x₁) (Id-Uℕ x₂) _ = let _ , net , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → IdUUℕ-elim net e }
  dec~↑! Γ≡Δ (Id-U x x₁) (Id-UΠ x₂ x₃) _ = let _ , net , _ = ne~↓! x in no λ { ( _ , ( _ , e )) → IdUUΠ-elim net e }
  dec~↑! Γ≡Δ (Id-U x' x'₁) (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e _) (leS size) =
    let X = (Id-U x' x'₁)
    in cast-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) A) (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B))
                       (stabilityConv↓Term (symConEq Γ≡Δ) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)))
                       (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                       (dec~↓! Γ≡Δ (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B)) A (<<-trans (<=-trans (<=-trans (≡-to-<= (PE.trans (PE.cong (λ X → X + size~↓! A) (sym~↓!Usize _))
                                                                                                (+-sym (size~↓! (stability~↓! (symConEq Γ≡Δ) B)) (size~↓! A))))
                                                                                                (<=-cong-+ (le-refl (size~↓! A)) (≡-to-<= (stabilitySize~↓! _ B))))
                                                                   (<=-help-abrem {x = removeSuc (size~↑! X)}
                                                                                  {a = size~↓! A + size~↓! B} {b = 2 + size~↑! k~l}) ) size))
                       (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A + size~↓! B} {c = size~↑! k~l}) size))
                       (λ { _ _ () }) (λ { () })    
  dec~↑! Γ≡Δ (Id-U x' x'₁) (cast-ℕ x x₁ x₂ x₃) _ = castℕ-refl-dec~ (stability~↓! (symConEq Γ≡Δ) x) (λ {_ _ ()}) (λ {_ ()}) (λ {()}) 
  dec~↑! Γ≡Δ (Id-U x' x'₁) (cast-Π x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-U x' x'₁) (cast-ℕΠ x x₁ x₂ x₃) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-U x' x'₁) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-U x' x'₁) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-U x' x'₁) (cast-refl A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (Id-U x' x'₁)
        _ , neA , neB = ne~↓! A~A
        _ , _ , eqU , A~A' = sym~↓! (symConEq Γ≡Δ) A~A
        _ , _ , ⊢B  = syntacticEqTerm (soundness~↓! A~A)
    in cast-refl'-dec neA neB (stabilityTerm (symConEq Γ≡Δ) ⊢B) (stabilityTerm (symConEq Γ≡Δ) x) (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                      (yes (_ , _ , A~A'))
                      (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size))
                      (λ { _ _ () }) λ { () }
  dec~↑! Γ≡Δ (Id-U x' x'₁) (castℕ-refl ([~] A D whnfB k~l) ⊢e) (leS size) =
      let X = (Id-U x' x'₁)
      in castℕℕ-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) ([~] A D whnfB k~l))
                           (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                           (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size))
                           (λ { _ _ () }) (λ { () })
  dec~↑! Γ≡Δ (Id-U x' x'₁) (cast-refl' A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (Id-U x' x'₁)
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size)
  dec~↑! Γ≡Δ (Id-U x' x'₁) (castℕ-refl' ([~] A D whnfB k~l) ⊢e) (leS size) =
    let X = (Id-U x' x'₁)
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size)
  dec~↑! Γ≡Δ (Id-U x' x'₁) (cast-neℕ x₂ x₃ x₄ x₅) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ  ;
                                                                                      (_ , _ , castℕ-refl' x x₁) → let _ , neℕ , _ = ne~↓! x₂ in noNeℕ neℕ })
  dec~↑! Γ≡Δ (Id-U x' x'₁) (cast-neΠ x₂ x₃ x₄ x₅ x₆) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })

  dec~↑! Γ≡Δ (Id-Uℕ x) (var-refl x₁ x₂) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-Uℕ x) (app-cong x₁ x₂) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-Uℕ x) (natrec-cong x₁ x₂ x₃ x₄) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-Uℕ x) (Emptyrec-cong x₁ x₂) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-Uℕ x) (Id-cong x₁ x₂ x₃) _ =
    let _ , neA , _ = ne~↓! x₁ in no λ { ( _ , ( _ , e )) → IdU-elim' neA e }
  dec~↑! Γ≡Δ (Id-Uℕ x) (Id-ℕ x₁ x₂) _ = no λ { ( _ , ( _ , e )) → IdUℕ-elim e }
  dec~↑! Γ≡Δ (Id-Uℕ x) (Id-ℕ0 x₁) _ = no λ { ( _ , ( _ , e )) → IdUℕ-elim e }
  dec~↑! Γ≡Δ (Id-Uℕ x) (Id-ℕS x₁ x₂) _ = no λ { ( _ , ( _ , e )) → IdUℕ-elim e }
  dec~↑! Γ≡Δ (Id-Uℕ x) (Id-U x₁ x₂) _ = let _ , net , _ = ne~↓! x₁ in no λ { ( _ , ( _ , e )) → IdUUℕ-elim' net e }
  dec~↑! Γ≡Δ (Id-Uℕ x) (Id-UΠ x₁ x₂) _ = no λ { ( _ , ( _ , e )) → IdUUΠℕ-elim' e }
  dec~↑! Γ≡Δ (Id-Uℕ x') (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e _) (leS size) =
    let X = (Id-Uℕ x')
    in cast-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) A) (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B))
                       (stabilityConv↓Term (symConEq Γ≡Δ) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)))
                       (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                       (dec~↓! Γ≡Δ (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B)) A (<<-trans (<=-trans (<=-trans (≡-to-<= (PE.trans (PE.cong (λ X → X + size~↓! A) (sym~↓!Usize _))
                                                                                                (+-sym (size~↓! (stability~↓! (symConEq Γ≡Δ) B)) (size~↓! A))))
                                                                                                (<=-cong-+ (le-refl (size~↓! A)) (≡-to-<= (stabilitySize~↓! _ B))))
                                                                   (<=-help-abrem {x = removeSuc (size~↑! X)}
                                                                                  {a = size~↓! A + size~↓! B} {b = 2 + size~↑! k~l}) ) size))
                       (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A + size~↓! B} {c = size~↑! k~l}) size))
                       (λ { _ _ () }) (λ { () })    
  dec~↑! Γ≡Δ (Id-Uℕ x') (cast-ℕ x x₁ x₂ x₃) _ = castℕ-refl-dec~ (stability~↓! (symConEq Γ≡Δ) x) (λ {_ _ ()}) (λ {_ ()}) (λ {()}) 
  dec~↑! Γ≡Δ (Id-Uℕ x') (cast-Π x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-Uℕ x') (cast-Πℕ x x₁ x₂ x₃) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-Uℕ x') (cast-ℕΠ x x₁ x₂ x₃) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-Uℕ x') (cast-ΠΠ%! x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-Uℕ x') (cast-ΠΠ!% x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-Uℕ x') (cast-refl A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (Id-Uℕ x')
        _ , neA , neB = ne~↓! A~A
        _ , _ , eqU , A~A' = sym~↓! (symConEq Γ≡Δ) A~A
        _ , _ , ⊢B  = syntacticEqTerm (soundness~↓! A~A)
    in cast-refl'-dec neA neB (stabilityTerm (symConEq Γ≡Δ) ⊢B) (stabilityTerm (symConEq Γ≡Δ) x) (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                      (yes (_ , _ , A~A'))
                      (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size))
                      (λ { _ _ () }) λ { () }
  dec~↑! Γ≡Δ (Id-Uℕ x') (castℕ-refl ([~] A D whnfB k~l) ⊢e) (leS size) =
      let X = (Id-Uℕ x')
      in castℕℕ-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) ([~] A D whnfB k~l))
                           (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                           (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size))
                           (λ { _ _ () }) (λ { () })
  dec~↑! Γ≡Δ (Id-Uℕ x') (cast-refl' A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (Id-Uℕ x')
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size)
  dec~↑! Γ≡Δ (Id-Uℕ x') (castℕ-refl' ([~] A D whnfB k~l) ⊢e) (leS size) =
    let X = (Id-Uℕ x')
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size)
  dec~↑! Γ≡Δ (Id-Uℕ x') (cast-neℕ x₂ x₃ x₄ x₅) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ  ;
                                                                                      (_ , _ , castℕ-refl' x x₁) → let _ , neℕ , _ = ne~↓! x₂ in noNeℕ neℕ })
  dec~↑! Γ≡Δ (Id-Uℕ x') (cast-neΠ x₂ x₃ x₄ x₅ x₆) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })

  dec~↑! Γ≡Δ (Id-UΠ x x₁) (var-refl x₂ x₃) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (app-cong x₂ x₃) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (natrec-cong x₂ x₃ x₄ x₅) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (Emptyrec-cong x₂ x₃) _ = no (λ { (_ , ()) })
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (Id-cong x₂ x₃ x₄) _ =
    let _ , neA , _ = ne~↓! x₂ in no λ { ( _ , ( _ , e )) → IdU-elim' neA e }
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (Id-ℕ x₂ x₃) _ = no λ { ( _ , ( _ , e )) → IdUℕ-elim e }
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (Id-ℕ0 x₂) _ = no λ { ( _ , ( _ , e )) → IdUℕ-elim e }
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (Id-ℕS x₂ x₃) _ = no λ { ( _ , ( _ , e )) → IdUℕ-elim e }
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (Id-U x₂ x₃) _ = let _ , net , _ = ne~↓! x₂ in no λ { ( _ , ( _ , e )) → IdUUΠ-elim' net e }
  dec~↑! Γ≡Δ (Id-UΠ x x₁) (Id-Uℕ x₂) _ = no λ { ( _ , ( _ , e )) → IdUUΠℕ-elim e }
  dec~↑! Γ≡Δ (Id-UΠ x' x'₁) (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e _) (leS size) =
    let X = (Id-UΠ x' x'₁)
    in cast-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) A) (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B))
                       (stabilityConv↓Term (symConEq Γ≡Δ) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)))
                       (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                       (dec~↓! Γ≡Δ (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B)) A (<<-trans (<=-trans (<=-trans (≡-to-<= (PE.trans (PE.cong (λ X → X + size~↓! A) (sym~↓!Usize _))
                                                                                                (+-sym (size~↓! (stability~↓! (symConEq Γ≡Δ) B)) (size~↓! A))))
                                                                                                (<=-cong-+ (le-refl (size~↓! A)) (≡-to-<= (stabilitySize~↓! _ B))))
                                                                   (<=-help-abrem {x = removeSuc (size~↑! X)}
                                                                                  {a = size~↓! A + size~↓! B} {b = 2 + size~↑! k~l}) ) size))
                       (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A + size~↓! B} {c = size~↑! k~l}) size))
                       (λ { _ _ () }) (λ { () })    
  dec~↑! Γ≡Δ (Id-UΠ x' x'₁) (cast-ℕ x x₁ x₂ x₃) _ = castℕ-refl-dec~ (stability~↓! (symConEq Γ≡Δ) x) (λ {_ _ ()}) (λ {_ ()}) (λ {()}) 
  dec~↑! Γ≡Δ (Id-UΠ x' x'₁) (cast-Π x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , neΠ = ne~↓! x in noNeΠ neΠcf })
  dec~↑! Γ≡Δ (Id-UΠ x' x'₁) (cast-ℕΠ x x₁ x₂ x₃) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-UΠ x' x'₁) (cast-ΠΠ%! x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-UΠ x' x'₁) (cast-ΠΠ!% x x₁ x₂ x₃ x₄) _ =  no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (Id-UΠ x' x'₁) (cast-refl A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (Id-UΠ x' x'₁)
        _ , neA , neB = ne~↓! A~A
        _ , _ , eqU , A~A' = sym~↓! (symConEq Γ≡Δ) A~A
        _ , _ , ⊢B  = syntacticEqTerm (soundness~↓! A~A)
    in cast-refl'-dec neA neB (stabilityTerm (symConEq Γ≡Δ) ⊢B) (stabilityTerm (symConEq Γ≡Δ) x) (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                      (yes (_ , _ , A~A'))
                      (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size))
                      (λ { _ _ () }) λ { () }
  dec~↑! Γ≡Δ (Id-UΠ x' x'₁) (castℕ-refl ([~] A D whnfB k~l) ⊢e) (leS size) =
      let X = (Id-UΠ x' x'₁)
      in castℕℕ-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) ([~] A D whnfB k~l))
                           (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                           (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size))
                           (λ { _ _ () }) (λ { () })
  dec~↑! Γ≡Δ (Id-UΠ x' x'₁) (cast-refl' A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (Id-UΠ x' x'₁)
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size)
  dec~↑! Γ≡Δ (Id-UΠ x' x'₁) (castℕ-refl' ([~] A D whnfB k~l) ⊢e) (leS size) =
    let X = (Id-UΠ x' x'₁)
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size)
  dec~↑! Γ≡Δ (Id-UΠ x' x'₁) (cast-neℕ x₂ x₃ x₄ x₅) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ  ;
                                                                                      (_ , _ , castℕ-refl' x x₁) → let _ , neℕ , _ = ne~↓! x₂ in noNeℕ neℕ })
  dec~↑! Γ≡Δ (Id-UΠ x' x'₁) (cast-neΠ x₂ x₃ x₄ x₅ x₆) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })

  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (var-refl {n} ⊢x n≡n) (leS size) =
    let X = var-refl ⊢x n≡n
    in cast-refl-dec~ A (sym~↓!U B) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e 
                      (dec~↓! (reflConEq (wfTerm ⊢e)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B))) (<=-help-barem {x = size~↑! X} {a = size~↓! A + size~↓! B})) size))
                      (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A + size~↓! B}) size)) 
                      (λ {_ _ ()}) (λ {()})
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (app-cong x₅ x₆) (leS size) =
    let X = app-cong x₅ x₆
    in cast-refl-dec~ A (sym~↓!U B) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e 
                      (dec~↓! (reflConEq (wfTerm ⊢e)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B))) (<=-help-barem {x = size~↑! X} {a = size~↓! A + size~↓! B})) size))
                      (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A + size~↓! B}) size)) 
                      (λ {_ _ ()}) (λ {()})

  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (natrec-cong x₅ x₆ x₇ x₈) (leS size) =
    let X = natrec-cong x₅ x₆ x₇ x₈
    in cast-refl-dec~ A (sym~↓!U B) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e 
                      (dec~↓! (reflConEq (wfTerm ⊢e)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B))) (<=-help-barem {x = size~↑! X} {a = size~↓! A + size~↓! B})) size))
                      (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A + size~↓! B}) size)) 
                      (λ {_ _ ()}) (λ {()})
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (Emptyrec-cong x₅ x₆) (leS size) =
    let X = Emptyrec-cong x₅ x₆
    in cast-refl-dec~ A (sym~↓!U B) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e 
                      (dec~↓! (reflConEq (wfTerm ⊢e)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B))) (<=-help-barem {x = size~↑! X} {a = size~↓! A + size~↓! B})) size))
                      (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A + size~↓! B}) size)) 
                      (λ {_ _ ()}) (λ {()})
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (Id-cong x₅ x₆ x₇) (leS size) =
    let X = Id-cong x₅ x₆ x₇
    in cast-refl-dec~ A (sym~↓!U B) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e 
                      (dec~↓! (reflConEq (wfTerm ⊢e)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B))) (<=-help-barem {x = size~↑! X} {a = size~↓! A + size~↓! B})) size))
                      (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A + size~↓! B}) size)) 
                      (λ {_ _ ()}) (λ {()})
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (Id-ℕ x₅ x₆) (leS size) =
    let X = Id-ℕ x₅ x₆
    in cast-refl-dec~ A (sym~↓!U B) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e 
                      (dec~↓! (reflConEq (wfTerm ⊢e)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B))) (<=-help-barem {x = size~↑! X} {a = size~↓! A + size~↓! B})) size))
                      (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A + size~↓! B}) size)) 
                      (λ {_ _ ()}) (λ {()})
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (Id-ℕ0 x₅) (leS size) =
    let X = Id-ℕ0 x₅
    in cast-refl-dec~ A (sym~↓!U B) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e 
                      (dec~↓! (reflConEq (wfTerm ⊢e)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B))) (<=-help-barem {x = size~↑! X} {a = size~↓! A + size~↓! B})) size))
                      (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A + size~↓! B}) size)) 
                      (λ {_ _ ()}) (λ {()})
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (Id-ℕS x₅ x₆) (leS size) =
    let X = Id-ℕS x₅ x₆
    in cast-refl-dec~ A (sym~↓!U B) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e 
                      (dec~↓! (reflConEq (wfTerm ⊢e)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B))) (<=-help-barem {x = size~↑! X} {a = size~↓! A + size~↓! B})) size))
                      (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A + size~↓! B}) size)) 
                      (λ {_ _ ()}) (λ {()})
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (Id-U x₅ x₆) (leS size) =
    let X = Id-U x₅ x₆
    in cast-refl-dec~ A (sym~↓!U B) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e 
                      (dec~↓! (reflConEq (wfTerm ⊢e)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B))) (<=-help-barem {x = size~↑! X} {a = size~↓! A + size~↓! B})) size))
                      (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A + size~↓! B}) size)) 
                      (λ {_ _ ()}) (λ {()})
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (Id-Uℕ x₅) (leS size) =
    let X = Id-Uℕ x₅
    in cast-refl-dec~ A (sym~↓!U B) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e 
                      (dec~↓! (reflConEq (wfTerm ⊢e)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B))) (<=-help-barem {x = size~↑! X} {a = size~↓! A + size~↓! B})) size))
                      (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A + size~↓! B}) size)) 
                      (λ {_ _ ()}) (λ {()})
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (Id-UΠ x₅ x₆) (leS size) =
    let X = Id-UΠ x₅ x₆
    in cast-refl-dec~ A (sym~↓!U B) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e 
                      (dec~↓! (reflConEq (wfTerm ⊢e)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B))) (<=-help-barem {x = size~↑! X} {a = size~↓! A + size~↓! B})) size))
                      (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A + size~↓! B}) size)) 
                      (λ {_ _ ()}) (λ {()})
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (cast-ℕ x₅ x₆ x₇ x₈) (leS size) = 
    let X = cast-ℕ x₅ x₆ x₇ x₈
    in cast-refl-dec~ A (sym~↓!U B) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e 
                      (dec~↓! (reflConEq (wfTerm ⊢e)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B))) (<=-help-barem {x = size~↑! X} {a = size~↓! A + size~↓! B})) size))
                      (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A + size~↓! B}) size)) 
                      (λ neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                     in noNeℕ (PE.subst Neutral (PE.sym eA) neA))
                      (λ e → let _ , _ , eB , _ = cast-PE-injectivity e
                                 _ , neB , _ = ne~↓! x₅
                             in noNeℕ (PE.subst Neutral eB neB))
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (cast-Π x₅ x₆ x₇ x₈ x₉) (leS size) =
    let X = cast-Π x₅ x₆ x₇ x₈ x₉
    in cast-refl-dec~ A (sym~↓!U B) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e 
                      (dec~↓! (reflConEq (wfTerm ⊢e)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B))) (<=-help-barem {x = size~↑! X} {a = size~↓! A + size~↓! B})) size))
                      (dec~↑! Γ≡Δ k~l X (<<-trans (<=-help-barem' {x = size~↑! X} {a = size~↓! A + size~↓! B}) size)) 
                      (λ neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                     in noNeΠ (PE.subst Neutral (PE.sym eA) neA))
                      (λ e → let _ , _ , eB , _ = cast-PE-injectivity e
                                 _ , neB , _ = ne~↓! x₆
                             in noNeℕ (PE.subst Neutral eB neB))
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (cast-Πℕ x₅ x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in ℕ≢ne! neR (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (cast-ℕΠ x₅ x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in IE.Π≢ne neR (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (cast-ΠΠ%! x₅ x₆ x₇ x₈ x₉) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in IE.Π≢ne neR (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (cast-ΠΠ!% x₅ x₆ x₇ x₈ x₉) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in IE.Π≢ne neR (sym (cast-cast-≡ X)))

  dec~↑! Γ≡Δ (cast-cong A B (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (cast-refl C~D (ne-ins ⊢u x₁' x₂' ([~] A₁' D₁' whnfB' k~l')) ⊢e'') (leS size) =
    let neA = proj₁ (proj₂ (ne~↓! A))
        neB = proj₁ (proj₂ (ne~↓! (sym~↓!U B)))
        _ , neC , neD = ne~↓! C~D
        _ , ⊢A , _ = syntacticEqTerm (soundness~↓! A)
        _ , _ , ⊢B = syntacticEqTerm (soundness~↓! B)
        _ , ⊢C , ⊢D = syntacticEqTerm (soundness~↓! C~D)
    in cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u ⊢e ⊢e''
                     (dec~↓! Γ≡Δ A C~D (<<-trans (<=-help-id-cong-c'' {a = size~↓! A} {b = size~↓! C~D}) size))
                     (dec~↓! (symConEq Γ≡Δ) (sym~↓!U C~D) (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.trans (PE.cong₂ _+_ (sym~↓!Usize C~D) (sym~↓!Usize B))
                                                                      (+-sym (size~↓! C~D) (size~↓! B))) )
                                                                      (<=-help-b'b-c'' {a = size~↓! A} {b = size~↓! C~D})) size) )
                     (dec~↓! (reflConEq (wfTerm ⊢e)) A (sym~↓!U B) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! A)) (sym~↓!Usize B)))
                                                                              (<=-help-id-cong-ab' {a = size~↓! A} {b = 0} {c' = size~↓! C~D})) size))
                     (yes (_ , _ , C~D))
                     (λ (_ , _ , A~C) →
                       decConv↓Term Γ≡Δ (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) (convert'~ Γ≡Δ A C~D A~C (ne-ins ⊢u x₁' x₂' ([~] A₁' D₁' whnfB' k~l')))
                          (<<-trans (PE.subst ( λ X →  (sizeConv↓Term (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) + X) <= _)
                                    (PE.sym (convert'~size Γ≡Δ A C~D A~C (ne-ins ⊢u x₁' x₂' ([~] A₁' D₁' whnfB' k~l'))))
                                              (<=-help-b''-c'' {a = size~↓! A} {b = size~↓! C~D})) 
                                    size))
                     (dec~↑! Γ≡Δ k~l (cast-refl C~D (ne-ins ⊢u x₁' x₂' ([~] A₁' D₁' whnfB' k~l')) ⊢e'')
                                     (<<-trans (<=-help-b''x {a = size~↓! A}) size))
                     (dec~↑! Γ≡Δ (cast-cong A B (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') k~l'
                                 (<<-trans (<=-help-ab'b''c'' {a = size~↓! A} {b = size~↓! C~D}) size))

  dec~↑! Γ≡Δ (cast-cong A B _ _ _) (castℕ-refl _ _) (leS size) =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in ℕ≢ne! neR (sym (cast-cast-≡ X))) 

  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (castℕ-refl' ([~] A' D' whnfB' k~l') ⊢e'') (leS size) =
    no (λ (_ , _ , X) → let _ , ⊢t , _ = syntacticEqTerm (soundness~↑! k~l')
                            _ , _ , neB = ne~↓! B
                        in ℕ≢ne! neB (sym (cast-t-≡ (stabilityTerm (symConEq Γ≡Δ) (conv ⊢t (subset* D'))) X))) 

  dec~↑! Γ≡Δ (cast-cong A B X ⊢e ⊢e') (cast-refl' A~A (ne-ins x' x₁' x₂' ([~] A₁' D₁' whnfB' k~l)) ⊢e'') (leS size) =
    let X = cast-cong A B X ⊢e ⊢e'
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size)

  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (cast-neℕ x₂' x₃' x₄' x₅') (leS size) =
        no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                            in ℕ≢ne! neR (sym (cast-cast-≡ X))) 

  dec~↑! Γ≡Δ (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (cast-neΠ x₂' x'₃ x₄' x'₅ x₆') (leS size) =
        no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                            in IE.Π≢ne neR (sym (cast-cast-≡ X))) 

  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (var-refl x₄ x₅) _ = castℕ-refl'-dec~ x (λ {_ _ ()}) (λ {_ ()}) (λ {()})
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (app-cong x₄ x₅) _ = castℕ-refl'-dec~ x (λ {_ _ ()}) (λ {_ ()}) (λ {()})
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (natrec-cong x₄ x₅ x₆ x₇) _ = castℕ-refl'-dec~ x (λ {_ _ ()}) (λ {_ ()}) (λ {()})
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (Emptyrec-cong x₄ x₅) _ = castℕ-refl'-dec~ x (λ {_ _ ()}) (λ {_ ()}) (λ {()})
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (Id-cong x₄ x₅ x₆) _ = castℕ-refl'-dec~ x (λ {_ _ ()}) (λ {_ ()}) (λ {()})
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (Id-ℕ x₄ x₅) _ = castℕ-refl'-dec~ x (λ {_ _ ()}) (λ {_ ()}) (λ {()})
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (Id-ℕ0 x₄) _ = castℕ-refl'-dec~ x (λ {_ _ ()}) (λ {_ ()}) (λ {()})
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (Id-ℕS x₄ x₅) _ = castℕ-refl'-dec~ x (λ {_ _ ()}) (λ {_ ()}) (λ {()})
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (Id-U x₄ x₅) _ = castℕ-refl'-dec~ x (λ {_ _ ()}) (λ {_ ()}) (λ {()})
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (Id-Uℕ x₄) _ = castℕ-refl'-dec~ x (λ {_ _ ()}) (λ {_ ()}) (λ {()})
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (Id-UΠ x₄ x₅) _ = castℕ-refl'-dec~ x (λ {_ _ ()}) (λ {_ ()}) (λ {()})
  dec~↑! Γ≡Δ (cast-ℕ x₄ x₅ x₆ x₇) (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (leS size) =
    let X = cast-ℕ x₄ x₅ x₆ x₇
    in cast-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) A) (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B))
                       (stabilityConv↓Term (symConEq Γ≡Δ) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)))
                       (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                       (dec~↓! Γ≡Δ (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B)) A (<<-trans (<=-trans (<=-trans (≡-to-<= (PE.trans (PE.cong (λ X → X + size~↓! A) (sym~↓!Usize _))
                                                                                                (+-sym (size~↓! (stability~↓! (symConEq Γ≡Δ) B)) (size~↓! A))))
                                                                                                (<=-cong-+ (le-refl (size~↓! A)) (≡-to-<= (stabilitySize~↓! _ B))))
                                                                   (<=-help-abrem {x = removeSuc (size~↑! X)}
                                                                                  {a = size~↓! A + size~↓! B} {b = 2 + size~↑! k~l}) ) size))
                       (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A + size~↓! B} {c = size~↑! k~l}) size))
                       (λ { neA neB e → let _ , eA , _ = cast-PE-injectivity e in noNeℕ (PE.subst Neutral (PE.sym eA) neA) })
                       (λ { e → let _ , _ , eB , _ = cast-PE-injectivity e
                                    _ , neB , _ = ne~↓! x₄
                              in noNeℕ (PE.subst Neutral eB neB) })
  dec~↑! Γ≡Δ (cast-ℕ B x₁ x₂ x₃) (cast-Πℕ x₄ x₅ x₆ x₇) _ =
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in ℕ≢ne! neR (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-ℕ B x₁ x₂ x₃) (cast-ℕΠ x₄ x₅ x₆ x₇) _ =
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in IE.Π≢ne neR (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-ℕ B x₁ x₂ x₃) (cast-ΠΠ%! x₄ x₅ x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in IE.Π≢ne neR (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-ℕ B x₁ x₂ x₃) (cast-ΠΠ!% x₄ x₅ x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in IE.Π≢ne neR (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) (cast-Π x₄ x₅ x₆ x₇ x₈) _ =
    castℕ-refl'-dec~ x
                    (λ neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                   in noNeΠ (PE.subst Neutral (PE.sym eA) neA))
                    (λ neA e → let _ , eA , _ = cast-PE-injectivity e in ℕ≢Π (PE.sym eA))
                    (λ e → let _ , _ , eB , _ = cast-PE-injectivity e
                               _ , neB , _ = ne~↓! x₅
                           in noNeℕ (PE.subst Neutral eB neB))

  dec~↑! Γ≡Δ (cast-ℕ x' x₁' x₂' x₃') (cast-refl A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (cast-ℕ x' x₁' x₂' x₃')
        _ , neA , neB = ne~↓! A~A
        _ , _ , eqU , A~A' = sym~↓! (symConEq Γ≡Δ) A~A
        _ , _ , ⊢B  = syntacticEqTerm (soundness~↓! A~A)
    in cast-refl'-dec neA neB (stabilityTerm (symConEq Γ≡Δ) ⊢B) (stabilityTerm (symConEq Γ≡Δ) x) (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                      (yes (_ , _ , A~A'))
                      (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size))
                      (λ { neA neB e → let _ , eA , _ = cast-PE-injectivity e in noNeℕ (PE.subst Neutral (PE.sym eA) neA) })
                      (λ { e → let _ , _ , eB , _ = cast-PE-injectivity e
                                   _ , neB , _ = ne~↓! x'
                               in noNeℕ (PE.subst Neutral eB neB) })
  dec~↑! Γ≡Δ (cast-ℕ x' x₁' x₂' x₃') (castℕ-refl ([~] A D whnfB k~l) ⊢e) (leS size) =
      let X = (cast-ℕ x' x₁' x₂' x₃')
      in castℕℕ-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) ([~] A D whnfB k~l))
                           (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                           (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size))
                           (λ { neA neB e → let _ , eA , _ = cast-PE-injectivity e in noNeℕ (PE.subst Neutral (PE.sym eA) neA) })
                           (λ { e → let _ , _ , eB , _ = cast-PE-injectivity e
                                        _ , neB , _ = ne~↓! x'
                                    in noNeℕ (PE.subst Neutral eB neB) })
  dec~↑! Γ≡Δ (cast-ℕ x' x₁' x₂' x₃') (cast-refl' A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (cast-ℕ x' x₁' x₂' x₃')
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size)
  dec~↑! Γ≡Δ (cast-ℕ x' x₁' x₂' x₃') (castℕ-refl' ([~] A D whnfB k~l) ⊢e) (leS size) =
    let X = (cast-ℕ x' x₁' x₂' x₃')
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size)
  dec~↑! Γ≡Δ (cast-ℕ x' x₁' x₂' x₃') (cast-neℕ x₂ x₃ x₄ x₅) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ  ;
                                                                                      (_ , _ , castℕ-refl' x x₁) → let _ , neℕ , _ = ne~↓! x₂ in noNeℕ neℕ })
  dec~↑! Γ≡Δ (cast-ℕ x' x₁' x₂' x₃') (cast-neΠ x₂ x₃ x₄ x₅ x₆) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })

{-
  dec~↑! Γ≡Δ (cast-ℕℕ x' x₁' x₂') (castℕ-refl x ⊢e) (leS size)
    with dec~↓! Γ≡Δ x' x (<<-trans (<=-help-ab1' {a = size~↓! x'}) size)
  ... | yes (_ , _ , p) = let _ , ⊢t , _  = syntacticEqTerm (soundness~↓! x')
                          in yes (_ , _ , cast-ℕℕ (~atℕ ⊢t (_ , _ , p)) x₁' (stabilityTerm (symConEq Γ≡Δ) ⊢e))
  ... | no ¬p = let _ , ⊢t , _  = syntacticEqTerm (soundness~↓! x')
                in no (λ (_ , _ , X) → let whnfcast , whnfcast' = ne~↑! X
                                           cast≡cast = soundness~↑! X
                                           _ , ⊢cast , ⊢cast' = syntacticEqTerm cast≡cast
                                           _ , _ , _ , _ , ⊢t , R≡R , eqR , _ = inversion-cast ⊢cast
                                           eqR , el = typeinfo-PE-injectivity eqR
                                           R≡R' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqR) R≡R
                                           cast≡cast' = PE.subst (λ X →  _ ⊢ _ ≡ _ ∷ _ ^ [ ! , X ]) el cast≡cast
                                           ⊢t' = PE.subst (λ X →  _ ⊢ _ ∷ _ ^ [ X , _ ]) (PE.sym eqR) ⊢t
                                           net = castℕInv whnfcast 
                                           neu = castℕInv whnfcast'
                                           _ , ⊢u , _ = syntacticEqTerm (soundness~↓! x)
                                       in ¬p (_ , _ , completeEqℕ net neu
                                                              (trans (sym (T.cast-refl (refl (ℕⱼ (wfTerm ⊢t))) x₁' ⊢t'))
                                                                (trans (conv cast≡cast' R≡R')
                                                                (T.cast-refl (refl (ℕⱼ (wfTerm ⊢t))) (stabilityTerm (symConEq Γ≡Δ) ⊢e) (stabilityTerm (symConEq Γ≡Δ) ⊢u))))))
                                                                -}

  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (var-refl x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (app-cong x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (natrec-cong x₅ x₆ x₇ x₈) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (Emptyrec-cong x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (Id-cong x₅ x₆ x₇) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (Id-ℕ x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (Id-ℕ0 x₅) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (Id-ℕS x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (Id-U x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (Id-Uℕ x₅) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (Id-UΠ x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (cast-Π x₅ x₆ x₇ x₈ x₉) (cast-cong A B (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e ⊢e') (leS size) =
    let X = cast-Π x₅ x₆ x₇ x₈ x₉
    in cast-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) A) (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B))
                       (stabilityConv↓Term (symConEq Γ≡Δ) (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)))
                       (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                       (dec~↓! Γ≡Δ (sym~↓!U (stability~↓! (symConEq Γ≡Δ) B)) A (<<-trans (<=-trans (<=-trans (≡-to-<= (PE.trans (PE.cong (λ X → X + size~↓! A) (sym~↓!Usize _))
                                                                                                (+-sym (size~↓! (stability~↓! (symConEq Γ≡Δ) B)) (size~↓! A))))
                                                                                                (<=-cong-+ (le-refl (size~↓! A)) (≡-to-<= (stabilitySize~↓! _ B))))
                                                                   (<=-help-abrem {x = removeSuc (size~↑! X)}
                                                                                  {a = size~↓! A + size~↓! B} {b = 2 + size~↑! k~l}) ) size))
                       (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A + size~↓! B} {c = size~↑! k~l}) size))
                      (λ neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                     in noNeΠ (PE.subst Neutral (PE.sym eA) neA))
                      (λ e → let _ , _ , eB , _ = cast-PE-injectivity e
                                 _ , neB , _ = ne~↓! x₆
                             in noNeℕ (PE.subst Neutral eB neB))
  dec~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) (cast-ℕ x₅ x₆ x₇ x₈) _ = 
      castℕ-refl-dec~ (stability~↓! (symConEq Γ≡Δ) x₅) 
                      (λ neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                     in noNeΠ (PE.subst Neutral (PE.sym eA) neA))
                      (λ neA e → let _ , eA , _ = cast-PE-injectivity e in ℕ≢Π (PE.sym eA))
                      (λ e → let _ , _ , eB , _ = cast-PE-injectivity e
                                 _ , neB , _ = ne~↓! x₁
                             in noNeℕ (PE.subst Neutral eB neB))
  dec~↑! Γ≡Δ (cast-Π x B x₂ x₃ x₄) (cast-Πℕ x₅ x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in ℕ≢ne! neR (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-Π x B x₂ x₃ x₄) (cast-ℕΠ x₅ x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in IE.Π≢ne neR (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-Π x B x₂ x₃ x₄) (cast-ΠΠ%! x₅ x₆ x₇ x₈ x₉) _ =
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in IE.Π≢ne neR (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-Π x B x₂ x₃ x₄) (cast-ΠΠ!% x₅ x₆ x₇ x₈ x₉) _ =
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in IE.Π≢ne neR (sym (cast-cast-≡ X)))

  dec~↑! Γ≡Δ (cast-Π x' B x₁' x₂' x₃') (cast-refl  A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = cast-Π x' B x₁' x₂' x₃'
        _ , neA , neB = ne~↓! A~A
        _ , _ , eqU , A~A' = sym~↓! (symConEq Γ≡Δ) A~A
        _ , _ , ⊢B  = syntacticEqTerm (soundness~↓! A~A)
    in cast-refl'-dec neA neB (stabilityTerm (symConEq Γ≡Δ) ⊢B) (stabilityTerm (symConEq Γ≡Δ) x) (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                      (yes (_ , _ , A~A'))
                      (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size))
                      (λ neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                     in noNeΠ (PE.subst Neutral (PE.sym eA) neA))
                      (λ e → let _ , _ , eB , _ = cast-PE-injectivity e
                                 _ , neB , _ = ne~↓! B
                             in noNeℕ (PE.subst Neutral eB neB))
  
  dec~↑! Γ≡Δ (cast-Π x' B x₁' x₂' x₃') (cast-refl' A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (cast-Π x' B x₁' x₂' x₃')
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size)
  dec~↑! Γ≡Δ (cast-Π x B x₂ x₃ x₄) (castℕ-refl x₅ x₆) _ =
      no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                          in ℕ≢ne! neR (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-Π x' B x₁' x₂' x₃') (castℕ-refl' ([~] A D whnfB k~l) ⊢e) (leS size) =
    let X = (cast-Π x' B x₁' x₂' x₃')
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size)
  dec~↑! Γ≡Δ (cast-Π x' B x₁' x₂' x₃') (cast-neℕ x₂ x₃ x₄ x₅) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ  ;
                                                                                      (_ , _ , castℕ-refl' x x₁) → let _ , neℕ , _ = ne~↓! x₂ in noNeℕ neℕ })
  dec~↑! Γ≡Δ (cast-Π x' B x₁' x₂' x₃') (cast-neΠ x₂ x₃ x₄ x₅ x₆) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })

  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (var-refl x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (app-cong x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (natrec-cong x₅ x₆ x₇ x₈) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (Emptyrec-cong x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (Id-cong x₅ x₆ x₇) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (Id-ℕ x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (Id-ℕ0 x₅) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (Id-ℕS x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (Id-U x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (Id-Uℕ x₅) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (Id-UΠ x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-cong A B x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B in ℕ≢ne! neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-ℕ B x₅ x₆ x₇) _ =
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B in ℕ≢ne! neR (cast-cast-≡ X))                            
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-Π x₄ B x₆ x₇ x₈) _ = 
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in ℕ≢ne! neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-ℕΠ x₄ x₅ x₆ x₇) _ =
    no (λ (_ , _ , X) → ℕ≢Π! (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-ΠΠ%! x₄ x₅ x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → ℕ≢Π! (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-ΠΠ!% x₄ x₅ x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → ℕ≢Π! (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-refl B x₆ x₇) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B in ℕ≢ne! neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-Πℕ x₃ x₄ x₅ x₆) (castℕ-refl ([~] A D whnfB k~l) ⊢e) (leS size) = 
    let X = cast-Πℕ x₃ x₄ x₅ x₆
    in castℕℕ-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) ([~] A D whnfB k~l))
                         (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                         (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size))
                         (λ { neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                          in noNeΠ (PE.subst Neutral (PE.sym eA) neA)})
                         (λ { () })
  dec~↑! Γ≡Δ (cast-Πℕ x' x₁' x₂' x₃') (cast-refl' A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (cast-Πℕ x' x₁' x₂' x₃')
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size)
  dec~↑! Γ≡Δ (cast-Πℕ x' x₁' x₂' x₃') (castℕ-refl' ([~] A D whnfB k~l) ⊢e) (leS size) =
    let X = (cast-Πℕ x' x₁' x₂' x₃')
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size)
  dec~↑! Γ≡Δ (cast-Πℕ x' x₁' x₂' x₃') (cast-neℕ x₂ x₃ x₄ x₅) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ  ;
                                                                                      (_ , _ , castℕ-refl' x x₁) → let _ , neℕ , _ = ne~↓! x₂ in noNeℕ neℕ })
  dec~↑! Γ≡Δ (cast-Πℕ x' x₁' x₂' x₃') (cast-neΠ x₂ x₃ x₄ x₅ x₆) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })

  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (var-refl x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ }) 
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (app-cong x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ }) 
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (natrec-cong x₅ x₆ x₇ x₈) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ }) 
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (Emptyrec-cong x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ }) 
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (Id-cong x₅ x₆ x₇) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ }) 
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (Id-ℕ x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ }) 
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (Id-ℕ0 x₅) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ }) 
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (Id-ℕS x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ }) 
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (Id-U x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ }) 
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (Id-Uℕ x₅) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ }) 
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (Id-UΠ x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ })
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-cong A B x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-ℕ B x₅ x₆ x₇) _ =
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-ℕΠ x₃ x₄ x₅ x₆) (castℕ-refl ([~] A D whnfB k~l) ⊢e) (leS size) = 
    let X = cast-ℕΠ x₃ x₄ x₅ x₆
    in castℕℕ-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) ([~] A D whnfB k~l))
                         (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                         (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size))
                         (λ { neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                          in noNeℕ (PE.subst Neutral (PE.sym eA) neA)})
                         (λ { () })
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-Π x₄ B x₆ x₇ x₈) _ = 
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-Πℕ x₄ x₅ x₆ x₇) _ =
    no (λ (_ , _ , X) → ℕ≢Π! (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-ΠΠ%! x₄ x₅ x₆ x₇ x₈) _ =
    no (λ { (_ , _ , cast-cong () x₁ x₂ x₃ x₄) ;
            (_ , _ , cast-refl () x₁ x₂) ;
            (_ , _ , cast-refl' () x₁ x₂) ;
            (_ , _ , cast-neΠ x () x₂ x₃ x₄)})
  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-ΠΠ!% x₄ x₅ x₆ x₇ x₈) _ =
    no (λ { (_ , _ , cast-cong () x₁ x₂ x₃ x₄) ;
            (_ , _ , cast-refl () x₁ x₂) ;
            (_ , _ , cast-refl' () x₁ x₂) ;
            (_ , _ , cast-neΠ x () x₂ x₃ x₄)})

  dec~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-refl B x₆ x₇) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))

  dec~↑! Γ≡Δ (cast-ℕΠ x' x₁' x₂' x₃') (cast-refl' A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (cast-ℕΠ x' x₁' x₂' x₃')
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size)
  dec~↑! Γ≡Δ (cast-ℕΠ x' x₁' x₂' x₃') (castℕ-refl' ([~] A D whnfB k~l) ⊢e) (leS size) =
    let X = (cast-ℕΠ x' x₁' x₂' x₃')
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size)
  dec~↑! Γ≡Δ (cast-ℕΠ x' x₁' x₂' x₃') (cast-neℕ x₂ x₃ x₄ x₅) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ  ;
                                                                                      (_ , _ , castℕ-refl' x x₁) → let _ , neℕ , _ = ne~↓! x₂ in noNeℕ neℕ })
  dec~↑! Γ≡Δ (cast-ℕΠ x' x₁' x₂' x₃') (cast-neΠ x₂ x₃ x₄ x₅ x₆) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })


  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (var-refl x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (app-cong x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (natrec-cong x₅ x₆ x₇ x₈) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (Emptyrec-cong x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (Id-cong x₅ x₆ x₇) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (Id-ℕ x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (Id-ℕ0 x₅) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (Id-ℕS x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (Id-U x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (Id-Uℕ x₅) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (Id-UΠ x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-cong A B x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-ℕ B x₅ x₆ x₇) _ =
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (castℕ-refl ([~] A D whnfB k~l) ⊢e) (leS size) = 
    let X = cast-ΠΠ%! x x₁ x₂ x₃ x₄
    in castℕℕ-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) ([~] A D whnfB k~l))
                         (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                         (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size))
                         (λ { neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                          in noNeΠ (PE.subst Neutral (PE.sym eA) neA)})
                         (λ { () })                         
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-Π A B x₆ x₇ x₈) _ = 
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-Πℕ A x₅ x₆ x₇) _ =
    no (λ (_ , _ , X) → ℕ≢Π! (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-ℕΠ x₅ x₆ x₇ x₈) _ =
    no (λ { (_ , _ , cast-cong () x₁ x₂ x₃ x₄) ;
            (_ , _ , cast-refl () x₁ x₂) ;
            (_ , _ , cast-refl' () x₁ x₂) ;
            (_ , _ , cast-neΠ x () x₂ x₃ x₄)})
  dec~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-ΠΠ!% A x₅ x₆ x₇ x₈) _ =
    no (λ { (_ , _ , cast-cong () x₁ x₂ x₃ x₄) ;
            (_ , _ , cast-refl () x₁ x₂) ;
            (_ , _ , cast-refl' () x₁ x₂)})
  dec~↑! Γ≡Δ (cast-ΠΠ%! x' x₁' x₂' x₃' x₄') (cast-refl B x₆ x₇) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-ΠΠ%! x' x₁' x₂' x₃' x₄') (cast-refl' A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (cast-ΠΠ%! x' x₁' x₂' x₃' x₄')
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size)
  dec~↑! Γ≡Δ (cast-ΠΠ%! x' x₁' x₂' x₃' x₄') (castℕ-refl' ([~] A D whnfB k~l) ⊢e) (leS size) =
    let X = (cast-ΠΠ%! x' x₁' x₂' x₃' x₄')
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size)
  dec~↑! Γ≡Δ (cast-ΠΠ%! x' x₁' x₂' x₃' x₄') (cast-neℕ x₂ x₃ x₄ x₅) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ  ;
                                                                                      (_ , _ , castℕ-refl' x x₁) → let _ , neℕ , _ = ne~↓! x₂ in noNeℕ neℕ })
  dec~↑! Γ≡Δ (cast-ΠΠ%! x' x₁' x₂' x₃' x₄') (cast-neΠ x₂ x₃ x₄ x₅ x₆) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })

  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (var-refl x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (app-cong x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (natrec-cong x₅ x₆ x₇ x₈) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (Emptyrec-cong x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (Id-cong x₅ x₆ x₇) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (Id-ℕ x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (Id-ℕ0 x₅) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (Id-ℕS x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (Id-U x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (Id-Uℕ x₅) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ }) 
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (Id-UΠ x₅ x₆) _ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ })
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-cong A B x₆ x₇ x₈) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-ℕ B x₅ x₆ x₇) _ =
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (castℕ-refl ([~] A D whnfB k~l) ⊢e) (leS size) = 
    let X = cast-ΠΠ!% x x₁ x₂ x₃ x₄
    in castℕℕ-refl'-dec~ (stability~↓! (symConEq Γ≡Δ) ([~] A D whnfB k~l))
                         (stabilityTerm (symConEq Γ≡Δ) ⊢e)
                         (dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size))
                         (λ { neA neB e → let _ , eA , _ = cast-PE-injectivity e
                                          in noNeΠ (PE.subst Neutral (PE.sym eA) neA)})
                         (λ { () })
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-Π A B x₆ x₇ x₈) _ = 
    no (λ (_ , _ , X) → let _ , neR , _ = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-Πℕ A x₅ x₆ x₇) _ =
    no (λ (_ , _ , X) → ℕ≢Π! (sym (cast-cast-≡ X)))
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-ℕΠ x₅ x₆ x₇ x₈) _ =
    no (λ { (_ , _ , cast-cong () x₁ x₂ x₃ x₄) ;
            (_ , _ , cast-refl () x₁ x₂) ;
            (_ , _ , cast-refl' () x₁ x₂) ;
            (_ , _ , cast-neΠ x () x₂ x₃ x₄)})
  dec~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-ΠΠ%! A x₅ x₆ x₇ x₈) _ =
    no (λ { (_ , _ , cast-cong () x₁ x₂ x₃ x₄) ;
            (_ , _ , cast-refl () x₁ x₂) ;
            (_ , _ , cast-refl' () x₁ x₂)})
  dec~↑! Γ≡Δ (cast-ΠΠ!% x' x₁' x₂' x₃' x₄') (cast-refl B x₆ x₇) _ =
    no (λ (_ , _ , X) → let _ , _ , neR = ne~↓! B
                        in IE.Π≢ne neR (cast-cast-≡ X))
  dec~↑! Γ≡Δ (cast-ΠΠ!% x' x₁' x₂' x₃' x₄') (cast-refl' A~A (ne-ins x x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (leS size) =
    let X = (cast-ΠΠ!% x' x₁' x₂' x₃' x₄')
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-abc {a = removeSuc (size~↑! X)} {b = size~↓! A~A} {c = size~↑! k~l}) size)
  dec~↑! Γ≡Δ (cast-ΠΠ!% x' x₁' x₂' x₃' x₄') (castℕ-refl' ([~] A D whnfB k~l) ⊢e) (leS size) =
    let X = (cast-ΠΠ!% x' x₁' x₂' x₃' x₄')
    in dec~↑! Γ≡Δ X k~l (<<-trans (<=-help-1-2 {a = removeSuc (size~↑! X)}) size)
  dec~↑! Γ≡Δ (cast-ΠΠ!% x' x₁' x₂' x₃' x₄') (cast-neℕ x₂ x₃ x₄ x₅) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neℕ , _ = ne~↓! x in noNeℕ neℕ  ;
                                                                                      (_ , _ , castℕ-refl' x x₁) → let _ , neℕ , _ = ne~↓! x₂ in noNeℕ neℕ })
  dec~↑! Γ≡Δ (cast-ΠΠ!% x' x₁' x₂' x₃' x₄') (cast-neΠ x₂ x₃ x₄ x₅ x₆) (leS size) = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neΠ , _ = ne~↓! x in noNeΠ neΠ  })
-}

  dec~↑! Γ≡Δ (cast-refl A~B (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) (cast-cong C D (ne-ins ⊢u x₁' x₂' ([~] A₁' D₁' whnfB' k~l'))  ⊢e' ⊢e'') (leS size) =
    let neC = proj₁ (proj₂ (ne~↓! C))
        neD = proj₁ (proj₂ (ne~↓! (sym~↓!U D)))
        _ , neA , neB = ne~↓! A~B
        _ , ⊢C , _ = syntacticEqTerm (soundness~↓! C)
        _ , _ , ⊢D = syntacticEqTerm (soundness~↓! D)
        _ , ⊢A , ⊢B = syntacticEqTerm (soundness~↓! A~B)
    in cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u ⊢e ⊢e'
                     (dec~↓! Γ≡Δ A~B C (<<-trans (<=-help-ab-c'' {a = size~↓! A~B} {b = size~↓! C}) size))
                     (dec~↓! (symConEq Γ≡Δ) (sym~↓!U D) (sym~↓!U A~B) (<<-trans (<=-trans (≡-to-<= (PE.trans (PE.cong₂ _+_ (sym~↓!Usize D) (sym~↓!Usize A~B))
                                                                      (+-sym (size~↓! D) (size~↓! A~B))) )
                                                                      (<=-help-ac'-c'' {a = size~↓! A~B} {b = size~↓! C})) size) )
                     (yes (_ , _ , A~B))
                     (dec~↓! (reflConEq (wfTerm ⊢e')) C (sym~↓!U D) (<<-trans (<=-trans (≡-to-<= (PE.cong (_+_ (size~↓! C)) (sym~↓!Usize D)))
                                                                              (<=-help-bc'-c'' {a = size~↓! A~B} {b = size~↓! C})) size))
                     (λ (_ , _ , A~C) →
                       decConv↓Term Γ≡Δ (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) (convert'~ Γ≡Δ A~B C A~C (ne-ins ⊢u x₁' x₂' ([~] A₁' D₁' whnfB' k~l')))
                          (<<-trans (PE.subst ( λ X →  (sizeConv↓Term (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) + X) <= _)
                                    (PE.sym (convert'~size Γ≡Δ A~B C A~C (ne-ins ⊢u x₁' x₂' ([~] A₁' D₁' whnfB' k~l'))))
                                              (<=-help-b'c'' {a = size~↓! A~B} {b = size~↓! C})) 
                                    size))
                     (dec~↑! Γ≡Δ k~l (cast-cong C D (ne-ins ⊢u x₁' x₂' ([~] A₁' D₁' whnfB' k~l'))  ⊢e' ⊢e'')
                                     (<<-trans (<=-help-b''x {a = 0} {b = size~↓! A~B}) size))
                     (dec~↑! Γ≡Δ (cast-refl A~B (ne-ins ⊢t x₁ x₂ ([~] A₁ D₁ whnfB k~l)) ⊢e) k~l'
                                 (<<-trans (<=-help-ab'c'' {a = size~↓! A~B} {b = size~↓! C}) size))


  dec~↑! Γ≡Δ X Y = {!!}

{-
  dec~↑! Γ≡Δ (cast-refl x x₁ x₂) Y = {!!}
  dec~↑! Γ≡Δ (castℕ-refl x x₁) Y = {!!}
  dec~↑! Γ≡Δ (cast-refl' x x₁ x₂) Y = {!!}
  dec~↑! Γ≡Δ (castℕ-refl' x x₁) Y = {!!}
  dec~↑! Γ≡Δ (cast-neℕ x x₁ x₂ x₃) Y = {!!}
  dec~↑! Γ≡Δ (cast-neΠ x x₁ x₂ x₃ x₄) Y = {!!}
-}

  -- Decidability of algorithmic equality of neutrals with types in WHNF.
  dec~↓! : ∀ {n k k' l l' R T Γ Δ lR lT}
        → ⊢ Γ ≡ Δ
        → (e : Γ ⊢ k ~ k' ↓! R ^ lR)
        → (e' : Δ ⊢ l ~ l' ↓! T ^ lT)
        → (size~↓! e + size~↓! e') << n
        → Dec (∃ λ A → ∃ λ lA → Γ ⊢ k ~ l ↓! A ^ lA)

{-
  dec~↓! {n = 0} _ _ _ ()
  dec~↓! Γ≡Δ ([~] A D whnfB k~l) ([~] A₁ D₁ whnfB₁ k~l₁) (leS size)
        with dec~↑! Γ≡Δ k~l k~l₁ (<<-trans <=-help-ab1' size)
  ... | yes (B , lB , k~l₂) =
    let ⊢B , _ , _ = syntacticEqTerm (soundness~↑! k~l₂)
        C , whnfC , D′ = whNorm ⊢B
    in  yes (C , _ , [~] B (red D′) whnfC k~l₂)
  ... | no ¬p =
    no (λ { (A₂ , _ , [~] A₃ D₂ whnfB₂ k~l₂) → ¬p (A₃ , _ , k~l₂) })
-}
  dec~↓! = {!!}

  -- Decidability of algorithmic equality of types.
  decConv↑ : ∀ {n A A' B B' r Γ Δ}
           → ⊢ Γ ≡ Δ
           → (e : Γ ⊢ A [conv↑] A' ^ r)
           → (e' : Δ ⊢ B [conv↑] B' ^ r)
           → (sizeConv↑ e + sizeConv↑ e') << n           
           → Dec (Γ ⊢ A [conv↑] B ^ r)

{-
  decConv↑ {n = 0} _ _ _ ()
  decConv↑ Γ≡Δ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′)
               ([↑] A″ B″ D₁ D″ whnfA″ whnfB″ A′<>B″) (leS size)
           with decConv↓ Γ≡Δ A′<>B′ A′<>B″ (<=-trans (<=-help-ab1' {a = 1+ (sizeConv↓ A′<>B′)}) size)
  ... | yes p =
    yes ([↑] A′ A″ D (stabilityRed* (symConEq Γ≡Δ) D₁) whnfA′ whnfA″ p)
  decConv↑ {r = r} Γ≡Δ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′)
               ([↑] A″ B″ D₁ D″ whnfA″ whnfB″ A′<>B″) (leS size) | no ¬p =
    no (λ { ([↑] A‴ B‴ D₂ D‴ whnfA‴ whnfB‴ A′<>B‴) →
        let A‴≡B′  = whrDet* (D₂ , whnfA‴) (D , whnfA′)
            B‴≡B″ = whrDet* (D‴ , whnfB‴)
                                (stabilityRed* (symConEq Γ≡Δ) D₁ , whnfA″)
        in  ¬p (PE.subst₂ (λ x y → _ ⊢ x [conv↓] y ^ r) A‴≡B′ B‴≡B″ A′<>B‴) })
-}
  decConv↑ = {!!}
  
  decConv↓ : ∀ {n A A' B B' r Γ Δ}
           → ⊢ Γ ≡ Δ
           → (e : Γ ⊢ A [conv↓] A' ^ r)
           → (e' : Δ ⊢ B [conv↓] B' ^ r)
           → (sizeConv↓ e + sizeConv↓ e') << n
           → Dec (Γ ⊢ A [conv↓] B ^ r)

  decConv↓ {n = 0} _ _ _ ()
  decConv↓ Γ≡Δ (U-refl {r = r} x x₁) (U-refl {r = r′} x₂ x₃) (leS size) with dec-relevance r r′
  ... | yes p = yes (U-refl p x₁)
  ... | no ¬p = no λ p → ¬p (proj₁ (Uinjectivity (soundnessConv↓ p)))
  decConv↓ Γ≡Δ (univ x) (univ x₁) (leS size) with decConv↓Term Γ≡Δ x x₁ (<=-trans (<=-help-ab1' {a = sizeConv↓ (univ x)}) size)
  ... | yes p = yes (univ p)
  ... | no ¬p = no (λ { (univ x) → ¬p x })

  -- decConv↓ = {!!}


  -- Decidability of algorithmic equality of terms.

  decConv↑Term : ∀ {n t t' u u' A Γ Δ l}
               → ⊢ Γ ≡ Δ
               → (e : Γ ⊢ t [conv↑] t' ∷ A ^ l)
               → (e' : Δ ⊢ u [conv↑] u' ∷ A ^ l)
               → (sizeConv↑Term e + sizeConv↑Term e') << n
               → Dec (Γ ⊢ t [conv↑] u ∷ A ^ l)

  decConv↑Term = {!!}
{-
  decConv↑Term {n = 0} _ _ _ ()
  decConv↑Term Γ≡Δ ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
                   ([↑]ₜ B₁ t″ u″ D₁ d₁ d″ whnfB₁ whnft″ whnfu″ t<>u₁) (leS size)
               rewrite whrDet* (D , whnfB) (stabilityRed* (symConEq Γ≡Δ) D₁ , whnfB₁)
               with decConv↓Term Γ≡Δ t<>u t<>u₁ (<=-trans (<=-help-ab1' {a = 1+ (sizeConv↓Term t<>u)}) size)
  ... | yes p =
    let Δ≡Γ = symConEq Γ≡Δ
    in  yes ([↑]ₜ B₁ t′ t″ (stabilityRed* Δ≡Γ D₁)
                  d (stabilityRed*Term Δ≡Γ d₁) whnfB₁ whnft′ whnft″ p)
  ... | no ¬p =
    no (λ { ([↑]ₜ B₂ t‴ u‴ D₂ d₂ d‴ whnfB₂ whnft‴ whnfu‴ t<>u₂) →
        let B₂≡B₁ = whrDet* (D₂ , whnfB₂)
                             (stabilityRed* (symConEq Γ≡Δ) D₁ , whnfB₁)
            t‴≡u′ = whrDet*Term (d₂ , whnft‴)
                              (PE.subst (λ x → _ ⊢ _ ⇒* _ ∷ x ^ _) (PE.sym B₂≡B₁) d
                              , whnft′)
            u‴≡u″ = whrDet*Term (d‴ , whnfu‴)
                               (PE.subst (λ x → _ ⊢ _ ⇒* _ ∷ x ^ _)
                                         (PE.sym B₂≡B₁)
                                         (stabilityRed*Term (symConEq Γ≡Δ) d₁)
                               , whnft″)
        in  ¬p (PE.subst₃ (λ x y z → _ ⊢ x [conv↓] y ∷ z ^ _)
                          t‴≡u′ u‴≡u″ B₂≡B₁ t<>u₂) })
-}

  -- Decidability of algorithmic equality of terms in WHNF.
  decConv↓Term : ∀ {n t t' u u' A Γ Δ l}
               → ⊢ Γ ≡ Δ
               → (e : Γ ⊢ t [conv↓] t' ∷ A ^ l)
               → (e' : Δ ⊢ u [conv↓] u' ∷ A ^ l)
               → (sizeConv↓Term e + sizeConv↓Term e') << n
               → Dec (Γ ⊢ t [conv↓] u ∷ A ^ l)

{-
  decConv↓Term {n = 0} _ _ _ ()
  decConv↓Term Γ≡Δ (U-refl {r = r} _ x) (U-refl {r = r′} _ x₁) (leS size)
    with dec-relevance r r′
  ... | yes p = yes (U-refl p x)
  ... | no ¬p = no λ p → ¬p (proj₁ (Uinjectivity (univ (soundnessConv↓Term p))))

  decConv↓Term Γ≡Δ (ne K) (ne K₁) (leS size)
    with dec~↓! Γ≡Δ K K₁ (<=-trans (<=-help-ab1' {a = 1+ (size~↓! K)}) size) 
  ... | yes (A , lA , K~K₁) = yes (ne (~atU' K (A , lA , K~K₁)))
  ... | no ¬p = no (λ { x → ¬p (Univ _ _ , _ , decConv↓Term-U-ins x K) })

  decConv↓Term Γ≡Δ (ℕ-refl x) (ℕ-refl x₁) _ = yes (ℕ-refl x)

  decConv↓Term Γ≡Δ (Empty-refl x₁) (Empty-refl x₃) _ = yes (Empty-refl x₁)

  decConv↓Term Γ≡Δ (Π-cong {rF = rF} {lF = lF} {lG = lG} {lΠ = l} l≡ PE.refl PE.refl PE.refl lF< lG< ⊢F F G)
    (Π-cong {rF = rH} {lF = lH} {lG = lE} {lΠ = l′} l′≡ PE.refl PE.refl PE.refl _ _ ⊢H H E) (leS size)
    with dec-relevance rF rH | dec-level lF lH | dec-level lG lE | dec-level l l′
  ... | yes PE.refl | yes PE.refl | yes PE.refl | no ¬p = no λ { (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) → ¬p PE.refl }
  ... | yes PE.refl | yes PE.refl | no ¬p | _ = no λ { (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) → ¬p x₃ }
  ... | yes PE.refl | no ¬p | _ | _ = no λ { (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) → ¬p x₂ }
  ... | no ¬p | _ | _ | _ = no λ { (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) → ¬p x₁ }
  ... | yes PE.refl | yes PE.refl | yes PE.refl | yes PE.refl
    with decConv↑Term Γ≡Δ F H (<=-trans (leS (<=-help-ab' {a = sizeConv↑Term F})) size)
  ... | no ¬p = no λ { (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) → ¬p x₇ }
  ... | yes pFH
    with decConv↑Term (Γ≡Δ ∙ univ (soundnessConv↑Term pFH)) G E (<=-trans (leS (<=-help-ab'' {a = sizeConv↑Term F} {c = sizeConv↑Term H})) size)
  ... | no ¬p = no λ { (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) → ¬p x₈ }
  ... | yes pGE = yes (Π-cong l≡ PE.refl PE.refl PE.refl lF< lG< ⊢F pFH pGE)

  decConv↓Term Γ≡Δ (∃-cong ⊢F F G) (∃-cong ⊢H H E) (leS size)
    with decConv↑Term Γ≡Δ F H (<=-trans (leS (<=-help-ab' {a = sizeConv↑Term F})) size)
  ... | no ¬p = no λ { (∃-cong x₁ x₂ x₃) → ¬p x₂ }
  ... | yes pFH
    with decConv↑Term (Γ≡Δ ∙ univ (soundnessConv↑Term pFH)) G E (<=-trans (leS (<=-help-ab'' {a = sizeConv↑Term F} {c = sizeConv↑Term H})) size)
  ... | no ¬p = no λ { (∃-cong x₁ x₂ x₃) → ¬p x₃ }
  ... | yes pGE = yes (∃-cong ⊢F pFH pGE)

  decConv↓Term Γ≡Δ (ℕ-ins K) (ℕ-ins K₁) (leS size)
    with dec~↓! Γ≡Δ K K₁ (<=-trans (<=-help-ab1' {a = 1+ (size~↓! K)}) size)
  ... | yes p = yes (ℕ-ins (let _ , ⊢k , _ = syntacticEqTerm (soundness~↓! K) in ~atℕ ⊢k p))
  ... | no ¬p = no λ x → ¬p (ℕ , _ , decConv↓Term-ℕ-ins x K)

  decConv↓Term Γ≡Δ (ne-ins ⊢k _ neA k) (ne-ins ⊢k₁ _ _ k₁) (leS size)
    with dec~↓! Γ≡Δ k k₁ (<=-trans (<=-help-ab1' {a = 1+ (size~↓! k)}) size)
  ... | yes (B , lB , k~k₁) =
    let whnfB , neK , neK₁ = ne~↓! k~k₁
        _ , ⊢k∷B , _ = syntacticEqTerm (soundness~↓! k~k₁)
        l≡l , ⊢A≡B = neTypeEq neK ⊢k∷B ⊢k
    in yes (ne-ins ⊢k (stabilityTerm (symConEq Γ≡Δ) ⊢k₁) neA (PE.subst (λ X → _ ⊢ _ ~ _ ↓! _ ^ X) l≡l k~k₁))
  ... | no ¬p = no λ x → ¬p (decConv↓Term-ne-ins neA x)

  decConv↓Term Γ≡Δ (zero-refl x) (zero-refl x₁) _ = yes (zero-refl x)

  decConv↓Term Γ≡Δ (suc-cong m) (suc-cong n) (leS size)
    with decConv↑Term Γ≡Δ m n (<=-trans (<=-help-ab1' {a = 1+ (sizeConv↑Term m)}) size)
  ... | yes p = yes (suc-cong p)
  ... | no ¬p = no λ { (suc-cong x) → ¬p x }

  decConv↓Term Γ≡Δ (η-eq lF< lG< ⊢F ⊢f _ funf _ f) (η-eq _ _ _ ⊢g _ fung _ g) (leS size)
    with decConv↑Term (Γ≡Δ ∙ refl ⊢F) f g (<=-trans (<=-help-ab1' {a = 1+ (sizeConv↑Term f)}) size)
  ... | yes p = yes (η-eq lF< lG< ⊢F ⊢f (stabilityTerm (symConEq Γ≡Δ) ⊢g) funf fung p)
  ... | no ¬p = no (λ { (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) → ¬p x₇ })

  decConv↓Term Γ≡Δ (U-refl x x₁) (ne x₂) _ =
    no (λ x₃ → decConv↓Term-U (symConv↓Term Γ≡Δ x₃) x₂ (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (U-refl x x₁) (Π-cong x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀) _ = no λ { (ne ()) }
  decConv↓Term Γ≡Δ (ne x) (U-refl x₁ x₂) _ =
    no (λ x₃ → decConv↓Term-U x₃ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (ne x) (ℕ-refl x₁) _ =
    no (λ x₃ → decConv↓Term-U x₃ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (ne x) (Empty-refl x₂) _ =
    no (λ x₃ → decConv↓Term-U x₃ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (ne x) (Π-cong x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉) _ =
    no (λ x₃ → decConv↓Term-U x₃ x (λ { ([~] A D whnfB (cast-refl x' x₁' x₂')) → ⁰-next x₁ ;
                                        ([~] .ℕ D whnfB (castℕ-refl x' x₁')) → ⁰-next x₁ }))
  decConv↓Term Γ≡Δ (ne x) (∃-cong x₂ x₃ x₄) _ =
    no (λ x₃ → decConv↓Term-U x₃ x (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (ℕ-refl x) (ne x₁) _ =
    no (λ x₃ → decConv↓Term-U (symConv↓Term Γ≡Δ x₃) x₁ (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (ℕ-refl x) (Π-cong x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉) _ = no λ { (ne ()) ; (ne-ins _ x₁ () x₃) }
  decConv↓Term Γ≡Δ (Empty-refl x₁) (ne x₂) _ =
    no (λ x₃ → decConv↓Term-U (symConv↓Term Γ≡Δ x₃) x₂ (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (Empty-refl x₁) (Π-cong x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀) _ = no λ { (ne ()) ; (ne-ins _ x₁ () x₃) }
  decConv↓Term Γ≡Δ (Empty-refl x₁) (∃-cong x₃ x₄ x₅) _ = no λ { (ne ()) ; (ne-ins _ x₁ () x₃) }
  decConv↓Term Γ≡Δ (Π-cong l x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (U-refl x₈ x₉) _ = no λ { (ne ()) }
  decConv↓Term Γ≡Δ (Π-cong l x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (ne x₈) _ =
    no (λ x₉ → decConv↓Term-U (symConv↓Term Γ≡Δ x₉) x₈ (λ { ([~] A D whnfB (cast-refl x x₁ x₂)) → ⁰-next l ;
                                                            ([~] .ℕ D whnfB (castℕ-refl x x₁)) → ⁰-next l }))
  decConv↓Term Γ≡Δ (Π-cong l x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (ℕ-refl x₈) _ = no λ { (ne ()) ; (ne-ins x x₁ () x₃) }
  decConv↓Term Γ≡Δ (Π-cong l x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (Empty-refl x₉) _ = no λ { (ne ()) ; (ne-ins x x₁ () x₃) }
  decConv↓Term Γ≡Δ (Π-cong l x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (∃-cong x₉ x₁₀ x₁₁) _ = no λ { (ne ()) ; (ne-ins x x₁ () x₃) }
  decConv↓Term Γ≡Δ (∃-cong x x₁ x₂) (ne x₃) _ =
    no (λ x₉ → decConv↓Term-U (symConv↓Term Γ≡Δ x₉) x₃ (λ { ([~] A D whnfB ()) }))
  decConv↓Term Γ≡Δ (∃-cong x x₁ x₂) (Empty-refl x₄) _ = no λ { (ne ()) ; (ne-ins x x₁ () _) }
  decConv↓Term Γ≡Δ (∃-cong x x₁ x₂) (Π-cong x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁) _ = no λ { (ne ()) ; (ne-ins x x₁ () x₃) }
  decConv↓Term Γ≡Δ (ℕ-ins x) (zero-refl x₁) _ =
    no (λ x₂ → decConv↓Term-ℕ x₂ x (λ { ([~] A D whnfB (cast-refl x x₁ x₂)) → let _ , _ , neA = ne~↓! x
                                                                                  e = whnfRed* D (ne neA)
                                                                              in ℕ≢ne neA (PE.sym e)  ;
                                        ([~] .ℕ D whnfB (castℕ-refl x x₁)) → let _ , _ , neZero = ne~↓! x in neutralZero neZero }))
  decConv↓Term Γ≡Δ (ℕ-ins x) (suc-cong x₁) _ =
    no (λ x₂ → decConv↓Term-ℕ x₂ x (λ { ([~] A D whnfB (cast-refl x x₁ x₂)) → let _ , _ , neA = ne~↓! x
                                                                                  e = whnfRed* D (ne neA)
                                                                              in ℕ≢ne neA (PE.sym e) ;
                                         ([~] .ℕ D whnfB (castℕ-refl x x₁)) → let _ , _ , neSuc = ne~↓! x in neutralSuc neSuc }))
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (ne x₄)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (ℕ-refl x₄)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (Empty-refl x₅)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (Π-cong x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (∃-cong x₅ x₆ x₇)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (ℕ-ins x₄)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (zero-refl x₄)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (suc-cong x₄)
  decConv↓Term Γ≡Δ (ne-ins x x₁ () x₃) (η-eq x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁)
  decConv↓Term Γ≡Δ (zero-refl x) (ℕ-ins x₁) _ =
    no (λ x₂ → decConv↓Term-ℕ (symConv↓Term Γ≡Δ x₂) x₁
                              (λ { ([~] A D whnfB (cast-refl x x₁ x₂)) → let _ , _ , neA = ne~↓! x
                                                                             e = whnfRed* D (ne neA)
                                                                         in ℕ≢ne neA (PE.sym e) ;
                                   ([~] .ℕ D whnfB (castℕ-refl x x₁)) → let _ , _ , neZero = ne~↓! x in neutralZero neZero }))
  decConv↓Term Γ≡Δ (zero-refl x) (suc-cong x₁) _ = no λ { (ℕ-ins ()) ; (ne-ins x x₁ () x₃) }
  decConv↓Term Γ≡Δ (suc-cong x) (ℕ-ins x₁) _ =
    no (λ x₂ → decConv↓Term-ℕ (symConv↓Term Γ≡Δ x₂) x₁
                              (λ { ([~] A D whnfB (cast-refl x x₁ x₂)) → let _ , _ , neA = ne~↓! x
                                                                             e = whnfRed* D (ne neA)
                                                                         in ℕ≢ne neA (PE.sym e) ;
                                   ([~] .ℕ D whnfB (castℕ-refl x x₁)) → let _ , _ , neSuc = ne~↓! x in neutralSuc neSuc }))
  decConv↓Term Γ≡Δ (suc-cong x) (zero-refl x₁) _ = no λ { (ℕ-ins ()) ; (ne-ins x x₁ () x₃) }
  decConv↓Term Γ≡Δ (η-eq x x₁ x₂ x₃ x₄ x₅ x₆ x₇) (ne-ins x₈ x₉ () x₁₁)
-}
  decConv↓Term Γ≡Δ X Y = {!!}

  -- Decidability of algorithmic equality of terms of equal types.
  decConv↑TermConv : ∀ {n t t' u u' A B r Γ Δ}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B ^ r
                → (e : Γ ⊢ t [genconv↑] t' ∷ A ^ r)
                → (e' : Δ ⊢ u [genconv↑] u' ∷ B ^ r)
                → (size[genconv↑] e + size[genconv↑] e') << n
                → Dec (Γ ⊢ t [genconv↑] u ∷ A ^ r)
  decConv↑TermConv {r = [ ! , l ]} Γ≡Δ A≡B t u size =
    decConv↑Term Γ≡Δ t (convConvTerm u (stabilityEq Γ≡Δ (sym A≡B))) (<<-trans (<=-cong-+ (le-refl (sizeConv↑Term t)) (≡-to-<= (convConv↑TermSize (reflConEq _) (stabilityEq Γ≡Δ (sym A≡B)) u))) size)
  decConv↑TermConv {r = [ % , l ]} Γ≡Δ A≡B (%~↑ ⊢t ⊢t') (%~↑ ⊢u ⊢u') _ =
    yes (%~↑ ⊢t (conv (stabilityTerm (symConEq Γ≡Δ) ⊢u) (sym A≡B)))

  decConv↑TermConv′ : ∀ {n t t' u u' A B r r₁ r₂ Γ Δ}
                → ⊢ Γ ≡ Δ
                → r PE.≡ r₁
                → r PE.≡ r₂
                → Γ ⊢ A ≡ B ^ r
                → (e : Γ ⊢ t [genconv↑] t' ∷ A ^ r₁)
                → (e' : Δ ⊢ u [genconv↑] u' ∷ B ^ r₂)
                → (size[genconv↑] e + size[genconv↑] e') << n
                → Dec (Γ ⊢ t [genconv↑] u ∷ A ^ r)
  decConv↑TermConv′ Γ≡Δ PE.refl PE.refl A≡B t u size = decConv↑TermConv Γ≡Δ A≡B t u size
