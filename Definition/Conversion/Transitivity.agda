-- {-# OPTIONS --safe #-}
{-# OPTIONS --allow-unsolved-metas #-}

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
open import Definition.Conversion.ConvSize
open import Definition.Conversion.ConversionProp
open import Definition.Conversion.StabilityProp
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

open import Tools.Nat as Nat
open import Tools.Product
open import Tools.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Tools.Empty
import Tools.PropositionalEquality as PE


<=inv-suc :  ∀ {n m : Nat} → 1+ n <= 1+ m → n <= m
<=inv-suc (leS e) = e

+-0 : ∀ {a : Nat} → a + 0 PE.≡ a
+-0 {0} = PE.refl
+-0 {1+ a} = PE.cong 1+ +-0

+-suc : ∀ {a b : Nat} → a + (1+ b) PE.≡ 1+ (a + b)
+-suc {0} {b} = PE.refl
+-suc {1+ a} {b} = PE.cong 1+ +-suc 

+-sym : ∀ (a b : Nat) → a + b PE.≡ b + a
+-sym 0 b = PE.sym +-0 
+-sym (1+ a) b = PE.trans (PE.cong 1+ (+-sym a b)) (PE.sym +-suc)

+-assoc : ∀ (a b c : Nat) → a + b + c PE.≡ a + (b + c)
+-assoc 0 b c = PE.refl
+-assoc (1+ a) b c = PE.cong 1+ (+-assoc a b c)

<=-trans :  ∀ {a b c : Nat} → a <= b → b <= c → a <= c
<=-trans le0 e = le0
<=-trans (leS e) (leS e') = leS (<=-trans e e')

<=+k :  ∀ {a b c : Nat} → a <= b → a <= (c + b)
<=+k {c = Nat.zero} e = e
<=+k {c = 1+ c} e = <=-trans (<=+k e) (le-suc (le-refl _))

<<-trans :  ∀ {a b c : Nat} → a <= b → b << c → a << c
<<-trans e e' = <=-trans (leS e) e'

≡-to-<= :  ∀ {a b : Nat} → a PE.≡ b → a <= b
≡-to-<= PE.refl = le-refl _

<=-cong-+ : ∀ {a a' b b' : Nat} → a <= a' → b <= b' → (a + b) <= (a' + b')
<=-cong-+ le0 e' = <=+k e'
<=-cong-+ (leS e) e' = leS (<=-cong-+ e e')

<=-cong-+3 : ∀ {a a' b b' c c' : Nat} → a <= a' → b <= b' → c <= c' → (a + b + c) <= (a' + b' + c')
<=-cong-+3 ea eb ec = <=-cong-+ (<=-cong-+ ea eb) ec

<=-cong-+4 : ∀ {a a' b b' c c' d d' : Nat} → a <= a' → b <= b' → c <= c' → d <= d' → (a + b + c + d) <= (a' + b' + c' + d')
<=-cong-+4 ea eb ec ed = <=-cong-+ (<=-cong-+ (<=-cong-+ ea eb) ec) ed

<<cong-right :  ∀ {a b c d : Nat} → (c + d) <= (a + c + (b + d))
<<cong-right {a} {b} {c} {d} = <=-trans (<=-cong-+ (<=+k (le-refl c)) (le-refl d))
                                            (<=-cong-+ (le-refl (a + c)) (<=+k (le-refl d)))
                     
<<bind :  ∀ {n a b : Nat} → (b <= a) → a << n → b << n
<<bind eba e = <<-trans eba e

<<bind-suc :  ∀ {n a b : Nat} → (b <= a) → 1+ a << n → 1+ b << n
<<bind-suc eba e = <<bind (leS eba) e

<=-switch-bc : ∀ {a b c d : Nat} → (a + b + (c + d)) <= (a + c + (b + d))
<=-switch-bc {a} {b} {c} {d} =
  ≡-to-<= (PE.trans (PE.trans (PE.sym (+-assoc (a + b) c d))
                    (PE.cong (λ X →  X + d) (PE.trans (+-assoc a b c)
                    (PE.trans (PE.cong (_+_ a) (+-sym b c)) (PE.sym (+-assoc a c b))))))
                    (+-assoc (a + c) b d))

<=-help-ab :  ∀ {a b c d : Nat} → 1+ (a + b) <= (a + (1+ c) + (b + d)) 
<=-help-ab = {!!}

<=-help-ab1 :  ∀ {a b : Nat} → 1+ (a + b) <= (a + 1 + (b + 1)) 
<=-help-ab1 = {!!}

<=-help-ab1' :  ∀ {a b : Nat} → (a + b) <= (a + 1+ b) 
<=-help-ab1' = {!!}

<=-help-ab' :  ∀ {a b c d : Nat} → (a + b) <= (a + c + 1+ (b + d)) 
<=-help-ab' = {!!}

<=-help-ab'' :  ∀ {a b c d : Nat} → (b + d) <= (a + (1+ b) + (c + d)) 
<=-help-ab'' = {!!}

<=-help-3-ab :  ∀ {a b b' c d : Nat} → (a + b) <= (a + c + 1+ (b + b' + d)) 
<=-help-3-ab = {!!}

<=-help-3-ab' :  ∀ {a b b' c d : Nat} → (b' + (1+ a)) <= (a + c + 1+ (b + (1+ b') + d))
<=-help-3-ab' = {!!}

<=-help-3-abb' :  ∀ {a b b' c d : Nat} → (b' + (1+ a) + b) <= (a + c + 1+ (b + (1+ b') + d)) 
<=-help-3-abb' = {!!}

<=-help-3-abcde :  ∀ {a b c d e : Nat} → (a + (1+ b) + c + (d + e)) <= (b + d + 1+ (c + (1+ a) + e)) 
<=-help-3-abcde = {!!}

<=-help-abcd-b :  ∀ {a b c d : Nat} → (a + c + d) <= (a + b + (c + d))
<=-help-abcd-b = {!!}

<=-help-3-abcd :  ∀ {a b c d : Nat} → (a + b + (c + d)) <= (a + c + 1+ (b + d)) 
<=-help-3-abcd = {!!}

<=-help-nat-cong :  ∀ {a b b' b'' b''' c' c'' c''' : Nat} → (a + b) <= (a + b' + b'' + b''' + 1+ (b + c' + c'' + c'''))
<=-help-nat-cong = {!!}

<=-help-id-cong :  ∀ {a b b' b'' c' c''  : Nat} → (a + b) <= (a + b' + b'' + 1+ (b + c' + c''))
<=-help-id-cong = {!!}

<=-help-id-cong' :  ∀ {a b b' b'' c' c''  : Nat} → (a + b + (b' + c') + (b'' + c'') ) <= (a + b' + b'' + 1+ (b + c' + c''))
<=-help-id-cong' = {!!}

sizeSubst-gen :  ∀ {A a b}
              → (P : A → Set)
              → (size : ∀ {a} → P a → Nat)
              → (t : P a)
              → (e : a PE.≡ b)
              → size (PE.subst P e t) PE.≡ size t
sizeSubst-gen _ _ _ PE.refl = PE.refl              

sizeSubst₃-gen :  ∀ {A B C a b c a' b' c'}
              → (P : A → B → C → Set)
              → (size : ∀ {a b c} → P a b c → Nat)
              → (t : P a b c)
              → (ea : a PE.≡ a')
              → (eb : b PE.≡ b')
              → (ec : c PE.≡ c')
              → size (PE.subst₃ P ea eb ec t) PE.≡ size t
sizeSubst₃-gen _ _ _ PE.refl PE.refl PE.refl = PE.refl              


mutual

  -- Transitivity of algorithmic equality of neutrals.
  trans~↑! : ∀ {n t u v A B Γ Δ l l'}
         → l PE.≡ l'
         → ⊢ Γ ≡ Δ
         → (e : Γ ⊢ t ~ u ↑! A ^ l)
         → (e' : Δ ⊢ u ~ v ↑! B ^ l')
         → (size~↑! e + size~↑! e') << n
         → ∃₂ λ C (e'' : Γ ⊢ t ~ v ↑! C ^ l) → Γ ⊢ A ≡ C ^ [ ! , l ] × Γ ⊢ C ≡ B ^ [ ! , l ] × size~↑! e'' <= (size~↑! e + size~↑! e')

  trans~↑! {n = 0} el Γ≡Δ X Y ()

{-

  trans~↑! {n = 1+ n} el Γ≡Δ (var-refl x₁ x≡y) (var-refl x₂ x≡y₁) e =
    _ , var-refl x₁ (PE.trans x≡y x≡y₁)
    , refl (syntacticTerm x₁) ,
      proj₂ (neTypeEq (var _) x₁
                (PE.subst (λ x → _ ⊢ var x ∷ _ ^ _) (PE.sym x≡y)
                         (stabilityTerm (symConEq Γ≡Δ) (PE.subst (λ lx → _ ⊢ _ ∷ _ ^ [ ! , lx ]) (PE.sym el) x₂)))) ,
      leS le0                   
                         

  trans~↑! {n = 1+ n} {Γ = Γ} el Γ≡Δ (app-cong {k = k} {rF = !} {lΠ = lΠ} t~u a<>b) (app-cong {l = l} {rF = !} u~v b<>c) (leS e) =
    let C , wC , t~v , ΠFG≡C , C≡ΠF′G′ , sizet~u = trans~↓! {n = n} PE.refl Γ≡Δ t~u u~v (<<bind (<=-help-ab {b = size~↓! u~v}) e)
        H , E , C≡ΠHE = Π≡A ΠFG≡C wC
        ⊢Γ = proj₁ (contextConvSubst Γ≡Δ)
        ΠFG≡C' = PE.subst (λ X → _ ⊢ _ ≡ X ^ [ ! , ι _ ]) C≡ΠHE ΠFG≡C
        C≡ΠF′G′' = PE.subst (λ X → _ ⊢ X ≡ _ ^ [ ! , ι _ ]) C≡ΠHE C≡ΠF′G′
        F≡F₁ , rF≡rF₁ , _ , lG≡lG₁ , G≡G₁ = injectivity ΠFG≡C'
        F≡F₁' , rF≡rF₁' , lF≡lF₁' , lG≡lG₁' , G≡G₁' = injectivity C≡ΠF′G′'
        t~v' = PE.subst (λ X →  Γ ⊢ k ~ l ↓! X ^ ι lΠ) C≡ΠHE t~v
        a<>c , sizea<>c = transConv↑Term {n = n} (PE.cong ι lF≡lF₁') Γ≡Δ (trans F≡F₁ F≡F₁') a<>b b<>c
                              (<<bind (<<cong-right {a = size~↑! (_⊢_~_↓!_^_.k~l t~u)} {b = size~↓! u~v}) e) 
        t≡v = soundnessConv↑Term a<>b
        _ , ⊢t , _ = syntacticEqTerm t≡v
    in _ , app-cong t~v' (convConv↑Term (reflConEq ⊢Γ) F≡F₁ a<>c) ,
       substTypeEq G≡G₁ (refl ⊢t) , substTypeEq G≡G₁' (conv t≡v F≡F₁) ,
       PE.subst₂ (λ X Y → (X + Y) <= (size~↑! (app-cong t~u a<>b) + size~↑! (app-cong u~v b<>c)))
                 (PE.sym (sizeSubst-gen  (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) size~↓! t~v C≡ΠHE)) (PE.sym (convConv↑TermSize (reflConEq ⊢Γ) F≡F₁ a<>c))
                 (<=-trans (<=-cong-+ sizet~u sizea<>c) (<=-switch-bc {a = size~↓! t~u} {b = size~↓! u~v}))

  trans~↑! {n = 1+ n} {Γ = Γ} el Γ≡Δ (app-cong {k = k} {rF = %} {lΠ = lΠ} t~u a<>b) (app-cong {l = l} {rF = %} u~v b<>c) (leS e) =
    let C , wC , t~v , ΠFG≡C , C≡ΠF′G′ , sizet~u = trans~↓! {n = n} PE.refl Γ≡Δ t~u u~v (<<bind (<=-help-ab1 {b = size~↓! u~v}) e)
        H , E , C≡ΠHE = Π≡A ΠFG≡C wC
        ⊢Γ = proj₁ (contextConvSubst Γ≡Δ)
        ΠFG≡C' = PE.subst (λ X → _ ⊢ _ ≡ X ^ [ ! , ι _ ]) C≡ΠHE ΠFG≡C
        C≡ΠF′G′' = PE.subst (λ X → _ ⊢ X ≡ _ ^ [ ! , ι _ ]) C≡ΠHE C≡ΠF′G′
        F≡F₁ , rF≡rF₁ , _ , lG≡lG₁ , G≡G₁ = injectivity ΠFG≡C'
        F≡F₁' , rF≡rF₁' , lF≡lF₁' , lG≡lG₁' , G≡G₁' = injectivity C≡ΠF′G′'
        t~v' = PE.subst (λ X →  Γ ⊢ k ~ l ↓! X ^ ι lΠ) C≡ΠHE t~v
        a<>c = trans~↑% Γ≡Δ a<>b
                            (conv~↑% (PE.subst (λ x → _ ⊢ _ ~ _ ↑% _ ^ ι x) (PE.sym lF≡lF₁') b<>c)
                            (stabilityEq Γ≡Δ (sym (trans F≡F₁ F≡F₁'))))
        _ , _ , t≡v = soundness~↑% a<>b
        _ , ⊢t , _ = syntacticEqTerm t≡v
    in _ , app-cong t~v' (conv~↑% a<>c F≡F₁) ,
       substTypeEq G≡G₁ (proof-irrelevance ⊢t ⊢t) ,
       substTypeEq G≡G₁' (conv t≡v F≡F₁) ,
       PE.subst (λ X → (X + 1) <= (size~↑! (app-cong t~u a<>b) + size~↑! (app-cong u~v b<>c)))
                (PE.sym (sizeSubst-gen  (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) size~↓! t~v C≡ΠHE))
                (<=-trans (<=-cong-+ sizet~u (le-refl 1)) (leS (<=-help-abcd-b {c = size~↓! u~v})))
                 
  trans~↑! el Γ≡Δ (app-cong {rF = !} t~u a<>b) (app-cong {rF = %} u~v b<>c) e =
   let whnfA , neK , neL = ne~↓! t~u
       ⊢A , ⊢k , ⊢l₁ = syntacticEqTerm (soundness~↓! t~u)
       ⊢A' , ⊢l₁' , ⊢l = syntacticEqTerm (soundness~↓! u~v)
       _ , ΠFG≡ΠF₂G₂ = neTypeEq neL ⊢l₁ (stabilityTerm (symConEq Γ≡Δ) ⊢l₁')
       F≡F₂ , rF≡rF₂ , G≡G₂ = injectivity ΠFG≡ΠF₂G₂
   in ⊥-elim (relevance-discr rF≡rF₂)
  trans~↑! el Γ≡Δ (app-cong {rF = %} t~u a<>b) (app-cong {rF = !} u~v b<>c) e =
   let whnfA , neK , neL = ne~↓! t~u
       ⊢A , ⊢k , ⊢l₁ = syntacticEqTerm (soundness~↓! t~u)
       ⊢A' , ⊢l₁' , ⊢l = syntacticEqTerm (soundness~↓! u~v)
       _ , ΠFG≡ΠF₂G₂ = neTypeEq neL ⊢l₁ (stabilityTerm (symConEq Γ≡Δ) ⊢l₁')
       F≡F₂ , rF≡rF₂ , G≡G₂ = injectivity ΠFG≡ΠF₂G₂
   in ⊥-elim (relevance-discr (PE.sym rF≡rF₂))

  trans~↑! {n = 1+ n} {Γ = Γ} PE.refl Γ≡Δ (natrec-cong {k = k} A<>B a₀<>b₀ aₛ<>bₛ t~u) (natrec-cong {l = l} B<>C b₀<>c₀ bₛ<>cₛ u~v) (leS e) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        A≡B = soundnessConv↑ A<>B
        F[0]≡F₁[0] = substTypeEq A≡B (refl (zeroⱼ ⊢Γ))
        ΠℕFs≡ΠℕF₁s = sucCong A≡B
        A<>C , sizeA<>C = transConv↑ {n = n} (Γ≡Δ ∙ (refl (univ (ℕⱼ ⊢Γ)))) A<>B B<>C
                                     (<<bind (leS (<=-help-nat-cong {b = sizeConv↑ B<>C})) e)
        a₀<>c₀ , sizea₀<>c₀ = transConv↑Term {n = n} PE.refl Γ≡Δ F[0]≡F₁[0] a₀<>b₀ b₀<>c₀
                                             (<<bind (leS {!!}) e) 
        aₛ<>cₛ , sizeaₛ<>cₛ = transConv↑Term {n = n} PE.refl Γ≡Δ ΠℕFs≡ΠℕF₁s aₛ<>bₛ bₛ<>cₛ (<<bind {!!} e)
        C , wC ,  t~v , ℕ≡C , _ , sizet~v = trans~↓! {n = n} PE.refl Γ≡Δ t~u u~v (<<bind {!!} e)
        ℕ≡C' = ℕ≡A ℕ≡C wC
    in  _ , natrec-cong A<>C a₀<>c₀ aₛ<>cₛ (PE.subst (λ X → Γ ⊢ k ~ l ↓! X ^ ι ⁰) ℕ≡C' t~v) ,
        substTypeEq (refl (proj₁ (syntacticEq A≡B))) (refl (proj₁ (proj₂ (syntacticEqTerm (soundness~↓! t~u))))) ,
        substTypeEq A≡B (soundness~↓! t~u) ,
        leS (<=-trans (<=-cong-+4 sizeA<>C sizea₀<>c₀ sizeaₛ<>cₛ
                                  (<=-trans (≡-to-<= (sizeSubst-gen (λ X →  _ ⊢ _ ~ _ ↓! X ^ ι _) size~↓! t~v ℕ≡C'))
                                            sizet~v))
            (leS {!!}))


  trans~↑! {n = 1+ n} PE.refl Γ≡Δ (Emptyrec-cong A<>B t~u) (Emptyrec-cong B<>C u~v) (leS e) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        A≡B = soundnessConv↑ A<>B
        A<>C , sizeA<>C = transConv↑ {n = n} Γ≡Δ A<>B B<>C
                                     (<<bind (leS <=-help-ab1') e)
        ⊢t , ⊢u , t≡u = soundness~↑% t~u
        _ , ⊢v , u≡v = soundness~↑% u~v
        t~v = %~↑ ⊢t (stabilityTerm (symConEq Γ≡Δ) ⊢v)
    in _ , Emptyrec-cong A<>C t~v , refl (proj₁ (syntacticEq A≡B)) , A≡B ,
      leS (<=-trans sizeA<>C (leS <=-help-ab1') )    
  trans~↑! {n = 1+ n} {Γ = Γ} _ Γ≡Δ (Id-cong {l = l} {A = A} X x x₁) (Id-cong {A' = A'} Y x₂ x₃) (leS e) =
    let _ , _ , [A'] = (syntacticEqTerm (soundness~↓! X))
        [A']Δ = stabilityTerm Γ≡Δ [A']
        _ , [A']Δ' , _ = syntacticEqTerm (soundness~↓! Y)
        _ , el' = relevance-unicity (univ [A']Δ) (univ [A']Δ')
        el = PE.cong next (ιinj el')
        K , wK , XY , [U] , [U]' , sizeXY = trans~↓! {n = n} el Γ≡Δ X Y
                                                     (<<bind (leS (<=-help-id-cong {b = size~↓! Y})) e)
        eqU = U≡A-whnf [U] wK
        XY' = PE.subst (λ X → Γ ⊢ A ~ A' ↓! X ^ next l) eqU XY
        X≡Y = univ (soundness~↓! XY')
        Y≡Y = PE.subst (λ lx → _ ⊢ _ ≡ _ ^ [ ! , ι lx ]) (PE.sym (next-inj el)) (univ (soundness~↓! Y))
        t~t , sizet~t = transConv↑Term {n = n} el' Γ≡Δ
                                       (trans X≡Y (stabilityEq (symConEq Γ≡Δ) (sym Y≡Y))) x x₂
                                       (<<bind (leS {!!}) e)
        u~u , sizeu~u = transConv↑Term {n = n} el' Γ≡Δ (trans X≡Y (stabilityEq (symConEq Γ≡Δ) (sym Y≡Y))) x₁ x₃ 
                                       (<<bind (leS {!!}) e)
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        sizeXY' = <=-trans (≡-to-<= (sizeSubst-gen (λ X →  Γ ⊢ A ~ A' ↓! X ^ next l) size~↓! XY eqU)) sizeXY
    in _ , Id-cong XY' t~t u~u , refl (Ugenⱼ ⊢Γ) , refl (Ugenⱼ ⊢Γ) ,
      leS (<=-trans (<=-cong-+3 sizeXY' sizet~t sizeu~u) 
          (leS (<=-help-id-cong' {b = size~↓! Y} {b' = sizeConv↑Term x} {b'' = sizeConv↑Term x₁})))
  trans~↑! {n = 1+ n} {Γ = Γ} el Γ≡Δ (Id-ℕ {t = t} X x) (Id-ℕ {t' = t'} Y x₁) (leS e) =
    let X , wX , t~t , ℕ≡X , X≡ℕ , sizet~t = trans~↓! {n = n} PE.refl Γ≡Δ X Y (<<bind-suc (<=-help-ab' {b = size~↓! Y}) e)
        u~u , sizeu~u = transConv↑Term {n = n} PE.refl Γ≡Δ (trans ℕ≡X X≡ℕ) x x₁
                         (<<bind-suc (<=-help-ab'' {c = 1+ (size~↓! Y)}) e)
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        eqℕ = ℕ≡A ℕ≡X wX
        t~t' =  PE.subst (λ X →  Γ ⊢ t ~ t' ↓! X ^ ι ⁰) eqℕ t~t
        sizet~t' = <=-trans (≡-to-<= (sizeSubst-gen (λ X → Γ ⊢ t ~ t' ↓! X ^ ι ⁰) size~↓! t~t eqℕ)) sizet~t
    in _ , Id-ℕ t~t' u~u , refl (Ugenⱼ ⊢Γ) , refl (Ugenⱼ ⊢Γ) ,
       leS (<=-trans (<=-cong-+ sizet~t' sizeu~u)
           (leS (<=-help-3-abcd {b = size~↓! Y} {c = sizeConv↑Term x})))

  trans~↑! {n = 1+ n} {Γ = Γ} el Γ≡Δ (Id-ℕ0 {t = t} X) (Id-ℕ0 {t' = t'} Y) (leS e) =
    let X , wX , t~t , ℕ≡X , X≡ℕ , sizet~t = trans~↓! {n = n} PE.refl Γ≡Δ X Y (<<bind-suc <=-help-ab1' e)
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        eqℕ = ℕ≡A ℕ≡X wX
        t~t' =  PE.subst (λ X →  Γ ⊢ t ~ t' ↓! X ^ ι ⁰) eqℕ t~t
        sizet~t' = <=-trans (≡-to-<= (sizeSubst-gen (λ X → Γ ⊢ t ~ t' ↓! X ^ ι ⁰) size~↓! t~t eqℕ)) sizet~t
    in _ , Id-ℕ0 t~t' , refl (Ugenⱼ ⊢Γ) , refl (Ugenⱼ ⊢Γ) ,
       leS (<=-trans sizet~t' (leS <=-help-ab1'))
-}
  trans~↑! {n = 1+ n} {Γ = Γ} el Γ≡Δ (Id-ℕS {u = u} x X) (Id-ℕS {u' = u'} x₁ Y) (leS e) =
    let _ , wX , t~t , ℕ≡X , X≡ℕ , sizet~t = trans~↓! {n = n} PE.refl Γ≡Δ X Y
               (<<bind-suc (<=-help-ab'' {c = 1+ (sizeConv↑Term x₁)}) e)
        u~u , sizeu~u = transConv↑Term {n = n} PE.refl Γ≡Δ (trans ℕ≡X X≡ℕ) x x₁
                         (<<bind-suc (<=-help-ab' {b = sizeConv↑Term x₁}) e)
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        eqℕ = ℕ≡A ℕ≡X wX
        t~t' = PE.subst (λ X →  Γ ⊢ u ~ u' ↓! X ^ ι ⁰) eqℕ t~t
        sizet~t' = <=-trans (≡-to-<= (sizeSubst-gen (λ X → Γ ⊢ u ~ u' ↓! X ^ ι ⁰) size~↓! t~t eqℕ)) sizet~t
    in _ , Id-ℕS u~u t~t' , refl (Ugenⱼ ⊢Γ) , refl (Ugenⱼ ⊢Γ) ,
       leS (<=-trans (<=-cong-+ sizeu~u sizet~t')
           (leS (<=-help-3-abcd {b = sizeConv↑Term x₁} {c = size~↓! X}))) 
{-
  trans~↑! {n = 1+ n} el Γ≡Δ (Id-U X x) (Id-U Y x₁) e =
    let K , wK , XY , [U] , [U]' = trans~↓! {n = n} el Γ≡Δ X Y {!!}
        eqU = U≡A-whnf [U] wK
        XY' = PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqU XY
        u~u = transConv↑Term {n = n} Γ≡Δ (trans [U] [U]') x x₁ {!!}
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
    in _ , Id-U XY' u~u , refl (Ugenⱼ ⊢Γ) , refl (Ugenⱼ ⊢Γ)
  trans~↑! {n = 1+ n} el Γ≡Δ (Id-Uℕ X) (Id-Uℕ Y) e =
    let K , wK , XY , [U] , [U]' = trans~↓! {n = n} el Γ≡Δ X Y {!!}
        eqU = U≡A-whnf [U] wK
        XY' = PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqU XY
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
    in _ , Id-Uℕ XY' , refl (Ugenⱼ ⊢Γ)  , refl (Ugenⱼ ⊢Γ)
  trans~↑! {n = 1+ n} el Γ≡Δ (Id-UΠ x X) (Id-UΠ x₁ Y) e =
    let K , wK , XY , [U] , [U]' = trans~↓! {n = n} el Γ≡Δ X Y {!!}
        eqU = U≡A-whnf [U] wK
        XY' = PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqU XY
        u~u = transConv↑Term {n = n} Γ≡Δ (trans [U] [U]') x x₁ {!!}
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
    in _ , Id-UΠ u~u XY' , refl (Ugenⱼ ⊢Γ) , refl (Ugenⱼ ⊢Γ)


  trans~↑! {n = 1+ n} el Γ≡Δ (cast-cong X x ⊢t ⊢t' x₁ x₂ x₃) (cast-cong Y x₄ ⊢u ⊢u' x₅ x₆ x₇) e =
    let K , wK , XY , [U] , _  = trans~↓! {n = n} PE.refl Γ≡Δ X Y {!!}
        eqU = U≡A-whnf [U] wK
        XY' = PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqU XY
        X≡Y = univ (soundness~↓! XY')
        Y≡Y = univ (soundness~↓! Y)
        K' , wK' , t~t , [U]' , _ = trans~↓! {n = n} PE.refl (symConEq Γ≡Δ) x₄ x {!!}
        eqU' = U≡A-whnf [U]' wK'
        t~t' = PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqU' (stability~↓! (symConEq Γ≡Δ)  t~t)
        _ , _ , neA = ne~↓! Y
        u~u = transConv↓Term {n = n} Γ≡Δ X≡Y PE.refl x₁ (convConv↓Term (reflConEq (wfTerm ⊢u)) Y≡Y (ne neA) x₅) {!!}
        A₁≡B = (trans (sym (soundness~↓! t~t')) (soundness~↓! (stability~↓! (symConEq Γ≡Δ) x₄)))
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
    in _ , cast-cong XY' t~t' ⊢t (stabilityTerm (symConEq Γ≡Δ) ⊢u') u~u x₂ (stabilityTerm (symConEq Γ≡Δ) x₇) ,
       refl (univ (proj₁ (proj₂ (syntacticEqTerm A₁≡B)))) , univ A₁≡B

  trans~↑! {n = 1+ n} el Γ≡Δ (cast-ℕ X x x₁ x₂) (cast-ℕ Y x₃ x₄ x₅) e =
    let K , wK , XY , [U] , _  = trans~↓! {n = n} PE.refl Γ≡Δ X Y {!!}
        eqU = U≡A-whnf [U] wK
        XY' = PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqU XY
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        t~t = transConv↑Term {n = n}  Γ≡Δ (refl (univ (ℕⱼ  ⊢Γ))) x x₃ {!!}
    in _ , cast-ℕ XY' t~t x₁ (stabilityTerm (symConEq Γ≡Δ) x₅) , refl (proj₁ (syntacticEq (univ (soundness~↓! X)))) , univ (soundness~↓! X)
  trans~↑! {n = 1+ n} el Γ≡Δ (cast-ℕℕ X x x₁) (cast-ℕℕ Y x₂ x₃) e =
    let X , wX , t~t , ℕ≡X , X≡ℕ = trans~↓! {n = n} PE.refl Γ≡Δ X Y {!!}
        eqℕ = ℕ≡A ℕ≡X wX
        t~t' =  PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqℕ t~t
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
    in _ , cast-ℕℕ t~t' x (stabilityTerm (symConEq Γ≡Δ) x₃) , refl (univ (ℕⱼ ⊢Γ)) , refl (univ (ℕⱼ ⊢Γ))
  trans~↑! {n = 1+ n} el Γ≡Δ (cast-Π x X x₁ x₂ x₃) (cast-Π x₄ Y x₅ x₆ x₇) e =
    let K , wK , XY , [U] , [U]'  = trans~↓! {n = n} PE.refl Γ≡Δ X Y {!!}
        eqU = U≡A-whnf [U] wK
        XY' = PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqU XY
        X≡Y = soundness~↓! XY'
        Y≡Y = univ (soundnessConv↑Term x₄)
        t~t = transConv↑Term {n = n} Γ≡Δ (trans [U] [U]') x x₄ {!!}
        u~u = transConv↑Term {n = n} Γ≡Δ (univ (soundnessConv↑Term t~t)) x₁ (convConvTerm x₅ Y≡Y) {!!}
        A₁≡B = trans X≡Y (sym (soundness~↓! (stability~↓! (symConEq Γ≡Δ) Y)))
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
    in _ , cast-Π t~t XY' u~u x₂ (stabilityTerm (symConEq Γ≡Δ) x₇) , refl (univ (proj₁ (proj₂ (syntacticEqTerm A₁≡B)))) , univ A₁≡B
  trans~↑! {n = 1+ n} el Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) (cast-Πℕ x₄ x₅ x₆ x₇) e =
    let Y≡Y = univ (soundnessConv↑Term x₄)
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        t~t = transConv↑Term {n = n} Γ≡Δ (refl (Ugenⱼ ⊢Γ)) x x₄ {!!}
        u~u = transConv↑Term {n = n} Γ≡Δ (univ (soundnessConv↑Term t~t)) x₁ (convConvTerm x₅ Y≡Y) {!!}
    in _ , cast-Πℕ t~t u~u x₂ (stabilityTerm (symConEq Γ≡Δ) x₇) , refl (univ (ℕⱼ  ⊢Γ)) , refl (univ (ℕⱼ  ⊢Γ))
  trans~↑! {n = 1+ n} el Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) (cast-ℕΠ x₄ x₅ x₆ x₇) e =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        t~t = transConv↑Term {n = n} Γ≡Δ (refl (Ugenⱼ ⊢Γ)) x x₄ {!!}
        u~u = transConv↑Term {n = n} Γ≡Δ (refl (univ (ℕⱼ  ⊢Γ))) x₁ x₅ {!!}
        Π≡Π = univ (soundnessConv↑Term x)
    in _ , cast-ℕΠ t~t u~u x₂ (stabilityTerm (symConEq Γ≡Δ) x₇) , refl (proj₁ (syntacticEq Π≡Π)) , Π≡Π
  trans~↑! {n = 1+ n} el Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) (cast-ΠΠ%! x₅ x₆ x₇ x₈ x₉) e =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        A~A = transConv↑Term {n = n} Γ≡Δ (refl (Ugenⱼ ⊢Γ)) x x₅ {!!}
        B~B = transConv↑Term {n = n} Γ≡Δ (refl (Ugenⱼ ⊢Γ)) x₁ x₆ {!!}
        u~u = transConv↑Term {n = n} Γ≡Δ (univ (soundnessConv↑Term x)) x₂ x₇ {!!}
        Π≡Π = trans (univ (soundnessConv↑Term B~B)) (sym (univ (soundnessConv↑Term (stabilityConv↑Term (symConEq Γ≡Δ) x₆))))
    in _ , cast-ΠΠ%! A~A B~B u~u x₃ (stabilityTerm (symConEq Γ≡Δ) x₉) ,
       refl (proj₁ (syntacticEq Π≡Π)) , Π≡Π
  trans~↑! {n = 1+ n} el Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) (cast-ΠΠ!% x₅ x₆ x₇ x₈ x₉) e =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        A~A = transConv↑Term {n = n} Γ≡Δ (refl (Ugenⱼ ⊢Γ)) x x₅ {!!}
        B~B = transConv↑Term {n = n} Γ≡Δ (refl (Ugenⱼ ⊢Γ)) x₁ x₆ {!!}
        u~u = transConv↑Term {n = n} Γ≡Δ (univ (soundnessConv↑Term x)) x₂ x₇ {!!}
        Π≡Π = trans (univ (soundnessConv↑Term B~B)) (sym (univ (soundnessConv↑Term (stabilityConv↑Term (symConEq Γ≡Δ) x₆))))
    in _ , cast-ΠΠ!% A~A B~B u~u x₃ (stabilityTerm (symConEq Γ≡Δ) x₉) ,
       refl (proj₁ (syntacticEq Π≡Π)) , Π≡Π

  trans~↑! {n = 1+ n} PE.refl Γ≡Δ t~u (cast-refl' A~B ⊢u ⊢v (ne-ins x' x₁' x₂' ([~] K D whK u~v)) x₄) e =
    let net , neu = ne~↑! t~u
        t≡u = soundness~↑! t~u
        _ , neB , neA = ne~↓! A~B
        ⊢A , ⊢t , ⊢u' = syntacticEqTerm t≡u
        _ , A≡B = neTypeEq neu ⊢u' (stabilityTerm (symConEq Γ≡Δ) ⊢u)
        _ , ⊢B = syntacticEq A≡B
        C , t~v' , A≡C , C≡B  = trans~↑! {n = n} PE.refl Γ≡Δ t~u u~v {!!}
        _ , ⊢C = syntacticEq A≡C
        XC , wXC , DXC = whNorm ⊢C
        t[conv↑]v = ne-ins (conv ⊢t A≡B) (stabilityTerm (symConEq Γ≡Δ) ⊢v) neA ([~] _ (red DXC) wXC t~v')
   in _ , cast-refl' (stability~↓! (symConEq Γ≡Δ) A~B)
                        (conv ⊢t A≡B) 
                        (stabilityTerm (symConEq Γ≡Δ) ⊢v) t[conv↑]v (stabilityTerm (symConEq Γ≡Δ) x₄) , A≡B , refl ⊢B

  trans~↑! {n = 1+ n} PE.refl Γ≡Δ (cast-refl A~B ⊢t ⊢u (ne-ins x' x₁' x₂' ([~] K D whK t~u)) x₄) u~v e =
    let neu , nev = ne~↑! u~v
        u≡v = soundness~↑! u~v
        _ , neA , neB = ne~↓! A~B
        ⊢B , ⊢u' , ⊢v = syntacticEqTerm u≡v
        _ , A≡B = neTypeEq neu ⊢u (stabilityTerm (symConEq Γ≡Δ) ⊢u')
        A≡B' = univ (soundness~↓! A~B)
        _ , ⊢A' = syntacticEq A≡B'
        C , t~v' , A≡C , C≡B  = trans~↑! {n = n} PE.refl Γ≡Δ t~u u~v {!!}
        _ , ⊢C = syntacticEq A≡C
        XC , wXC , DXC = whNorm ⊢C
        t[conv↑]v = ne-ins ⊢t (conv (stabilityTerm (symConEq Γ≡Δ) ⊢v) (sym A≡B)) neA ([~] _ (red DXC) wXC t~v')
    in _ , cast-refl A~B ⊢t 
                       (conv (stabilityTerm (symConEq Γ≡Δ) ⊢v) (sym A≡B)) t[conv↑]v x₄ , refl ⊢A' , trans (sym A≡B') A≡B


  trans~↑! {n = 1+ n} PE.refl Γ≡Δ t~u (castℕ-refl' ([~] A D whnfB u~v) x₃) e =
    let net , neu = ne~↑! t~u
        t≡u = soundness~↑! t~u
        ⊢A , ⊢t , ⊢u' = syntacticEqTerm t≡u
        C , t~v , A≡C , C≡B = trans~↑! {n = n} PE.refl Γ≡Δ t~u u~v {!!}
        _ , ⊢C = syntacticEq A≡C 
        X , wX , DX = whNorm ⊢C
        eqℕ = ℕ≡A (trans (sym (subset* D)) (trans (stabilityEq Γ≡Δ (sym C≡B)) (stabilityEq Γ≡Δ (subset* (red DX))))) wX
        DN =  PE.subst (λ X → _ ⊢ C ⇒* X ^ [ ! , ι ⁰ ]) eqℕ (red DX)
        A≡ℕ = trans A≡C (trans C≡B (stabilityEq (symConEq Γ≡Δ) (subset* D)))
    in _ , castℕ-refl' ([~] _ DN ℕₙ t~v) (stabilityTerm (symConEq Γ≡Δ) x₃) , A≡ℕ , refl (proj₁ (syntacticEq (sym A≡ℕ)))

  trans~↑! {n = 1+ n} PE.refl Γ≡Δ (castℕ-refl ([~] A D whnfB t~u) x₃) u~v e =
    let neu , nev = ne~↑! u~v
        u≡v = soundness~↑! u~v
        ⊢B , ⊢u , ⊢v = syntacticEqTerm u≡v
        C , t~v , A≡C , C≡B = trans~↑! {n = n} PE.refl Γ≡Δ t~u u~v {!!}
        _ , ⊢C = syntacticEq A≡C 
        X , wX , DX = whNorm ⊢C
        eqℕ = ℕ≡A (trans (sym (subset* D)) (trans A≡C (subset* (red DX)))) wX 
        DN =  PE.subst (λ X → _ ⊢ C ⇒* X ^ [ ! , ι ⁰ ]) eqℕ (red DX)
        A≡ℕ = trans (sym (subset* D)) (trans A≡C C≡B)
    in _ , castℕ-refl ([~] _ DN ℕₙ t~v) x₃  , refl (proj₁ (syntacticEq A≡ℕ)) , A≡ℕ

  trans~↑! {n = 1+ n} {A = A} {Γ = Γ} el Γ≡Δ (cast-cong {A'} x x₁ x₂ x₃' x₄' x₅ x₆) (cast-refl A~B ⊢t ⊢u x₃ x₄) e =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        t~v = transConv↓Term {n = n} Γ≡Δ (univ (soundness~↓! x)) PE.refl x₄' x₃ {!!}
        K , wK , XY , [U] , _  = trans~↓! {n = n}  PE.refl Γ≡Δ x A~B {!!}
        K'' , wK'' , A~A , [U]'' , _  = trans~↓! {n = n}  PE.refl (reflConEq ⊢Γ) XY x₁ {!!}
        eqU'' = U≡A-whnf (trans [U] [U]'' ) wK''
        A~A' = PE.subst (λ X → Γ ⊢ A' ~ A ↓! X ^ ι ¹) eqU'' A~A
    in _ , cast-refl A~A' x₂ (conv (stabilityTerm (symConEq Γ≡Δ) ⊢u) (sym (univ (soundness~↓! x)))) t~v x₅ ,
       refl (proj₂ (syntacticEq (univ (soundness~↓! A~A')))) , sym (univ (soundness~↓! x₁))

  trans~↑! {n = 1+ n} {A = A} {Δ = Δ} el Γ≡Δ (cast-refl' {B = B} B~A ⊢t ⊢u x₃ x₄) (cast-cong {A' = A'} {B' = B'} x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁) (leS e) =
    let ⊢Γ , ⊢Δ , _ = contextConvSubst Γ≡Δ
        t~v , sizet~v = transConv↓Term {n = n} Γ≡Δ (refl (syntacticTerm ⊢t)) PE.refl x₃ x₉
                             (<<bind (<<cong-right {b = 1+ (1+ (size~↑! (_⊢_~_↓!_^_.k~l x₅) + size~↓! x₆))} ) (<<rem-suc e)) 
        K , wK , B~A' , [U] , _  = trans~↓! {n = n} PE.refl Γ≡Δ B~A x₅
                                            (<<bind-suc (<=-help-3-ab {c = sizeConv↓Term x₃}) e) 
        K'' , wK'' , B'~A , [U]'' , _ , sizeB~A  = trans~↓! {n = n} PE.refl (symConEq Γ≡Δ) x₆ B~A
                                                  (<<bind-suc (<=-help-3-ab' {b = 1+ (size~↑! (_⊢_~_↓!_^_.k~l x₅))}) e)
        K' , wK' , B'~A' , [U]' , [U]''' , sizeB~A'  = trans~↓! {n = n} PE.refl (reflConEq ⊢Δ) B'~A x₅
                                                         (<<-trans (<=-cong-+ sizeB~A (le-refl _))
                                                                   (<<bind-suc (<=-help-3-abb' {b = size~↓! x₅}) e))
        eqU' =  U≡A-whnf (sym [U]''') wK'
        A~A' = stability~↓! (symConEq Γ≡Δ) (PE.subst (λ X →  Δ ⊢ B' ~ A' ↓! X ^ ι ¹) eqU' B'~A')
        _ , neA , neA' = ne~↓! x₅
        A≡A' = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! x₅))
        eqU = U≡A-whnf [U] wK
        B~A'U = PE.subst (λ X →  _ ⊢ B ~ A' ↓! X ^ ι ¹) eqU B~A'
        sizeB~A' = <=inv-suc sizeB~A'
    in _ , cast-refl' A~A' (conv ⊢t (stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! x₅))))
                      (stabilityTerm (symConEq Γ≡Δ) x₈) (convConv↓Term (reflConEq ⊢Γ) A≡A' (ne neA') t~v)
                      (stabilityTerm (symConEq Γ≡Δ) x₁₁) ,
      A≡A' ,  sym (univ (soundness~↓! B~A'U)) ,
      PE.subst₂ (λ X Y → 1+ (X + Y) <= (size~↑! (cast-refl' B~A ⊢t ⊢u x₃ x₄) + size~↑! (cast-cong x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁)))
                (PE.sym (PE.trans (stabilitySize~↓! (symConEq Γ≡Δ) (PE.subst (λ X →  Δ ⊢ B' ~ A' ↓! X ^ ι ¹) eqU' B'~A'))
                                  (sizeSubst-gen (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) size~↓!  B'~A' eqU')))
                (PE.sym (convConv↓TermSize (reflConEq ⊢Γ) A≡A' (ne neA') t~v))
                (leS (leS (<=-trans (<=-cong-+ (<=-trans sizeB~A' (<=-cong-+ (<=inv-suc sizeB~A) (le-refl _))) sizet~v) (<=-help-3-abcde {c = size~↓! x₅}))))

  trans~↑! {n = 1+ n} el Γ≡Δ (cast-refl' x x₁ x₂ (ne-ins x₃ x₁₀ x₁₁ ([~] A D whnfB t~u)) x₄) (cast-refl x₅ x₆ x₇ (ne-ins x₈ x₁₃ x₁₄ ([~] A' D' whnfB' u~v)) x₉) e =
    let X , t~v , A≡X , X≡B = trans~↑! {n = n} PE.refl Γ≡Δ t~u u~v {!!}
        _ , neu = ne~↑! t~u
        _ , _ , ⊢u = syntacticEqTerm (soundness~↑! t~u)
        _ , ⊢u' , _ = syntacticEqTerm (soundness~↑! u~v)
        _ , A₁≡A = neTypeEq neu x₂ ⊢u
        _ , A₁≡A' = neTypeEq neu x₂ (stabilityTerm (symConEq Γ≡Δ) ⊢u')
    in _ , t~v , trans A₁≡A A≡X , trans X≡B (trans (sym A₁≡A') (sym (univ (soundness~↓! x))))

  trans~↑! {n = 1+ n} el Γ≡Δ (castℕ-refl' x x₁) (castℕ-refl x₂ x₃) e =
    let X , wX , t~t , ℕ≡X , X≡ℕ = trans~↓! {n = n} PE.refl Γ≡Δ x x₂ {!!}
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        eqℕ = ℕ≡A ℕ≡X wX
        t~t' =  PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqℕ t~t
        [~] K D wK t~t'' = t~t'
    in _ , t~t'' , sym (subset* D) , subset* D
  trans~↑! {n = 1+ n} el Γ≡Δ (castℕ-refl' x x₁) (cast-ℕℕ x₂ x₃ x₄) e =
    let X , wX , t~t , ℕ≡X , X≡ℕ = trans~↓! {n = n} PE.refl Γ≡Δ x x₂ {!!}
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        eqℕ = ℕ≡A ℕ≡X wX
        t~t' =  PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqℕ t~t
    in _ , castℕ-refl' t~t' (stabilityTerm (symConEq Γ≡Δ) x₄) , refl (univ (ℕⱼ ⊢Γ) ) , refl (univ (ℕⱼ ⊢Γ) )
  trans~↑! {n = 1+ n} PE.refl Γ≡Δ (cast-neℕ x₁ x₂ x₃ x₄) (cast-neℕ x₅ x₆ x₇ x₈) e =
    let K , wK , XY , [U] , _  = trans~↓! {n = n} PE.refl Γ≡Δ x₁ x₅ {!!}
        eqU = U≡A-whnf [U] wK
        XY' = PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqU XY
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        t~t = transConv↑Term {n = n} Γ≡Δ (univ (soundness~↓! x₁)) x₂ x₆ {!!}
    in _ , cast-neℕ XY' t~t x₃ (stabilityTerm (symConEq Γ≡Δ) x₈) , refl (univ (ℕⱼ ⊢Γ)) , refl (univ (ℕⱼ ⊢Γ))

  trans~↑! {n = 1+ n} PE.refl Γ≡Δ (cast-neΠ x₁ x₂ x₃ x₄ x₅) (cast-neΠ x₆ x₇ x₈ x₉ x₁₀) e =
    let K , wK , XY , [U] , _  = trans~↓! {n = n} PE.refl Γ≡Δ x₂ x₇ {!!}
        eqU = U≡A-whnf [U] wK
        XY' = PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqU XY
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        Π~Π = transConv↑Term {n = n} Γ≡Δ (refl (Ugenⱼ ⊢Γ)) x₁ x₆ {!!}
        t~t = transConv↑Term {n = n} Γ≡Δ (univ (soundness~↓! x₂)) x₃ x₈ {!!}
        Π≡Π = soundnessConv↑Term x₁
    in _ , cast-neΠ Π~Π XY' t~t x₄ (stabilityTerm (symConEq Γ≡Δ) x₁₀) , refl (univ (proj₁ (proj₂ (syntacticEqTerm Π≡Π)))) , univ Π≡Π

  trans~↑! {n = 1+ n} el Γ≡Δ (cast-ℕℕ x₂ x₃ x₄) (castℕ-refl x x₁) e =
    let X , wX , t~t , ℕ≡X , X≡ℕ = trans~↓! {n = n} PE.refl Γ≡Δ x₂ x {!!}
        ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        eqℕ = ℕ≡A ℕ≡X wX
        t~t' =  PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ _) eqℕ t~t
    in _ , castℕ-refl t~t' x₃ , refl (univ (ℕⱼ ⊢Γ) ) , refl (univ (ℕⱼ ⊢Γ) )

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
  trans~↑! {n = 1+ n} el Γ≡Δ X Y = {!!}

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
  trans~↓! : ∀ {n t u v A B Γ Δ l l'}
          → l PE.≡ l'
          → ⊢ Γ ≡ Δ
          → (e : Γ ⊢ t ~ u ↓! A ^ l)
          → (e' : Δ ⊢ u ~ v ↓! B ^ l')
          → (size~↓! e + size~↓! e') << n
          → ∃ λ C → Whnf C × ∃ λ (e'' : Γ ⊢ t ~ v ↓! C ^ l) → Γ ⊢ A ≡ C ^ [ ! , l ] × Γ ⊢ C ≡ B ^ [ ! , l ] × size~↓! e'' <= (size~↓! e + size~↓! e')

  trans~↓! {n = 0} PE.refl Γ≡Δ ([~] A₁ D whnfA k~l) ([~] A₂ D₁ whnfA₁ k~l₁) ()
                   
  trans~↓! {n = 1+ n} PE.refl Γ≡Δ ([~] A₁ D whnfA k~l) ([~] A₂ D₁ whnfA₁ k~l₁) (leS e) =
   let leq = (<=-cong-+ (le-refl _) (le-suc (le-refl _)))
       C , t~v , A≡C , C≡B , size = trans~↑! {n = n} PE.refl Γ≡Δ k~l k~l₁ (<<bind leq e)
       ⊢C , _ = syntacticEq C≡B
       X , wX , DX = whNorm ⊢C
   in X , wX , [~] _ (red DX) wX t~v , trans (sym (subset* D)) (trans A≡C (subset* (red DX))) , trans (trans (sym (subset* (red DX))) C≡B) (subset* (stabilityRed* (symConEq Γ≡Δ) D₁)) , leS (<=-trans size leq)

  -- Transitivity of algorithmic equality of types.
  transConv↑ : ∀ {n A B C r Γ Δ}
            → ⊢ Γ ≡ Δ
            → (e : Γ ⊢ A [conv↑] B ^ r)
            → (e' : Δ ⊢ B [conv↑] C ^ r)
            → (sizeConv↑ e + sizeConv↑ e') << n
            → ∃ λ (e'' : Γ ⊢ A [conv↑] C ^ r) → sizeConv↑ e'' <= (sizeConv↑ e + sizeConv↑ e')

  transConv↑ {n = 0} _ _ _ ()
  
  transConv↑ {n = 1+ n} {r = r} Γ≡Δ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′)
             ([↑] A″ B″ D₁ D″ whnfA″ whnfB″ A′<>B″) (leS e) =
    let leq = <=-cong-+ (le-refl _ ) 
                        (le-suc (≡-to-<= (sizeSubst-gen (λ x → _ ⊢ x [conv↓] B″ ^ r)
                                                        sizeConv↓ A′<>B″ (whrDet* (D₁ , whnfA″)
                                                        (stabilityRed* Γ≡Δ D′ , whnfB′)))))
        A<>B , size = transConv↓ {n = n} Γ≡Δ A′<>B′
                                 (PE.subst (λ x → _ ⊢ x [conv↓] B″ ^ r)
                                   (whrDet* (D₁ , whnfA″) (stabilityRed* Γ≡Δ D′ , whnfB′))
                                 A′<>B″) (<<bind leq e)
    in [↑] A′ B″ D (stabilityRed* (symConEq Γ≡Δ) D″) whnfA′ whnfB″ A<>B ,
       leS (<=-trans size leq)
        

  -- Transitivity of algorithmic equality of types in WHNF.
  transConv↓ : ∀ {n A B C r Γ Δ}
            → ⊢ Γ ≡ Δ
            → (e : Γ ⊢ A [conv↓] B ^ r)
            → (e' : Δ ⊢ B [conv↓] C ^ r)
            → (sizeConv↓ e + sizeConv↓ e') << n
            → ∃ λ (e'' : Γ ⊢ A [conv↓] C ^ r) → sizeConv↓ e'' <= (sizeConv↓ e + sizeConv↓ e')

  transConv↓ {n = 0} _ _ _ ()
  
  transConv↓ Γ≡Δ (U-refl e x) (U-refl e₁ x₁) _ = U-refl (PE.trans e e₁) x , leS le0
  transConv↓ {n = 1+ n} Γ≡Δ (univ x) (univ y) (leS e) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        leq = <=-cong-+ (le-refl _) (le-suc (le-refl _))
        X , size = transConv↓Term {n = n} Γ≡Δ (refl (Ugenⱼ ⊢Γ )) PE.refl x y (<<bind leq e)
    in univ X , leS (<=-trans size leq)

  -- Transitivity of algorithmic equality of terms.
  transConv↑Term : ∀ {n t u v A B Γ Δ l l'}
                → l PE.≡ l'
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B ^ [ ! , l ]
                → (e : Γ ⊢ t [conv↑] u ∷ A ^ l)
                → (e' : Δ ⊢ u [conv↑] v ∷ B ^ l')
                → (sizeConv↑Term e + sizeConv↑Term e') << n
                → ∃ λ (e'' : Γ ⊢ t [conv↑] v ∷ A ^ l) → sizeConv↑Term e'' <= (sizeConv↑Term e + sizeConv↑Term e')
  transConv↑Term {n = 0} _ _ _ _ _ ()
  transConv↑Term {n = 1+ n} PE.refl Γ≡Δ A≡B ([↑]ₜ B₁ t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
                 ([↑]ₜ B₂ t″ u″ D₁ d₁ d″ whnfB₁ whnft″ whnfu″ t<>u₁) (leS e) =
    let B₁≡B₂ = trans (sym (subset* D))
                      (trans A≡B
                             (subset* (stabilityRed* (symConEq Γ≡Δ) D₁)))
        d₁″ = conv* (stabilityRed*Term (symConEq Γ≡Δ) d″) (sym B₁≡B₂)
        d₁′  = stabilityRed*Term Γ≡Δ (conv* d′ B₁≡B₂)
        eq = whrDet*Term (d₁ , whnft″) (d₁′ , whnfu′)
        leq = <=-cong-+ (le-refl _) (le-suc (≡-to-<= (sizeSubst-gen (λ x → _ ⊢ x [conv↓] u″ ∷ B₂ ^ _) sizeConv↓Term  t<>u₁ eq)))
        t<>v , sizet<>v = transConv↓Term {n = n} Γ≡Δ B₁≡B₂ PE.refl t<>u
                                         (PE.subst (λ x → _ ⊢ x [conv↓] u″ ∷ B₂ ^ _) eq t<>u₁)
                                         (<<bind leq e)
    in  [↑]ₜ B₁ t′ u″ D d d₁″ whnfB whnft′ whnfu″ t<>v ,
        leS (<=-trans sizet<>v leq)


  -- Transitivity of algorithmic equality of terms in WHNF.
  transConv↓Term : ∀ {n t u v A B Γ Δ l l'}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B ^ [ ! , l ]
                → l PE.≡ l'
                → (e : Γ ⊢ t [conv↓] u ∷ A ^ l)
                → (e' : Δ ⊢ u [conv↓] v ∷ B ^ l')
                → (sizeConv↓Term e + sizeConv↓Term e') << n
                → ∃ λ (e'' : Γ ⊢ t [conv↓] v ∷ A ^ l) → sizeConv↓Term e'' <= (sizeConv↓Term e + sizeConv↓Term e')

{-
  transConv↓Term {n = 0} _ _ _ _ _ () 

  transConv↓Term {1+ n} {t} {u} {v} {A} {B} {Γ} {Δ} {l} Γ≡Δ A≡B el (ne x) (ne x₁) (leS e) =
    let leq = leS (<=-cong-+ (le-refl _) (le-suc (le-refl _)))
        C , wC , x~x , A≡C , C≡B , size = trans~↓! {n = n} el Γ≡Δ x x₁ (<<bind leq e)
        eqU = U≡A-whnf A≡C wC
        x~x' = PE.subst (λ X →  Γ ⊢ t ~ v ↓! X ^ l) eqU x~x
    in ne x~x' , PE.subst (λ X → 1+ X <= 1+ (1+ (size~↑! (_⊢_~_↓!_^_.k~l x) + 1+ (size~↓! x₁))))
                          (PE.sym (sizeSubst-gen (λ X →  Γ ⊢ t ~ v ↓! X ^ l) size~↓! x~x eqU))
                          (leS (<=-trans size leq)) 
  transConv↓Term {1+ n} {t} {u} {v} {A} {B} {Γ} {Δ} {l} Γ≡Δ A≡B el (ℕ-ins x) (ℕ-ins x₁) (leS e) =
    let leq = leS (<=-cong-+ (le-refl _) (le-suc (le-refl _)))
        C , wC , x~x , A≡C , C≡B , size = trans~↓! {n = n}  PE.refl Γ≡Δ x x₁ (<<bind leq e)
        eqℕ = ℕ≡A A≡C wC
        x~x' = PE.subst (λ X →  Γ ⊢ t ~ v ↓! X ^ l) eqℕ x~x
    in ℕ-ins x~x' , PE.subst (λ X → 1+ X <= 1+ (1+ (size~↑! (_⊢_~_↓!_^_.k~l x) + 1+ (size~↓! x₁))))
                             (PE.sym (sizeSubst-gen (λ X →  Γ ⊢ t ~ v ↓! X ^ l) size~↓! x~x eqℕ))
                             (leS (<=-trans size leq))
  transConv↓Term {n = 1+ n} {Δ = Δ} Γ≡Δ A≡B el (ne-ins t u x x₁) (ne-ins {k} {l} {M} {N} t′ u′ x₂ x₃) (leS e) =
    let leq = leS (<=-cong-+ (le-refl _) (le-suc (le-refl _)))
        C , wC , x~x , A≡C , C≡B , size = trans~↓! {n = n} el Γ≡Δ x₁ x₃ (<<bind leq e)
    in ne-ins t (conv (stabilityTerm (symConEq Γ≡Δ) (PE.subst (λ lx → Δ ⊢ l ∷ N ^ [ ! , lx ]) (PE.sym el) u′))
                      (sym A≡B)) x
              x~x ,
       leS (<=-trans size leq)
  transConv↓Term Γ≡Δ A≡B el (zero-refl x) (zero-refl x₁) _ =
    zero-refl x , leS (le0)
  transConv↓Term {n = 1+ n} Γ≡Δ A≡B el (suc-cong x) (suc-cong x₁) (leS e) =
    let leq = leS (<=-cong-+ (le-refl _) (le-suc (le-refl _)))
        t~v , size = transConv↑Term {n = n} el Γ≡Δ A≡B x x₁ (<<bind leq e)
    in suc-cong t~v ,
       leS (<=-trans size leq)
  transConv↓Term {n = 1+ n} {Δ = Δ} Γ≡Δ A≡B el
                 (η-eq {rF = rF₁} l< l<' x x₁ x₂ y y₁ x₃)
                 (η-eq {u} {v} {F} {G} {rF} {lF} {lG} {l} l<'' l<''' x₄ x₅ x₆ y₂ y₃ x₇)
                 (leS e) =
    let F₁≡F , rF₁≡rF , lF₁≡lF , lG₁≡lG , G₁≡G = injectivity (PE.subst (λ lx → _ ⊢ _ ≡ Π _ ^ _ ° _ ▹ _ ° _ ° lx ^ _ ^ _) (ιinj (PE.sym el)) A≡B )
        lesubst = sizeSubst₃-gen (λ lx lx' rx → Δ ∙ F ^ [ rx , lx' ] ⊢  wk1 u ∘ var 0 ^ lx [conv↑] wk1 v ∘ var 0 ^ lx ∷ G ^ ι lG)
                                sizeConv↑Term x₇ (PE.sym (ιinj el)) (PE.sym (PE.cong ι lF₁≡lF)) (PE.sym rF₁≡rF)
        leq = leS (<=-cong-+ (le-refl (sizeConv↓Term (_⊢_[conv↑]_∷_^_.t<>u x₃)))
                             (le-suc (≡-to-<= lesubst)))
        t~v , size = transConv↑Term {n = n} (PE.cong ι lG₁≡lG) (Γ≡Δ ∙ F₁≡F) G₁≡G x₃ 
                                  (PE.subst₃ (λ lx lx' rx → Δ ∙ F ^ [ rx , lx' ] ⊢  wk1 u ∘ var 0 ^ lx [conv↑] wk1 v ∘ var 0 ^ lx ∷ G ^ ι lG)
                                             (PE.sym (ιinj el))
                                             (PE.sym (PE.cong ι lF₁≡lF))
                                             (PE.sym rF₁≡rF) x₇)
                                  (<<bind leq e)
    in η-eq l< l<' x x₁ (conv (stabilityTerm (symConEq Γ≡Δ)
                                           (PE.subst (λ lx → Δ ⊢ v ∷ Π F ^ rF ° lF ▹ G ° lG ° l ^ ! ^ [ ! , lx ]) (PE.sym el) x₆))
                            (sym A≡B))
             y y₃ t~v ,
       leS (<=-trans size leq)
  transConv↓Term Γ≡Δ A≡B el (ℕ-refl x) (ℕ-refl x₁) _ = ℕ-refl x , leS le0
  transConv↓Term Γ≡Δ A≡B el (Empty-refl x) (Empty-refl x₁) _ = Empty-refl x , leS le0
  transConv↓Term Γ≡Δ A≡B el (U-refl e x) (U-refl e₁ x₁) _ = U-refl (PE.trans e e₁) x , leS le0
  transConv↓Term {n = 1+ n} Γ≡Δ A≡B el
                 (Π-cong PE.refl PE.refl PE.refl PE.refl l< l<' x₅ x₆ x₇)
                 (Π-cong PE.refl PE.refl PE.refl PE.refl x₁₁ x₁₂ x₁₃ x₁₄ x₁₅) (leS e) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        rF≡rF₁ , _ = Uinjectivity A≡B
        F~F , sizeF = transConv↑Term {n = n} PE.refl Γ≡Δ (refl (Ugenⱼ ⊢Γ )) x₆ x₁₄
                                     (<<bind (leS (<=-help-ab' {b = sizeConv↑Term x₁₄})) e)
        G~G , sizeG = transConv↑Term {n = n} PE.refl (Γ≡Δ ∙ univ (soundnessConv↑Term x₆))
                              (refl (Ugenⱼ (⊢Γ ∙ x₅))) x₇ x₁₅
                              (<<bind (leS (<=-help-ab'' {c = 1+ (1+ (sizeConv↓Term (_⊢_[conv↑]_∷_^_.t<>u x₁₄)))})) e)
    in Π-cong PE.refl PE.refl PE.refl PE.refl l< l<' x₅
              F~F
              G~G ,
       leS (<=-trans (<=-cong-+ sizeF sizeG) (leS (<=-help-3-abcd {b = sizeConv↑Term x₁₄} {c = sizeConv↑Term x₇}))) 
  transConv↓Term {n = 1+ n} Γ≡Δ A≡B el (∃-cong x₅ x₆ x₇) (∃-cong x₁₃ x₁₄ x₁₅) (leS e) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        rF≡rF₁ , _ = Uinjectivity A≡B
        F~F , sizeF = transConv↑Term {n = n} PE.refl Γ≡Δ (refl (Ugenⱼ ⊢Γ )) x₆ x₁₄
                                     (<<bind (leS (<=-help-ab' {b = sizeConv↑Term x₁₄})) e)
        G~G , sizeG = transConv↑Term {n = n} PE.refl (Γ≡Δ ∙ univ (soundnessConv↑Term x₆)) (refl (Ugenⱼ (⊢Γ ∙ x₅))) x₇ x₁₅
                                     (<<bind (leS (<=-help-ab'' {c = 1+ (1+ (sizeConv↓Term (_⊢_[conv↑]_∷_^_.t<>u x₁₄)))})) e)
    in ∃-cong x₅ F~F G~G ,
       leS (<=-trans (<=-cong-+ sizeF sizeG) (leS (<=-help-3-abcd {b = sizeConv↑Term x₁₄} {c = sizeConv↑Term x₇}))) 
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

  transConv↓Term Γ≡Δ A≡B el (ne x) (U-refl x₁ x₂) with ne~↓! x
  transConv↓Term Γ≡Δ A≡B el (ne x) (U-refl x₁ x₂) | _ , _ , ()
  transConv↓Term Γ≡Δ A≡B el (ne x) (ℕ-refl x₁) with ne~↓! x
  transConv↓Term Γ≡Δ A≡B el (ne x) (ℕ-refl x₁) | _ , _ , ()
  transConv↓Term Γ≡Δ A≡B el (ne x) (Empty-refl x₁) with ne~↓! x
  transConv↓Term Γ≡Δ A≡B el (ne x) (Empty-refl x₁) | _ , _ , ()
  transConv↓Term Γ≡Δ A≡B el (ne x) (Π-cong x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉) with ne~↓! x
  transConv↓Term Γ≡Δ A≡B el (ne x) (Π-cong x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉) | _ , _ , ()
  transConv↓Term Γ≡Δ A≡B el (ne x) (∃-cong x₁ x₂ x₃) with ne~↓! x
  transConv↓Term Γ≡Δ A≡B el (ne x) (∃-cong x₁ x₂ x₃) | _ , _ , ()
  transConv↓Term Γ≡Δ A≡B el (ne x) (zero-refl x₁) = ⊥-elim (WF.U≢ℕ! A≡B)
  transConv↓Term Γ≡Δ A≡B el (ne x) (suc-cong x₁) = ⊥-elim (WF.U≢ℕ! A≡B)
  transConv↓Term Γ≡Δ A≡B el (ℕ-refl x) (ne x₁) with ne~↓! x₁
  transConv↓Term Γ≡Δ A≡B el (ℕ-refl x) (ne x₁) | _ , () , _
  transConv↓Term Γ≡Δ A≡B el (ℕ-refl x) (ne-ins x₁ x₂ x₃ x₄) with ne~↓! x₄
  transConv↓Term Γ≡Δ A≡B el (ℕ-refl x) (ne-ins x₁ x₂ x₃ x₄) | _ , () , _
  transConv↓Term Γ≡Δ A≡B el (Empty-refl x) (ne x₁) with ne~↓! x₁
  transConv↓Term Γ≡Δ A≡B el (Empty-refl x) (ne x₁) | _ , () , _
  transConv↓Term Γ≡Δ A≡B el (Empty-refl x) (ne-ins x₁ x₂ x₃ x₄) with ne~↓! x₄
  transConv↓Term Γ≡Δ A≡B el (Empty-refl x) (ne-ins x₁ x₂ x₃ x₄) | _ , () , _
  transConv↓Term Γ≡Δ A≡B el (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) (ne x₉) with ne~↓! x₉
  transConv↓Term Γ≡Δ A≡B el (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) (ne x₉) | _ , () , _
  transConv↓Term Γ≡Δ A≡B el (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) (ℕ-ins x₉) = ⊥-elim (WF.U≢ℕ! A≡B)
  transConv↓Term Γ≡Δ A≡B el (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) (ne-ins x₉ x₁₀ x₁₁ x₁₂) with ne~↓! x₁₂
  transConv↓Term Γ≡Δ A≡B el (Π-cong x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈) (ne-ins x₉ x₁₀ x₁₁ x₁₂) | _ , () , _
  transConv↓Term Γ≡Δ A≡B el (∃-cong x x₁ x₂) (ne x₃) with ne~↓! x₃
  transConv↓Term Γ≡Δ A≡B el (∃-cong x x₁ x₂) (ne x₃) | _ , () , _
  transConv↓Term Γ≡Δ A≡B el (∃-cong x x₁ x₂) (ne-ins x₃ x₄ x₅ x₆) with ne~↓! x₆
  transConv↓Term Γ≡Δ A≡B el (∃-cong x x₁ x₂) (ne-ins x₃ x₄ x₅ x₆) | _ , () , _
  transConv↓Term Γ≡Δ A≡B el (ℕ-ins x) (Π-cong x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉) = ⊥-elim (WF.U≢ℕ! (sym A≡B))
  transConv↓Term Γ≡Δ A≡B el (ℕ-ins x) (zero-refl x₁) with ne~↓! x
  transConv↓Term Γ≡Δ A≡B el (ℕ-ins x) (zero-refl x₁) | _ , _ , ()
  transConv↓Term Γ≡Δ A≡B el (ℕ-ins x) (suc-cong x₁) with ne~↓! x
  transConv↓Term Γ≡Δ A≡B el (ℕ-ins x) (suc-cong x₁) | _ , _ , ()
  transConv↓Term Γ≡Δ A≡B el (ne-ins x x₁ x₂ x₃) (ℕ-refl x₄) with ne~↓! x₃
  transConv↓Term Γ≡Δ A≡B el (ne-ins x x₁ x₂ x₃) (ℕ-refl x₄) | _ , _ , ()
  transConv↓Term Γ≡Δ A≡B el (ne-ins x x₁ x₂ x₃) (Empty-refl x₄) with ne~↓! x₃
  transConv↓Term Γ≡Δ A≡B el (ne-ins x x₁ x₂ x₃) (Empty-refl x₄) | _ , _ , () 
  transConv↓Term Γ≡Δ A≡B el (ne-ins x x₁ x₂ x₃) (Π-cong x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂) with ne~↓! x₃
  transConv↓Term Γ≡Δ A≡B el (ne-ins x x₁ x₂ x₃) (Π-cong x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂) | _ , _ , () 
  transConv↓Term Γ≡Δ A≡B el (ne-ins x x₁ x₂ x₃) (∃-cong x₄ x₅ x₆) with ne~↓! x₃
  transConv↓Term Γ≡Δ A≡B el (ne-ins x x₁ x₂ x₃) (∃-cong x₄ x₅ x₆) | _ , _ , () 
  transConv↓Term Γ≡Δ A≡B el (ne-ins x x₁ x₂ x₃) (zero-refl x₄) with ne~↓! x₃ 
  transConv↓Term Γ≡Δ A≡B el (ne-ins x x₁ x₂ x₃) (zero-refl x₄) | _ , _ , () 
  transConv↓Term Γ≡Δ A≡B el (ne-ins x x₁ x₂ x₃) (suc-cong x₄) with ne~↓! x₃
  transConv↓Term Γ≡Δ A≡B el (ne-ins x x₁ x₂ x₃) (suc-cong x₄) | _ , _ , ()
  transConv↓Term Γ≡Δ A≡B el (zero-refl x) (ne x₁) with ne~↓! x₁
  transConv↓Term Γ≡Δ A≡B el (zero-refl x) (ne x₁) | _ , () , _
  transConv↓Term Γ≡Δ A≡B el (zero-refl x) (ℕ-ins x₁) with ne~↓! x₁
  transConv↓Term Γ≡Δ A≡B el (zero-refl x) (ℕ-ins x₁) | _ , () , _
  transConv↓Term Γ≡Δ A≡B el (zero-refl x) (ne-ins x₁ x₂ x₃ x₄) with ne~↓! x₄
  transConv↓Term Γ≡Δ A≡B el (zero-refl x) (ne-ins x₁ x₂ x₃ x₄) | _ , () , _
  transConv↓Term Γ≡Δ A≡B el (suc-cong x) (ne x₁) with ne~↓! x₁
  transConv↓Term Γ≡Δ A≡B el (suc-cong x) (ne x₁) | _ , () , _
  transConv↓Term Γ≡Δ A≡B el (suc-cong x) (ℕ-ins x₁) with ne~↓! x₁
  transConv↓Term Γ≡Δ A≡B el (suc-cong x) (ℕ-ins x₁) | _ , () , _
  transConv↓Term Γ≡Δ A≡B el (suc-cong x) (ne-ins x₁ x₂ x₃ x₄) with ne~↓! x₄
  transConv↓Term Γ≡Δ A≡B el (suc-cong x) (ne-ins x₁ x₂ x₃ x₄) | _ , () , _
  transConv↓Term Γ≡Δ A≡B el (U-refl x x₁) (ne x₂) with ne~↓! x₂
  transConv↓Term Γ≡Δ A≡B el (U-refl x x₁) (ne x₂) | _ , () , _
-}
  transConv↓Term = {!!}


-- Transitivity of algorithmic equality of types of the same context.
transConv : ∀ {A B C r Γ}
          → Γ ⊢ A [conv↑] B ^ r
          → Γ ⊢ B [conv↑] C ^ r
          → Γ ⊢ A [conv↑] C ^ r
transConv A<>B B<>C =
  let Γ≡Γ = reflConEq (wfEq (soundnessConv↑ A<>B))
  in  proj₁ (transConv↑ Γ≡Γ A<>B B<>C (le-refl _))

-- Transitivity of algorithmic equality of terms of the same context.
transConvTerm : ∀ {t u v A Γ l}
              → Γ ⊢ t [conv↑] u ∷ A ^ l
              → Γ ⊢ u [conv↑] v ∷ A ^ l
              → Γ ⊢ t [conv↑] v ∷ A ^ l
transConvTerm t<>u u<>v =
  let t≡u = soundnessConv↑Term t<>u
      Γ≡Γ = reflConEq (wfEqTerm t≡u)
      ⊢A , _ , _ = syntacticEqTerm t≡u
  in proj₁ (transConv↑Term PE.refl Γ≡Γ (refl ⊢A) t<>u u<>v (le-refl _))

trans~↑!Term : ∀ {t u v A Γ l}
              → Γ ⊢ t ~ u ↑% A ^ l
              → Γ ⊢ u ~ v ↑% A ^ l
              → Γ ⊢ t ~ v ↑% A ^ l
trans~↑!Term t<>u u<>v =
  let _ , _ , t≡u = soundness~↑% t<>u
      Γ≡Γ = reflConEq (wfEqTerm t≡u)
  in  trans~↑% Γ≡Γ t<>u u<>v
