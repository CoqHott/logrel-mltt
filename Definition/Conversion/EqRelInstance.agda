{-# OPTIONS --safe #-}

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
open import Definition.Conversion.Symmetry

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Function


-- Algorithmic equality of neutrals with injected conversion.
data _⊢_~_∷_^_ (Γ : Con Term) (k l A : Term) (r : TypeInfo) : Set where
  ↑ : ∀ {B} → Γ ⊢ A ≡ B ^ r → Γ ⊢ k ~ l ↑ B ^ r → Γ ⊢ k ~ l ∷ A ^ r

-- Properties of algorithmic equality of neutrals with injected conversion.

~-var : ∀ {x A r Γ} → Γ ⊢ var x ∷ A ^ r → Γ ⊢ var x ~ var x ∷ A ^ r
~-var x =
  let ⊢A = syntacticTerm x
  in  ↑ (refl ⊢A) (var-refl′ x)

~-app : ∀ {f g a b F G Γ rF lF lG lΠ}
      → Γ ⊢ f ~ g ∷ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ [ ! , ι lΠ ]
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
      Γ ⊢ s [conv↑] s′ ∷ (Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° lF ▹▹ F [ suc (var 0) ]↑ ° lF ° lF) ° lF ° lF) ^ ι lF →
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


~-Emptyrec : ∀ {e e' F F′ Γ l lEmpty}
         → Γ ⊢ F [conv↑] F′ ^ [ ! , l ] →
         Γ ⊢ e ∷ Empty lEmpty ^ [ % , ι lEmpty ] →
         Γ ⊢ e' ∷ Empty lEmpty ^ [ % , ι lEmpty ] →
         Γ ⊢ Emptyrec lEmpty F e ~ Emptyrec lEmpty F′ e' ∷ F ^ [ ! , l ]
~-Emptyrec {e = e} {e' = e'} x ⊢e ⊢e' =
  let k~l′ = %~↑ ⊢e ⊢e' 
      ⊢F , _ = syntacticEq (soundnessConv↑ x)
  in  ↑ (refl ⊢F) (Emptyrec-cong′ x k~l′)

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
      k~m , _ = trans~↑! PE.refl (reflConEq ⊢Γ) x₁ x₃
  in  ↑ x (~↑! k~m)
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
        → lF ≤ lΠ
        → lG ≤ lΠ
        → Γ ⊢ F ^ [ rF , ι lF ]
        → Γ ⊢ F [conv↑] H ∷ Univ rF lF ^ next lF
        → Γ ∙ F ^ [ rF , ι lF ] ⊢ G [conv↑] E ∷ Univ rG lG ^ next lG
        → Γ ⊢ Π F ^ rF ° lF ▹ G ° lG ° lΠ [conv↑] Π H ^ rF ° lF ▹ E ° lG ° lΠ ∷ Univ rG lΠ ^ next lΠ
Πₜ-cong lF< lG< x x₁ x₂ = liftConvTerm (Π-cong PE.refl PE.refl PE.refl lF< lG< x x₁ x₂) 
  -- let _ , F∷U , H∷U = syntacticEqTerm (soundnessConv↑Term x₁)
  --     _ , G∷U , E∷U = syntacticEqTerm (soundnessConv↑Term x₂)
  --     ⊢Γ = wfTerm F∷U
  --     F<>H = univConv↑ x₁
  --     G<>E = univConv↑ x₂
  --     F≡H = soundnessConv↑ F<>H
  --     E∷U′ = stabilityTerm (reflConEq ⊢Γ ∙ F≡H) E∷U
      -- in liftConvTerm (Π-cong PE.refl PE.refl PE.refl lF< lG< x x₁ x₂) 
      -- liftConvTerm (univ (Πⱼ l<F ▹ l<G ▹ F∷U ▹ G∷U) (Πⱼ l<H ▹ l<E ▹ H∷U ▹ E∷U′)
      --                       (Π-cong PE.refl x F<>H G<>E))

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
                      -- (λ x → liftConvTerm (univ (ℕⱼ x) (ℕⱼ x) (ℕ-refl x)))
                      (liftConvTerm ∘ᶠ Empty-refl)
                      -- (λ x → liftConvTerm (univ (Emptyⱼ x) (Emptyⱼ x) (Empty-refl x)))
                      -- (λ x x₁ x₂ → liftConvTerm (Π-cong PE.refl x x₁ x₂))
                      Πₜ-cong
                      (λ x x₁ x₂ → liftConvTerm (∃-cong x x₁ x₂))
                      (liftConvTerm ∘ᶠ zero-refl)
                      (liftConvTerm ∘ᶠ suc-cong)
                      (λ l< l<' x x₁ x₂ x₃ x₄ x₅ → liftConvTerm (η-eq l< l<' x x₁ x₂ x₃ x₄ x₅))
                      ~-var ~-app ~-natrec ~-Emptyrec
                      {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!}
                      ~-irrelevance
