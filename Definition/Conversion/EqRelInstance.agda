{-# OPTIONS --without-K  #-}

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
open import Definition.Conversion.Symmetry
open import Definition.Conversion.Transitivity
open import Definition.Conversion.Weakening
open import Definition.Conversion.Whnf
open import Definition.Typed.EqualityRelation
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.Equality
open import Definition.Typed.Consequences.Reduction

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Function


-- Algorithmic equality of neutrals with injected conversion.
data _⊢_~_∷_⦂_ (Γ : Con Term) (k l A : Term) (s : 𝕊) : Set where
  ↑ : ∀ {B} → Γ ⊢ A ≡ B ⦂ s → Γ ⊢ k ~ l ↑ B ⦂ s → Γ ⊢ k ~ l ∷ A ⦂ s

-- Properties of algorithmic equality of neutrals with injected conversion.

~-var : ∀ {x A s Γ} → Γ ⊢ var x ∷ A ⦂ s → Γ ⊢ var x ~ var x ∷ A ⦂ s
~-var x =
  let ⊢A = syntacticTerm x
  in  ↑ (refl ⊢A) (var-refl′ x)

~-app : ∀ {f g a b F sF G sG Γ}
      → Γ ⊢ f ~ g ∷ Π F ⦂ sF ▹ G ⦂ sG
      → Γ ⊢ a [conv↑] b ∷ F ⦂ sF
      → Γ ⊢ f ∘ a ~ g ∘ b ∷ G [ a ] ⦂ sG
~-app (↑ A≡B x) x₁ =
  let _ , ⊢B = syntacticEq A≡B
      B′ , whnfB′ , D = whNorm ⊢B
      ΠFG≡B′ = trans A≡B (subset* (red D))
      H , E , B≡ΠHE = Π≡A ΠFG≡B′ whnfB′
      F≡H , _ , G≡E = injectivity (PE.subst (λ x → _ ⊢ _ ≡ x ⦂ _) B≡ΠHE ΠFG≡B′)
      _ , ⊢f , _ = syntacticEqTerm (soundnessConv↑Term x₁)
  in  ↑ (substTypeEq G≡E (refl ⊢f))
        (app-cong′ (PE.subst (λ x → _ ⊢ _ ~ _ ↓ x ⦂ _)
                       B≡ΠHE ([~]′ _ (red D) whnfB′ x))
             (convConvTerm x₁ F≡H))

~-natrec : ∀ {z z′ s s′ n n′ F F′ sF Γ}
         → (Γ ∙ ℕ ⦂ 𝕥y) ⊢ F [conv↑] F′ ⦂ sF →
      Γ ⊢ z [conv↑] z′ ∷ (F [ zero ]) ⦂ sF →
      Γ ⊢ s [conv↑] s′ ∷ (Π ℕ ⦂ 𝕥y ▹ (F ⦂ sF ▹▹ F [ suc (var 0) ]↑)) ⦂ sF →
      Γ ⊢ n ~ n′ ∷ ℕ ⦂ 𝕥y →
      Γ ⊢ natrec F z s n ~ natrec F′ z′ s′ n′ ∷ (F [ n ]) ⦂ sF
~-natrec x x₁ x₂ (↑ A≡B x₄) =
  let _ , ⊢B = syntacticEq A≡B
      B′ , whnfB′ , D = whNorm ⊢B
      ℕ≡B′ = trans A≡B (subset* (red D))
      B≡ℕ = ℕ≡A ℕ≡B′ whnfB′
      k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x  ⦂ _) B≡ℕ
                      ([~]′ _ (red D) whnfB′ x₄)
      ⊢F , _ = syntacticEq (soundnessConv↑ x)
      _ , ⊢n , _ = syntacticEqTerm (soundness~↓ k~l′)
  in  ↑ (refl (substType ⊢F ⊢n)) (natrec-cong′ x x₁ x₂ k~l′)

~-Emptyrec : ∀ {n n′ F F′ sF Γ}
         → Γ ⊢ F [conv↑] F′ ⦂ sF →
      Γ ⊢ n ~ n′ ∷ Empty ⦂ 𝕥y →
      Γ ⊢ Emptyrec F n ~ Emptyrec F′ n′ ∷ F ⦂ sF
~-Emptyrec x (↑ A≡B x₄) =
  let _ , ⊢B = syntacticEq A≡B
      B′ , whnfB′ , D = whNorm ⊢B
      Empty≡B′ = trans A≡B (subset* (red D))
      B≡Empty = Empty≡A Empty≡B′ whnfB′
      k~l′ = PE.subst (λ x → _ ⊢ _ ~ _ ↓ x ⦂ _) B≡Empty
                      ([~]′ _ (red D) whnfB′ x₄)
      ⊢F , _ = syntacticEq (soundnessConv↑ x)
      _ , ⊢n , _ = syntacticEqTerm (soundness~↓ k~l′)
  in  ↑ (refl ⊢F) (Emptyrec-cong′ x k~l′)

~-sym : {k l A : Term} {s : 𝕊} {Γ : Con Term} → Γ ⊢ k ~ l ∷ A ⦂ s → Γ ⊢ l ~ k ∷ A ⦂ s
~-sym (↑ A≡B x) =
  let ⊢Γ = wfEq A≡B
      B , A≡B′ , l~k = sym~↑ (reflConEq ⊢Γ) x
  in  ↑ (trans A≡B A≡B′) l~k

~-trans : {k l m A : Term} {s : 𝕊} {Γ : Con Term}
        → Γ ⊢ k ~ l ∷ A ⦂ s → Γ ⊢ l ~ m ∷ A ⦂ s
        → Γ ⊢ k ~ m ∷ A ⦂ s
~-trans (↑ x x₁) (↑ x₂ x₃) =
  let ⊢Γ = wfEq x
      k~m , _ = trans~↑ (reflConEq ⊢Γ) x₁ x₃
  in  ↑ x k~m

~-wk : {k l A : Term} {s : 𝕊} {ρ : Wk} {Γ Δ : Con Term} →
      ρ ∷ Δ ⊆ Γ →
      ⊢ Δ → Γ ⊢ k ~ l ∷ A ⦂ s → Δ ⊢ wk ρ k ~ wk ρ l ∷ wk ρ A ⦂ s
~-wk x x₁ (↑ x₂ x₃) = ↑ (wkEq x x₁ x₂) (wk~↑ x x₁ x₃)

~-conv : {k l A B : Term} {s : 𝕊} {Γ : Con Term} →
      Γ ⊢ k ~ l ∷ A ⦂ s → Γ ⊢ A ≡ B ⦂ s → Γ ⊢ k ~ l ∷ B ⦂ s
~-conv (↑ x x₁) x₂ = ↑ (trans (sym x₂) x) x₁

~-to-conv : {k l A : Term} {s : 𝕊} {Γ : Con Term} →
      Γ ⊢ k ~ l ∷ A ⦂ s → Γ ⊢ k [conv↑] l ∷ A ⦂ s
~-to-conv (↑ x x₁) = convConvTerm (lift~toConv↑ x₁) (sym x)

Πₜ-cong : ∀ {F G H E sF sG Γ}
        → Γ ⊢ F ⦂ sF
        → Γ ⊢ F [conv↑] H ∷ (Univ sF) ⦂ 𝕥y
        → Γ ∙ F ⦂ sF ⊢ G [conv↑] E ∷ (Univ sG) ⦂ 𝕥y
        → Γ ⊢ Π F ⦂ sF ▹ G [conv↑] Π H ⦂ sF ▹ E ∷ (Univ sG) ⦂ 𝕥y
Πₜ-cong x x₁ x₂ =
  let _ , F∷U , H∷U = syntacticEqTerm (soundnessConv↑Term x₁)
      _ , G∷U , E∷U = syntacticEqTerm (soundnessConv↑Term x₂)
      ⊢Γ = wfTerm F∷U
      F<>H = univConv↑ x₁
      G<>E = univConv↑ x₂
      F≡H = soundnessConv↑ F<>H
      E∷U′ = stabilityTerm (reflConEq ⊢Γ ∙ F≡H) E∷U
      in  liftConvTerm (univ (Πⱼ F∷U ▹ G∷U) (Πⱼ H∷U ▹ E∷U′)
                       (Π-cong PE.refl x F<>H G<>E))

~-irrelevance : {k l A : Term} {Γ : Con Term}
               → Γ ⊢ k ∷ A ⦂ 𝕥y
               → Γ ⊢ l ∷ A ⦂ 𝕥y
               → Γ ⊢ k ~ k ∷ A ⦂ 𝕥y
               → Γ ⊢ l ~ l ∷ A ⦂ 𝕥y
               → Γ ⊢ k ~ l ∷ A ⦂ 𝕥y
~-irrelevance ⊢k ⊢l (↑ A≡B (~↑𝕥y (𝕥y~↑ neN _ _ _))) (↑ A≡C (~↑𝕥y (𝕥y~↑ neL _ _ _))) =
  ↑ (trans A≡B (sym A≡B)) (~↑𝕥y (𝕥y~↑ neN neL ⊢k ⊢l))

-- Algorithmic equality instance of the generic equality relation.
instance eqRelInstance : EqRelSet
eqRelInstance = eqRel _⊢_[conv↑]_⦂_ _⊢_[conv↑]_∷_⦂_ _⊢_~_∷_⦂_
                      ~-to-conv soundnessConv↑ soundnessConv↑Term
                      univConv↑
                      symConv symConvTerm ~-sym
                      transConv transConvTerm ~-trans
                      convConvTerm ~-conv
                      wkConv↑ wkConv↑Term ~-wk
                      reductionConv↑ reductionConv↑Term
                      (liftConv ∘ᶠ (U-refl PE.refl))
                      (liftConv ∘ᶠ ℕ-refl)
                      (λ x → liftConvTerm (univ (ℕⱼ x) (ℕⱼ x) (ℕ-refl x)))
                      (liftConv ∘ᶠ Empty-refl)
                      (λ x → liftConvTerm (univ (Emptyⱼ x) (Emptyⱼ x) (Empty-refl x)))
                      (λ x x₁ x₂ → liftConv (Π-cong PE.refl x x₁ x₂))
                      Πₜ-cong
                      (liftConvTerm ∘ᶠ zero-refl)
                      (liftConvTerm ∘ᶠ suc-cong)
                      (λ x x₁ x₂ x₃ x₄ x₅ → liftConvTerm (η-eq x x₁ x₂ x₃ x₄ x₅))
                      ~-var ~-app ~-natrec ~-Emptyrec
                      ~-irrelevance
