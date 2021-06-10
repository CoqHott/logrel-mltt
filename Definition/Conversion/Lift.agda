{-# OPTIONS --without-K  #-}

module Definition.Conversion.Lift where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.Typed.EqRelInstance
open import Definition.Conversion
open import Definition.Conversion.Whnf
open import Definition.Conversion.Soundness
open import Definition.Conversion.Reduction
open import Definition.Conversion.Weakening
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Fundamental.Reducibility
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Reduction

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Lifting of algorithmic equality of types from WHNF to generic types.
liftConv : ∀ {A B sA Γ}
          → Γ ⊢ A [conv↓] B ⦂ sA
          → Γ ⊢ A [conv↑] B ⦂ sA
liftConv A<>B =
  let ⊢A , ⊢B = syntacticEq (soundnessConv↓ A<>B)
      whnfA , whnfB = whnfConv↓ A<>B
  in  [↑] _ _ (id ⊢A) (id ⊢B) whnfA whnfB A<>B

-- Lifting of algorithmic equality of terms from WHNF to generic terms.
liftConvTerm : ∀ {t u A sA Γ}
             → Γ ⊢ t [conv↓] u ∷ A ⦂ sA
             → Γ ⊢ t [conv↑] u ∷ A ⦂ sA
liftConvTerm t<>u =
  let ⊢A , ⊢t , ⊢u = syntacticEqTerm (soundnessConv↓Term t<>u)
      whnfA , whnfT , whnfU = whnfConv↓Term t<>u
  in  [↑]ₜ _ _ _ (id ⊢A) (id ⊢t) (id ⊢u) whnfA whnfT whnfU t<>u


mutual
  -- Helper function for lifting from neutrals to generic terms in WHNF.
  lift~toConv↓𝕥y′ : ∀ {t u A A′ Γ l}
                → Γ ⊩⟨ l ⟩ A′ ⦂ 𝕥y
                → Γ ⊢ A′ ⇒* A ⦂ 𝕥y
                → Γ ⊢ t ~ u ↓𝕥y A
                → Γ ⊢ t [conv↓] u ∷ A ⦂ 𝕥y
  lift~toConv↓𝕥y′ (Uᵣ′ _ .⁰ 0<1 ⊢Γ) D ([~] A D₁ whnfB k~l)
                rewrite PE.sym (whnfRed* D Uₙ) =
    let _ , ⊢t , ⊢u = syntacticEqTerm (conv (soundness~↑𝕥y k~l) (subset* D₁))
    in  univ ⊢t ⊢u (ne ([~] A D₁ Uₙ k~l))
  lift~toConv↓𝕥y′ (ℕᵣ D) D₁ ([~] A D₂ whnfB k~l)
                rewrite PE.sym (whrDet* (red D , ℕₙ) (D₁ , whnfB)) =
    ℕ-ins ([~] A D₂ ℕₙ k~l)
  lift~toConv↓𝕥y′ (ne′ K D neK K≡K) D₁ ([~] A D₂ whnfB k~l)
                rewrite PE.sym (whrDet* (red D , ne neK) (D₁ , whnfB)) =
    let _ , ⊢t , ⊢u = syntacticEqTerm (soundness~↑𝕥y k~l)
        A≡K = subset* D₂
    in  ne-ins (conv ⊢t A≡K) (conv ⊢u A≡K) neK (~↓𝕥y ([~] A D₂ (ne neK) k~l))
  lift~toConv↓𝕥y′ (Πᵣ′ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext) D₁ ([~] A D₂ whnfB k~l) with PE.sym (whrDet* (red D , Πₙ) (D₁ , whnfB))
  lift~toConv↓𝕥y′ (Πᵣ′ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext) D₁ ([~] A D₂ whnfB k~l) | PE.refl =
    let ⊢ΠFG , ⊢t , ⊢u = syntacticEqTerm (soundness~↓𝕥y ([~] A D₂ Πₙ k~l))
        neT , neU = ne~↑𝕥y k~l
        ⊢Γ = wf ⊢F
        var0 = neuTerm ([F] (step id) (⊢Γ ∙ ⊢F)) (var 0) (var (⊢Γ ∙ ⊢F) here)
                       (refl (var (⊢Γ ∙ ⊢F) here))
        0≡0 = lift~toConv↑′ ([F] (step id) (⊢Γ ∙ ⊢F)) (var-refl′ (var (⊢Γ ∙ ⊢F) here))
        k∘0≡l∘0 = lift~toConv↑′ ([G] (step id) (⊢Γ ∙ ⊢F) var0)
                                (~↑𝕥y (app-cong (wk~↓𝕥y (step id) (⊢Γ ∙ ⊢F) ([~] A D₂ Πₙ k~l)) 0≡0))
    in  η-eq ⊢F ⊢t ⊢u (ne neT) (ne neU)
             (PE.subst (λ x → _ ⊢ _ [conv↑] _ ∷ x ⦂ _)
                       (wkSingleSubstId _)
                       k∘0≡l∘0)
  lift~toConv↓𝕥y′ (emb 0<1 [A]) D t~u = lift~toConv↓𝕥y′ [A] D t~u

  lift~toConv↓𝕥y′ : ∀ {t u A A′ Γ l}
                → Γ ⊩⟨ l ⟩ A′ ⦂ 𝕥y
                → Γ ⊢ A′ ⇒* A ⦂ 𝕥y
                → Γ ⊢ t ~ u ↓𝕥y A
                → Γ ⊢ t [conv↓] u ∷ A ⦂ 𝕥y

  lift~toConv↓𝕥y′ (Emptyᵣ D) D₁ ([~] A D₂ whnfB k~l)
                rewrite PE.sym (whrDet* (red D , Emptyₙ) (D₁ , whnfB)) =
    Empty-ins ([~] A D₂ Emptyₙ k~l)
  lift~toConv↓𝕥y′ (ne′ K D neK K≡K) D₁ ([~] A D₂ whnfB k~l)
                rewrite PE.sym (whrDet* (red D , ne neK) (D₁ , whnfB)) =
    let _ , ⊢t , ⊢u = syntacticEqTerm (soundness~↑𝕥y k~l)
        A≡K = subset* D₂
    in  ne-ins (conv ⊢t A≡K) (conv ⊢u A≡K) neK (~↓𝕥y ([~] A D₂ (ne neK) k~l))
  lift~toConv↓𝕥y′ (Πᵣ′ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext) D₁ ([~] A D₂ whnfB k~l) with PE.sym (whrDet* (red D , Πₙ) (D₁ , whnfB))
  ... | PE.refl =
    let ⊢ΠFG , ⊢t , ⊢u = syntacticEqTerm (soundness~↓𝕥y ([~] A D₂ Πₙ k~l))
        neT , neU = ne~↑𝕥y k~l
        ⊢Γ = wf ⊢F
        ⊢var0 = var (⊢Γ ∙ ⊢F) here
        var0 = neuTerm ([F] (step id) (⊢Γ ∙ ⊢F)) (var 0) ⊢var0 (refl ⊢var0)
        0≡0 = lift~toConv↑′ ([F] (step id) (⊢Γ ∙ ⊢F)) (var-refl′ (var (⊢Γ ∙ ⊢F) here))
        k∘0≡l∘0 = lift~toConv↑′ ([G] (step id) (⊢Γ ∙ ⊢F) var0)
                                (~↑𝕥y (𝕥y~↑ (∘ₙ (wkNeutral _ neT)) (∘ₙ (wkNeutral _ neU))
                                          (wkTerm (step id) (⊢Γ ∙ ⊢F) ⊢t ∘ⱼ ⊢var0)
                                          (wkTerm (step id) (⊢Γ ∙ ⊢F) ⊢u ∘ⱼ ⊢var0)))
    in  η-eq ⊢F ⊢t ⊢u (ne neT) (ne neU)
             (PE.subst (λ x → _ ⊢ _ [conv↑] _ ∷ x ⦂ _)
                       (wkSingleSubstId _)
                       k∘0≡l∘0)
  lift~toConv↓𝕥y′ (emb 0<1 [A]) D t~u = lift~toConv↓𝕥y′ [A] D t~u

  -- Helper function for lifting from neutrals to generic terms.
  lift~toConv↑𝕥y′ : ∀ {t u A Γ l}
                → Γ ⊩⟨ l ⟩ A ⦂ 𝕥y
                → Γ ⊢ t ~ u ↑𝕥y A
                → Γ ⊢ t [conv↑] u ∷ A ⦂ 𝕥y
  lift~toConv↑𝕥y′ [A] t~u =
    let B , whnfB , D = whNorm′ [A]
        t~u↓ = [~] _ (red D) whnfB t~u
        neT , neU = ne~↑𝕥y t~u
        _ , ⊢t , ⊢u = syntacticEqTerm (soundness~↓𝕥y t~u↓)
    in  [↑]ₜ _ _ _ (red D) (id ⊢t) (id ⊢u) whnfB
             (ne neT) (ne neU) (lift~toConv↓𝕥y′ [A] (red D) t~u↓)

  lift~toConv↑𝕥y′ : ∀ {t u A Γ l}
                → Γ ⊩⟨ l ⟩ A ⦂ 𝕥y
                → Γ ⊢ t ~ u ↑𝕥y A
                → Γ ⊢ t [conv↑] u ∷ A ⦂ 𝕥y
  lift~toConv↑𝕥y′ [A] t~u =
    let B , whnfB , D = whNorm′ [A]
        t~u↓ = [~] _ (red D) whnfB t~u
        neT , neU = ne~↑𝕥y t~u
        _ , ⊢t , ⊢u = syntacticEqTerm (soundness~↓𝕥y t~u↓)
    in  [↑]ₜ _ _ _ (red D) (id ⊢t) (id ⊢u) whnfB
             (ne neT) (ne neU) (lift~toConv↓𝕥y′ [A] (red D) t~u↓)

  lift~toConv↑′ : ∀ {t u A sA Γ l}
                → Γ ⊩⟨ l ⟩ A ⦂ sA
                → Γ ⊢ t ~ u ↑ A ⦂ sA
                → Γ ⊢ t [conv↑] u ∷ A ⦂ sA
  lift~toConv↑′ [A] (~↑𝕥y x) = lift~toConv↑𝕥y′ [A] x
  lift~toConv↑′ [A] (~↑𝕥y x) = lift~toConv↑𝕥y′ [A] x

-- Lifting of algorithmic equality of terms from neutrals to generic terms in WHNF.
lift~toConv↓𝕥y : ∀ {t u A Γ}
             → Γ ⊢ t ~ u ↓𝕥y A
             → Γ ⊢ t [conv↓] u ∷ A ⦂ 𝕥y
lift~toConv↓𝕥y ([~] A D whnfB k~l) =
  lift~toConv↓𝕥y′ (reducible (proj₁ (syntacticRed D))) D ([~] A D whnfB k~l)

lift~toConv↓𝕥y : ∀ {t u A Γ}
             → Γ ⊢ t ~ u ↓𝕥y A
             → Γ ⊢ t [conv↓] u ∷ A ⦂ 𝕥y
lift~toConv↓𝕥y ([~] A D whnfB k~l) =
  lift~toConv↓𝕥y′ (reducible (proj₁ (syntacticRed D))) D ([~] A D whnfB k~l)

lift~toConv↓ : ∀ {t u A sA Γ}
             → Γ ⊢ t ~ u ↓ A ⦂ sA
             → Γ ⊢ t [conv↓] u ∷ A ⦂ sA
lift~toConv↓ (~↓𝕥y x) = lift~toConv↓𝕥y x
lift~toConv↓ (~↓𝕥y x) = lift~toConv↓𝕥y x

-- Lifting of algorithmic equality of terms from neutrals to generic terms.
lift~toConv↑𝕥y : ∀ {t u A Γ}
             → Γ ⊢ t ~ u ↑𝕥y A
             → Γ ⊢ t [conv↑] u ∷ A ⦂ 𝕥y
lift~toConv↑𝕥y t~u =
  lift~toConv↑𝕥y′ (reducible (proj₁ (syntacticEqTerm (soundness~↑𝕥y t~u)))) t~u

lift~toConv↑𝕥y : ∀ {t u A Γ}
             → Γ ⊢ t ~ u ↑𝕥y A
             → Γ ⊢ t [conv↑] u ∷ A ⦂ 𝕥y
lift~toConv↑𝕥y t~u =
  lift~toConv↑𝕥y′ (reducible (proj₁ (syntacticEqTerm (soundness~↑𝕥y t~u)))) t~u

lift~toConv↑ : ∀ {t u A sA Γ}
             → Γ ⊢ t ~ u ↑ A ⦂ sA
             → Γ ⊢ t [conv↑] u ∷ A ⦂ sA
lift~toConv↑ (~↑𝕥y t~u) = lift~toConv↑𝕥y t~u
lift~toConv↑ (~↑𝕥y t~u) = lift~toConv↑𝕥y t~u
