{-# OPTIONS --without-K  #-}

module Definition.Typed.Consequences.Injectivity where

open import Definition.Untyped hiding (wk)
import Definition.Untyped as U
open import Definition.Untyped.Properties

open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.Typed.EqRelInstance
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Fundamental.Reducibility

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Helper function of injectivity for specific reducible Π-types
injectivity′ : ∀ {F G H E sF sH sG Γ l}
               ([ΠFG] : Γ ⊩⟨ l ⟩Π Π F ⦂ sF ▹ G ⦂ sG)
             → Γ ⊩⟨ l ⟩ Π F ⦂ sF ▹ G ≡ Π H ⦂ sH ▹ E ⦂ sG / Π-intr [ΠFG]
             → Γ ⊢ F ≡ H ⦂ sF
             × sF PE.≡ sH
             × Γ ∙ F ⦂ sF ⊢ G ≡ E ⦂ sG
injectivity′ (noemb (Πᵣ sF′ F G D ⊢F ⊢G A≡A [F] [G] G-ext))
         (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  let F≡F₁ , sF≡sF₁ , G≡G₁ = Π-PE-injectivity (whnfRed* (red D) Πₙ)
      H≡F′ , sH≡sF′ , E≡G′ = Π-PE-injectivity (whnfRed* D′ Πₙ)
      ⊢Γ = wf ⊢F
      [F]₁ = [F] id ⊢Γ
      [F]′ = irrelevance′ (PE.trans (wk-id _) (PE.sym F≡F₁)) [F]₁
      [x∷F] = neuTerm ([F] (step id) (⊢Γ ∙ ⊢F)) (var 0) (var (⊢Γ ∙ ⊢F) here)
                      (refl (var (⊢Γ ∙ ⊢F) here))
      [G]₁ = [G] (step id) (⊢Γ ∙ ⊢F) [x∷F]
      [G]′ = PE.subst₂ (λ x y → _ ∙ y ⦂ _ ⊩⟨ _ ⟩ x ⦂ _)
                       (PE.trans (wkSingleSubstId _) (PE.sym G≡G₁))
                       (PE.sym F≡F₁) [G]₁
      [F≡H]₁ = [F≡F′] id ⊢Γ
      [F≡H]′ = irrelevanceEq″ (PE.trans (wk-id _) (PE.sym F≡F₁))
                               (PE.trans (wk-id _) (PE.sym H≡F′))
                               [F]₁ [F]′ [F≡H]₁
      [G≡E]₁ = [G≡G′] (step id) (⊢Γ ∙ ⊢F) [x∷F]
      [G≡E]′ = irrelevanceEqLift″ (PE.trans (wkSingleSubstId _) (PE.sym G≡G₁))
                                   (PE.trans (wkSingleSubstId _) (PE.sym E≡G′))
                                   (PE.sym F≡F₁) [G]₁ [G]′ [G≡E]₁
  in  PE.subst _ (PE.sym sF≡sF₁) (escapeEq [F]′ [F≡H]′)
    , PE.trans sF≡sF₁ (PE.sym sH≡sF′)
    , PE.subst _ (PE.sym sF≡sF₁) (escapeEq [G]′ [G≡E]′)
injectivity′ (emb 0<1 x) [ΠFG≡ΠHE] = injectivity′ x [ΠFG≡ΠHE]

-- Injectivity of Π
injectivity : ∀ {Γ F G H E sF sH sG} → Γ ⊢ Π F ⦂ sF ▹ G ≡ Π H ⦂ sH ▹ E ⦂ sG
            → Γ ⊢ F ≡ H ⦂ sF
            × sF PE.≡ sH
            × Γ ∙ F ⦂ sF ⊢ G ≡ E ⦂ sG
injectivity ⊢ΠFG≡ΠHE =
  let [ΠFG] , _ , [ΠFG≡ΠHE] = reducibleEq ⊢ΠFG≡ΠHE
  in  injectivity′ (Π-elim [ΠFG])
                   (irrelevanceEq [ΠFG] (Π-intr (Π-elim [ΠFG])) [ΠFG≡ΠHE])

Uinjectivity′ : ∀ {Γ s₁ s₂ l}
               ([U] : Γ ⊩⟨ l ⟩U)
             → Γ ⊩⟨ l ⟩ Univ s₁ ≡ Univ s₂ ⦂ 𝕥y / U-intr [U]
             → s₁ PE.≡ s₂
Uinjectivity′ (noemb x) PE.refl = PE.refl -- probably more complicated if we had large univs
Uinjectivity′ (emb 0<1 a) b = Uinjectivity′ a b

Uinjectivity : ∀ {Γ s₁ s₂} → Γ ⊢ Univ s₁ ≡ Univ s₂ ⦂ 𝕥y → s₁ PE.≡ s₂
Uinjectivity ⊢U≡U =
  let [U] , _ , [U≡U] = reducibleEq ⊢U≡U
  in Uinjectivity′ (U-elim [U]) (irrelevanceEq [U] (U-intr (U-elim [U])) [U≡U])
