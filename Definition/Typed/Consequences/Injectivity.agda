{-# OPTIONS --safe #-}

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
injectivity′ : ∀ {F G H E rF lF rH lH  rΠ lG lE Γ lΠ l}
               ([ΠFG] : Γ ⊩⟨ l ⟩Π Π F ^ rF ° lF  ▹ G ° lG ^[ rΠ , lΠ ] )
             → Γ ⊩⟨ l ⟩ Π F ^ rF ° lF ▹ G ° lG  ≡ Π H ^ rH ° lH  ▹ E ° lE ^ [ rΠ , ι lΠ ] / Π-intr [ΠFG]
             → Γ ⊢ F ≡ H ^ [ rF , ι lF ]
             × rF PE.≡ rH
             × lF PE.≡ lH
             × lG PE.≡ lE
             × Γ ∙ F ^ [ rF , ι lF ] ⊢ G ≡ E ^ [ rΠ , ι  lG ]
injectivity′ {F₁} {G₁} {H} {E} {lF = lF₁} {rΠ = rΠ} {Γ = Γ} 
         (noemb (Πᵣ ! lF lG lF≤ lG≤ F G D ⊢F ⊢G A≡A [F] [G] G-ext))
         (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  let F≡F₁ , rF≡rF₁ , lF≡lF₁ , G≡G₁ , lG≡lG₁ = Π-PE-injectivity (whnfRed* (red D) Πₙ)
      H≡F′ , rH≡rF′ , lH≡lF′ , E≡G′ , lE≡lG′ = Π-PE-injectivity (whnfRed* D′ Πₙ)
      ⊢Γ = wf ⊢F
      [F]₁ = [F] id ⊢Γ
      [F]′ = irrelevance′ (PE.trans (wk-id _) (PE.sym F≡F₁)) [F]₁
      [x∷F] = neuTerm ([F] (step id) (⊢Γ ∙ ⊢F)) (var 0) (var (⊢Γ ∙ ⊢F) here)
                      (refl (var (⊢Γ ∙ ⊢F) here))
      [G]₁ = [G] (step id) (⊢Γ ∙ ⊢F) [x∷F]
      [G]′ = PE.subst₂ (λ x y → _ ∙ y ^ _ ⊩⟨ _ ⟩ x ^ _)
                       (PE.trans (wkSingleSubstId _) (PE.sym G≡G₁))
                       (PE.sym F≡F₁) [G]₁
      [F≡H]₁ = [F≡F′] id ⊢Γ
      [F≡H]′ = irrelevanceEq″ (PE.trans (wk-id _) (PE.sym F≡F₁))
                              (PE.trans (wk-id _) (PE.sym H≡F′))
                              PE.refl PE.refl 
                              [F]₁ [F]′ [F≡H]₁
      [G≡E]₁ = [G≡G′] (step id) (⊢Γ ∙ ⊢F) [x∷F]
      [G≡E]′ = irrelevanceEqLift″ (PE.trans (wkSingleSubstId _) (PE.sym G≡G₁))
                                   (PE.trans (wkSingleSubstId _) (PE.sym E≡G′))
                                   (PE.sym F≡F₁) [G]₁ [G]′ [G≡E]₁
  in  PE.subst (λ r → Γ ⊢ _ ≡ _ ^ [ r , ι lF₁ ] ) (PE.sym rF≡rF₁)
        (PE.subst (λ l → Γ ⊢ F₁ ≡ H ^ [ ! , l ] ) (PE.cong ι (PE.sym lF≡lF₁))
          (escapeEq [F]′ [F≡H]′)) ,
     ( PE.trans rF≡rF₁ (PE.sym rH≡rF′) ,
     ( PE.trans lF≡lF₁ (PE.sym lH≡lF′) ,
     ( PE.trans lG≡lG₁ (PE.sym lE≡lG′) ,
        PE.subst (λ r → (_ ∙ _ ^ [ r , _ ] ) ⊢ _ ≡ _ ^ _) (PE.sym rF≡rF₁)
         (PE.subst (λ l → (Γ ∙ F₁  ^ [ ! , ι lF₁ ] ) ⊢ G₁ ≡ E ^ [ rΠ , l ]) (PE.cong ι  (PE.sym lG≡lG₁))
          (PE.subst (λ l → (Γ ∙ F₁ ^ [ ! , l ] ) ⊢ G₁ ≡ E ^  [ rΠ , ι lG ]) (PE.cong ι (PE.sym lF≡lF₁))
           (escapeEq [G]′ [G≡E]′))))))

injectivity′ {F₁} {G₁} {H} {E} {lF = lF₁} {rΠ = rΠ} {Γ = Γ} 
         (noemb (Πᵣ % lF lG lF≤ lG≤ F G D ⊢F ⊢G A≡A [F] [G] G-ext))
         (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  let F≡F₁ , rF≡rF₁ , lF≡lF₁ , G≡G₁ , lG≡lG₁ = Π-PE-injectivity (whnfRed* (red D) Πₙ)
      H≡F′ , rH≡rF′ , lH≡lF′ , E≡G′ , lE≡lG′ = Π-PE-injectivity (whnfRed* D′ Πₙ)
      ⊢Γ = wf ⊢F
      [F]₁ = [F] id ⊢Γ
      [F]′ = irrelevance′ (PE.trans (wk-id _) (PE.sym F≡F₁)) [F]₁
      [x∷F] = neuTerm ([F] (step id) (⊢Γ ∙ ⊢F)) (var 0) (var (⊢Γ ∙ ⊢F) here)
                      (proof-irrelevance (var (⊢Γ ∙ ⊢F) here) (var (⊢Γ ∙ ⊢F) here))
      [G]₁ = [G] (step id) (⊢Γ ∙ ⊢F) [x∷F]
      [G]′ = PE.subst₂ (λ x y → _ ∙ y ^ _ ⊩⟨ _ ⟩ x ^ _)
                       (PE.trans (wkSingleSubstId _) (PE.sym G≡G₁))
                       (PE.sym F≡F₁) [G]₁
      [F≡H]₁ = [F≡F′] id ⊢Γ
      [F≡H]₁ = [F≡F′] id ⊢Γ
      [F≡H]′ = irrelevanceEq″ (PE.trans (wk-id _) (PE.sym F≡F₁))
                              (PE.trans (wk-id _) (PE.sym H≡F′))
                              PE.refl PE.refl 
                              [F]₁ [F]′ [F≡H]₁
      [G≡E]₁ = [G≡G′] (step id) (⊢Γ ∙ ⊢F) [x∷F]
      [G≡E]′ = irrelevanceEqLift″ (PE.trans (wkSingleSubstId _) (PE.sym G≡G₁))
                                   (PE.trans (wkSingleSubstId _) (PE.sym E≡G′))
                                   (PE.sym F≡F₁) [G]₁ [G]′ [G≡E]₁
  in  PE.subst (λ r → Γ ⊢ _ ≡ _ ^ [ r , ι lF₁ ] ) (PE.sym rF≡rF₁)
        (PE.subst (λ l → Γ ⊢ F₁ ≡ H ^ [ % , l ] ) (PE.cong ι (PE.sym lF≡lF₁))
          (escapeEq [F]′ [F≡H]′)) ,
     ( PE.trans rF≡rF₁ (PE.sym rH≡rF′) ,
     ( PE.trans lF≡lF₁ (PE.sym lH≡lF′) ,
     ( PE.trans lG≡lG₁ (PE.sym lE≡lG′) ,
        PE.subst (λ r → (_ ∙ _ ^ [ r , _ ] ) ⊢ _ ≡ _ ^ _) (PE.sym rF≡rF₁)
         (PE.subst (λ l → (Γ ∙ F₁  ^ [ % , ι lF₁ ] ) ⊢ G₁ ≡ E ^ [ rΠ , l ]) (PE.cong ι  (PE.sym lG≡lG₁))
          (PE.subst (λ l → (Γ ∙ F₁ ^ [ % , l ] ) ⊢ G₁ ≡ E ^  [ rΠ , ι lG ]) (PE.cong ι (PE.sym lF≡lF₁))
           (escapeEq [G]′ [G≡E]′))))))

injectivity′ (emb emb< x) [ΠFG≡ΠHE] = injectivity′ x [ΠFG≡ΠHE]
injectivity′ (emb ∞< x) [ΠFG≡ΠHE] = injectivity′ x [ΠFG≡ΠHE]


-- Injectivity of Π
injectivity : ∀ {Γ F G H E rF lF lH lG lE rH rΠ lΠ} →
              Γ ⊢ Π F ^ rF ° lF ▹ G ° lG ≡ Π H ^ rH ° lH ▹ E ° lE ^ [ rΠ , ι lΠ ]
            → Γ ⊢ F ≡ H ^ [ rF , ι lF ]
            × rF PE.≡ rH
            × lF PE.≡ lH
            × lG PE.≡ lE
            × Γ ∙ F ^ [ rF , ι lF ] ⊢ G ≡ E ^ [ rΠ , ι lG ]
injectivity ⊢ΠFG≡ΠHE =
  let [ΠFG] , _ , [ΠFG≡ΠHE] = reducibleEq ⊢ΠFG≡ΠHE
  in  injectivity′ (Π-elim [ΠFG])
                   (irrelevanceEq [ΠFG] (Π-intr (Π-elim [ΠFG])) [ΠFG≡ΠHE])


Uinjectivity′ : ∀ {Γ r₁ r₂ l₁ l₂ lU l}
               ([U] : Γ ⊩⟨ l ⟩U Univ r₁ l₁ ^ lU)
             → Γ ⊩⟨ l ⟩ Univ r₁ l₁ ≡ Univ r₂ l₂ ^ [ ! , lU ] / U-intr [U]
             → r₁ PE.≡ r₂ × l₁ PE.≡ l₂
Uinjectivity′ (noemb (Uᵣ r l′ l< eq d)) D =
  let A , B = Univ-PE-injectivity (whnfRed* D Uₙ) 
      A' , B' = Univ-PE-injectivity (whnfRed* (red d) Uₙ)
  in (PE.trans A' (PE.sym A)) , (PE.trans B' (PE.sym B))
Uinjectivity′ (emb emb< a) b = Uinjectivity′ a b
Uinjectivity′ (emb ∞< a) b = Uinjectivity′ a b


Uinjectivity : ∀ {Γ r₁ r₂ l₁ l₂ lU} →
                 Γ ⊢ Univ r₁ l₁ ≡ Univ r₂ l₂  ^ [ ! , lU ] →
                 r₁ PE.≡ r₂ × l₁ PE.≡ l₂
Uinjectivity ⊢U≡U =
  let [U] , _ , [U≡U] = reducibleEq ⊢U≡U
  in Uinjectivity′ (U-elim [U]) (irrelevanceEq [U] (U-intr (U-elim [U])) [U≡U])

