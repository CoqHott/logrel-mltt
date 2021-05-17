{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Application {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Weakening using (id)
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.Typed.Reduction
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties

open import Tools.Product
import Tools.PropositionalEquality as PE
import Data.Nat as Nat

-- Helper function for application of specific type derivations.
appTerm′ : ∀ {F G t u Γ rF lF rΠ lG l l′ l″}
          ([F] : Γ ⊩⟨ l″ ⟩ F ^ [ rF , ι lF ])
          ([G[u]] : Γ ⊩⟨ l′ ⟩ G [ u ] ^ [ TypeInfo.r rΠ , ι lG ])
          ([ΠFG] : Γ ⊩⟨ l ⟩Π Π F ^ rF ° lF ▹ G ° lG ^ rΠ)
          ([t] : Γ ⊩⟨ l ⟩ t ∷ Π F ^ rF ° lF ▹ G ° lG ^ rΠ / Π-intr [ΠFG])
          ([u] : Γ ⊩⟨ l″ ⟩ u ∷ F ^ [ rF , ι lF ] / [F])
        → Γ ⊩⟨ l′ ⟩ t ∘ u ∷ G [ u ] ^ [ TypeInfo.r rΠ , ι lG ] / [G[u]]
appTerm′ {t = t} {Γ = Γ} {rΠ = [ ! , lΠ ]} [F] [G[u]] (noemb (Πᵣ rF′ lF lG F G D ⊢F ⊢G A≡A [F′] [G′] G-ext))
         (Πₜ f d funcF f≡f [f] [f]₁) [u] =
  let ΠFG≡ΠF′G′ = whnfRed* (red D) Πₙ
      F≡F′ , rF≡rF′ , lF≡lF′ , G≡G′ , lG≡lG′ = Π-PE-injectivity ΠFG≡ΠF′G′
      F≡idF′ = PE.trans F≡F′ (PE.sym (wk-id _))
      idG′ᵤ≡Gᵤ = PE.cong (λ x → x [ _ ]) (PE.trans (wk-lift-id _) (PE.sym G≡G′))
      idf∘u≡f∘u = (PE.cong (λ x → x ∘ _) (wk-id _))
      ⊢Γ = wf ⊢F
      [u]′ = irrelevanceTerm′ F≡idF′ rF≡rF′ (PE.cong ι lF≡lF′) [F] ([F′] id ⊢Γ) [u]
      [f∘u] = irrelevanceTerm″ idG′ᵤ≡Gᵤ PE.refl (PE.cong ι (PE.sym lG≡lG′)) idf∘u≡f∘u
                                ([G′] id ⊢Γ [u]′) [G[u]] ([f]₁ id ⊢Γ [u]′)
      ⊢u = escapeTerm [F] [u]
      d′ = PE.subst (λ x → Γ ⊢ t ⇒* f ∷ x ^ lΠ) (PE.sym ΠFG≡ΠF′G′) (redₜ d)
  in  proj₁ (redSubst*Term (app-subst* d′ ⊢u) [G[u]] [f∘u])
appTerm′ {t = t} {Γ = Γ} {rΠ = [ % , lΠ ]} [F] [G[u]] (noemb (Πᵣ rF′ lF lG F G D ⊢F ⊢G A≡A [F′] [G′] G-ext))
         [t] [u] =
  let ⊢u = escapeTerm [F] [u]
      ⊢t = escapeTerm (Πᵣ (Πᵣ rF′ lF lG F G D ⊢F ⊢G A≡A [F′] [G′] G-ext)) [t]
  in logRelIrr [G[u]] (⊢t ∘ⱼ  ⊢u)
appTerm′ {l = ι ¹} [F] [G[u]] (emb emb< x) [t] [u] = appTerm′ [F] [G[u]] x [t] [u]
appTerm′ {l = ∞} [F] [G[u]] (emb ∞< x) [t] [u] = appTerm′ [F] [G[u]] x [t] [u]


-- Application of reducible terms.
appTerm : ∀ {F G t u Γ rF lF rF' rΠ lG l l′ l″} (eqr : rF PE.≡ rF') 
          ([F] : Γ ⊩⟨ l″ ⟩ F ^ [ rF , ι lF ])
          ([G[u]] : Γ ⊩⟨ l′ ⟩ G [ u ] ^ [ TypeInfo.r rΠ , ι lG ])
          ([ΠFG] : Γ ⊩⟨ l ⟩ Π F ^ rF' ° lF ▹ G ° lG  ^ rΠ)
          ([t] : Γ ⊩⟨ l ⟩ t ∷ Π F ^ rF' ° lF ▹ G ° lG  ^ rΠ / [ΠFG])
          ([u] : Γ ⊩⟨ l″ ⟩ u ∷ F ^ [ rF , ι lF ] / [F])
        → Γ ⊩⟨ l′ ⟩ t ∘ u ∷ G [ u ] ^ [ TypeInfo.r rΠ , ι lG ] / [G[u]]
appTerm PE.refl [F] [G[u]] [ΠFG] [t] [u] =
  let [t]′ = irrelevanceTerm [ΠFG] (Π-intr (Π-elim [ΠFG])) [t]
  in  appTerm′ [F] [G[u]] (Π-elim [ΠFG]) [t]′ [u]

-- Helper function for application congurence of specific type derivations.
app-congTerm′ : ∀ {F G t t′ u u′ Γ rF lF rΠ lG l l′}
          ([F] : Γ ⊩⟨ l′ ⟩ F ^ [ rF , ι lF ])
          ([G[u]] : Γ ⊩⟨ l′ ⟩ G [ u ] ^ [ TypeInfo.r rΠ , ι lG ])
          ([ΠFG] : Γ ⊩⟨ l ⟩Π Π F ^ rF ° lF ▹ G ° lG  ^ rΠ)
          ([t≡t′] : Γ ⊩⟨ l ⟩ t ≡ t′ ∷ Π F ^ rF ° lF ▹ G ° lG ^ rΠ / Π-intr [ΠFG])
          ([u] : Γ ⊩⟨ l′ ⟩ u ∷ F ^ [ rF , ι lF ] / [F])
          ([u′] : Γ ⊩⟨ l′ ⟩ u′ ∷ F ^ [ rF , ι lF ] / [F])
          ([u≡u′] : Γ ⊩⟨ l′ ⟩ u ≡ u′ ∷ F ^ [ rF , ι lF ] / [F])
        → Γ ⊩⟨ l′ ⟩ t ∘ u ≡ t′ ∘ u′ ∷ G [ u ] ^ [ TypeInfo.r rΠ , ι lG ] / [G[u]]
app-congTerm′ {F′} {G′} {t = t} {t′ = t′} {Γ = Γ} {rF = rF} {lF = lF} {rΠ = [ ! , lΠ ]} {lG = lG}
              [F] [G[u]] (noemb (Πᵣ rF′ lF' lG' F G D ⊢F ⊢G A≡A [F]₁ [G] G-ext))
              (Πₜ₌ f g [[ ⊢t , ⊢f , d ]] [[ ⊢t′ , ⊢g , d′ ]] funcF funcG t≡u
                   (Πₜ f′ [[ _ , ⊢f′ , d″ ]] funcF′ f≡f [f] [f]₁)
                   (Πₜ g′ [[ _ , ⊢g′ , d‴ ]] funcG′ g≡g [g] [g]₁) [t≡u])
              [a] [a′] [a≡a′] =
  let ΠFG≡ΠF′G′ = whnfRed* (red D) Πₙ
      F≡F′ , rF≡rF′ , lF≡lF′ , G≡G′ , lG≡lG′ = Π-PE-injectivity ΠFG≡ΠF′G′
      f≡f′ = whrDet*Term (d , functionWhnf funcF) (d″ , functionWhnf funcF′)
      g≡g′ = whrDet*Term (d′ , functionWhnf funcG) (d‴ , functionWhnf funcG′)
      F≡wkidF′ = PE.trans F≡F′ (PE.sym (wk-id _))
      [ΠFG] = Πᵣ′ rF′ lF' lG' F G (PE.subst _ rF≡rF′ D) ⊢F ⊢G A≡A [F]₁ [G] G-ext
      t∘x≡wkidt∘x : {a b : Term} → wk id a ∘ b PE.≡ a ∘ b
      t∘x≡wkidt∘x {a} {b} = PE.cong (λ x → x ∘ b) (wk-id a)
      t∘x≡wkidt∘x′ : {a : Term} → wk id g′ ∘ a PE.≡ g ∘ a
      t∘x≡wkidt∘x′ {a} = PE.cong (λ x → x ∘ a) (PE.trans (wk-id _) (PE.sym g≡g′))
      wkidG₁[u]≡G[u] = PE.cong (λ x → x [ _ ])
                               (PE.trans (wk-lift-id _) (PE.sym G≡G′))
      wkidG₁[u′]≡G[u′] = PE.cong (λ x → x [ _ ])
                                 (PE.trans (wk-lift-id _) (PE.sym G≡G′))
      ⊢Γ = wf ⊢F
      [u]′ = irrelevanceTerm′ F≡wkidF′ rF≡rF′ (PE.cong ι lF≡lF′) [F] ([F]₁ id ⊢Γ) [a]
      [u′]′ = irrelevanceTerm′ F≡wkidF′ rF≡rF′ (PE.cong ι lF≡lF′) [F] ([F]₁ id ⊢Γ) [a′]
      [u≡u′]′ = irrelevanceEqTerm′ F≡wkidF′ rF≡rF′ (PE.cong ι lF≡lF′) [F] ([F]₁ id ⊢Γ) [a≡a′]
      [G[u′]] = irrelevance′′ wkidG₁[u′]≡G[u′] PE.refl (PE.cong ι (PE.sym lG≡lG′)) ([G] id ⊢Γ [u′]′)
      [G[u≡u′]] = irrelevanceEq″ wkidG₁[u]≡G[u] wkidG₁[u′]≡G[u′] PE.refl (PE.cong ι (PE.sym lG≡lG′))
                                  ([G] id ⊢Γ [u]′) [G[u]]
                                  (G-ext id ⊢Γ [u]′ [u′]′ [u≡u′]′)
      [f′] : Γ ⊩⟨ _ ⟩ f′ ∷ Π F′ ^ rF′ ° lF ▹ G′ ° lG  ^ [ ! , lΠ ] / [ΠFG]
      [f′] = Πₜ f′ (idRedTerm:*: ⊢f′) funcF′ f≡f [f] [f]₁
      [f∘u] = appTerm rF≡rF′ [F] [G[u]] [ΠFG]
                      (irrelevanceTerm″ PE.refl PE.refl PE.refl (PE.sym f≡f′) [ΠFG] [ΠFG] [f′])
                      [a]
      [g′] : Γ ⊩⟨ _ ⟩ g′ ∷ Π F′ ^ rF′ ° lF ▹ G′ ° lG ^ [ ! , lΠ ] / [ΠFG]
      [g′] = Πₜ g′ (idRedTerm:*: ⊢g′) funcG′ g≡g [g] [g]₁
      [g∘u′] = appTerm rF≡rF′ [F] [G[u′]] [ΠFG]
                       (irrelevanceTerm″ PE.refl PE.refl PE.refl (PE.sym g≡g′) [ΠFG] [ΠFG] [g′])
                       [a′]
      [tu≡t′u] = irrelevanceEqTerm″ PE.refl (PE.cong ι (PE.sym lG≡lG′)) t∘x≡wkidt∘x t∘x≡wkidt∘x wkidG₁[u]≡G[u]
                                     ([G] id ⊢Γ [u]′) [G[u]]
                                     ([t≡u] id ⊢Γ [u]′)
      [t′u≡t′u′] = irrelevanceEqTerm″ PE.refl (PE.cong ι (PE.sym lG≡lG′)) t∘x≡wkidt∘x′ t∘x≡wkidt∘x′ wkidG₁[u]≡G[u]
                                      ([G] id ⊢Γ [u]′) [G[u]]
                                      ([g] id ⊢Γ [u]′ [u′]′ [u≡u′]′)
      d₁ = PE.subst (λ x → Γ ⊢ t ⇒* f ∷ x ^ lΠ) (PE.sym ΠFG≡ΠF′G′) d
      d₂ = PE.subst (λ x → Γ ⊢ t′ ⇒* g ∷ x ^ lΠ) (PE.sym ΠFG≡ΠF′G′) d′
      [tu≡fu] = proj₂ (redSubst*Term (app-subst* d₁ (escapeTerm [F] [a]))
                                     [G[u]] [f∘u])
      [gu′≡t′u′] = convEqTerm₂ [G[u]] [G[u′]] [G[u≡u′]] 
                     (symEqTerm [G[u′]]
                       (proj₂ (redSubst*Term (app-subst* d₂ (escapeTerm [F] [a′]))
                                             [G[u′]]
                                             [g∘u′])))
  in  transEqTerm [G[u]] (transEqTerm [G[u]] [tu≡fu] [tu≡t′u])
                         (transEqTerm [G[u]] [t′u≡t′u′] [gu′≡t′u′])
app-congTerm′ {F′} {G′} {t = t} {t′ = t′} {Γ = Γ} {rF = rF} {rΠ = [ % , lΠ ]}
              [F] [G[u]] (noemb (Πᵣ rF′ lF' lG' F G D ⊢F ⊢G A≡A [F′] [G′] G-ext))
              ([t] , [t′])
              [u] [u′] [u≡u′] =
  let ΠFG≡ΠF′G′ = whnfRed* (red D) Πₙ
      F≡F′ , rF≡rF′ , lF≡lF′ , G≡G′ , lG≡lG′ = Π-PE-injectivity ΠFG≡ΠF′G′
      F≡wkidF′ = PE.trans F≡F′ (PE.sym (wk-id _))
      t∘x≡wkidt∘x : {a b : Term} → wk id a ∘ b PE.≡ a ∘ b
      t∘x≡wkidt∘x {a} {b} = PE.cong (λ x → x ∘ b) (wk-id a)
      wkidG₁[u]≡G[u] = PE.cong (λ x → x [ _ ])
                               (PE.trans (wk-lift-id _) (PE.sym G≡G′))
      wkidG₁[u′]≡G[u′] = PE.cong (λ x → x [ _ ])
                                 (PE.trans (wk-lift-id _) (PE.sym G≡G′))
      ⊢Γ = wf ⊢F
      [u]′ = irrelevanceTerm′ F≡wkidF′ rF≡rF′ (PE.cong ι lF≡lF′) [F] ([F′] id ⊢Γ) [u]
      [u′]′ = irrelevanceTerm′ F≡wkidF′ rF≡rF′ (PE.cong ι lF≡lF′) [F] ([F′] id ⊢Γ) [u′]
      [u≡u′]′ = irrelevanceEqTerm′ F≡wkidF′ rF≡rF′ (PE.cong ι lF≡lF′) [F] ([F′] id ⊢Γ) [u≡u′]
      [G[u′]] = irrelevance′ wkidG₁[u′]≡G[u′] ([G′] id ⊢Γ [u′]′)
      [G[u≡u′]] = irrelevanceEq″  wkidG₁[u]≡G[u] wkidG₁[u′]≡G[u′] PE.refl (PE.cong ι (PE.sym lG≡lG′))
                                  ([G′] id ⊢Γ [u]′) [G[u]]
                                  (G-ext id ⊢Γ [u]′ [u′]′ [u≡u′]′)
      ⊢u = escapeTerm [F] [u]
      ⊢u′ = escapeTerm [F] [u′]
      ⊢t = escapeTerm (Πᵣ (Πᵣ rF′ lF' lG' F G D ⊢F ⊢G A≡A [F′] [G′] G-ext)) [t]
      ⊢t′ = escapeTerm (Πᵣ (Πᵣ rF′ lF' lG' F G D ⊢F ⊢G A≡A [F′] [G′] G-ext)) [t′]
  in logRelIrrEq [G[u]] (⊢t ∘ⱼ  ⊢u) let X =  ⊢t′ ∘ⱼ  ⊢u′
                                        Y = escapeEq [G[u]] [G[u≡u′]] in conv X (sym (≅-eq Y))
app-congTerm′ {l = ι ¹} [F] [G[u]] (emb emb< x) [t≡t′] [u] [u′] [u≡u′] = app-congTerm′ [F] [G[u]] x [t≡t′] [u] [u′] [u≡u′]
app-congTerm′ {l = ∞} [F] [G[u]] (emb ∞< x) [t≡t′] [u] [u′] [u≡u′] = app-congTerm′ [F] [G[u]] x [t≡t′] [u] [u′] [u≡u′]

-- Application congurence of reducible terms.
app-congTerm : ∀ {F G t t′ u u′ Γ rF lF rΠ lG l l′}
          ([F] : Γ ⊩⟨ l′ ⟩ F ^ [ rF , ι lF ])
          ([G[u]] : Γ ⊩⟨ l′ ⟩ G [ u ] ^ [ TypeInfo.r rΠ , ι lG ])
          ([ΠFG] : Γ ⊩⟨ l ⟩ Π F ^ rF ° lF ▹ G ° lG ^ rΠ)
          ([t≡t′] : Γ ⊩⟨ l ⟩ t ≡ t′ ∷ Π F ^ rF ° lF ▹ G ° lG ^ rΠ / [ΠFG])
          ([u] : Γ ⊩⟨ l′ ⟩ u ∷ F ^ [ rF , ι lF ] / [F])
          ([u′] : Γ ⊩⟨ l′ ⟩ u′ ∷ F ^ [ rF , ι lF ] / [F])
          ([u≡u′] : Γ ⊩⟨ l′ ⟩ u ≡ u′ ∷ F ^ [ rF , ι lF ] / [F])
        → Γ ⊩⟨ l′ ⟩ t ∘ u ≡ t′ ∘ u′ ∷ G [ u ] ^ [ TypeInfo.r rΠ , ι lG ] / [G[u]]
app-congTerm [F] [G[u]] [ΠFG] [t≡t′] =
  let [t≡t′]′ = irrelevanceEqTerm [ΠFG] (Π-intr (Π-elim [ΠFG])) [t≡t′]
  in  app-congTerm′ [F] [G[u]] (Π-elim [ΠFG]) [t≡t′]′
