{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Pi {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Weakening using (_∷_⊆_ ; _•ₜ_)
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Weakening
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Weakening
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Substitution.MaybeEmbed
import Definition.LogicalRelation.Substitution.Irrelevance as S
open import Definition.LogicalRelation.Substitution.Introductions.Universe

open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Empty using (⊥; ⊥-elim)

GappGen : ∀ {F G Γ rF lF lG rΠ l Δ σ ρ Δ₁}
         ([Γ] : ⊩ᵛ Γ)
         ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / [Γ])
         → Γ ∙ F ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ G ^ [ rΠ , ι lG ] / [Γ] ∙ [F]  
         → ∀ ⊢Δ [σ] a ([ρ] : ρ ∷ Δ₁ ⊆ Δ) (⊢Δ₁ : ⊢ Δ₁)
         ([a] : Δ₁ ⊩⟨ l ⟩ a ∷ subst (ρ •ₛ σ) F ^ [ rF , ι lF ]
                / proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ])))
         → Σ (Δ₁ ⊩⟨ l ⟩ subst (consSubst (ρ •ₛ σ) a) G ^ [ rΠ , ι lG ])
               (λ [Aσ] →
               {σ′ : Nat → Term} →
               (Σ (Δ₁ ⊩ˢ tail σ′ ∷ Γ / [Γ] / ⊢Δ₁)
               (λ [tailσ] →
                  Δ₁ ⊩⟨ l ⟩ head σ′ ∷ subst (tail σ′) F ^ [ rF , ι lF ] / proj₁ ([F] ⊢Δ₁ [tailσ]))) →
               Δ₁ ⊩ˢ consSubst (ρ •ₛ σ) a ≡ σ′ ∷ Γ ∙ F ^ [ rF , ι lF ] /
               [Γ] ∙ [F] / ⊢Δ₁ /
               consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]) [F]
               [a] →
               Δ₁ ⊩⟨ l ⟩ subst (consSubst (ρ •ₛ σ) a) G ≡
               subst σ′ G ^ [ rΠ , ι lG ] / [Aσ])
GappGen {F} {G} {Γ} {rF} {lF} {lG} {rΠ} {l} {Δ} {σ} {ρ} {Δ₁} [Γ] [F] [G] ⊢Δ [σ] a [ρ] ⊢Δ₁ [a] =
 [G] {σ = consSubst (ρ •ₛ σ) a} ⊢Δ₁
                              (consSubstS {t = a} {A = F} [Γ] ⊢Δ₁
                                          (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ])
                                          [F] [a])

Gapp : ∀ {F G Γ rF lF lG rΠ l Δ σ ρ Δ₁}
         ([Γ] : ⊩ᵛ Γ)
         ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / [Γ])
         → Γ ∙ F ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ G ^ [ rΠ , ι lG ] / [Γ] ∙ [F]  
         → ∀ ⊢Δ [σ] a ([ρ] : ρ ∷ Δ₁ ⊆ Δ) (⊢Δ₁ : ⊢ Δ₁)
         ([a] : Δ₁ ⊩⟨ l ⟩ a ∷ subst (ρ •ₛ σ) F ^ [ rF , ι lF ]
                / proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ])))
         → Δ₁ ⊩⟨ l ⟩ U.wk (lift ρ) (subst (liftSubst σ) G) [ a ] ^ [ rΠ , ι lG ]
Gapp {F} {G} {Γ} {rF} {lF} {lG} {rΠ} {l} {Δ} {σ} {ρ} {Δ₁} [Γ] [F] [G] ⊢Δ [σ] a [ρ] ⊢Δ₁ [a] =
   let [G]a : ∀ {ρ Δ₁} a ([ρ] : ρ ∷ Δ₁ ⊆ Δ) (⊢Δ₁ : ⊢ Δ₁)
             ([a] : Δ₁ ⊩⟨ l ⟩ a ∷ subst (ρ •ₛ σ) F ^ [ rF , ι lF ]
                / proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ])))
           → Σ (Δ₁ ⊩⟨ l ⟩ subst (consSubst (ρ •ₛ σ) a) G ^ [ rΠ , ι lG ])
               (λ [Aσ] →
               {σ′ : Nat → Term} →
               (Σ (Δ₁ ⊩ˢ tail σ′ ∷ Γ / [Γ] / ⊢Δ₁)
               (λ [tailσ] →
                  Δ₁ ⊩⟨ l ⟩ head σ′ ∷ subst (tail σ′) F ^ [ rF , ι lF ] / proj₁ ([F] ⊢Δ₁ [tailσ]))) →
               Δ₁ ⊩ˢ consSubst (ρ •ₛ σ) a ≡ σ′ ∷ Γ ∙ F ^ [ rF , ι lF ] /
               [Γ] ∙ [F] / ⊢Δ₁ /
               consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]) [F]
               [a] →
               Δ₁ ⊩⟨ l ⟩ subst (consSubst (ρ •ₛ σ) a) G ≡
               subst σ′ G ^ [ rΠ , ι lG ] / [Aσ])
       [G]a {ρ} a [ρ] ⊢Δ₁ [a] = [G] {σ = consSubst (ρ •ₛ σ) a} ⊢Δ₁
                              (consSubstS {t = a} {A = F} [Γ] ⊢Δ₁
                                          (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ])
                                          [F] [a])
  in irrelevance′ (PE.sym (singleSubstWkComp a σ G)) (proj₁ ([G]a a [ρ] ⊢Δ₁ [a]))




un-univ⇒ : ∀ {l Γ A B r} → Γ ⊢ A ⇒ B ^ [ r , ι l ] → Γ ⊢ A ⇒ B ∷ Univ r l ^ next l
un-univ⇒ (univ x) = x

univ⇒* : ∀ {l Γ A B r} → Γ ⊢ A ⇒* B ∷ Univ r l ^ next l → Γ ⊢ A ⇒* B ^ [ r , ι l ]
univ⇒* (id x) = id (univ x)
univ⇒* (x ⇨ D) = univ x ⇨ univ⇒* D

un-univ⇒* : ∀ {l Γ A B r} → Γ ⊢ A ⇒* B ^ [ r , ι l ] → Γ ⊢ A ⇒* B ∷ Univ r l ^ next l
un-univ⇒* (id x) = id (un-univ x)
un-univ⇒* (x ⇨ D) = un-univ⇒ x ⇨ un-univ⇒* D

univ:⇒*: : ∀ {l Γ A B r} →  Γ ⊢ A :⇒*: B ∷ Univ r l ^ next l → Γ ⊢ A :⇒*: B ^ [ r , ι l ]
univ:⇒*: [[ ⊢A , ⊢B , D ]] = [[ (univ ⊢A) , (univ ⊢B) , (univ⇒* D) ]]

un-univ:⇒*: : ∀ {l Γ A B r} → Γ ⊢ A :⇒*: B ^ [ r , ι l ] → Γ ⊢ A :⇒*: B ∷ Univ r l ^ next l
un-univ:⇒*: [[ ⊢A , ⊢B , D ]] = [[ (un-univ ⊢A) , (un-univ ⊢B) , (un-univ⇒* D) ]]

notredUterm* : ∀ {Γ r l l' A B} → Γ ⊢ Univ r l ⇒ A ∷ B ^ l' → ⊥
notredUterm* (conv D x) = notredUterm* D

notredU* : ∀ {Γ r l l' A} → Γ ⊢ Univ r l ⇒ A ^ [ ! , l' ] → ⊥
notredU* (univ x) = notredUterm* x

redU*gen : ∀ {Γ r l r' l' l''} → Γ ⊢ Univ r l ⇒* Univ r' l' ^ [ ! , l'' ] → Univ r l PE.≡ Univ r' l'
redU*gen (id x) = PE.refl
redU*gen (univ (conv x x₁) ⇨ D) = ⊥-elim (notredUterm* x)

{-

neutralWk : ∀ {K ρ} → Neutral K → Neutral (U.wk ρ K)
neutralWk {K} {id} N = {!!}
neutralWk {K} {step ρ} N = {!!}
neutralWk {K} {lift ρ} N = {!!}

un-univEq : ∀ {l Γ A r l′ ll′}
       → ([U] : Γ ⊩⟨ l ⟩ Univ r l′ ^ [ ! , ll′ ] )
       → Γ ⊩⟨ ι l′ ⟩ A ^ [ r , ι l′ ]
       → Γ ⊩⟨ l ⟩ A ∷ Univ r l′ ^ [ ! , ll′ ] / [U]
un-univEq {A = A} (Uᵣ (Uᵣ r l′ l< eq d)) (Uᵣ (Uᵣ r₁ l′₁ l<₁ eq₁ d₁)) = Uₜ {!A!} {!!} {!!} {!!} {!!}
un-univEq {l} {A = A} (Uᵣ (Uᵣ r l′ l< eq [[ ⊢A₁ , ⊢B₁ , D₁ ]])) (ℕᵣ D) = 
  let er , el = Univ-PE-injectivity (redU*gen D₁)
      redA = un-univ:⇒*: D
      redA' = univ:⇒*: redA
      [[ ⊢A , _ , _ ]] = D 
  in Uₜ ℕ (PE.subst (λ l → _ ⊢ _ :⇒*: _ ∷ Univ _ l ^ next l)  el (PE.subst (λ r → _ ⊢ _ :⇒*: _ ∷ Univ r _ ^ _) er redA)) ℕₙ
          (PE.subst (λ l → _ ⊢ _ ≅ _ ∷ Univ _ l ^ [ _ , next l ]) el (PE.subst (λ r → _ ⊢ _ ≅ _ ∷ Univ r _ ^ [ ! , next _ ]) er (≅ₜ-ℕrefl (wf ⊢A))))
        λ x ⊢Δ → let redA'' = Definition.Typed.Weakening.wkRed:*: x ⊢Δ redA'
                 in PE.subst _ el (PE.subst _ er (ℕᵣ redA''))
un-univEq (Uᵣ (Uᵣ r l′ l< eq [[ ⊢A , ⊢B , D₁ ]])) (Emptyᵣ D) =
  let er , el = Univ-PE-injectivity (redU*gen D₁)
      redA = un-univ:⇒*: D
      redA' = univ:⇒*: redA
      [[ ⊢A , _ , _ ]] = D 
  in Uₜ Empty (PE.subst (λ l → _ ⊢ _ :⇒*: _ ∷ Univ _ l ^ next l)  el (PE.subst (λ r → _ ⊢ _ :⇒*: _ ∷ Univ r _ ^ _) er redA)) Emptyₙ
        (PE.subst (λ l → _ ⊢ _ ≅ _ ∷ Univ _ l ^ [ _ , next l ]) el (PE.subst (λ r → _ ⊢ _ ≅ _ ∷ Univ r _ ^ [ ! , next _ ]) er (≅ₜ-Emptyrefl (wf ⊢A))))
         λ x ⊢Δ → let redA'' = Definition.Typed.Weakening.wkRed:*: x ⊢Δ redA'
                  in PE.subst _ el (PE.subst _ er (Emptyᵣ redA''))
un-univEq {∞} (Uᵣ (Uᵣ r l′ l< eq [[ ⊢A , ⊢B , D₁ ]])) (ne′ K D neK K≡K) =
  let er , el = Univ-PE-injectivity (redU*gen D₁)
      redA = un-univ:⇒*: D
      redA' = univ:⇒*: redA
      [[ ⊢A , _ , _ ]] = D 
  in Uₜ K (PE.subst (λ l → _ ⊢ _ :⇒*: _ ∷ Univ _ l ^ next l)  el (PE.subst (λ r → _ ⊢ _ :⇒*: _ ∷ Univ r _ ^ _) er redA)) (ne neK)
          (PE.subst (λ l → _ ⊢ _ ≅ _ ∷ Univ _ l ^ [ _ , next l ]) el (PE.subst (λ r → _ ⊢ _ ≅ _ ∷ Univ r _ ^ [ ! , next _ ]) er {!!}))
          λ {ρ} x ⊢Δ → let redA'' = Definition.Typed.Weakening.wkRed:*: x ⊢Δ redA'
                   in ne′ (U.wk ρ K) (PE.subst _ el (PE.subst _ er redA'')) (neutralWk neK) {!K≡K!} --
                   -- PE.subst (λ l → (logRelRec _ _ LogRelKit.⊩ _ ^ _ ) ( [ _ , ι l ] )) el
                   --   (PE.subst (λ r → (logRelRec _ _ LogRelKit.⊩ _ ^ _ ) ( [ r , _ ] )) er (ne′ {!K!} {!!} {!!} {!!}))
un-univEq (Uᵣ (Uᵣ r l′ l< eq d)) (Πᵣ x) = Uₜ {!!} {!!} {!!} {!!} {!!}
un-univEq (Uᵣ (Uᵣ r l′ l< eq d)) (∃ᵣ x) = Uₜ {!!} {!!} {!!} {!!} {!!}
un-univEq (Uᵣ (Uᵣ r l′ l< eq d)) (emb l<₁ [A]) = Uₜ {!!} {!!} {!!} {!!} {!!}
un-univEq (ℕᵣ X) [A] = ⊥-elim (UnivNotℕ X)
un-univEq (ne′ K D neK K≡K) [A] = ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
un-univEq (Πᵣ X) [A] = ⊥-elim (UnivNotΠ X)
un-univEq (emb l< [A]₁) [A] = {!!}
-}



-- Validity of Π.
Πᵛ : ∀ {F G Γ rF lF lG rΠ lΠ l}
     (lF< : lF ≤ lΠ)
     (lG< : lG ≤ lΠ)
     ([Γ] : ⊩ᵛ Γ)
     ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / [Γ])
   → Γ ∙ F ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ G ^ [ rΠ , ι lG ] / [Γ] ∙ [F]
   → Γ ⊩ᵛ⟨ l ⟩ Π F ^ rF ° lF ▹ G ° lG ^ [ rΠ , ι lΠ ] / [Γ]
Πᵛ {F} {G} {Γ} {rF} {lF} {lG} {rΠ} {lΠ} {l} lF< lG< [Γ] [F] [G] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let [F]σ {σ′} [σ′] = [F] {σ = σ′} ⊢Δ [σ′]
      [σF] = proj₁ ([F]σ [σ])
      ⊢F {σ′} [σ′] = escape (proj₁ ([F]σ {σ′} [σ′]))
      ⊢F≡F = escapeEq [σF] (reflEq [σF])
      [G]σ {σ′} [σ′] = [G] {σ = liftSubst σ′} (⊢Δ ∙ ⊢F [σ′])
                           (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ′])
      ⊢G {σ′} [σ′] = escape (proj₁ ([G]σ {σ′} [σ′]))
      ⊢G≡G = escapeEq (proj₁ ([G]σ [σ])) (reflEq (proj₁ ([G]σ [σ])))
      ⊢ΠF▹G = Πⱼ lF< ▹ lG< ▹ un-univ (⊢F [σ]) ▹ un-univ (⊢G [σ])
      [G]a : ∀ {ρ Δ₁} a ([ρ] : ρ ∷ Δ₁ ⊆ Δ) (⊢Δ₁ : ⊢ Δ₁)
             ([a] : Δ₁ ⊩⟨ l ⟩ a ∷ subst (ρ •ₛ σ) F ^ [ rF , ι lF ]
                / proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ])))
           → Σ (Δ₁ ⊩⟨ l ⟩ subst (consSubst (ρ •ₛ σ) a) G ^ [ rΠ , ι lG ])
               (λ [Aσ] →
               {σ′ : Nat → Term} →
               (Σ (Δ₁ ⊩ˢ tail σ′ ∷ Γ / [Γ] / ⊢Δ₁)
               (λ [tailσ] →
                  Δ₁ ⊩⟨ l ⟩ head σ′ ∷ subst (tail σ′) F ^ [ rF , ι lF ] / proj₁ ([F] ⊢Δ₁ [tailσ]))) →
               Δ₁ ⊩ˢ consSubst (ρ •ₛ σ) a ≡ σ′ ∷ Γ ∙ F ^ [ rF , ι lF ] /
               [Γ] ∙ [F] / ⊢Δ₁ /
               consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]) [F]
               [a] →
               Δ₁ ⊩⟨ l ⟩ subst (consSubst (ρ •ₛ σ) a) G ≡
               subst σ′ G ^ [ rΠ , ι lG ] / [Aσ])
      [G]a {ρ} a [ρ] ⊢Δ₁ [a] = ([G] {σ = consSubst (ρ •ₛ σ) a} ⊢Δ₁
                              (consSubstS {t = a} {A = F} [Γ] ⊢Δ₁
                                          (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ])
                                          [F] [a]))
      G'[a] : ∀ {ρ Δ₁} a ([ρ] : ρ ∷ Δ₁ ⊆ Δ) (⊢Δ₁ : ⊢ Δ₁)
         ([a] : Δ₁ ⊩⟨ l ⟩ a ∷ subst (ρ •ₛ σ) F ^ [ rF , ι lF ]
                / proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ])))
         → Δ₁ ⊩⟨ l ⟩ U.wk (lift ρ) (subst (liftSubst σ) G) [ a ] ^ [ rΠ , ι lG ]
      G'[a] a [ρ] ⊢Δ₁ [a] =  irrelevance′ (PE.sym (singleSubstWkComp a σ G)) (proj₁ ([G]a a [ρ] ⊢Δ₁ [a]))
  in Πᵣ′ rF lF lG (subst σ F) (subst (liftSubst σ) G)
         (idRed:*: (univ ⊢ΠF▹G)) (⊢F [σ]) (⊢G [σ]) (≅-univ (≅ₜ-Π-cong (⊢F [σ]) (≅-un-univ ⊢F≡F) (≅-un-univ ⊢G≡G)))
         (λ ρ ⊢Δ₁ → wk ρ ⊢Δ₁ [σF])
         (λ {ρ} {Δ₁} {a} [ρ] ⊢Δ₁ [a] →
            let [a]′ = irrelevanceTerm′
                         (wk-subst F) PE.refl PE.refl (wk [ρ] ⊢Δ₁ [σF])
                         (proj₁ ([F] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]))) [a]
            in  Gapp {F = F} {G = G} {σ = σ} [Γ] [F] [G] ⊢Δ [σ] a [ρ] ⊢Δ₁ [a]′)
         (λ {ρ} {Δ₁} {a} {b} [ρ] ⊢Δ₁ [a] [b] [a≡b] →
            let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]
                [a]′ = irrelevanceTerm′
                         (wk-subst F) PE.refl PE.refl (wk [ρ] ⊢Δ₁ [σF])
                         (proj₁ ([F] ⊢Δ₁ [ρσ])) [a]
                [b]′ = irrelevanceTerm′
                         (wk-subst F) PE.refl PE.refl (wk [ρ] ⊢Δ₁ [σF])
                         (proj₁ ([F] ⊢Δ₁ [ρσ])) [b]
                [a≡b]′ = irrelevanceEqTerm′
                           (wk-subst F) PE.refl PE.refl (wk [ρ] ⊢Δ₁ [σF])
                           (proj₁ ([F] ⊢Δ₁ [ρσ])) [a≡b]
                X = Gapp {F = F} {G = G} {σ = σ} [Γ] [F] [G] ⊢Δ [σ] a [ρ] ⊢Δ₁ [a]′
            in  irrelevanceEq″
                  (PE.sym (singleSubstWkComp a σ G))
                  (PE.sym (singleSubstWkComp b σ G)) PE.refl PE.refl
                  (proj₁ ([G]a a [ρ] ⊢Δ₁ [a]′)) 
                  (Gapp {F = F} {G = G} {σ = σ} [Γ] [F] [G] ⊢Δ [σ] a [ρ] ⊢Δ₁ [a]′)
                  (proj₂ ([G]a a [ρ] ⊢Δ₁ [a]′)
                         ([ρσ] , [b]′)
                         (reflSubst [Γ] ⊢Δ₁ [ρσ] , [a≡b]′)))
  ,  (λ {σ′} [σ′] [σ≡σ′] →
        let var0 = var (⊢Δ ∙ ⊢F [σ])
                       (PE.subst (λ x → 0 ∷ x ^ [ rF , ι lF ] ∈ (Δ ∙ subst σ F ^ [ rF , ι lF ]))
                                 (wk-subst F) here)
            [wk1σ] = wk1SubstS [Γ] ⊢Δ (⊢F [σ]) [σ]
            [wk1σ′] = wk1SubstS [Γ] ⊢Δ (⊢F [σ]) [σ′]
            [wk1σ≡wk1σ′] = wk1SubstSEq [Γ] ⊢Δ (⊢F [σ]) [σ] [σ≡σ′]
            [F][wk1σ] = proj₁ ([F] (⊢Δ ∙ ⊢F [σ]) [wk1σ])
            [F][wk1σ′] = proj₁ ([F] (⊢Δ ∙ ⊢F [σ]) [wk1σ′])
            var0′ = conv var0
                         (≅-eq (escapeEq [F][wk1σ]
                                             (proj₂ ([F] (⊢Δ ∙ ⊢F [σ]) [wk1σ])
                                                    [wk1σ′] [wk1σ≡wk1σ′])))
        in  Π₌ _ _ (id (univ (Πⱼ lF< ▹ lG< ▹ un-univ (⊢F [σ′]) ▹ un-univ (⊢G [σ′]))))
               (≅-univ (≅ₜ-Π-cong (⊢F [σ])
                                  (≅-un-univ (escapeEq (proj₁ ([F] ⊢Δ [σ]))
                                    (proj₂ ([F] ⊢Δ [σ]) [σ′] [σ≡σ′])))
                                  (≅-un-univ (escapeEq (proj₁ ([G]σ [σ])) (proj₂ ([G]σ [σ])
                                  ([wk1σ′] , neuTerm [F][wk1σ′] (var 0) var0′ (~-var var0′))
                                  ([wk1σ≡wk1σ′] , neuEqTerm [F][wk1σ]
                                  (var 0) (var 0) var0 var0 (~-var var0)))))))
               (λ ρ ⊢Δ₁ → wkEq ρ ⊢Δ₁ [σF] (proj₂ ([F] ⊢Δ [σ]) [σ′] [σ≡σ′]))
               (λ {ρ} {Δ₁} {a} [ρ] ⊢Δ₁ [a] →
                  let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]
                      [ρσ′] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ′]
                      [a]′ = irrelevanceTerm′ (wk-subst F) PE.refl PE.refl (wk [ρ] ⊢Δ₁ [σF])
                                 (proj₁ ([F] ⊢Δ₁ [ρσ])) [a]
                      [a]″ = convTerm₁ (proj₁ ([F] ⊢Δ₁ [ρσ]))
                                        (proj₁ ([F] ⊢Δ₁ [ρσ′]))
                                        (proj₂ ([F] ⊢Δ₁ [ρσ]) [ρσ′]
                                               (wkSubstSEq [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ] [σ≡σ′]))
                                        [a]′
                      [ρσa≡ρσ′a] = consSubstSEq {t = a} {A = F} [Γ] ⊢Δ₁
                                                (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ])
                                                (wkSubstSEq [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ] [σ≡σ′])
                                                [F] [a]′
                  in  irrelevanceEq″ (PE.sym (singleSubstWkComp a σ G))
                                      (PE.sym (singleSubstWkComp a σ′ G)) PE.refl PE.refl
                                      (proj₁ ([G]a a [ρ] ⊢Δ₁ [a]′))
                                      (G'[a] a [ρ] ⊢Δ₁ [a]′)
                                      (proj₂ ([G]a a [ρ] ⊢Δ₁ [a]′)
                                             (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ′] , [a]″)
                                             [ρσa≡ρσ′a])))

-- Validity of Π-congurence.
Π-congᵛ : ∀ {F G H E Γ rF lF lG rΠ lΠ l}
          (lF< : lF ≤ lΠ)
          (lG< : lG ≤ lΠ)
          ([Γ] : ⊩ᵛ Γ)
          ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / [Γ])
          ([G] : Γ ∙ F ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ G ^ [ rΠ , ι lG ] / [Γ] ∙ [F])
          ([H] : Γ ⊩ᵛ⟨ l ⟩ H ^ [ rF , ι lF ] / [Γ])
          ([E] : Γ ∙ H ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ E ^ [ rΠ , ι lG ] / [Γ] ∙ [H])
          ([F≡H] : Γ ⊩ᵛ⟨ l ⟩ F ≡ H ^ [ rF , ι lF ] / [Γ] / [F])
          ([G≡E] : Γ ∙ F ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ G ≡ E ^ [ rΠ , ι lG ] / [Γ] ∙ [F] / [G])
        → Γ ⊩ᵛ⟨ l ⟩ Π F ^ rF ° lF ▹ G ° lG  ≡ Π H ^ rF ° lF ▹ E ° lG ^ [ rΠ , ι lΠ ] / [Γ] / Πᵛ {F} {G} lF< lG< [Γ] [F] [G]
Π-congᵛ {F} {G} {H} {E} lF< lG< [Γ] [F] [G] [H] [E] [F≡H] [G≡E] {σ = σ} ⊢Δ [σ] =
  let [ΠFG] = Πᵛ {F} {G} lF< lG< [Γ] [F] [G]
      [σΠFG] = proj₁ ([ΠFG] ⊢Δ [σ])
      _ , Πᵣ rF′ lF' lG' F′ G′ D′ ⊢F′ ⊢G′ A≡A′ [F]′ [G]′ G-ext′ = extractMaybeEmb (Π-elim [σΠFG])
      [σF] = proj₁ ([F] ⊢Δ [σ])
      ⊢σF = escape [σF]
      [σG] = proj₁ ([G] (⊢Δ ∙ ⊢σF) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
      ⊢σH = escape (proj₁ ([H] ⊢Δ [σ]))
      ⊢σE = escape (proj₁ ([E] (⊢Δ ∙ ⊢σH) (liftSubstS {F = H} [Γ] ⊢Δ [H] [σ])))
      ⊢σF≡σH = escapeEq [σF] ([F≡H] ⊢Δ [σ])
      ⊢σG≡σE = escapeEq [σG] ([G≡E] (⊢Δ ∙ ⊢σF) (liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]))
  in  Π₌ (subst σ H)
         (subst (liftSubst σ) E)
         (id (univ (Πⱼ lF< ▹ lG< ▹ (un-univ ⊢σH) ▹ (un-univ ⊢σE))))
         (≅-univ (≅ₜ-Π-cong ⊢σF (≅-un-univ ⊢σF≡σH) (≅-un-univ ⊢σG≡σE)))
         (λ ρ ⊢Δ₁ → let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ ρ [σ]
                    in  irrelevanceEq″ (PE.sym (wk-subst F))
                                        (PE.sym (wk-subst H)) PE.refl PE.refl
                                        (proj₁ ([F] ⊢Δ₁ [ρσ]))
                                        ([F]′ ρ ⊢Δ₁)
                                        ([F≡H] ⊢Δ₁ [ρσ]))
         (λ {ρ} {Δ} {a} [ρ] ⊢Δ₁ [a] →
            let [ρσ] = wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]
                [a]′ = irrelevanceTerm′ (wk-subst F) PE.refl PE.refl 
                                        ([F]′ [ρ] ⊢Δ₁)
                                        (proj₁ ([F] ⊢Δ₁ [ρσ])) [a]
                [aρσ] = consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ [ρσ] [F] [a]′
            in  irrelevanceEq″ (PE.sym (singleSubstWkComp a σ G))
                                (PE.sym (singleSubstWkComp a σ E)) PE.refl PE.refl
                                (proj₁ ([G] ⊢Δ₁ [aρσ]))
                                ([G]′ [ρ] ⊢Δ₁ [a])
                                ([G≡E] ⊢Δ₁ [aρσ]))

{-
-- Validity of Π as a term.
Πᵗᵛ : ∀ {F G rF lF lG rΠ lΠ l Γ}
      (lΠ< : ι lΠ <∞ l)
      (lFΠ< : lF ≤ lΠ)  (lGΠ< : lG ≤ lΠ) 
      ([Γ] : ⊩ᵛ Γ)
      ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ [ rF , ι lF ] / [Γ])
      ([U] : Γ ∙ F ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ Univ rΠ lG ^ [ ! , next lG ] / [Γ] ∙ [F])
    → Γ ⊩ᵛ⟨ l ⟩ F ∷ Univ rF lF ^ [ ! , next lF ] / [Γ] / Uᵛgen lFΠ< lΠ< [Γ]
    → Γ ∙ F ^ [ rF , ι lF ] ⊩ᵛ⟨ l ⟩ G ∷ Univ rΠ lG ^ [ ! , next lG ] / [Γ] ∙ [F] / (λ {Δ} {σ} → [U] {Δ} {σ})
    → Γ ⊩ᵛ⟨ l ⟩ Π F ^ rF ° lF ▹ G ° lG ∷ Univ rΠ lΠ ^ [ ! , next lΠ ] / [Γ] / Uᵛ lΠ< [Γ]
Πᵗᵛ {F} {G} {rF} {lF} {lG} {rΠ} {lΠ} {l} {Γ} ∞< lFΠ< lGΠ< [Γ] [F] [U] [Fₜ] [Gₜ] {Δ = Δ} {σ = σ} ⊢Δ [σ] =
  let
      lΠ< = ∞<
      [liftσ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
      ⊢F = escape (proj₁ ([F] ⊢Δ [σ]))
      univΔ = proj₁ (Uᵛgen lFΠ< lΠ< [Γ] ⊢Δ [σ])
      -- [Fₜ]σ {σ′} [σ′] = [Fₜ] {σ = σ′} ⊢Δ [σ′]
      ⊢Fₜ = escapeTerm univΔ (proj₁ ([Fₜ] ⊢Δ [σ]))
      ⊢F≡Fₜ = escapeTermEq univΔ (reflEqTerm univΔ (proj₁ ([Fₜ] ⊢Δ [σ])))
      ⊢Gₜ = escapeTerm (proj₁ ([U] (⊢Δ ∙ ⊢F) [liftσ]))
                           (proj₁ ([Gₜ] (⊢Δ ∙ ⊢F) [liftσ]))
      ⊢G≡Gₜ = escapeTermEq (proj₁ ([U] (⊢Δ ∙ ⊢F) [liftσ]))
                               (reflEqTerm (proj₁ ([U] (⊢Δ ∙ ⊢F) [liftσ]))
                                           (proj₁ ([Gₜ] (⊢Δ ∙ ⊢F) [liftσ])))
      [F]₀ = univᵛ {F} [Γ] lFΠ< (Uᵛgen lFΠ< lΠ< [Γ]) [Fₜ]
      [Gₜ]′ = S.irrelevanceTerm {A = Univ rΠ lG} {t = G}
                                (_∙_ {A = F} [Γ] [F]) (_∙_ {A = F} [Γ] [F]₀)
                                (λ {Δ} {σ} → [U] {Δ} {σ})
                                (λ {Δ} {σ} → Uᵛgen lGΠ< lΠ< (_∙_ {A = F} [Γ] [F]₀) {Δ} {σ})
                                [Gₜ]
      [G]₀ = univᵛ {G} (_∙_ {A = F} [Γ] [F]₀) lGΠ<
                   (λ {Δ} {σ} → Uᵛgen lGΠ< lΠ< (_∙_ {A = F} [Γ] [F]₀) {Δ} {σ})
                   (λ {Δ} {σ} → [Gₜ]′ {Δ} {σ})
      [ΠFG] = (Πᵛ {F} {G} lFΠ< lGΠ< [Γ] [F]₀ [G]₀ ⊢Δ [σ])
      [Funiv] = univᵛ {A = F} [Γ] lFΠ< (Uᵛgen lFΠ< lΠ< [Γ]) [Fₜ]
      [Guniv] = univᵛ {A = G} (_∙_ {A = F} [Γ] [Funiv]) lGΠ< (Uᵛgen lGΠ< lΠ< (_∙_ {A = F} [Γ] [Funiv])) {!S.irrelevanceLift [Γ] [F] [Funiv] ? [Gₜ]!} -- [Gₜ]
  in Uₜ (Π subst σ F ^ rF ° lF ▹ subst (liftSubst σ) G ° lG) (idRedTerm:*: (Πⱼ lFΠ< ▹ lGΠ< ▹ ⊢Fₜ ▹ ⊢Gₜ)) Πₙ (≅ₜ-Π-cong ⊢F ⊢F≡Fₜ ⊢G≡Gₜ)
        (λ {ρ} {Δ₁} [ρ] ⊢Δ₁ →
                        let ⊢Fₜ' = Definition.Typed.Weakening.wkTerm [ρ] ⊢Δ₁ ⊢Fₜ
                            ⊢Gₜ' = Definition.Typed.Weakening.wkTerm
                                      (Definition.Typed.Weakening.lift [ρ]) (⊢Δ₁ ∙ univ ⊢Fₜ') ⊢Gₜ
                            [wkFₜ] = wkTerm [ρ] ⊢Δ₁ univΔ (proj₁ ([Fₜ] ⊢Δ [σ]))
                            [wkGₜ] = wkTerm (Definition.Typed.Weakening.lift [ρ]) (⊢Δ₁ ∙ univ ⊢Fₜ') (proj₁ ([U] (⊢Δ ∙ ⊢F) [liftσ])) (proj₁ ([Gₜ] (⊢Δ ∙ ⊢F) [liftσ]))
                            [⊢weakF≡Fₜ] = escapeTermEq (wk [ρ] ⊢Δ₁ univΔ)
                                                       (reflEqTerm (wk [ρ] ⊢Δ₁ univΔ) [wkFₜ])
                            [⊢weakG≡Gₜ] = escapeTermEq (wk (Definition.Typed.Weakening.lift [ρ]) (⊢Δ₁ ∙ univ ⊢Fₜ') (proj₁ ([U] (⊢Δ ∙ ⊢F) [liftσ])))
                                                       (reflEqTerm (wk (Definition.Typed.Weakening.lift [ρ]) (⊢Δ₁ ∙ univ ⊢Fₜ') (proj₁ ([U] (⊢Δ ∙ ⊢F) [liftσ])))
                                                       (wkTerm (Definition.Typed.Weakening.lift [ρ]) (⊢Δ₁ ∙ univ ⊢Fₜ') (proj₁ ([U] (⊢Δ ∙ ⊢F) [liftσ])) (proj₁ ([Gₜ] (⊢Δ ∙ ⊢F) [liftσ]))))
                            [G]a : ∀ {ρ Δ₁} a ([ρ] : ρ ∷ Δ₁ ⊆ Δ) (⊢Δ₁ : ⊢ Δ₁)
                              ([a] : Δ₁ ⊩⟨ ι ¹ ⟩ a ∷ subst (ρ •ₛ σ) F ^ [ rF , ι lF ]
                              / proj₁ ([Funiv] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ])))
                              → Σ (Δ₁ ⊩⟨ ι ¹ ⟩ subst (consSubst (ρ •ₛ σ) a) G ^ [ rΠ , ι lG ])
                              (λ [Aσ] →
                                {σ′ : Nat → Term} →
                                (Σ (Δ₁ ⊩ˢ tail σ′ ∷ Γ / [Γ] / ⊢Δ₁)
                                (λ [tailσ] →
                                  Δ₁ ⊩⟨ ι ¹ ⟩ head σ′ ∷ subst (tail σ′) F ^ [ rF , ι lF ] / proj₁ ([Funiv] ⊢Δ₁ [tailσ]))) →
                                  Δ₁ ⊩ˢ consSubst (ρ •ₛ σ) a ≡ σ′ ∷ Γ ∙ F ^ [ rF , ι lF ] /
                                  [Γ] ∙ [Funiv] / ⊢Δ₁ /
                                  consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]) [Funiv]
                                    [a] →
                                  Δ₁ ⊩⟨ ι ¹ ⟩ subst (consSubst (ρ •ₛ σ) a) G ≡
                                  subst σ′ G ^ [ rΠ , ι lG ] / [Aσ])
                            [G]a {ρ} a [ρ] ⊢Δ₁ [a] = [Guniv] {σ = consSubst (ρ •ₛ σ) a} ⊢Δ₁ (consSubstS {t = a} {A = F} [Γ] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ]) [Funiv] [a])
                            [G'a] : ∀ {ρ Δ₁} a ([ρ] : ρ ∷ Δ₁ ⊆ Δ) (⊢Δ₁ : ⊢ Δ₁)
                                  ([a] : Δ₁ ⊩⟨ ι ¹ ⟩ a ∷ subst (ρ •ₛ σ) F ^ [ rF , ι lF ]
                                    / proj₁ ([Funiv] ⊢Δ₁ (wkSubstS [Γ] ⊢Δ ⊢Δ₁ [ρ] [σ])))
                                    → Δ₁ ⊩⟨ ι ¹ ⟩ U.wk (lift ρ) (subst (liftSubst σ) G) [ a ] ^ [ rΠ , ι lG ]
                            [G'a] a [ρ] ⊢Δ₁ [a] =  irrelevance′ (PE.sym (singleSubstWkComp a σ G)) (proj₁ ([G]a a [ρ] ⊢Δ₁ [a]))
                        in
                          Πᵣ′ rF lF lG (U.wk ρ (subst σ F)) (U.wk (lift ρ) (subst (liftSubst σ) G))
                             (idRed:*: (univ (Πⱼ lFΠ< ▹ lGΠ< ▹ ⊢Fₜ' ▹ ⊢Gₜ')))
                             (univ ⊢Fₜ') (univ ⊢Gₜ') (≅-univ (≅ₜ-Π-cong (univ ⊢Fₜ') [⊢weakF≡Fₜ] [⊢weakG≡Gₜ]))
                             (λ {ρ'} {Δ₂} [ρ₁] ⊢Δ₂ → let [wkFₜ]Type = univEq (wk [ρ₁] ⊢Δ₂ (wk [ρ] ⊢Δ₁ (proj₁ (Uᵛgen lFΠ< ∞< [Γ] ⊢Δ [σ]))))
                                                                      (wkTerm [ρ₁] ⊢Δ₂ (wk [ρ] ⊢Δ₁ (proj₁ (Uᵛgen lFΠ< lΠ< [Γ] ⊢Δ [σ]))) [wkFₜ])
                                                   in maybeEmb′ lFΠ< [wkFₜ]Type)
                             {!!}
                             -- (λ {ρ₁} {Δ₂} {a} [ρ₁] ⊢Δ₂ [a] → let X = [G'a] a ([ρ₁] •ₜ [ρ]) ⊢Δ₂ [a] in PE.subst (λ X → _ ⊩⟨ ι ¹ ⟩ X ^ _) (wk-comp-subst _ _ _) X )
                             (λ [ρ]₁ ⊢Δ₂ [a] [b] x → {!!}))
  , {!!} 
  {- (λ {σ′} [σ′] [σ≡σ′] →
         let [liftσ′] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ′]
             [wk1σ] = wk1SubstS [Γ] ⊢Δ ⊢F [σ]
             [wk1σ′] = wk1SubstS [Γ] ⊢Δ ⊢F [σ′]
             var0 = conv (var (⊢Δ ∙ ⊢F)
                         (PE.subst (λ x → 0 ∷ x ^ [ rF , ι lF ] ∈ (Δ ∙ subst σ F ^ [ rF , ι lF ]))
                                   (wk-subst F) here))
                    (≅-eq (escapeEq (proj₁ ([F] (⊢Δ ∙ ⊢F) [wk1σ]))
                                        (proj₂ ([F] (⊢Δ ∙ ⊢F) [wk1σ]) [wk1σ′]
                                               (wk1SubstSEq [Γ] ⊢Δ ⊢F [σ] [σ≡σ′]))))
             [liftσ′]′ = [wk1σ′]
                       , neuTerm (proj₁ ([F] (⊢Δ ∙ ⊢F) [wk1σ′])) (var 0)
                                 var0 (~-var var0)
             ⊢F′ = escape (proj₁ ([F] ⊢Δ [σ′]))
             univΔ = proj₁ (Uᵛgen lFΠ< lΠ< [Γ] ⊢Δ [σ′])
             ⊢Fₜ′ = escapeTerm univΔ (proj₁ ([Fₜ] ⊢Δ [σ′]))
             ⊢Gₜ′ = escapeTerm (proj₁ ([U] (⊢Δ ∙ ⊢F′) [liftσ′]))
                                  (proj₁ ([Gₜ] (⊢Δ ∙ ⊢F′) [liftσ′]))
             ⊢F≡F′ = escapeTermEq univΔ {!!} -- (proj₂ ([Fₜ] ⊢Δ [σ]) [σ′] [σ≡σ′])
             ⊢G≡G′ = escapeTermEq (proj₁ ([U] (⊢Δ ∙ ⊢F) [liftσ]))
                                     (proj₂ ([Gₜ] (⊢Δ ∙ ⊢F) [liftσ]) [liftσ′]′
                                            (liftSubstSEq {F = F} [Γ] ⊢Δ [F] [σ] [σ≡σ′]))
             [ΠFG]′ = Πᵛ {F} {G} lFΠ< lGΠ< [Γ] [F]₀ [G]₀ ⊢Δ [σ′]
             [ΠFG-cong] = Π-congᵛ {F} {G} lFΠ< lGΠ< [Γ] [F]₀ [G]₀ [F]₀ [G]₀ {!!} {!!}
         in {!!} ) -}
          -- Uₜ₌ {!!} {!!} {!!} {!!}) 
                 -- (Π subst σ F ^ rF ° lF ▹ subst (liftSubst σ) G ° lG)
                 -- (Π subst σ′ F ^ rF ° lF ▹ subst (liftSubst σ′) G ° lG)
                 -- (idRedTerm:*: (Πⱼ ? ▹ ? ▹ ⊢Fₜ ▹ ⊢Gₜ))
                 -- (idRedTerm:*: (Πⱼ ? ▹ ? ▹ ⊢Fₜ′ ▹ ⊢Gₜ′))
                 -- Πₙ Πₙ                 
                 -- (proj₁ [ΠFG]) (proj₁ [ΠFG]′)
                 -- (≅ₜ-Π-cong ⊢F ⊢F≡F′ ⊢G≡G′)
                 -- (proj₂ [ΠFG] [σ′] [σ≡σ′]))



{-
-- Validity of Π-congurence as a term equality.
Π-congᵗᵛ : ∀ {F G H E rF lF lG rΠ lΠ Γ}
           ([Γ] : ⊩ᵛ Γ)
           ([F] : Γ ⊩ᵛ⟨ ¹ ⟩ F ^ [ rF , ι lF ] / [Γ])
           ([H] : Γ ⊩ᵛ⟨ ¹ ⟩ H ^ [ rF , ι lF ] / [Γ])
           ([UF] : Γ ∙ F ^ rF ⊩ᵛ⟨ ¹ ⟩ Univ rΠ lG ^ [ ! , next lG ] / [Γ] ∙ [F])
           ([UH] : Γ ∙ H ^ rF ⊩ᵛ⟨ ¹ ⟩ Univ rΠ lG ^ [ ! , next lG ] / [Γ] ∙ [H])
           ([F]ₜ : Γ ⊩ᵛ⟨ ¹ ⟩ F ∷ Univ rF lF ^ [ ! , next lF ] / [Γ] / Uᵛ [Γ])
           ([G]ₜ : Γ ∙ F ^ rF ⊩ᵛ⟨ ¹ ⟩ G ∷ Univ rΠ lG ^ [ ! , next lG ] / [Γ] ∙ [F]
                                / (λ {Δ} {σ} → [UF] {Δ} {σ}))
           ([H]ₜ : Γ ⊩ᵛ⟨ ¹ ⟩ H ∷ Univ rF lF ^ [ ! , next lF ] / [Γ] / Uᵛ [Γ])
           ([E]ₜ : Γ ∙ H ^ rF ⊩ᵛ⟨ ¹ ⟩ E ∷ Univ rΠ lG ^ [ ! , next lG ] / [Γ] ∙ [H]
                                / (λ {Δ} {σ} → [UH] {Δ} {σ}))
           ([F≡H]ₜ : Γ ⊩ᵛ⟨ ¹ ⟩ F ≡ H ∷ Univ rF lF ^ [ ! , next lF ] / [Γ] / Uᵛ [Γ])
           ([G≡E]ₜ : Γ ∙ F ^ rF ⊩ᵛ⟨ ¹ ⟩ G ≡ E ∷ Univ rΠ lG ^ [ ! , next lG ] / [Γ] ∙ [F]
                                  / (λ {Δ} {σ} → [UF] {Δ} {σ}))
         → Γ ⊩ᵛ⟨ ¹ ⟩ Π F ^ rF ° lF ▹ G ° lG ≡ Π H ^ rF ° lF  ▹ E ° lG ∷ Univ rΠ lΠ ^ [ ! , next lΠ ] / [Γ] / Uᵛ [Γ]
Π-congᵗᵛ {F} {G} {H} {E} {rF} {lF} {lG} {rΠ} {lΠ}
        {Γ} [Γ] [F] [H] [UF] [UH] [F]ₜ [G]ₜ [H]ₜ [E]ₜ [F≡H]ₜ [G≡E]ₜ {Δ} {σ} ⊢Δ [σ] =
  let ⊢F = escape (proj₁ ([F] ⊢Δ [σ]))
      ⊢H = escape (proj₁ ([H] ⊢Δ [σ]))
      [liftFσ] = liftSubstS {F = F} [Γ] ⊢Δ [F] [σ]
      [liftHσ] = liftSubstS {F = H} [Γ] ⊢Δ [H] [σ]
      [F]ᵤ = univᵛ {F} [Γ] (Uᵛ [Γ]) [F]ₜ
      [G]ᵤ₁ = univᵛ {G} {l′ = ⁰} (_∙_ {A = F} [Γ] [F])
                    (λ {Δ} {σ} → [UF] {Δ} {σ}) [G]ₜ
      [G]ᵤ = S.irrelevance {A = G} (_∙_ {A = F} [Γ] [F])
                           (_∙_ {A = F} [Γ] [F]ᵤ) [G]ᵤ₁
      [H]ᵤ = univᵛ {H} [Γ] (Uᵛ [Γ]) [H]ₜ
      [E]ᵤ = S.irrelevance {A = E} (_∙_ {A = H} [Γ] [H]) (_∙_ {A = H} [Γ] [H]ᵤ)
                           (univᵛ {E} {l′ = ⁰} (_∙_ {A = H} [Γ] [H])
                                  (λ {Δ} {σ} → [UH] {Δ} {σ}) [E]ₜ)
      [F≡H]ᵤ = univEqᵛ {F} {H} [Γ] (Uᵛ [Γ]) [F]ᵤ [F≡H]ₜ
      [G≡E]ᵤ = S.irrelevanceEq {A = G} {B = E} (_∙_ {A = F} [Γ] [F])
                               (_∙_ {A = F} [Γ] [F]ᵤ) [G]ᵤ₁ [G]ᵤ
                 (univEqᵛ {G} {E} (_∙_ {A = F} [Γ] [F])
                          (λ {Δ} {σ} → [UF] {Δ} {σ}) [G]ᵤ₁ [G≡E]ₜ)
      ΠFGₜ = Πⱼ ? ▹ ? ▹ escapeTerm {l = ¹} (Uᵣ′ _ ⁰ 0<1 ⊢Δ) (proj₁ ([F]ₜ ⊢Δ [σ]))
                ▹  escapeTerm (proj₁ ([UF] (⊢Δ ∙ ⊢F) [liftFσ]))
                           (proj₁ ([G]ₜ (⊢Δ ∙ ⊢F) [liftFσ]))
      ΠHEₜ = Πⱼ ? ▹ ? ▹ escapeTerm {l = ¹} (Uᵣ′ _ ⁰ 0<1 ⊢Δ) (proj₁ ([H]ₜ ⊢Δ [σ]))
             ▹  escapeTerm (proj₁ ([UH] (⊢Δ ∙ ⊢H) [liftHσ]))
                           (proj₁ ([E]ₜ (⊢Δ ∙ ⊢H) [liftHσ]))
  in 
  Uₜ₌ (Π subst σ F ^ rF ° lF ▹ subst (liftSubst σ) G ° lG)
          (Π subst σ H ^ rF ° lF ▹ subst (liftSubst σ) E ° lG)
          (idRedTerm:*: ΠFGₜ) (idRedTerm:*: ΠHEₜ)
          Πₙ Πₙ
          (≅ₜ-Π-cong ⊢F (escapeTermEq (Uᵣ′ _ ⁰ 0<1 ⊢Δ) ([F≡H]ₜ ⊢Δ [σ]))
                        (escapeTermEq (proj₁ ([UF] (⊢Δ ∙ ⊢F) [liftFσ]))
                                          ([G≡E]ₜ (⊢Δ ∙ ⊢F) [liftFσ])))
          (proj₁ (Πᵛ {F} {G} [Γ] [F]ᵤ [G]ᵤ ⊢Δ [σ]))
          (proj₁ (Πᵛ {H} {E} [Γ] [H]ᵤ [E]ᵤ ⊢Δ [σ]))
          (Π-congᵛ {F} {G} {H} {E} [Γ] [F]ᵤ [G]ᵤ [H]ᵤ [E]ᵤ [F≡H]ᵤ [G≡E]ᵤ ⊢Δ [σ])

{-
-- Validity of non-dependent function types.
▹▹ᵛ : ∀ {F G rF rG Γ l}
      ([Γ] : ⊩ᵛ Γ)
      ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ rF / [Γ])
    → Γ ⊩ᵛ⟨ l ⟩ G ^ rG / [Γ]
    → Γ ⊩ᵛ⟨ l ⟩ F ^ rF ▹▹ G ^ rG / [Γ]
▹▹ᵛ {F} {G} [Γ] [F] [G] =
  Πᵛ {F} {wk1 G} [Γ] [F] (wk1ᵛ {G} {F} [Γ] [F] [G])

-- Validity of non-dependent function type congurence.
▹▹-congᵛ : ∀ {F F′ G G′ rF rG Γ l}
           ([Γ] : ⊩ᵛ Γ)
           ([F] : Γ ⊩ᵛ⟨ l ⟩ F ^ rF / [Γ])
           ([F′] : Γ ⊩ᵛ⟨ l ⟩ F′ ^ rF / [Γ])
           ([F≡F′] : Γ ⊩ᵛ⟨ l ⟩ F ≡ F′ ^ rF / [Γ] / [F])
           ([G] : Γ ⊩ᵛ⟨ l ⟩ G ^ rG / [Γ])
           ([G′] : Γ ⊩ᵛ⟨ l ⟩ G′ ^ rG / [Γ])
           ([G≡G′] : Γ ⊩ᵛ⟨ l ⟩ G ≡ G′ ^ rG / [Γ] / [G])
         → Γ ⊩ᵛ⟨ l ⟩ F ^ rF ▹▹ G ≡ F′ ^ rF ▹▹ G′ ^ rG / [Γ] / ▹▹ᵛ {F} {G} [Γ] [F] [G]
▹▹-congᵛ {F} {F′} {G} {G′} [Γ] [F] [F′] [F≡F′] [G] [G′] [G≡G′] =
  Π-congᵛ {F} {wk1 G} {F′} {wk1 G′} [Γ]
          [F] (wk1ᵛ {G} {F} [Γ] [F] [G])
          [F′] (wk1ᵛ {G′} {F′} [Γ] [F′] [G′])
          [F≡F′] (wk1Eqᵛ {G} {G′} {F} [Γ] [F] [G] [G≡G′])
-}
-}

-}
