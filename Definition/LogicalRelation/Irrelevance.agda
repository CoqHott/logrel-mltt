{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Irrelevance {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Tools.Empty using (⊥; ⊥-elim)

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView

open import Tools.Product
import Tools.PropositionalEquality as PE

import Data.Fin as Fin
import Data.Nat as Nat

-- Irrelevance for propositionally equal types
irrelevance′ : ∀ {A A′ Γ r l}
             → A PE.≡ A′
             → Γ ⊩⟨ l ⟩ A ^ r
             → Γ ⊩⟨ l ⟩ A′ ^ r
irrelevance′ PE.refl [A] = [A]

-- Irrelevance for propositionally equal types and contexts
irrelevanceΓ′ : ∀ {l A A′ r Γ Γ′}
              → Γ PE.≡ Γ′
              → A PE.≡ A′
              → Γ  ⊩⟨ l ⟩ A ^ r
              → Γ′ ⊩⟨ l ⟩ A′ ^ r
irrelevanceΓ′ PE.refl PE.refl [A] = [A]

-- helper function to deal with relevance

reduction-irrelevant-Univ : ∀ {Γ A t l l' ll ll' l< l<' r r' el el' D D'}
        (e : r PE.≡ r') →
        Γ ⊩⟨ l ⟩ t ∷ A ^ [ ! , next ll ] / Uᵣ (Uᵣ r ll l< el D) →
        Γ ⊩⟨ l' ⟩ t ∷ A ^ [ ! , next ll ] / Uᵣ (Uᵣ r' ll' l<' el' D')
reduction-irrelevant-Univ {Γ} {A} {t} {l} {ι ¹} {ll} {¹} {l<} {Nat.s≤s ()} PE.refl _ 
reduction-irrelevant-Univ {Γ} {A} {t} {ι ¹} {l} {¹} {ll} {Nat.s≤s ()} {l<'} PE.refl _
reduction-irrelevant-Univ {Γ} {A} {t} {ι ¹} {ι ¹} {⁰} {⁰} PE.refl (Uₜ K d typeK K≡K [t] [IdK] IdKExt [castK] castKExt) = Uₜ K d typeK K≡K [t] [IdK] IdKExt [castK] castKExt
reduction-irrelevant-Univ {Γ} {A} {t} {ι ¹} {∞} {⁰} {⁰} PE.refl (Uₜ K d typeK K≡K [t] [IdK] IdKExt [castK] castKExt) = Uₜ K d typeK K≡K [t] [IdK] IdKExt [castK] castKExt
reduction-irrelevant-Univ {Γ} {A} {t} {∞} {ι ¹} {⁰} {⁰} PE.refl (Uₜ K d typeK K≡K [t] [IdK] IdKExt [castK] castKExt) = Uₜ K d typeK K≡K [t] [IdK] IdKExt [castK] castKExt
reduction-irrelevant-Univ {Γ} {A} {t} {∞} {∞} {⁰} {⁰} PE.refl (Uₜ K d typeK K≡K [t] [IdK] IdKExt [castK] castKExt) = Uₜ K d typeK K≡K [t] [IdK] IdKExt [castK] castKExt
reduction-irrelevant-Univ {Γ} {A} {t} {∞} {∞} {¹} {¹} PE.refl (Uₜ K d typeK K≡K [t] [IdK] IdKExt [castK] castKExt) = Uₜ K d typeK K≡K [t] [IdK] IdKExt [castK] castKExt

{-
reduction-irrelevant-Univ-K : ∀ {Γ A t l l' ll ll' l< l<' r r' el el' D D' e e'} →
                                (X : Γ ⊩⟨ l ⟩ t ∷ A ^ [ ! , next ll ] / Uᵣ (Uᵣ r ll l< el D)) →
                                LogRel._⊩¹U_∷_^_/_.K (reduction-irrelevant-Univ {l' = l'} {ll' = ll'} {l<' = l<'} {r' = r'} {el' = el'} {D' = D'} e e' X) PE.≡
                                LogRel._⊩¹U_∷_^_/_.K X
reduction-irrelevant-Univ-K {l = l} {ι ¹} {ll} {¹} {l<} {Nat.s≤s ()} {e = PE.refl} {PE.refl} _
reduction-irrelevant-Univ-K {l = ι ¹} {l} {¹} {ll} {Nat.s≤s ()} {l<'} {e = PE.refl} {PE.refl} _
reduction-irrelevant-Univ-K {l = ι ¹} {ι ¹} {⁰} {⁰} {e = PE.refl} {PE.refl} (Uₜ K d typeK K≡K [t] [IdK] IdKExt [castK] castKext) = PE.refl
reduction-irrelevant-Univ-K {l = ι ¹} {∞} {⁰} {⁰} {e = PE.refl} {PE.refl} (Uₜ K d typeK K≡K [t] [IdK] IdKExt [castK] castKext) = PE.refl
reduction-irrelevant-Univ-K {l = ∞} {ι ¹} {⁰} {⁰} {e = PE.refl} {PE.refl} (Uₜ K d typeK K≡K [t] [IdK] IdKExt [castK] castKext) = PE.refl
reduction-irrelevant-Univ-K {l = ∞} {∞} {⁰} {.⁰} {e = PE.refl} {PE.refl} (Uₜ K d typeK K≡K [t] [IdK] IdKExt [castK] castKext) = PE.refl
reduction-irrelevant-Univ-K {l = ∞} {∞} {¹} {.¹} {e = PE.refl} {PE.refl} (Uₜ K d typeK K≡K [t] [IdK] IdKExt [castK] castKext) = PE.refl
-}

reduction-irrelevant-Univ= : ∀ {Γ A t u l l' ll ll' l< l<' r r' el el' D D'}
        (e : r PE.≡ r') →
        Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ [ ! , next ll ] / Uᵣ (Uᵣ r ll l< el D) →
        Γ ⊩⟨ l' ⟩ t ≡ u ∷ A ^ [ ! , next ll ] / Uᵣ (Uᵣ r' ll' l<' el' D')
reduction-irrelevant-Univ= {l = ι ¹} {ι ¹} {⁰} {⁰} PE.refl (Uₜ₌ [t] [u] A≡B [t≡u] IdHo castHo) = Uₜ₌ (reduction-irrelevant-Univ PE.refl [t]) (reduction-irrelevant-Univ PE.refl [u]) A≡B [t≡u] IdHo castHo
reduction-irrelevant-Univ= {l = l} {ι ¹} {ll} {¹} {l<} {Nat.s≤s ()} PE.refl _
reduction-irrelevant-Univ= {l = ι ¹} {l} {¹} {ll} {Nat.s≤s ()} {l<'} PE.refl  _
reduction-irrelevant-Univ= {l = ι ¹} {∞} {⁰} {⁰} {l<} {l<'} PE.refl (Uₜ₌ [t] [u] A≡B [t≡u] IdHo castHo) = Uₜ₌ (reduction-irrelevant-Univ PE.refl [t]) (reduction-irrelevant-Univ PE.refl [u]) A≡B [t≡u] IdHo castHo
reduction-irrelevant-Univ= {l = ∞} {ι ¹} {⁰} {⁰} {l<} {l<'} PE.refl (Uₜ₌ [t] [u] A≡B [t≡u] IdHo castHo) = Uₜ₌ (reduction-irrelevant-Univ PE.refl [t]) (reduction-irrelevant-Univ PE.refl [u]) A≡B [t≡u] IdHo castHo
reduction-irrelevant-Univ= {l = ∞} {∞} {⁰} {⁰} {l<} {l<'} PE.refl (Uₜ₌ [t] [u] A≡B [t≡u] IdHo castHo) = Uₜ₌ (reduction-irrelevant-Univ PE.refl [t]) (reduction-irrelevant-Univ PE.refl [u]) A≡B [t≡u] IdHo castHo
reduction-irrelevant-Univ= {l = ∞} {∞} {¹} {¹} {l<} {l<'} PE.refl (Uₜ₌ [t] [u] A≡B [t≡u] IdHo castHo) = Uₜ₌ (reduction-irrelevant-Univ PE.refl [t]) (reduction-irrelevant-Univ PE.refl [u]) A≡B [t≡u] IdHo castHo


-- NB: for Pi cases it seems like it would be cleaner to do
-- irrelevanceFoo (Pi ...) rewrite whrDet* ...
-- instead of messing with PE.subst and irrelevanceEq′ etc
-- however for some reason the termination checker doesn't accept it

mutual
  -- Irrelevance for type equality
  irrelevanceEq : ∀ {Γ A B r l l′} (p : Γ ⊩⟨ l ⟩ A ^ r) (q : Γ ⊩⟨ l′ ⟩ A ^ r)
                → Γ ⊩⟨ l ⟩ A ≡ B ^ r / p → Γ ⊩⟨ l′ ⟩ A ≡ B ^ r / q
  irrelevanceEq p q A≡B = irrelevanceEqT (goodCasesRefl p q) A≡B

  -- Irrelevance for type equality with propositionally equal first types
  irrelevanceEq′ : ∀ {Γ A A′ B r r' l l′ ll ll'} (eq : A PE.≡ A′) (eqr : r PE.≡ r') (eql : ll PE.≡ ll')
                   (p : Γ ⊩⟨ l ⟩ A ^ [ r , ll ]) (q : Γ ⊩⟨ l′ ⟩ A′ ^ [ r' , ll' ])
                 → Γ ⊩⟨ l ⟩ A ≡ B ^ [ r , ll ] / p → Γ ⊩⟨ l′ ⟩ A′ ≡ B ^ [ r' , ll' ] / q
  irrelevanceEq′ PE.refl PE.refl PE.refl p q A≡B = irrelevanceEq p q A≡B

  -- Irrelevance for type equality with propositionally equal types
  irrelevanceEq″ : ∀ {Γ A A′ B B′ r l l′} (eqA : A PE.≡ A′) (eqB : B PE.≡ B′)
                    (p : Γ ⊩⟨ l ⟩ A ^ r) (q : Γ ⊩⟨ l′ ⟩ A′ ^ r)
                  → Γ ⊩⟨ l ⟩ A ≡ B ^ r / p → Γ ⊩⟨ l′ ⟩ A′ ≡ B′ ^ r / q
  irrelevanceEq″ PE.refl PE.refl p q A≡B = irrelevanceEq p q A≡B

  -- Irrelevance for type equality with propositionally equal second types
  irrelevanceEqR′ : ∀ {Γ A B B′ r l} (eqB : B PE.≡ B′) (p : Γ ⊩⟨ l ⟩ A ^ r)
                  → Γ ⊩⟨ l ⟩ A ≡ B ^ r / p → Γ ⊩⟨ l ⟩ A ≡ B′ ^ r / p
  irrelevanceEqR′ PE.refl p A≡B = A≡B

  -- Irrelevance for type equality with propositionally equal types and
  -- a lifting of propositionally equal types
  irrelevanceEqLift″ : ∀ {Γ A A′ B B′ C C′ rC r l l′}
                        (eqA : A PE.≡ A′) (eqB : B PE.≡ B′) (eqC : C PE.≡ C′)
                        (p : Γ ∙ C ^ rC ⊩⟨ l ⟩ A ^ r) (q : Γ ∙ C′ ^ rC ⊩⟨ l′ ⟩ A′ ^ r)
                      → Γ ∙ C ^ rC ⊩⟨ l ⟩ A ≡ B ^ r / p → Γ ∙ C′ ^ rC ⊩⟨ l′ ⟩ A′ ≡ B′ ^ r / q
  irrelevanceEqLift″ PE.refl PE.refl PE.refl p q A≡B = irrelevanceEq p q A≡B

  -- Helper for irrelevance of type equality using shape view
  irrelevanceEqT : ∀ {Γ A B r l l′} {p : Γ ⊩⟨ l ⟩ A ^ r} {q : Γ ⊩⟨ l′ ⟩ A ^ r}
                       → ShapeView Γ l l′ A A r r p q
                       → Γ ⊩⟨ l ⟩ A ≡ B ^ r / p → Γ ⊩⟨ l′ ⟩ A ≡ B ^ r / q
  irrelevanceEqT (ℕᵥ D D′) A≡B = A≡B
  irrelevanceEqT (Emptyᵥ D D′) A≡B = A≡B
  irrelevanceEqT (ne (ne K D neK _) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
                 rewrite whrDet* (red D , ne neK) (red D₁ , ne neK₁) =
    ne₌ M D′ neM K≡M
  irrelevanceEqT {Γ} {r = r} (Πᵥ (Πᵣ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                         (Πᵣ rF₁ lF₁ lG₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
                 (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
    let ΠFG≡ΠF₁G₁   = whrDet* (red D , Πₙ) (red D₁ , Πₙ)
        F≡F₁ , rF≡rF₁ , lF≡lF₁ , G≡G₁ , lG≡lG₁ = Π-PE-injectivity ΠFG≡ΠF₁G₁
    in  Π₌ F′ G′ (PE.subst₃ _ rF≡rF₁ lF≡lF₁ lG≡lG₁ D′)
        (PE.subst₄ (λ x rx lx lx' → Γ ⊢ x ≅ Π F′ ^ rx ° lx ▹ G′ ° lx' ^ r) ΠFG≡ΠF₁G₁ rF≡rF₁ lF≡lF₁ lG≡lG₁ A≡B)
           (λ {ρ} [ρ] ⊢Δ → irrelevanceEq′ (PE.cong (wk ρ) F≡F₁) rF≡rF₁ (PE.cong ι lF≡lF₁) ([F] [ρ] ⊢Δ)
                                          ([F]₁ [ρ] ⊢Δ)
                                          ([F≡F′] [ρ] ⊢Δ))
           (λ {ρ} [ρ] ⊢Δ [a]₁ →
              let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁)) (PE.sym rF≡rF₁) (PE.cong ι (PE.sym lF≡lF₁))
                                         ([F]₁ [ρ] ⊢Δ)
                                         ([F] [ρ] ⊢Δ)
                                         [a]₁
              in  irrelevanceEq′ (PE.cong (λ y → wk (lift ρ) y [ _ ]) G≡G₁) PE.refl (PE.cong ι lG≡lG₁)
                                 ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁) ([G≡G′] [ρ] ⊢Δ [a])) 
  irrelevanceEqT {Γ} {r = r} (∃ᵥ (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                         (∃ᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
                 (∃₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
    let ∃FG≡∃F₁G₁   = whrDet* (red D , ∃ₙ) (red D₁ , ∃ₙ)
        F≡F₁ , G≡G₁ = ∃-PE-injectivity ∃FG≡∃F₁G₁
    in  ∃₌ F′ G′ D′
    (PE.subst (λ x → Γ ⊢ x ≅ ∃ F′ ▹ G′ ^ r) ∃FG≡∃F₁G₁ A≡B)
           (λ {ρ} [ρ] ⊢Δ → irrelevanceEq′ (PE.cong (wk ρ) F≡F₁) PE.refl PE.refl ([F] [ρ] ⊢Δ)
                                          ([F]₁ [ρ] ⊢Δ)
                                          ([F≡F′] [ρ] ⊢Δ))
           (λ {ρ} [ρ] ⊢Δ [a]₁ →
              let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁)) (PE.refl) (PE.refl)
                                         ([F]₁ [ρ] ⊢Δ)
                                         ([F] [ρ] ⊢Δ)
                                         [a]₁
              in  irrelevanceEq′ (PE.cong (λ y → wk (lift ρ) y [ _ ]) G≡G₁) PE.refl PE.refl
                                 ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁) ([G≡G′] [ρ] ⊢Δ [a]))
  irrelevanceEqT (Uᵥ (Uᵣ _ _ _ PE.refl D) (Uᵣ _ _ _ e D')) A≡B = let U≡U  = whrDet* (red D , Uₙ) (red D' , Uₙ) in
                                                                let r≡r , l≡l = Univ-PE-injectivity U≡U in
                                                                 PE.subst _ l≡l (PE.subst _ r≡r A≡B)
  irrelevanceEqT (emb⁰¹ x) A≡B = irrelevanceEqT x A≡B
  irrelevanceEqT (emb¹⁰ x) A≡B = irrelevanceEqT x A≡B
  irrelevanceEqT (emb⁰∞ x) A≡B = irrelevanceEqT x A≡B
  irrelevanceEqT (emb∞⁰ x) A≡B = irrelevanceEqT x A≡B
  irrelevanceEqT (emb¹∞ x) A≡B = irrelevanceEqT x A≡B
  irrelevanceEqT (emb∞¹ x) A≡B = irrelevanceEqT x A≡B

--------------------------------------------------------------------------------

  -- Irrelevance for terms
  irrelevanceTerm : ∀ {Γ A t r l l′} (p : Γ ⊩⟨ l ⟩ A ^ r) (q : Γ ⊩⟨ l′ ⟩ A ^ r)
                  → Γ ⊩⟨ l ⟩ t ∷ A ^ r / p → Γ ⊩⟨ l′ ⟩ t ∷ A ^ r / q
  irrelevanceTerm p q t = irrelevanceTermT (goodCasesRefl p q) t

  -- Irrelevance for terms with propositionally equal types
  irrelevanceTerm′ : ∀ {Γ A A′ t r r' l l′ ll ll'} (eq : A PE.≡ A′) (req : r PE.≡ r') (leq : ll PE.≡ ll')
                     (p : Γ ⊩⟨ l ⟩ A ^ [ r , ll ]) (q : Γ ⊩⟨ l′ ⟩ A′ ^ [ r' , ll' ])
                   → Γ ⊩⟨ l ⟩ t ∷ A ^ [ r , ll ] / p → Γ ⊩⟨ l′ ⟩ t ∷ A′ ^ [ r' , ll' ] / q
  irrelevanceTerm′ PE.refl PE.refl PE.refl p q t = irrelevanceTerm p q t

  -- Irrelevance for terms with propositionally equal types and terms
  irrelevanceTerm″ : ∀ {Γ A A′ t t′ r l l′}
                      (eqA : A PE.≡ A′) (eqt : t PE.≡ t′)
                      (p : Γ ⊩⟨ l ⟩ A ^ r) (q : Γ ⊩⟨ l′ ⟩ A′ ^ r)
                    → Γ ⊩⟨ l ⟩ t ∷ A ^ r / p → Γ ⊩⟨ l′ ⟩ t′ ∷ A′ ^ r / q
  irrelevanceTerm″ PE.refl PE.refl p q t = irrelevanceTerm p q t

  -- Irrelevance for terms with propositionally equal types, terms and contexts
  irrelevanceTermΓ″ : ∀ {l l′ A A′ t t′ r Γ Γ′}
                     → Γ PE.≡ Γ′
                     → A PE.≡ A′
                     → t PE.≡ t′
                     → ([A]  : Γ  ⊩⟨ l  ⟩ A ^ r)
                       ([A′] : Γ′ ⊩⟨ l′ ⟩ A′ ^ r)
                     → Γ  ⊩⟨ l  ⟩ t ∷ A ^ r / [A]
                     → Γ′ ⊩⟨ l′ ⟩ t′ ∷ A′ ^ r / [A′]
  irrelevanceTermΓ″ PE.refl PE.refl PE.refl [A] [A′] [t] = irrelevanceTerm [A] [A′] [t]

  -- Helper for irrelevance of terms using shape view
  irrelevanceTermT : ∀ {Γ A t r l l′} {p : Γ ⊩⟨ l ⟩ A ^ r} {q : Γ ⊩⟨ l′ ⟩ A ^ r}
                         → ShapeView Γ l l′ A A r r p q
                         → Γ ⊩⟨ l ⟩ t ∷ A ^ r / p → Γ ⊩⟨ l′ ⟩ t ∷ A ^ r / q
  irrelevanceTermT (ℕᵥ D D′) t = t
  irrelevanceTermT (Emptyᵥ D D′) t = t
  irrelevanceTermT { r = [ ! , ll ]  } (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (neₜ k d nf)
                   with whrDet* (red D₁ , ne neK₁) (red D , ne neK)
  irrelevanceTermT {r = [ ! , ll ]} (ne (ne K D neK K≡K) (ne .K D₁ neK₁ K≡K₁)) (neₜ k d nf)
    | PE.refl = neₜ k d nf
  irrelevanceTermT { r = [ % , ll ] } (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (neₜ d)
                   with whrDet* (red D₁ , ne neK₁) (red D , ne neK)
  irrelevanceTermT {r = [ % , ll ]} (ne (ne K D neK K≡K) (ne .K D₁ neK₁ K≡K₁)) (neₜ d)
    | PE.refl = neₜ d
  irrelevanceTermT {Γ} {t = t} {r = [ ! , ll ]} (Πᵥ (Πᵣ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                   (Πᵣ rF₁ lF₁ lG₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
                   (Πₜ f d funcF f≡f [f] [f]₁) =
    let ΠFG≡ΠF₁G₁   = whrDet* (red D , Πₙ) (red D₁ , Πₙ)
        F≡F₁ , rF≡rF₁ , lF≡lF₁ , G≡G₁ , lG≡lG₁ = Π-PE-injectivity ΠFG≡ΠF₁G₁
    in  Πₜ f (PE.subst (λ x → Γ ⊢ t :⇒*: f ∷ x ^ ll) ΠFG≡ΠF₁G₁ d) funcF
           (PE.subst (λ x → Γ ⊢ f ≅ f ∷ x ^ [ ! , ll ]) ΠFG≡ΠF₁G₁ f≡f)
           (λ {ρ} [ρ] ⊢Δ [a]₁ [b]₁ [a≡b]₁ →
              let [a]   = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁)) (PE.sym rF≡rF₁) (PE.cong ι (PE.sym lF≡lF₁))
                                           ([F]₁ [ρ] ⊢Δ)
                                           ([F] [ρ] ⊢Δ)
                                           [a]₁
                  [b]   = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁)) (PE.sym rF≡rF₁) (PE.cong ι (PE.sym lF≡lF₁))
                                           ([F]₁ [ρ] ⊢Δ)
                                           ([F] [ρ] ⊢Δ)
                                           [b]₁
                  [a≡b] = irrelevanceEqTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁)) (PE.sym rF≡rF₁) (PE.cong ι (PE.sym lF≡lF₁))
                                             ([F]₁ [ρ] ⊢Δ)
                                             ([F] [ρ] ⊢Δ)
                                             [a≡b]₁
              in  irrelevanceEqTerm′ (PE.cong (λ G → wk (lift ρ) G [ _ ]) G≡G₁) PE.refl (PE.cong ι lG≡lG₁)
                                     ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁)
                                     ([f] [ρ] ⊢Δ [a] [b] [a≡b]))
          (λ {ρ} [ρ] ⊢Δ [a]₁ →
             let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁)) (PE.sym rF≡rF₁) (PE.cong ι (PE.sym lF≡lF₁))
                                        ([F]₁ [ρ] ⊢Δ)
                                        ([F] [ρ] ⊢Δ)
                                        [a]₁
             in  irrelevanceTerm′ (PE.cong (λ G → wk (lift ρ) G [ _ ]) G≡G₁) PE.refl (PE.cong ι lG≡lG₁)
                                  ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁) ([f]₁ [ρ] ⊢Δ [a]))
  irrelevanceTermT {Γ} {t = t} {r = [ % , ll ]} (Πᵥ (Πᵣ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                   (Πᵣ rF₁ lF₁ lG₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
                  d = let ΠFG≡ΠF₁G₁   = whrDet* (red D , Πₙ) (red D₁ , Πₙ)
                       in PE.subst (λ x → Γ ⊢ t ∷ x ^ [ % , ll ]) ΠFG≡ΠF₁G₁ d
  irrelevanceTermT {Γ} {t = t} {r = [ % , ll ]} (∃ᵥ (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                   (∃ᵣ  F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
                   d = let ∃FG≡∃F₁G₁   = whrDet* (red D , ∃ₙ) (red D₁ , ∃ₙ)
                       in PE.subst (λ x → Γ ⊢ t ∷ x ^ [ % , ll ]) ∃FG≡∃F₁G₁ d
  irrelevanceTermT (Uᵥ (Uᵣ r ll l< PE.refl D) (Uᵣ r' ll' l<' _ D')) t =
    let U≡U   = whrDet* (red D , Uₙ) (red D' , Uₙ)
        r≡r , l≡l = Univ-PE-injectivity U≡U
    in reduction-irrelevant-Univ r≡r t
  irrelevanceTermT (emb⁰¹ x) t = irrelevanceTermT x t
  irrelevanceTermT (emb¹⁰ x) t = irrelevanceTermT x t
  irrelevanceTermT (emb⁰∞ x) t = irrelevanceTermT x t
  irrelevanceTermT (emb∞⁰ x) t = irrelevanceTermT x t
  irrelevanceTermT (emb¹∞ x) t = irrelevanceTermT x t
  irrelevanceTermT (emb∞¹ x) t = irrelevanceTermT x t

--------------------------------------------------------------------------------

  -- Irrelevance for term equality
  irrelevanceEqTerm : ∀ {Γ A t u r l l′} (p : Γ ⊩⟨ l ⟩ A ^ r) (q : Γ ⊩⟨ l′ ⟩ A ^ r)
                    → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ r / p → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A ^ r / q
  irrelevanceEqTerm p q t≡u = irrelevanceEqTermT (goodCasesRefl p q) t≡u

  -- Irrelevance for term equality with propositionally equal types
  irrelevanceEqTerm′ : ∀ {Γ A A′ t u r r' l l′ ll ll'} (eq : A PE.≡ A′) (req : r PE.≡ r') (leq : ll PE.≡ ll')
                       (p : Γ ⊩⟨ l ⟩ A ^ [ r , ll ]) (q : Γ ⊩⟨ l′ ⟩ A′ ^ [ r' , ll' ])
                     → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ [ r , ll ] / p → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A′ ^ [ r' , ll' ] / q
  irrelevanceEqTerm′ PE.refl PE.refl PE.refl p q t≡u = irrelevanceEqTerm p q t≡u

  -- Irrelevance for term equality with propositionally equal types and terms
  irrelevanceEqTerm″ : ∀ {Γ A A′ t t′ u u′ r l l′}
                        (eqt : t PE.≡ t′) (equ : u PE.≡ u′) (eqA : A PE.≡ A′)
                        (p : Γ ⊩⟨ l ⟩ A ^ r) (q : Γ ⊩⟨ l′ ⟩ A′ ^ r)
                      → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ r / p → Γ ⊩⟨ l′ ⟩ t′ ≡ u′ ∷ A′ ^ r / q
  irrelevanceEqTerm″ PE.refl PE.refl PE.refl p q t≡u = irrelevanceEqTerm p q t≡u

  -- Helper for irrelevance of term equality using shape view
  irrelevanceEqTermT : ∀ {Γ A t u r} {l l′} {p : Γ ⊩⟨ l ⟩ A ^ r} {q : Γ ⊩⟨ l′ ⟩ A ^ r}
                           → ShapeView Γ l l′ A A r r p q
                           → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ r / p → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A ^ r / q
  irrelevanceEqTermT (ℕᵥ D D′) t≡u = t≡u
  irrelevanceEqTermT (Emptyᵥ D D′) t≡u = t≡u
  irrelevanceEqTermT { r = [ ! , ll ] } (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (neₜ₌ k m d d′ nf)
                     with whrDet* (red D₁ , ne neK₁) (red D , ne neK)
  irrelevanceEqTermT (ne (ne K D neK K≡K) (ne .K D₁ neK₁ K≡K₁)) (neₜ₌ k m d d′ nf)
    | PE.refl = neₜ₌ k m d d′ nf
  irrelevanceEqTermT { r = [ % , ll ] } (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (neₜ₌ d d′)
                     with whrDet* (red D₁ , ne neK₁) (red D , ne neK)
  irrelevanceEqTermT (ne (ne K D neK K≡K) (ne .K D₁ neK₁ K≡K₁)) (neₜ₌ d d′)
    | PE.refl = neₜ₌ d d′
  irrelevanceEqTermT {Γ} {t = t} {u = u} {r = [ ! , ll ]}
                     (Πᵥ (Πᵣ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                         (Πᵣ rF₁ lF₁ lG₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
                     (Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g]) =
    let ΠFG≡ΠF₁G₁   = whrDet* (red D , Πₙ) (red D₁ , Πₙ)
        F≡F₁ , rF≡rF₁ , lF≡lF₁ , G≡G₁ , lG≡lG₁ = Π-PE-injectivity ΠFG≡ΠF₁G₁
        [A]         = Πᵣ′ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext
        [A]₁        = Πᵣ′ rF₁ lF₁ lG₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁
    in  Πₜ₌ f g (PE.subst (λ x → Γ ⊢ t :⇒*: f ∷ x ^ ll) ΠFG≡ΠF₁G₁ d)
            (PE.subst (λ x → Γ ⊢ u :⇒*: g ∷ x ^ ll) ΠFG≡ΠF₁G₁ d′) funcF funcG
            (PE.subst (λ x → Γ ⊢ f ≅ g ∷ x ^ [ ! , ll ]) ΠFG≡ΠF₁G₁ f≡g)
            (irrelevanceTerm [A] [A]₁ [f]) (irrelevanceTerm [A] [A]₁ [g])
            (λ {ρ} [ρ] ⊢Δ [a]₁ →
               let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁)) (PE.sym rF≡rF₁) (PE.cong ι (PE.sym lF≡lF₁))
                                          ([F]₁ [ρ] ⊢Δ)
                                          ([F] [ρ] ⊢Δ)
                                          [a]₁
               in  irrelevanceEqTerm′ (PE.cong (λ G → wk (lift ρ) G [ _ ]) G≡G₁) PE.refl (PE.cong ι lG≡lG₁)
                                     ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁) ([f≡g] [ρ] ⊢Δ [a]))
  irrelevanceEqTermT {Γ} {t = t} {u = u} {r = [ % , ll ]}
                     (Πᵥ (Πᵣ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                         (Πᵣ rF₁ lF₁ lG₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
                     (d , d′) = let ΠFG≡ΠF₁G₁   = whrDet* (red D , Πₙ) (red D₁ , Πₙ) in
                                (PE.subst (λ x → Γ ⊢ t ∷ x ^ [ % , ll ]) ΠFG≡ΠF₁G₁ d , PE.subst (λ x → Γ ⊢ u ∷ x ^ [ % , ll ]) ΠFG≡ΠF₁G₁ d′)
  irrelevanceEqTermT {Γ} {t = t} {u = u} {r = [ % , ll ]}
                     (∃ᵥ (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                         (∃ᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
                     (d , d′) = let ∃FG≡∃F₁G₁   = whrDet* (red D , ∃ₙ) (red D₁ , ∃ₙ) in
                                (PE.subst (λ x → Γ ⊢ t ∷ x ^ [ % , ll ]) ∃FG≡∃F₁G₁ d , PE.subst (λ x → Γ ⊢ u ∷ x ^ [ % , ll ]) ∃FG≡∃F₁G₁ d′)
  irrelevanceEqTermT (Uᵥ (Uᵣ r ll l< PE.refl D) (Uᵣ r' ll' l<' _ D')) t =
    let U≡U   = whrDet* (red D , Uₙ) (red D' , Uₙ)
        r≡r , l≡l = Univ-PE-injectivity U≡U
    in reduction-irrelevant-Univ= r≡r t
  irrelevanceEqTermT (emb⁰¹ x) t≡u = irrelevanceEqTermT x t≡u
  irrelevanceEqTermT (emb¹⁰ x) t≡u = irrelevanceEqTermT x t≡u
  irrelevanceEqTermT (emb⁰∞ x) t≡u = irrelevanceEqTermT x t≡u
  irrelevanceEqTermT (emb∞⁰ x) t≡u = irrelevanceEqTermT x t≡u
  irrelevanceEqTermT (emb¹∞ x) t≡u = irrelevanceEqTermT x t≡u
  irrelevanceEqTermT (emb∞¹ x) t≡u = irrelevanceEqTermT x t≡u
