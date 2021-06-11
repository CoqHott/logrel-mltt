{-# OPTIONS --without-K  #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Irrelevance {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView

open import Tools.Product
import Tools.PropositionalEquality as PE

-- []-cstr-PE : ∀ {K K' t} (K≡K' : K PE.≡ K') (d : [ K ]-cstr t) → [ K' ]-cstr t
-- []-cstr-PE PE.refl d = d

Cstr-prop-ext : ∀ {K K' Γ Pi Pi' t a s}
                  (K≡K' : K PE.≡ K')
                  (Pi→Pi' : ∀ ki kiK  kiK' t → Pi ki kiK t → Pi' ki kiK' t)
                  (d : Cstr-prop K Γ Pi a s t)
                → Cstr-prop K' Γ Pi' a s t
Cstr-prop-ext PE.refl Pi→Pi' (cstrᵣ kK x) = cstrᵣ kK (Pi→Pi' _ kK kK _ x)
Cstr-prop-ext PE.refl Pi→Pi' (ne x) = ne x

[Cstr]-prop-ext : ∀ {K K' Γ Pi Pi' t t' a s}
                    (K≡K' : K PE.≡ K')
                    (Pi→Pi' : ∀ ki kiK  kiK' t t' → Pi ki kiK t t' → Pi' ki kiK' t t')
                    (d : [Cstr]-prop K Γ Pi a s t t')
                  → [Cstr]-prop K' Γ Pi' a s t t'
[Cstr]-prop-ext PE.refl Pi→Pi' (cstrᵣ kK x) = cstrᵣ kK (Pi→Pi' _ kK kK _ _ x)
[Cstr]-prop-ext PE.refl Pi→Pi' (ne x) = ne x

-- Irrelevance for propositionally equal types
irrelevance′ : ∀ {A A′ Γ s l}
             → A PE.≡ A′
             → Γ ⊩⟨ l ⟩ A ⦂ s
             → Γ ⊩⟨ l ⟩ A′ ⦂ s
irrelevance′ PE.refl [A] = [A]

-- Irrelevance for propositionally equal types and contexts
irrelevanceΓ′ : ∀ {l A A′ s Γ Γ′}
              → Γ PE.≡ Γ′
              → A PE.≡ A′
              → Γ  ⊩⟨ l ⟩ A ⦂ s
              → Γ′ ⊩⟨ l ⟩ A′ ⦂ s
irrelevanceΓ′ PE.refl PE.refl [A] = [A]

-- NB: for Pi cases it seems like it would be cleaner to do
-- irrelevanceFoo (Pi ...) rewrite whrDet* ...
-- instead of messing with PE.subst and irrelevanceEq′ etc
-- however for some reason the termination checker doesn't accept it

mutual
  -- Irrelevance for type equality
  irrelevanceEq : ∀ {Γ A B s l l′} (p : Γ ⊩⟨ l ⟩ A ⦂ s) (q : Γ ⊩⟨ l′ ⟩ A ⦂ s)
                → Γ ⊩⟨ l ⟩ A ≡ B ⦂ s / p → Γ ⊩⟨ l′ ⟩ A ≡ B ⦂ s / q
  irrelevanceEq p q A≡B = irrelevanceEqT (goodCasesRefl p q) A≡B

  -- Irrelevance for type equality with propositionally equal first types
  irrelevanceEq′ : ∀ {Γ A A′ B s s' l l′} (eq : A PE.≡ A′) (eqr : s PE.≡ s')
                   (p : Γ ⊩⟨ l ⟩ A ⦂ s) (q : Γ ⊩⟨ l′ ⟩ A′ ⦂ s')
                 → Γ ⊩⟨ l ⟩ A ≡ B ⦂ s / p → Γ ⊩⟨ l′ ⟩ A′ ≡ B ⦂ s' / q
  irrelevanceEq′ PE.refl PE.refl p q A≡B = irrelevanceEq p q A≡B

  -- Irrelevance for type equality with propositionally equal types
  irrelevanceEq″ : ∀ {Γ A A′ B B′ s l l′} (eqA : A PE.≡ A′) (eqB : B PE.≡ B′)
                    (p : Γ ⊩⟨ l ⟩ A ⦂ s) (q : Γ ⊩⟨ l′ ⟩ A′ ⦂ s)
                  → Γ ⊩⟨ l ⟩ A ≡ B ⦂ s / p → Γ ⊩⟨ l′ ⟩ A′ ≡ B′ ⦂ s / q
  irrelevanceEq″ PE.refl PE.refl p q A≡B = irrelevanceEq p q A≡B

  -- Irrelevance for type equality with propositionally equal second types
  irrelevanceEqR′ : ∀ {Γ A B B′ s l} (eqB : B PE.≡ B′) (p : Γ ⊩⟨ l ⟩ A ⦂ s)
                  → Γ ⊩⟨ l ⟩ A ≡ B ⦂ s / p → Γ ⊩⟨ l ⟩ A ≡ B′ ⦂ s / p
  irrelevanceEqR′ PE.refl p A≡B = A≡B

  -- Irrelevance for type equality with propositionally equal types and
  -- a lifting of propositionally equal types
  irrelevanceEqLift″ : ∀ {Γ A A′ B B′ C C′ sC s l l′}
                        (eqA : A PE.≡ A′) (eqB : B PE.≡ B′) (eqC : C PE.≡ C′)
                        (p : Γ ∙ C ⦂ sC ⊩⟨ l ⟩ A ⦂ s) (q : Γ ∙ C′ ⦂ sC ⊩⟨ l′ ⟩ A′ ⦂ s)
                      → Γ ∙ C ⦂ sC ⊩⟨ l ⟩ A ≡ B ⦂ s / p → Γ ∙ C′ ⦂ sC ⊩⟨ l′ ⟩ A′ ≡ B′ ⦂ s / q
  irrelevanceEqLift″ PE.refl PE.refl PE.refl p q A≡B = irrelevanceEq p q A≡B

  -- Helper for irrelevance of type equality using shape view
  irrelevanceEqT : ∀ {Γ A B s l l′} {p : Γ ⊩⟨ l ⟩ A ⦂ s} {q : Γ ⊩⟨ l′ ⟩ A ⦂ s}
                       → ShapeView Γ l l′ A A s s p q
                       → Γ ⊩⟨ l ⟩ A ≡ B ⦂ s / p → Γ ⊩⟨ l′ ⟩ A ≡ B ⦂ s / q
  irrelevanceEqT (ℕᵥ D D′) A≡B = A≡B
  irrelevanceEqT (Emptyᵥ D D′) A≡B = A≡B
  irrelevanceEqT (ne (ne K D neK _) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
                 rewrite whrDet* (red D , ne neK) (red D₁ , ne neK₁) =
    ne₌ M D′ neM K≡M
  irrelevanceEqT {Γ} {s = s} {l′ = l′} (cstrᵥ (cstrᵣ K KcodU a D ⊢a A≡A [domK] [a] [Yi])
                        (cstrᵣ K₁ _ _ D₁ _ _ [domK]₁ [a]₁ [Yi]₁))
                 (cstr₌ a' D' A≡B [a≡a']) =
    let Ka≡K₁a₁ = whrDet* (red D , cstrₙ) (red D₁ , cstrₙ)
        K≡K₁    = cstr-app-PE-injectivity Ka≡K₁a₁
        a≡a₁    = cstr-app-PE-arg-injectivity Ka≡K₁a₁
    in
    cstr₌ a' (PE.subst (λ x → _ ⊢ _ :⇒*: cstr x ∘ a' ⦂ _) K≡K₁ D')
             (PE.subst₂ (λ x y → Γ ⊢ x ≅ a' ∷ wkAll Γ (cstr-dom y) ⦂ cstr-dom-sort y) a≡a₁ K≡K₁ A≡B)
             (PE.subst (λ x → Γ ⊩⟨ l′ ⟩ x ≡ a' ∷ _ ⦂ cstr-dom-sort K₁ / [domK]₁) a≡a₁
                       (irrelevanceEqTerm′ (PE.cong (λ x → wkAll Γ (cstr-dom x)) K≡K₁) (PE.cong cstr-dom-sort K≡K₁) [domK] [domK]₁ [a≡a']) )
  irrelevanceEqT {Γ} {s = s} (Πᵥ (Πᵣ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                         (Πᵣ sF₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
                 (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
    let ΠFG≡ΠF₁G₁   = whrDet* (red D , Πₙ) (red D₁ , Πₙ)
        F≡F₁ , sF≡sF₁ , G≡G₁ = Π-PE-injectivity ΠFG≡ΠF₁G₁
    in  Π₌ F′ G′ (PE.subst _ sF≡sF₁ D′)
    (PE.subst₂ (λ x sx → Γ ⊢ x ≅ Π F′ ⦂ sx ▹ G′ ⦂ s) ΠFG≡ΠF₁G₁ sF≡sF₁ A≡B)
           (λ {ρ} [ρ] ⊢Δ → irrelevanceEq′ (PE.cong (wk ρ) F≡F₁) sF≡sF₁ ([F] [ρ] ⊢Δ)
                                          ([F]₁ [ρ] ⊢Δ)
                                          ([F≡F′] [ρ] ⊢Δ))
           (λ {ρ} [ρ] ⊢Δ [a]₁ →
              let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁)) (PE.sym sF≡sF₁)
                                         ([F]₁ [ρ] ⊢Δ)
                                         ([F] [ρ] ⊢Δ)
                                         [a]₁
              in  irrelevanceEq′ (PE.cong (λ y → wk (lift ρ) y [ _ ]) G≡G₁) PE.refl
                                 ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁) ([G≡G′] [ρ] ⊢Δ [a]))
  irrelevanceEqT (Uᵥ (Uᵣ _ _ _) (Uᵣ _ _ _)) A≡B = A≡B
  irrelevanceEqT (emb⁰¹ x) A≡B = irrelevanceEqT x A≡B
  irrelevanceEqT (emb¹⁰ x) A≡B = irrelevanceEqT x A≡B

--------------------------------------------------------------------------------

  -- Irrelevance for terms
  irrelevanceTerm : ∀ {Γ A t s l l′} (p : Γ ⊩⟨ l ⟩ A ⦂ s) (q : Γ ⊩⟨ l′ ⟩ A ⦂ s)
                  → Γ ⊩⟨ l ⟩ t ∷ A ⦂ s / p → Γ ⊩⟨ l′ ⟩ t ∷ A ⦂ s / q
  irrelevanceTerm p q t = irrelevanceTermT (goodCasesRefl p q) t

  -- Irrelevance for terms with propositionally equal types
  irrelevanceTerm′ : ∀ {Γ A A′ t s s' l l′} (eq : A PE.≡ A′) (req : s PE.≡ s')
                     (p : Γ ⊩⟨ l ⟩ A ⦂ s) (q : Γ ⊩⟨ l′ ⟩ A′ ⦂ s')
                   → Γ ⊩⟨ l ⟩ t ∷ A ⦂ s / p → Γ ⊩⟨ l′ ⟩ t ∷ A′ ⦂ s' / q
  irrelevanceTerm′ PE.refl PE.refl p q t = irrelevanceTerm p q t

  -- Irrelevance for terms with propositionally equal types and terms
  irrelevanceTerm″ : ∀ {Γ A A′ t t′ s l l′}
                      (eqA : A PE.≡ A′) (eqt : t PE.≡ t′)
                      (p : Γ ⊩⟨ l ⟩ A ⦂ s) (q : Γ ⊩⟨ l′ ⟩ A′ ⦂ s)
                    → Γ ⊩⟨ l ⟩ t ∷ A ⦂ s / p → Γ ⊩⟨ l′ ⟩ t′ ∷ A′ ⦂ s / q
  irrelevanceTerm″ PE.refl PE.refl p q t = irrelevanceTerm p q t

  -- Irrelevance for terms with propositionally equal types, terms and contexts
  irrelevanceTermΓ″ : ∀ {l l′ A A′ t t′ s Γ Γ′}
                     → Γ PE.≡ Γ′
                     → A PE.≡ A′
                     → t PE.≡ t′
                     → ([A]  : Γ  ⊩⟨ l  ⟩ A ⦂ s)
                       ([A′] : Γ′ ⊩⟨ l′ ⟩ A′ ⦂ s)
                     → Γ  ⊩⟨ l  ⟩ t ∷ A ⦂ s / [A]
                     → Γ′ ⊩⟨ l′ ⟩ t′ ∷ A′ ⦂ s / [A′]
  irrelevanceTermΓ″ PE.refl PE.refl PE.refl [A] [A′] [t] = irrelevanceTerm [A] [A′] [t]

  -- Helper for irrelevance of terms using shape view
  irrelevanceTermT : ∀ {Γ A t s l l′} {p : Γ ⊩⟨ l ⟩ A ⦂ s} {q : Γ ⊩⟨ l′ ⟩ A ⦂ s}
                         → ShapeView Γ l l′ A A s s p q
                         → Γ ⊩⟨ l ⟩ t ∷ A ⦂ s / p → Γ ⊩⟨ l′ ⟩ t ∷ A ⦂ s / q
  irrelevanceTermT (ℕᵥ D D′) t = t
  irrelevanceTermT (Emptyᵥ D D′) t = t
  irrelevanceTermT (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (neₜ k d nf)
                   with whrDet* (red D₁ , ne neK₁) (red D , ne neK)
  irrelevanceTermT (ne (ne K D neK K≡K) (ne .K D₁ neK₁ K≡K₁)) (neₜ k d nf)
    | PE.refl = neₜ k d nf

  irrelevanceTermT {Γ} {t = t} {s = s}
                   (cstrᵥ (cstrᵣ K KcodU a D ⊢a A≡A [domK] [a] [Yi])
                          (cstrᵣ K₁ _ _ D₁ _ _ [domK]₁ [a]₁ [Yi]₁))
                   (cstrₜ k d k≡k [k]) =
    let Ka≡K₁a₁ = whrDet* (red D , cstrₙ) (red D₁ , cstrₙ)
        K≡K₁    = cstr-app-PE-injectivity Ka≡K₁a₁
        a≡a₁    = cstr-app-PE-arg-injectivity Ka≡K₁a₁
    in
    cstrₜ k
         (PE.subst (λ x → Γ ⊢ t :⇒*: k ∷ x ⦂ s) Ka≡K₁a₁ d)
         (PE.subst (λ x → Γ ⊢ k ≅ k ∷ x ⦂ s) Ka≡K₁a₁ k≡k)
         (PE.subst (λ a → Cstr-prop K₁ Γ _ a s k) a≡a₁
                   (Cstr-prop-ext  K≡K₁  (λ ki kiK kiK' t d → irrelevanceTerm ([Yi] ki kiK) ([Yi]₁ ki kiK') d) [k]))
  irrelevanceTermT {Γ} {t = t} {s = s} (Πᵥ (Πᵣ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                   (Πᵣ sF₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
                   (Πₜ f d funcF f≡f [f] [f]₁) =
    let ΠFG≡ΠF₁G₁   = whrDet* (red D , Πₙ) (red D₁ , Πₙ)
        F≡F₁ , sF≡sF₁ , G≡G₁ = Π-PE-injectivity ΠFG≡ΠF₁G₁
    in  Πₜ f (PE.subst (λ x → Γ ⊢ t :⇒*: f ∷ x ⦂ s) ΠFG≡ΠF₁G₁ d) funcF
           (PE.subst (λ x → Γ ⊢ f ≅ f ∷ x ⦂ s) ΠFG≡ΠF₁G₁ f≡f)
           (λ {ρ} [ρ] ⊢Δ [a]₁ [b]₁ [a≡b]₁ →
              let [a]   = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁)) (PE.sym sF≡sF₁)
                                           ([F]₁ [ρ] ⊢Δ)
                                           ([F] [ρ] ⊢Δ)
                                           [a]₁
                  [b]   = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁)) (PE.sym sF≡sF₁)
                                           ([F]₁ [ρ] ⊢Δ)
                                           ([F] [ρ] ⊢Δ)
                                           [b]₁
                  [a≡b] = irrelevanceEqTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁)) (PE.sym sF≡sF₁)
                                             ([F]₁ [ρ] ⊢Δ)
                                             ([F] [ρ] ⊢Δ)
                                             [a≡b]₁
              in  irrelevanceEqTerm′ (PE.cong (λ G → wk (lift ρ) G [ _ ]) G≡G₁) PE.refl
                                     ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁)
                                     ([f] [ρ] ⊢Δ [a] [b] [a≡b]))
          (λ {ρ} [ρ] ⊢Δ [a]₁ →
             let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁)) (PE.sym sF≡sF₁)
                                        ([F]₁ [ρ] ⊢Δ)
                                        ([F] [ρ] ⊢Δ)
                                        [a]₁
             in  irrelevanceTerm′ (PE.cong (λ G → wk (lift ρ) G [ _ ]) G≡G₁) PE.refl
                                  ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁) ([f]₁ [ρ] ⊢Δ [a]))
  irrelevanceTermT (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) t = t
  irrelevanceTermT (emb⁰¹ x) t = irrelevanceTermT x t
  irrelevanceTermT (emb¹⁰ x) t = irrelevanceTermT x t

--------------------------------------------------------------------------------

  -- Irrelevance for term equality
  irrelevanceEqTerm : ∀ {Γ A t u s l l′} (p : Γ ⊩⟨ l ⟩ A ⦂ s) (q : Γ ⊩⟨ l′ ⟩ A ⦂ s)
                    → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ⦂ s / p → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A ⦂ s / q
  irrelevanceEqTerm p q t≡u = irrelevanceEqTermT (goodCasesRefl p q) t≡u

  -- Irrelevance for term equality with propositionally equal types
  irrelevanceEqTerm′ : ∀ {Γ A A′ t u s s' l l′} (eq : A PE.≡ A′) (req : s PE.≡ s')
                       (p : Γ ⊩⟨ l ⟩ A ⦂ s) (q : Γ ⊩⟨ l′ ⟩ A′ ⦂ s')
                     → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ⦂ s / p → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A′ ⦂ s' / q
  irrelevanceEqTerm′ PE.refl PE.refl p q t≡u = irrelevanceEqTerm p q t≡u

  -- Irrelevance for term equality with propositionally equal types and terms
  irrelevanceEqTerm″ : ∀ {Γ A A′ t t′ u u′ s l l′}
                        (eqt : t PE.≡ t′) (equ : u PE.≡ u′) (eqA : A PE.≡ A′)
                        (p : Γ ⊩⟨ l ⟩ A ⦂ s) (q : Γ ⊩⟨ l′ ⟩ A′ ⦂ s)
                      → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ⦂ s / p → Γ ⊩⟨ l′ ⟩ t′ ≡ u′ ∷ A′ ⦂ s / q
  irrelevanceEqTerm″ PE.refl PE.refl PE.refl p q t≡u = irrelevanceEqTerm p q t≡u

  -- Helper for irrelevance of term equality using shape view
  irrelevanceEqTermT : ∀ {Γ A t u s} {l l′} {p : Γ ⊩⟨ l ⟩ A ⦂ s} {q : Γ ⊩⟨ l′ ⟩ A ⦂ s}
                           → ShapeView Γ l l′ A A s s p q
                           → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ⦂ s / p → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A ⦂ s / q
  irrelevanceEqTermT (ℕᵥ D D′) t≡u = t≡u
  irrelevanceEqTermT (Emptyᵥ D D′) t≡u = t≡u
  irrelevanceEqTermT (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (neₜ₌ k m d d′ nf)
                     with whrDet* (red D₁ , ne neK₁) (red D , ne neK)
  irrelevanceEqTermT (ne (ne K D neK K≡K) (ne .K D₁ neK₁ K≡K₁)) (neₜ₌ k m d d′ nf)
    | PE.refl = neₜ₌ k m d d′ nf
  irrelevanceEqTermT {Γ} {t = t} {u = u} {s = s}
                     (cstrᵥ (cstrᵣ K KcodU a D ⊢a A≡A [domK] [a] [Yi])
                            (cstrᵣ K₁ KcodU₁ a₁ D₁ ⊢a₁ A≡A₁ [domK]₁ [a]₁ [Yi]₁))
                     (cstrₜ₌ k k' d d' k≡k' [k] [k'] [k≡k']) =
    let Ka≡K₁a₁ = whrDet* (red D , cstrₙ) (red D₁ , cstrₙ)
        K≡K₁    = cstr-app-PE-injectivity Ka≡K₁a₁
        a≡a₁    = cstr-app-PE-arg-injectivity Ka≡K₁a₁
        cstrA   = (cstrᵣ′ K KcodU a D ⊢a A≡A [domK] [a] [Yi])
        cstrB   = (cstrᵣ′ K₁ KcodU₁ a₁ D₁ ⊢a₁ A≡A₁ [domK]₁ [a]₁ [Yi]₁)
    in
    cstrₜ₌ k k'
             (PE.subst (λ x → Γ ⊢ t :⇒*: k ∷ x ⦂ s) Ka≡K₁a₁ d)
             (PE.subst (λ x → Γ ⊢ u :⇒*: k' ∷ x ⦂ s) Ka≡K₁a₁ d')
             (PE.subst (λ x → Γ ⊢ k ≅ k' ∷ x ⦂ s) Ka≡K₁a₁ k≡k')
             (irrelevanceTerm cstrA cstrB [k])
             (irrelevanceTerm cstrA cstrB [k'])
             (PE.subst (λ a → [Cstr]-prop K₁ Γ _ a s k k') a≡a₁
                       ([Cstr]-prop-ext K≡K₁ (λ ki kiK kiK' t t' d → irrelevanceEqTerm ([Yi] ki kiK) ([Yi]₁ ki kiK') d) [k≡k']))
  irrelevanceEqTermT {Γ} {t = t} {u = u} {s = s}
                     (Πᵥ (Πᵣ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                         (Πᵣ sF₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
                     (Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g]) =
    let ΠFG≡ΠF₁G₁   = whrDet* (red D , Πₙ) (red D₁ , Πₙ)
        F≡F₁ , sF≡sF₁ , G≡G₁ = Π-PE-injectivity ΠFG≡ΠF₁G₁
        [A]         = Πᵣ′ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext
        [A]₁        = Πᵣ′ sF₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁
    in  Πₜ₌ f g (PE.subst (λ x → Γ ⊢ t :⇒*: f ∷ x ⦂ s) ΠFG≡ΠF₁G₁ d)
            (PE.subst (λ x → Γ ⊢ u :⇒*: g ∷ x ⦂ s) ΠFG≡ΠF₁G₁ d′) funcF funcG
            (PE.subst (λ x → Γ ⊢ f ≅ g ∷ x ⦂ s) ΠFG≡ΠF₁G₁ f≡g)
            (irrelevanceTerm [A] [A]₁ [f]) (irrelevanceTerm [A] [A]₁ [g])
            (λ {ρ} [ρ] ⊢Δ [a]₁ →
               let [a] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F≡F₁)) (PE.sym sF≡sF₁)
                                          ([F]₁ [ρ] ⊢Δ)
                                          ([F] [ρ] ⊢Δ)
                                          [a]₁
               in  irrelevanceEqTerm′ (PE.cong (λ G → wk (lift ρ) G [ _ ]) G≡G₁) PE.refl
                                     ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁) ([f≡g] [ρ] ⊢Δ [a]))
  irrelevanceEqTermT (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) t≡u = t≡u
  irrelevanceEqTermT (emb⁰¹ x) t≡u = irrelevanceEqTermT x t≡u
  irrelevanceEqTermT (emb¹⁰ x) t≡u = irrelevanceEqTermT x t≡u
