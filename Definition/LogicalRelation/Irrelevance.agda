{-# OPTIONS --without-K  #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Irrelevance {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView

open import Tools.Product
import Tools.PropositionalEquality as PE

-- Conversion of syntactic reduction closures.
convRed:*: : ∀ {t u A B s Γ} → Γ ⊢ t :⇒*: u ∷ A ⦂ s → Γ ⊢ A ≡ B ⦂ s → Γ ⊢ t :⇒*: u ∷ B ⦂ s
convRed:*: [ ⊢t , ⊢u , d ] A≡B = [ conv ⊢t  A≡B , conv ⊢u  A≡B , conv* d  A≡B ]


module extCstr {K K' : constructors}
               {Pi : ∀ ki → [ K ]-cstr (cstr-cod ki) → Term → Set}
               {Pi' : ∀ ki → [ K' ]-cstr (cstr-cod ki) → Term → Set}
               (Pi→Pi' : ∀ ki kiK  kiK' t → Pi ki kiK t → Pi' ki kiK' t)
               where

  module C = Cstr K Pi
  module C' = Cstr K' Pi'

  irrelevance : ∀ {Γ t a a' s} (K≡K' : K PE.≡ K') (⊢Ka≡Ka' : Γ ⊢ cstr K a ≡ cstr K a' ⦂ s) → Γ C.⊩cstr t ∷K a ⦂ s → Γ C'.⊩cstr t ∷K a' ⦂ s
  prop-ext : ∀ {Γ t a a' s} (K≡K' : K PE.≡ K') (⊢Ka≡Ka' : Γ ⊢ cstr K a ≡ cstr K a' ⦂ s) (d : C.Cstr-prop Γ a s t) → C'.Cstr-prop Γ a' s t

  irrelevance PE.refl ⊢Ka≡Ka' (C.cstrₜ k D k≡k [k]) =
    C'.cstrₜ k (convRed:*: D ⊢Ka≡Ka') (≅-conv k≡k ⊢Ka≡Ka') (prop-ext PE.refl ⊢Ka≡Ka' [k])

  prop-ext PE.refl ⊢Ka≡Ka' (C.cstrᵣ kK x) = C'.cstrᵣ kK (Pi→Pi' _ kK kK _ x)
  prop-ext PE.refl ⊢Ka≡Ka' (C.cstr-recᵣ kK kdomK x ⊢Kx d) =
    C'.cstr-recᵣ kK kdomK (Pi→Pi' _ kK kK _ x) ⊢Kx (irrelevance PE.refl (refl ⊢Kx) d)
  prop-ext PE.refl ⊢Ka≡Ka' (C.ne (neNfₜ neK ⊢k k≡k)) = C'.ne (neNfₜ neK (conv ⊢k ⊢Ka≡Ka') (~-conv k≡k ⊢Ka≡Ka'))

module ext[Cstr] {K K' : constructors}
                 {Pi : ∀ ki → [ K ]-cstr (cstr-cod ki) → Term → Term → Set}
                 {Pi' : ∀ ki → [ K' ]-cstr (cstr-cod ki) → Term → Term → Set}
                 (Pi→Pi' : ∀ ki kiK  kiK' t t' → Pi ki kiK t t' → Pi' ki kiK' t t')
                 where

  module C = [Cstr] K Pi
  module C' = [Cstr] K' Pi'

  irrelevance : ∀ {Γ t t' a a' s} (K≡K' : K PE.≡ K') (⊢Ka≡Ka' : Γ ⊢ cstr K a ≡ cstr K a' ⦂ s) → Γ C.⊩cstr t ≡ t' ∷K a ⦂ s → Γ C'.⊩cstr t ≡ t' ∷K a' ⦂ s
  prop-ext : ∀ {Γ t t' a a' s} (K≡K' : K PE.≡ K') (⊢Ka≡Ka' : Γ ⊢ cstr K a ≡ cstr K a' ⦂ s) (d : C.[Cstr]-prop Γ a s t t') → C'.[Cstr]-prop Γ a' s t t'

  irrelevance PE.refl ⊢Ka≡Ka' (C.cstrₜ k k' D D' k≡k' [k≡k']) =
    C'.cstrₜ k k' (convRed:*: D ⊢Ka≡Ka') (convRed:*: D' ⊢Ka≡Ka') (≅-conv k≡k' ⊢Ka≡Ka') (prop-ext PE.refl ⊢Ka≡Ka' [k≡k'])

  prop-ext PE.refl ⊢Ka≡Ka' (C.cstrᵣ kK x) = C'.cstrᵣ kK (Pi→Pi' _ kK kK _ _ x)
  prop-ext PE.refl ⊢Ka≡Ka' (C.cstr-recᵣ kK kdomK x ⊢Kx d) =
    C'.cstr-recᵣ kK kdomK (Pi→Pi' _ kK kK _ _ x) ⊢Kx (irrelevance PE.refl (refl ⊢Kx) d)
  prop-ext PE.refl ⊢Ka≡Ka' (C.ne (neNfₜ₌ neK neM k≡m)) = C'.ne (neNfₜ₌ neK neM (~-conv k≡m ⊢Ka≡Ka'))


Box-prop-ext : ∀ {P P' Γ F F' sF sF' b}
             → (∀ x → P x → P' x)
             → sF PE.≡ sF'
             → Γ ⊢ Box sF F ≡ Box sF' F' ⦂ 𝕥y
             → Box-prop P Γ F sF b
             → Box-prop P' Γ F' sF' b
Box-prop-ext PP' e F≡F' (boxᵣ x) rewrite e = boxᵣ (PP' _ x)
Box-prop-ext PP' e F≡F' (ne (neNfₜ neK ⊢k k≡k)) = ne (neNfₜ neK (conv ⊢k F≡F') (~-conv k≡k F≡F'))

[Box]-prop-ext : ∀ {P P' Γ F F' sF sF' b b'}
             → (∀ x x' → P x x' → P' x x')
             → sF PE.≡ sF'
             → Γ ⊢ Box sF F ≡ Box sF' F' ⦂ 𝕥y
             → [Box]-prop P Γ F sF b b'
             → [Box]-prop P' Γ F' sF' b b'
[Box]-prop-ext PP' e F≡F' (boxᵣ x) rewrite e = boxᵣ (PP' _ _ x)
[Box]-prop-ext PP' e F≡F' (ne (neNfₜ₌ neK neM k≡m)) = ne (neNfₜ₌ neK neM (~-conv k≡m F≡F'))


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
  irrelevanceEqT {Γ} {s = s} {l′ = l′} (cstrᵥ (cstrᵣ K KcodU [domK] [Yi] a D ⊢a A≡A [a])
                        (cstrᵣ K₁ _ [domK]₁ [Yi]₁ _ D₁ _ _ [a]₁))
                 (cstr₌ a' D' A≡B [a≡a']) =
    let Ka≡K₁a₁ = whrDet* (red D , cstrₙ) (red D₁ , cstrₙ)
        K≡K₁    = cstr-app-PE-injectivity Ka≡K₁a₁
        a≡a₁    = cstr-app-PE-arg-injectivity Ka≡K₁a₁
    in
    cstr₌ a' (PE.subst (λ x → _ ⊢ _ :⇒*: cstr x a' ⦂ _) K≡K₁ D')
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
  irrelevanceEqT {Γ = Γ} {B = B} (Boxᵥ (Boxᵣ F sF D ⊢F A≡A [F]) (Boxᵣ F' sF' D' ⊢F' A≡A' [F]')) (Box₌ F'' D'' A≡B [F≡F']) =
    let BF≡BF' = whrDet* (red D , Boxₙ) (red D' , Boxₙ)
        sF≡sF' = Box-sort-inj BF≡BF'
        F≡F'   = Box-inj BF≡BF'
    in Box₌ F'' (PE.subst (λ s → Γ ⊢ B :⇒*: Box s F'' ⦂ 𝕥y) sF≡sF' D'')
            (PE.subst₂ (λ s F → Γ ⊢ Box s F ≅ Box s F'' ⦂ 𝕥y) sF≡sF' F≡F' A≡B)
            (irrelevanceEq′ F≡F' (PE.cong ‼ sF≡sF') [F] [F]' [F≡F'])
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

  irrelevanceTermT {Γ} {t = t} {s = s} {l} {l′}
                   (cstrᵥ (cstrᵣ K KcodU [domK] [Yi] a [ ⊢A , ⊢Ka , D ] ⊢a A≡A [a])
                          (cstrᵣ K₁ _ [domK]₁ [Yi]₁ _ D₁ _ _ [a]₁))
                   d =
    let Ka≡K₁a₁ = whrDet* (D , cstrₙ) (red D₁ , cstrₙ)
        K≡K₁    = cstr-app-PE-injectivity Ka≡K₁a₁
        a≡a₁    = cstr-app-PE-arg-injectivity Ka≡K₁a₁
        ⊢Ka≡Ka₁ = PE.subst (λ a' → Γ ⊢ cstr K a ≡ cstr K a' ⦂ s) a≡a₁ (refl ⊢Ka)
    in
    extCstr.irrelevance {!!} K≡K₁ ⊢Ka≡Ka₁ d
    where
      aux-ext : (ki : constructors) (kiK : [ K ]-cstr (cstr-cod ki))
                (kiK' : [ K₁ ]-cstr (cstr-cod ki)) (t : Term) →
                LogRel.cstr-arg-dispatch l (logRelRec l) Γ s K [domK] [Yi] ki kiK t →
                LogRel.cstr-arg-dispatch l′ (logRelRec l′) Γ s K₁ [domK]₁ [Yi]₁ ki kiK' t
      aux-ext ki kiK kiK' t d with [Yi] ki kiK with [Yi]₁
      ... | LogRel.cstᵣ [A] = {!!}
      ... | LogRel.monᵣ d₁ x = {!!}
      -- irrelevanceTerm ([Yi] ki kiK) ([Yi]₁ ki kiK') d
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
  irrelevanceTermT {Γ = Γ} {t = t} (Boxᵥ (Boxᵣ F sF D ⊢F A≡A [F]) (Boxᵣ F' sF' D' ⊢F' A≡A' [F]')) (boxₜ b d b≡b [b]) =
    let BF≡BF' = whrDet* (red D , Boxₙ) (red D' , Boxₙ)
        sF≡sF' = Box-sort-inj BF≡BF'
        F≡F'   = Box-inj BF≡BF'
    in boxₜ b (PE.subst (λ BF → Γ ⊢ t :⇒*: b ∷ BF ⦂ 𝕥y) BF≡BF' d)
            (PE.subst (λ BF → Γ ⊢ b ≅ b ∷ BF ⦂ 𝕥y) BF≡BF' b≡b)
            (Box-prop-ext (λ x d → irrelevanceTerm′ F≡F' (PE.cong ‼ sF≡sF') [F] [F]' d)
                          sF≡sF' (PE.subst (λ BF → Γ ⊢ Box sF F ≡ BF ⦂ 𝕥y) BF≡BF' (refl (Boxⱼ ⊢F))) [b])
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
                     (cstrᵥ (cstrᵣ K KcodU [domK] [Yi] a [ ⊢A , ⊢Ka , D ] ⊢a A≡A [a])
                            (cstrᵣ K₁ KcodU₁ [domK]₁ [Yi]₁ a₁ D₁ ⊢a₁ A≡A₁ [a]₁))
                     (cstrₜ₌ [k] [k'] ([Cstr].cstrₜ k k' d d' k≡k'  [k≡k'])) =
                     {!!}
    -- let Ka≡K₁a₁ = whrDet* ( D , cstrₙ) (red D₁ , cstrₙ)
    --     K≡K₁    = cstr-app-PE-injectivity Ka≡K₁a₁
    --     a≡a₁    = cstr-app-PE-arg-injectivity Ka≡K₁a₁
    --     cstrA   = (cstrᵣ′ K KcodU a [ ⊢A , ⊢Ka , D ] ⊢a A≡A [domK] [a] [Yi])
    --     cstrB   = (cstrᵣ′ K₁ KcodU₁ a₁ D₁ ⊢a₁ A≡A₁ [domK]₁ [a]₁ [Yi]₁)
    -- in
    -- cstrₜ₌ k k'
    --          (PE.subst (λ x → Γ ⊢ t :⇒*: k ∷ x ⦂ s) Ka≡K₁a₁ d)
    --          (PE.subst (λ x → Γ ⊢ u :⇒*: k' ∷ x ⦂ s) Ka≡K₁a₁ d')
    --          (PE.subst (λ x → Γ ⊢ k ≅ k' ∷ x ⦂ s) Ka≡K₁a₁ k≡k')
    --          (irrelevanceTerm cstrA cstrB [k])
    --          (irrelevanceTerm cstrA cstrB [k'])
    --          (PE.subst (λ a → [Cstr]-prop K₁ Γ _ a s k k') a≡a₁
    --                    ([Cstr]-prop-ext K≡K₁ (λ ki kiK kiK' t t' d → irrelevanceEqTerm ([Yi] ki kiK) ([Yi]₁ ki kiK') d) (refl ⊢Ka) [k≡k']))
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
  irrelevanceEqTermT {Γ = Γ} {t = t} {u = u} (Boxᵥ (Boxᵣ F sF D ⊢F A≡A [F]) (Boxᵣ F' sF' D' ⊢F' A≡A' [F]')) (boxₜ₌ b b' d d' b≡b' [b] [b'] [b≡b']) =
    let BF≡BF' = whrDet* (red D , Boxₙ) (red D' , Boxₙ)
        sF≡sF' = Box-sort-inj BF≡BF'
        F≡F'   = Box-inj BF≡BF'
        BoxA   = Boxᵣ′ F sF D ⊢F A≡A [F]
        BoxB   = Boxᵣ′ F' sF' D' ⊢F' A≡A' [F]'
    in boxₜ₌ b b'
             (PE.subst (λ BF → Γ ⊢ t :⇒*: b ∷ BF ⦂ 𝕥y) BF≡BF' d)
             (PE.subst (λ BF → Γ ⊢ u :⇒*: b' ∷ BF ⦂ 𝕥y) BF≡BF' d')
             (PE.subst (λ BF → Γ ⊢ b ≅ b' ∷ BF ⦂ 𝕥y) BF≡BF' b≡b')
             (irrelevanceTerm BoxA BoxB [b])
             (irrelevanceTerm BoxA BoxB [b'])
             ([Box]-prop-ext (λ x x' d → irrelevanceEqTerm′ F≡F' (PE.cong ‼ sF≡sF') [F] [F]' d)
                             sF≡sF' (PE.subst (λ BF → Γ ⊢ Box sF F ≡ BF ⦂ 𝕥y) BF≡BF' (refl (Boxⱼ ⊢F))) [b≡b'])
  irrelevanceEqTermT (emb⁰¹ x) t≡u = irrelevanceEqTermT x t≡u
  irrelevanceEqTermT (emb¹⁰ x) t≡u = irrelevanceEqTermT x t≡u
