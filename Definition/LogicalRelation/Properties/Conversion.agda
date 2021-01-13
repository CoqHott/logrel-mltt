{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Conversion {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.RedSteps
open import Definition.Typed.Reduction
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Conversion of syntactic reduction closures.
convRed:*: : ∀ {t u A B Γ} → Γ ⊢ t :⇒*: u ∷ A → Γ ⊢ A ≡ B ^ ! → Γ ⊢ t :⇒*: u ∷ B 
convRed:*: [ ⊢t , ⊢u , d ] A≡B = [ conv ⊢t  A≡B , conv ⊢u  A≡B , conv* d  A≡B ]

mutual
  -- Helper function for conversion of terms converting from left to right.
  convTermT₁ : ∀ {l l′ Γ A B r t} {[A] : Γ ⊩⟨ l ⟩ A ^ r} {[B] : Γ ⊩⟨ l′ ⟩ B ^ r}
             → ShapeView Γ l l′ A B r r [A] [B]
             → Γ ⊩⟨ l ⟩  A ≡ B ^ r / [A]
             → Γ ⊩⟨ l ⟩  t ∷ A ^ r / [A]
             → Γ ⊩⟨ l′ ⟩ t ∷ B ^ r / [B]
  convTermT₁ (ℕᵥ D D′) A≡B t = t
  convTermT₁ (Emptyᵥ D D′) A≡B t = t
  convTermT₁ {r = !} (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
             (neₜ k d (neNfₜ neK₂ ⊢k k≡k)) =
    let K≡K₁ = PE.subst (λ x → _ ⊢ _ ≡ x ^ _)
                        (whrDet* (red D′ , ne neM) (red D₁ , ne neK₁))
                        (≅-eq (~-to-≅ K≡M))
    in  neₜ k (convRed:*: d K≡K₁)
              (neNfₜ neK₂ (conv ⊢k K≡K₁) (~-conv k≡k K≡K₁))
  convTermT₁ {r = %} (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
             (neₜ d) = let K≡K₁ = PE.subst (λ x → _ ⊢ _ ≡ x ^ _)
                                          (whrDet* (red D′ , ne neM) (red D₁ , ne neK₁))
                                          (≅-eq (~-to-≅ K≡M))
                       in neₜ (conv d (reduction  (red D) (red D₁) (ne neK) (ne neK₁) K≡K₁))
  convTermT₁ {Γ = Γ} {r = !} (Πᵥ (Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                         (Πᵣ rF₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
             (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
             (Πₜ f d funcF f≡f [f] [f]₁) =
    let ΠF₁G₁≡ΠF′G′   = whrDet* (red D₁ , Πₙ) (D′ , Πₙ)
        F₁≡F′ , rF₁≡rF′ , G₁≡G′ = Π-PE-injectivity ΠF₁G₁≡ΠF′G′
        ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ ⊢ Π F ^ rF ▹ G ≡ x ^ !) (PE.sym ΠF₁G₁≡ΠF′G′)
                             (≅-eq A≡B)
    in  Πₜ f (convRed:*: d ΠFG≡ΠF₁G₁) funcF (≅-conv f≡f ΠFG≡ΠF₁G₁)
           (λ {ρ} [ρ] ⊢Δ [a] [b] [a≡b] →
              let [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                           ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                  [a]₁ = convTerm₂′ PE.refl (PE.sym rF₁≡rF′) ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                  [b]₁ = convTerm₂′ PE.refl (PE.sym rF₁≡rF′) ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [b]
                  [a≡b]₁ = convEqTerm₂′ (PE.sym rF₁≡rF′) ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a≡b]
                  [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                                    (PE.sym G₁≡G′))
                                           ([G] [ρ] ⊢Δ [a]₁)
                                           ([G≡G′] [ρ] ⊢Δ [a]₁)
              in  convEqTerm₁ ([G] [ρ] ⊢Δ [a]₁) ([G]₁ [ρ] ⊢Δ [a]) [G≡G₁]
                              ([f] [ρ] ⊢Δ [a]₁ [b]₁ [a≡b]₁))
          (λ {ρ} [ρ] ⊢Δ [a] →
             let [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                          ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                 [a]₁ = convTerm₂′ PE.refl (PE.sym rF₁≡rF′) ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                 [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                                   (PE.sym G₁≡G′))
                                          ([G] [ρ] ⊢Δ [a]₁)
                                          ([G≡G′] [ρ] ⊢Δ [a]₁)
             in  convTerm₁ ([G] [ρ] ⊢Δ [a]₁) ([G]₁ [ρ] ⊢Δ [a]) [G≡G₁] ([f]₁ [ρ] ⊢Δ [a]₁))
  convTermT₁ {Γ = Γ} {r = %} (Πᵥ (Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                         (Πᵣ rF₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
             (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
             d = let ΠF₁G₁≡ΠF′G′   = whrDet* (red D₁ , Πₙ) (D′ , Πₙ)
                     F₁≡F′ , rF₁≡rF′ , G₁≡G′ = Π-PE-injectivity ΠF₁G₁≡ΠF′G′
                     ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ ⊢ Π F ^ rF ▹ G ≡ x ^ %) (PE.sym ΠF₁G₁≡ΠF′G′)
                                          (≅-eq A≡B)
                 in conv d ΠFG≡ΠF₁G₁
  convTermT₁ (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) A≡B t rewrite Univ-PE-injectivity A≡B = t
  convTermT₁ (emb⁰¹ x) A≡B t = convTermT₁ x A≡B t
  convTermT₁ (emb¹⁰ x) A≡B t = convTermT₁ x A≡B t

  -- Helper function for conversion of terms converting from right to left.
  convTermT₂ : ∀ {l l′ Γ A B r t} {[A] : Γ ⊩⟨ l ⟩ A ^ r} {[B] : Γ ⊩⟨ l′ ⟩ B ^ r}
           → ShapeView Γ l l′ A B r r [A] [B]
           → Γ ⊩⟨ l ⟩  A ≡ B ^ r / [A]
           → Γ ⊩⟨ l′ ⟩ t ∷ B ^ r / [B]
           → Γ ⊩⟨ l ⟩  t ∷ A ^ r / [A]
  convTermT₂ (ℕᵥ D D′) A≡B t = t
  convTermT₂ (Emptyᵥ D D′) A≡B t = t
  convTermT₂ {r = !} (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
             (neₜ k d (neNfₜ neK₂ ⊢k k≡k)) =
    let K₁≡K = PE.subst (λ x → _ ⊢ x ≡ _ ^ _)
                        (whrDet* (red D′ , ne neM) (red D₁ , ne neK₁))
                        (sym (≅-eq (~-to-≅ K≡M)))
    in  neₜ k (convRed:*: d K₁≡K)
            (neNfₜ neK₂ (conv ⊢k K₁≡K) (~-conv k≡k K₁≡K))
  convTermT₂ {r = %} (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
             (neₜ d) = let K₁≡K = PE.subst (λ x → _ ⊢ x ≡ _ ^ _)
                                           (whrDet* (red D′ , ne neM) (red D₁ , ne neK₁))
                                           (sym (≅-eq (~-to-≅ K≡M)))
                       in neₜ (conv d (reduction  (red D₁) (red D) (ne neK₁) (ne neK) K₁≡K))
  convTermT₂ {Γ = Γ} {r = !} (Πᵥ (Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                         (Πᵣ rF₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
             (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
             (Πₜ f d funcF f≡f [f] [f]₁) =
    let ΠF₁G₁≡ΠF′G′   = whrDet* (red D₁ , Πₙ) (D′ , Πₙ)
        F₁≡F′ , rF₁≡rF′ , G₁≡G′ = Π-PE-injectivity ΠF₁G₁≡ΠF′G′
        ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ ⊢ Π F ^ rF ▹ G ≡ x ^ !)
                             (PE.sym ΠF₁G₁≡ΠF′G′) (≅-eq A≡B)
    in  Πₜ f (convRed:*: d (sym ΠFG≡ΠF₁G₁)) funcF (≅-conv f≡f (sym ΠFG≡ΠF₁G₁))
           (λ {ρ} [ρ] ⊢Δ [a] [b] [a≡b] →
              let [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                           ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                  [a]₁ = convTerm₁′ (PE.sym rF₁≡rF′) ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                  [b]₁ = convTerm₁′ (PE.sym rF₁≡rF′) ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [b]
                  [a≡b]₁ = convEqTerm₁′ (PE.sym rF₁≡rF′) ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a≡b]
                  [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                                    (PE.sym G₁≡G′))
                                           ([G] [ρ] ⊢Δ [a])
                                           ([G≡G′] [ρ] ⊢Δ [a])
              in  convEqTerm₂ ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁)
                              [G≡G₁] ([f] [ρ] ⊢Δ [a]₁ [b]₁ [a≡b]₁))
           (λ {ρ} [ρ] ⊢Δ [a] →
              let [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                           ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                  [a]₁ = convTerm₁′ (PE.sym rF₁≡rF′) ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                  [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                                    (PE.sym G₁≡G′))
                                           ([G] [ρ] ⊢Δ [a])
                                           ([G≡G′] [ρ] ⊢Δ [a])
              in  convTerm₂ ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁)
                            [G≡G₁] ([f]₁ [ρ] ⊢Δ [a]₁))
  convTermT₂ {Γ = Γ} {r = %} (Πᵥ (Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                         (Πᵣ rF₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
             (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
             d = let ΠF₁G₁≡ΠF′G′   = whrDet* (red D₁ , Πₙ) (D′ , Πₙ)
                     F₁≡F′ , rF₁≡rF′ , G₁≡G′ = Π-PE-injectivity ΠF₁G₁≡ΠF′G′
                     ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ ⊢ Π F ^ rF ▹ G ≡ x ^ %)
                                          (PE.sym ΠF₁G₁≡ΠF′G′) (≅-eq A≡B)
                 in  conv d (sym ΠFG≡ΠF₁G₁)
  convTermT₂ (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) A≡B t rewrite Univ-PE-injectivity A≡B = t
  convTermT₂ (emb⁰¹ x) A≡B t = convTermT₂ x A≡B t
  convTermT₂ (emb¹⁰ x) A≡B t = convTermT₂ x A≡B t

  -- Conversion of terms converting from left to right.
  convTerm₁ : ∀ {Γ A B r t l l′} ([A] : Γ ⊩⟨ l ⟩ A ^ r) ([B] : Γ ⊩⟨ l′ ⟩ B ^ r)
            → Γ ⊩⟨ l ⟩  A ≡ B ^ r / [A]
            → Γ ⊩⟨ l ⟩  t ∷ A ^ r / [A]
            → Γ ⊩⟨ l′ ⟩ t ∷ B ^ r / [B]
  convTerm₁ [A] [B] A≡B t = convTermT₁ (goodCases [A] [B] A≡B) A≡B t

  -- Conversion of terms converting from left to right. with PE
  convTerm₁′ : ∀ {Γ A B r r' t l l′} (eq : r PE.≡ r') ([A] : Γ ⊩⟨ l ⟩ A ^ r) ([B] : Γ ⊩⟨ l′ ⟩ B ^ r')
            → Γ ⊩⟨ l ⟩  A ≡ B ^ r / [A]
            → Γ ⊩⟨ l ⟩  t ∷ A ^ r / [A]
            → Γ ⊩⟨ l′ ⟩ t ∷ B ^ r' / [B]
  convTerm₁′ PE.refl [A] [B] A≡B t = convTerm₁ [A] [B] A≡B t

  -- Conversion of terms converting from right to left.
  convTerm₂ : ∀ {Γ A B r t l l′} ([A] : Γ ⊩⟨ l ⟩ A ^ r) ([B] : Γ ⊩⟨ l′ ⟩ B ^ r)
          → Γ ⊩⟨ l ⟩  A ≡ B ^ r / [A]
          → Γ ⊩⟨ l′ ⟩ t ∷ B ^ r / [B]
          → Γ ⊩⟨ l ⟩  t ∷ A ^ r / [A]
  convTerm₂ [A] [B] A≡B t = convTermT₂ (goodCases [A] [B] A≡B) A≡B t

  -- Conversion of terms converting from right to left
  -- with some propsitionally equal types.
  convTerm₂′ : ∀ {Γ A r r' B B′ t l l′} → B PE.≡ B′ → r PE.≡ r'
          → ([A] : Γ ⊩⟨ l ⟩ A ^ r) ([B] : Γ ⊩⟨ l′ ⟩ B ^ r')
          → Γ ⊩⟨ l ⟩  A ≡ B′ ^ r / [A]
          → Γ ⊩⟨ l′ ⟩ t ∷ B ^ r' / [B]
          → Γ ⊩⟨ l ⟩  t ∷ A ^ r / [A]
  convTerm₂′ PE.refl PE.refl [A] [B] A≡B t = convTerm₂ [A] [B] A≡B t


  -- Helper function for conversion of term equality converting from left to right.
  convEqTermT₁ : ∀ {l l′ Γ A B r t u} {[A] : Γ ⊩⟨ l ⟩ A ^ r} {[B] : Γ ⊩⟨ l′ ⟩ B ^ r}
               → ShapeView Γ l l′ A B r r [A] [B]
               → Γ ⊩⟨ l ⟩  A ≡ B ^ r / [A]
               → Γ ⊩⟨ l ⟩  t ≡ u ∷ A ^ r / [A]
               → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B ^ r / [B]
  convEqTermT₁ (ℕᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₁ (Emptyᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₁ {r = !} (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
               (neₜ₌ k m d d′ (neNfₜ₌ neK₂ neM₁ k≡m)) =
    let K≡K₁ = PE.subst (λ x → _ ⊢ _ ≡ x ^ _)
                        (whrDet* (red D′ , ne neM) (red D₁ , ne neK₁))
                        (≅-eq (~-to-≅ K≡M))
    in  neₜ₌ k m (convRed:*: d K≡K₁)
                 (convRed:*: d′ K≡K₁)
                 (neNfₜ₌ neK₂ neM₁ (~-conv k≡m K≡K₁))
  convEqTermT₁ {r = %} (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
               (neₜ₌ d d′) =
    let K≡K₁ = PE.subst (λ x → _ ⊢ _ ≡ x ^ _)
                        (whrDet* (red D′ , ne neM) (red D₁ , ne neK₁))
                        (≅-eq (~-to-≅ K≡M))
    in neₜ₌ (conv d (reduction  (red D) (red D₁) (ne neK) (ne neK₁) K≡K₁))
            (conv d′ (reduction  (red D) (red D₁) (ne neK) (ne neK₁) K≡K₁))
  convEqTermT₁ {Γ = Γ} {r = !} (Πᵥ (Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                           (Πᵣ rF₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
               (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
               (Πₜ₌ f g d d′ funcF funcG t≡u [t] [u] [t≡u]) =
    let [A] = Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext
        [B] = Πᵣ′ rF₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁
        [A≡B] = Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]
        ΠF₁G₁≡ΠF′G′ = whrDet* (red D₁ , Πₙ) (D′ , Πₙ)
        ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ ⊢ Π F ^ rF ▹ G ≡ x ^ !)
                             (PE.sym ΠF₁G₁≡ΠF′G′) (≅-eq A≡B)
    in  Πₜ₌ f g (convRed:*: d ΠFG≡ΠF₁G₁) (convRed:*: d′ ΠFG≡ΠF₁G₁)
            funcF funcG (≅-conv t≡u ΠFG≡ΠF₁G₁)
            (convTerm₁ [A] [B] [A≡B] [t]) (convTerm₁ [A] [B] [A≡B] [u])
            (λ {ρ} [ρ] ⊢Δ [a] →
               let F₁≡F′ , rF₁≡rF′ , G₁≡G′ = Π-PE-injectivity (whrDet* (red D₁ , Πₙ) (D′ , Πₙ))
                   [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                            ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                   [a]₁ = convTerm₂′ PE.refl (PE.sym rF₁≡rF′) ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                   [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                                     (PE.sym G₁≡G′))
                                            ([G] [ρ] ⊢Δ [a]₁)
                                            ([G≡G′] [ρ] ⊢Δ [a]₁)
               in  convEqTerm₁ ([G] [ρ] ⊢Δ [a]₁) ([G]₁ [ρ] ⊢Δ [a])
                               [G≡G₁] ([t≡u] [ρ] ⊢Δ [a]₁))
  convEqTermT₁ {Γ = Γ} {r = %} (Πᵥ (Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                           (Πᵣ rF₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
               (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
               (d , d′) = let ΠF₁G₁≡ΠF′G′ = whrDet* (red D₁ , Πₙ) (D′ , Πₙ)
                              ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ ⊢ Π F ^ rF ▹ G ≡ x ^ %)
                                                   (PE.sym ΠF₁G₁≡ΠF′G′) (≅-eq A≡B)
                          in (conv d ΠFG≡ΠF₁G₁) , conv d′ ΠFG≡ΠF₁G₁
  convEqTermT₁ (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) A≡B t≡u rewrite Univ-PE-injectivity A≡B = t≡u
  convEqTermT₁ (emb⁰¹ x) A≡B t≡u = convEqTermT₁ x A≡B t≡u
  convEqTermT₁ (emb¹⁰ x) A≡B t≡u = convEqTermT₁ x A≡B t≡u

  -- Helper function for conversion of term equality converting from right to left.
  convEqTermT₂ : ∀ {l l′ Γ A B t u r} {[A] : Γ ⊩⟨ l ⟩ A ^ r} {[B] : Γ ⊩⟨ l′ ⟩ B ^ r}
             → ShapeView Γ l l′ A B r r [A] [B]
             → Γ ⊩⟨ l ⟩  A ≡ B ^ r / [A]
             → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B ^ r / [B]
             → Γ ⊩⟨ l ⟩  t ≡ u ∷ A ^ r / [A]
  convEqTermT₂ (ℕᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₂ (Emptyᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₂ {r = !} (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
               (neₜ₌ k m d d′ (neNfₜ₌ neK₂ neM₁ k≡m)) =
    let K₁≡K = PE.subst (λ x → _ ⊢ x ≡ _ ^ _)
                        (whrDet* (red D′ , ne neM) (red D₁ , ne neK₁))
                        (sym (≅-eq (~-to-≅ K≡M)))
    in  neₜ₌ k m (convRed:*: d K₁≡K) (convRed:*: d′ K₁≡K)
                 (neNfₜ₌ neK₂ neM₁ (~-conv k≡m K₁≡K))
  convEqTermT₂ {r = %} (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
               (neₜ₌ d d′) =
    let K₁≡K = PE.subst (λ x → _ ⊢ x ≡ _ ^ _)
                        (whrDet* (red D′ , ne neM) (red D₁ , ne neK₁))
                        (sym (≅-eq (~-to-≅ K≡M)))
    in neₜ₌ (conv d (reduction  (red D₁) (red D) (ne neK₁) (ne neK) K₁≡K))
            (conv d′ (reduction  (red D₁) (red D) (ne neK₁) (ne neK) K₁≡K))
  convEqTermT₂ {Γ = Γ} {r = !} (Πᵥ (Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                           (Πᵣ rF₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
               (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
               (Πₜ₌ f g d d′ funcF funcG t≡u [t] [u] [t≡u]) =
    let [A] = Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext
        [B] = Πᵣ′ rF₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁
        [A≡B] = Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]
        ΠF₁G₁≡ΠF′G′ = whrDet* (red D₁ , Πₙ) (D′ , Πₙ)
        ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ ⊢ Π F ^ rF ▹ G ≡ x ^ !)
                             (PE.sym ΠF₁G₁≡ΠF′G′) (≅-eq A≡B)
    in  Πₜ₌ f g (convRed:*: d (sym ΠFG≡ΠF₁G₁)) (convRed:*: d′ (sym ΠFG≡ΠF₁G₁))
            funcF funcG (≅-conv t≡u (sym ΠFG≡ΠF₁G₁))
            (convTerm₂ [A] [B] [A≡B] [t]) (convTerm₂ [A] [B] [A≡B] [u])
            (λ {ρ} [ρ] ⊢Δ [a] →
               let F₁≡F′ , rF₁≡rF′ , G₁≡G′ = Π-PE-injectivity (whrDet* (red D₁ , Πₙ) (D′ , Πₙ))
                   [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                            ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                   [a]₁ = convTerm₁′ (PE.sym rF₁≡rF′) ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                   [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                                     (PE.sym G₁≡G′))
                                            ([G] [ρ] ⊢Δ [a])
                                            ([G≡G′] [ρ] ⊢Δ [a])
               in  convEqTerm₂ ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁)
                               [G≡G₁] ([t≡u] [ρ] ⊢Δ [a]₁))
  convEqTermT₂ {Γ = Γ} {r = %} (Πᵥ (Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                           (Πᵣ rF₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
               (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
               (d , d′) =
               let ΠF₁G₁≡ΠF′G′ = whrDet* (red D₁ , Πₙ) (D′ , Πₙ)
                   ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ ⊢ Π F ^ rF ▹ G ≡ x ^ %)
                                        (PE.sym ΠF₁G₁≡ΠF′G′) (≅-eq A≡B)
               in (conv d (sym ΠFG≡ΠF₁G₁)) , (conv d′ (sym ΠFG≡ΠF₁G₁))
  convEqTermT₂ (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) A≡B t≡u rewrite Univ-PE-injectivity A≡B = t≡u
  convEqTermT₂ (emb⁰¹ x) A≡B t≡u = convEqTermT₂ x A≡B t≡u
  convEqTermT₂ (emb¹⁰ x) A≡B t≡u = convEqTermT₂ x A≡B t≡u

  -- Conversion of term equality converting from left to right.
  convEqTerm₁ : ∀ {l l′ Γ A B t u r} ([A] : Γ ⊩⟨ l ⟩ A ^ r) ([B] : Γ ⊩⟨ l′ ⟩ B ^ r)
              → Γ ⊩⟨ l ⟩  A ≡ B ^ r / [A]
              → Γ ⊩⟨ l ⟩  t ≡ u ∷ A ^ r / [A]
              → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B ^ r / [B]
  convEqTerm₁ [A] [B] A≡B t≡u = convEqTermT₁ (goodCases [A] [B] A≡B) A≡B t≡u

  -- Conversion of term equality converting from left to right. with PE
  convEqTerm₁′ : ∀ {l l′ Γ A B t u r r'} (eq : r PE.≡ r') ([A] : Γ ⊩⟨ l ⟩ A ^ r) ([B] : Γ ⊩⟨ l′ ⟩ B ^ r')
              → Γ ⊩⟨ l ⟩  A ≡ B ^ r / [A]
              → Γ ⊩⟨ l ⟩  t ≡ u ∷ A ^ r / [A]
              → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B ^ r' / [B]
  convEqTerm₁′ PE.refl [A] [B] A≡B t≡u = convEqTerm₁ [A] [B] A≡B t≡u

  -- Conversion of term equality converting from right to left.
  convEqTerm₂ : ∀ {l l′ Γ A B t u r} ([A] : Γ ⊩⟨ l ⟩ A ^ r) ([B] : Γ ⊩⟨ l′ ⟩ B ^ r)
            → Γ ⊩⟨ l ⟩  A ≡ B ^ r / [A]
            → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B ^ r / [B]
            → Γ ⊩⟨ l ⟩  t ≡ u ∷ A ^ r / [A]
  convEqTerm₂ [A] [B] A≡B t≡u = convEqTermT₂ (goodCases [A] [B] A≡B) A≡B t≡u

  -- Conversion of term equality converting from right to left with PE
  convEqTerm₂′ : ∀ {l l′ Γ A B t u r r'} (eq : r PE.≡ r') ([A] : Γ ⊩⟨ l ⟩ A ^ r) ([B] : Γ ⊩⟨ l′ ⟩ B ^ r')
            → Γ ⊩⟨ l ⟩  A ≡ B ^ r / [A]
            → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B ^ r' / [B]
            → Γ ⊩⟨ l ⟩  t ≡ u ∷ A ^ r / [A]
  convEqTerm₂′ PE.refl [A] [B] A≡B t≡u = convEqTerm₂ [A] [B] A≡B t≡u
