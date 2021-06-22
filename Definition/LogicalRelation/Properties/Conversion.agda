{-# OPTIONS --without-K  #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Conversion {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.RedSteps
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance

open import Tools.Product
import Tools.PropositionalEquality as PE



mutual
  -- Helper function for conversion of terms converting from left to right.
  convTermT₁ : ∀ {l l′ Γ A B s t} {[A] : Γ ⊩⟨ l ⟩ A ⦂ s} {[B] : Γ ⊩⟨ l′ ⟩ B ⦂ s}
             → ShapeView Γ l l′ A B s s [A] [B]
             → Γ ⊩⟨ l ⟩  A ≡ B ⦂ s / [A]
             → Γ ⊩⟨ l ⟩  t ∷ A ⦂ s / [A]
             → Γ ⊩⟨ l′ ⟩ t ∷ B ⦂ s / [B]
  convTermT₁ (ℕᵥ D D′) A≡B t = t
  convTermT₁ (Emptyᵥ D D′) A≡B t = t
  convTermT₁ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
             (neₜ k d (neNfₜ neK₂ ⊢k k≡k)) =
    let K≡K₁ = PE.subst (λ x → _ ⊢ _ ≡ x ⦂ _)
                        (whrDet* (red D′ , ne neM) (red D₁ , ne neK₁))
                        (≅-eq (~-to-≅ K≡M))
    in  neₜ k (convRed:*: d K≡K₁)
            (neNfₜ neK₂ (conv ⊢k K≡K₁) (~-conv k≡k K≡K₁))
  convTermT₁ {Γ = Γ} {s = s} {t = t}
         (cstrᵥ (cstrᵣ K KcodU a D ⊢a A≡A [domK] [a] [Yi])
                (cstrᵣ K₁ KcodU₁ a₁ D₁ ⊢a₁ A≡A₁ [domK]₁ [a]₁ [Yi]₁))
         (cstr₌ a' D' A≡B [a≡a'])
         (cstrₜ k d k≡k [k]) =
    let Ka'≡K₁a₁ = PE.sym (whrDet* (red D₁ , cstrₙ) (red D' , cstrₙ))
        K≡K₁    = cstr-app-PE-injectivity Ka'≡K₁a₁
        a'≡a₁   = cstr-app-PE-arg-injectivity Ka'≡K₁a₁
        -- cstrA   = (cstrᵣ′ K KcodU a D ⊢a A≡A [domK] [a] [Yi])
        -- cstrB   = (cstrᵣ′ K₁ KcodU₁ a₁ D₁ ⊢a₁ A≡A₁ [domK]₁ [a]₁ [Yi]₁)
        ⊢Ka≡Ka'  = ≅-eq (≅-cstr-cong KcodU A≡B)
    in cstrₜ k
             (PE.subst (λ x → Γ ⊢ t :⇒*: k ∷ x ⦂ s) Ka'≡K₁a₁ (convRed:*: d ⊢Ka≡Ka'))
             (PE.subst (λ x → Γ ⊢ k ≅ k ∷ x ⦂ s) Ka'≡K₁a₁ (≅-conv k≡k ⊢Ka≡Ka'))
             (PE.subst (λ a → Cstr-prop K₁ Γ _ a _ k)  a'≡a₁
                   (Cstr-prop-ext K≡K₁ (λ ki kiK kiK' t d → irrelevanceTerm ([Yi] ki kiK) ([Yi]₁ ki kiK') d) ⊢Ka≡Ka' [k]))
  convTermT₁ {Γ = Γ} {s = s} {t = t}
             (Boxᵥ (Boxᵣ F sF D ⊢F A≡A [F])
                   (Boxᵣ F' sF' D' ⊢F' A≡A' [F]'))
             (Box₌ F'' D'' A≡B [F≡F'])
             (boxₜ b d b≡b [b]) =
    let BF''≡BF' = whrDet* (red D'' , Boxₙ) (red D' , Boxₙ)
        sF≡sF' = Box-sort-inj BF''≡BF'
        F''≡F'   = Box-inj BF''≡BF'
        ⊢BF≡BF'' = ≅-eq A≡B
    in boxₜ b
         (PE.subst (λ x → Γ ⊢ t :⇒*: b ∷ x ⦂ 𝕥y) BF''≡BF'
                    (convRed:*: d ⊢BF≡BF''))
         (PE.subst (λ x → Γ ⊢ b ≅ b ∷ x ⦂ 𝕥y) BF''≡BF'
                     (≅-conv b≡b ⊢BF≡BF''))
         (Box-prop-ext (λ x d → convTerm₁′ (PE.cong ‼ sF≡sF') [F] [F]' (PE.subst (λ G → Γ ⊩⟨ _ ⟩ F ≡ G ⦂ ‼ sF / [F] ) F''≡F' [F≡F']) d)
                       sF≡sF'
                       (PE.subst (λ BF → Γ ⊢ Box sF F ≡ BF ⦂ 𝕥y) BF''≡BF' ⊢BF≡BF'')
                       [b])
  convTermT₁ {Γ = Γ} {s = s} (Πᵥ (Πᵣ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                         (Πᵣ sF₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
             (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
             (Πₜ f d funcF f≡f [f] [f]₁) =
    let ΠF₁G₁≡ΠF′G′   = whrDet* (red D₁ , Πₙ) (D′ , Πₙ)
        F₁≡F′ , sF₁≡sF′ , G₁≡G′ = Π-PE-injectivity ΠF₁G₁≡ΠF′G′
        ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ ⊢ Π F ⦂ sF ▹ G ≡ x ⦂ s) (PE.sym ΠF₁G₁≡ΠF′G′)
                             (≅-eq A≡B)
    in  Πₜ f (convRed:*: d ΠFG≡ΠF₁G₁) funcF (≅-conv f≡f ΠFG≡ΠF₁G₁)
           (λ {ρ} [ρ] ⊢Δ [a] [b] [a≡b] →
              let [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                           ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                  [a]₁ = convTerm₂′ PE.refl (PE.sym sF₁≡sF′) ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                  [b]₁ = convTerm₂′ PE.refl (PE.sym sF₁≡sF′) ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [b]
                  [a≡b]₁ = convEqTerm₂′ (PE.sym sF₁≡sF′) ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a≡b]
                  [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                                    (PE.sym G₁≡G′))
                                           ([G] [ρ] ⊢Δ [a]₁)
                                           ([G≡G′] [ρ] ⊢Δ [a]₁)
              in  convEqTerm₁ ([G] [ρ] ⊢Δ [a]₁) ([G]₁ [ρ] ⊢Δ [a]) [G≡G₁]
                              ([f] [ρ] ⊢Δ [a]₁ [b]₁ [a≡b]₁))
          (λ {ρ} [ρ] ⊢Δ [a] →
             let [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                          ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                 [a]₁ = convTerm₂′ PE.refl (PE.sym sF₁≡sF′) ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                 [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                                   (PE.sym G₁≡G′))
                                          ([G] [ρ] ⊢Δ [a]₁)
                                          ([G≡G′] [ρ] ⊢Δ [a]₁)
             in  convTerm₁ ([G] [ρ] ⊢Δ [a]₁) ([G]₁ [ρ] ⊢Δ [a]) [G≡G₁] ([f]₁ [ρ] ⊢Δ [a]₁))
  convTermT₁ (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) A≡B t rewrite Univ-PE-injectivity A≡B = t
  convTermT₁ (emb⁰¹ x) A≡B t = convTermT₁ x A≡B t
  convTermT₁ (emb¹⁰ x) A≡B t = convTermT₁ x A≡B t

  -- Helper function for conversion of terms converting from right to left.
  convTermT₂ : ∀ {l l′ Γ A B s t} {[A] : Γ ⊩⟨ l ⟩ A ⦂ s} {[B] : Γ ⊩⟨ l′ ⟩ B ⦂ s}
           → ShapeView Γ l l′ A B s s [A] [B]
           → Γ ⊩⟨ l ⟩  A ≡ B ⦂ s / [A]
           → Γ ⊩⟨ l′ ⟩ t ∷ B ⦂ s / [B]
           → Γ ⊩⟨ l ⟩  t ∷ A ⦂ s / [A]
  convTermT₂ (ℕᵥ D D′) A≡B t = t
  convTermT₂ (Emptyᵥ D D′) A≡B t = t
  convTermT₂ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
             (neₜ k d (neNfₜ neK₂ ⊢k k≡k)) =
    let K₁≡K = PE.subst (λ x → _ ⊢ x ≡ _ ⦂ _)
                        (whrDet* (red D′ , ne neM) (red D₁ , ne neK₁))
                        (sym (≅-eq (~-to-≅ K≡M)))
    in  neₜ k (convRed:*: d K₁≡K)
            (neNfₜ neK₂ (conv ⊢k K₁≡K) (~-conv k≡k K₁≡K))
  convTermT₂ {Γ = Γ} {s = s} {t = t}
         (cstrᵥ (cstrᵣ K KcodU a D ⊢a A≡A [domK] [a] [Yi])
                (cstrᵣ K₁ KcodU₁ a₁ D₁ ⊢a₁ A≡A₁ [domK]₁ [a]₁ [Yi]₁))
         (cstr₌ a' D' A≡B [a≡a'])
         (cstrₜ k d k≡k [k]) =
    let K₁a₁≡Ka' = whrDet* (red D₁ , cstrₙ) (red D' , cstrₙ)
        K₁≡K    = cstr-app-PE-injectivity K₁a₁≡Ka'
        a₁≡a'   = cstr-app-PE-arg-injectivity K₁a₁≡Ka'
        ⊢Ka'≡Ka  = ≅-eq (≅-sym (≅-cstr-cong KcodU A≡B))
        ⊢K₁a'≡K₁a  = PE.subst (λ k → Γ ⊢ cstr k ∘ a' ≡ cstr k ∘ a ⦂ s) (PE.sym K₁≡K) ⊢Ka'≡Ka
    in cstrₜ k
             (convRed:*: (PE.subst (λ x → Γ ⊢ t :⇒*: k ∷ x ⦂ s) K₁a₁≡Ka' d) ⊢Ka'≡Ka)
             (≅-conv (PE.subst (λ x → Γ ⊢ k ≅ k ∷ x ⦂ s) K₁a₁≡Ka' k≡k) ⊢Ka'≡Ka)
             (Cstr-prop-ext K₁≡K
                             (λ ki kiK kiK' t d → irrelevanceTerm ([Yi]₁ ki kiK) ([Yi] ki kiK') d)
                              ⊢K₁a'≡K₁a
                             (PE.subst (λ a → Cstr-prop K₁ Γ _ a _ k) a₁≡a' [k]))
  convTermT₂ {Γ = Γ} {s = s} (Πᵥ (Πᵣ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                         (Πᵣ sF₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
             (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
             (Πₜ f d funcF f≡f [f] [f]₁) =
    let ΠF₁G₁≡ΠF′G′   = whrDet* (red D₁ , Πₙ) (D′ , Πₙ)
        F₁≡F′ , sF₁≡sF′ , G₁≡G′ = Π-PE-injectivity ΠF₁G₁≡ΠF′G′
        ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ ⊢ Π F ⦂ sF ▹ G ≡ x ⦂ s)
                             (PE.sym ΠF₁G₁≡ΠF′G′) (≅-eq A≡B)
    in  Πₜ f (convRed:*: d (sym ΠFG≡ΠF₁G₁)) funcF (≅-conv f≡f (sym ΠFG≡ΠF₁G₁))
           (λ {ρ} [ρ] ⊢Δ [a] [b] [a≡b] →
              let [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                           ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                  [a]₁ = convTerm₁′ (PE.sym sF₁≡sF′) ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                  [b]₁ = convTerm₁′ (PE.sym sF₁≡sF′) ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [b]
                  [a≡b]₁ = convEqTerm₁′ (PE.sym sF₁≡sF′) ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a≡b]
                  [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                                    (PE.sym G₁≡G′))
                                           ([G] [ρ] ⊢Δ [a])
                                           ([G≡G′] [ρ] ⊢Δ [a])
              in  convEqTerm₂ ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁)
                              [G≡G₁] ([f] [ρ] ⊢Δ [a]₁ [b]₁ [a≡b]₁))
           (λ {ρ} [ρ] ⊢Δ [a] →
              let [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                           ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                  [a]₁ = convTerm₁′ (PE.sym sF₁≡sF′) ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                  [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                                    (PE.sym G₁≡G′))
                                           ([G] [ρ] ⊢Δ [a])
                                           ([G≡G′] [ρ] ⊢Δ [a])
              in  convTerm₂ ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁)
                            [G≡G₁] ([f]₁ [ρ] ⊢Δ [a]₁))
  convTermT₂ {Γ = Γ} {s = s} {t = t}
             (Boxᵥ (Boxᵣ F sF D ⊢F A≡A [F])
                   (Boxᵣ F' sF' D' ⊢F' A≡A' [F]'))
             (Box₌ F'' D'' A≡B [F≡F'])
             (boxₜ b d b≡b [b]) =
    let BF'≡BF'' = whrDet* (red D' , Boxₙ) (red D'' , Boxₙ)
        sF'≡sF = Box-sort-inj BF'≡BF''
        F'≡F''   = Box-inj BF'≡BF''
        ⊢BF''≡BF = ≅-eq (≅-sym A≡B)
    in boxₜ b
         (convRed:*: (PE.subst (λ x → Γ ⊢ t :⇒*: b ∷ x ⦂ 𝕥y) BF'≡BF'' d)
                     ⊢BF''≡BF)
         (≅-conv (PE.subst (λ x → Γ ⊢ b ≅ b ∷ x ⦂ 𝕥y) BF'≡BF'' b≡b)
                  ⊢BF''≡BF)
         (Box-prop-ext (λ x d →  convTerm₂′ F'≡F'' (PE.cong ‼ (PE.sym sF'≡sF)) [F] [F]' [F≡F'] d)
                       sF'≡sF
                       (PE.subst (λ BF → Γ ⊢ BF ≡ Box sF F ⦂ 𝕥y)
                                 (PE.sym BF'≡BF'')
                                 ⊢BF''≡BF)
                       [b])

  convTermT₂ (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) A≡B t rewrite Univ-PE-injectivity A≡B = t
  convTermT₂ (emb⁰¹ x) A≡B t = convTermT₂ x A≡B t
  convTermT₂ (emb¹⁰ x) A≡B t = convTermT₂ x A≡B t

  -- Conversion of terms converting from left to right.
  convTerm₁ : ∀ {Γ A B s t l l′} ([A] : Γ ⊩⟨ l ⟩ A ⦂ s) ([B] : Γ ⊩⟨ l′ ⟩ B ⦂ s)
            → Γ ⊩⟨ l ⟩  A ≡ B ⦂ s / [A]
            → Γ ⊩⟨ l ⟩  t ∷ A ⦂ s / [A]
            → Γ ⊩⟨ l′ ⟩ t ∷ B ⦂ s / [B]
  convTerm₁ [A] [B] A≡B t = convTermT₁ (goodCases [A] [B] A≡B) A≡B t

  -- Conversion of terms converting from left to right. with PE
  convTerm₁′ : ∀ {Γ A B s s' t l l′} (eq : s PE.≡ s') ([A] : Γ ⊩⟨ l ⟩ A ⦂ s) ([B] : Γ ⊩⟨ l′ ⟩ B ⦂ s')
            → Γ ⊩⟨ l ⟩  A ≡ B ⦂ s / [A]
            → Γ ⊩⟨ l ⟩  t ∷ A ⦂ s / [A]
            → Γ ⊩⟨ l′ ⟩ t ∷ B ⦂ s' / [B]
  convTerm₁′ PE.refl [A] [B] A≡B t = convTerm₁ [A] [B] A≡B t

  -- Conversion of terms converting from right to left.
  convTerm₂ : ∀ {Γ A B s t l l′} ([A] : Γ ⊩⟨ l ⟩ A ⦂ s) ([B] : Γ ⊩⟨ l′ ⟩ B ⦂ s)
          → Γ ⊩⟨ l ⟩  A ≡ B ⦂ s / [A]
          → Γ ⊩⟨ l′ ⟩ t ∷ B ⦂ s / [B]
          → Γ ⊩⟨ l ⟩  t ∷ A ⦂ s / [A]
  convTerm₂ [A] [B] A≡B t = convTermT₂ (goodCases [A] [B] A≡B) A≡B t

  -- Conversion of terms converting from right to left
  -- with some propsitionally equal types.
  convTerm₂′ : ∀ {Γ A s s' B B′ t l l′} → B PE.≡ B′ → s PE.≡ s'
          → ([A] : Γ ⊩⟨ l ⟩ A ⦂ s) ([B] : Γ ⊩⟨ l′ ⟩ B ⦂ s')
          → Γ ⊩⟨ l ⟩  A ≡ B′ ⦂ s / [A]
          → Γ ⊩⟨ l′ ⟩ t ∷ B ⦂ s' / [B]
          → Γ ⊩⟨ l ⟩  t ∷ A ⦂ s / [A]
  convTerm₂′ PE.refl PE.refl [A] [B] A≡B t = convTerm₂ [A] [B] A≡B t


  -- Helper function for conversion of term equality converting from left to right.
  convEqTermT₁ : ∀ {l l′ Γ A B s t u} {[A] : Γ ⊩⟨ l ⟩ A ⦂ s} {[B] : Γ ⊩⟨ l′ ⟩ B ⦂ s}
               → ShapeView Γ l l′ A B s s [A] [B]
               → Γ ⊩⟨ l ⟩  A ≡ B ⦂ s / [A]
               → Γ ⊩⟨ l ⟩  t ≡ u ∷ A ⦂ s / [A]
               → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B ⦂ s / [B]
  convEqTermT₁ (ℕᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₁ (Emptyᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₁ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
               (neₜ₌ k m d d′ (neNfₜ₌ neK₂ neM₁ k≡m)) =
    let K≡K₁ = PE.subst (λ x → _ ⊢ _ ≡ x ⦂ _)
                        (whrDet* (red D′ , ne neM) (red D₁ , ne neK₁))
                        (≅-eq (~-to-≅ K≡M))
    in  neₜ₌ k m (convRed:*: d K≡K₁)
                 (convRed:*: d′ K≡K₁)
                 (neNfₜ₌ neK₂ neM₁ (~-conv k≡m K≡K₁))
  convEqTermT₁ {Γ = Γ} {s = s} {t = t} {u = u}
         (cstrᵥ (cstrᵣ K KcodU a D ⊢a A≡A [domK] [a] [Yi])
                (cstrᵣ K₁ KcodU₁ a₁ D₁ ⊢a₁ A≡A₁ [domK]₁ [a]₁ [Yi]₁))
         (cstr₌ a' D' A≡B [a≡a'])
         (cstrₜ₌ k k' d d' k≡k' [k] [k'] [k≡k']) =
    let Ka'≡K₁a₁ = PE.sym (whrDet* (red D₁ , cstrₙ) (red D' , cstrₙ))
        K≡K₁    = cstr-app-PE-injectivity Ka'≡K₁a₁
        a'≡a₁   = cstr-app-PE-arg-injectivity Ka'≡K₁a₁
        cstrA   = (cstrᵣ′ K KcodU a D ⊢a A≡A [domK] [a] [Yi])
        cstrB   = (cstrᵣ′ K₁ KcodU₁ a₁ D₁ ⊢a₁ A≡A₁ [domK]₁ [a]₁ [Yi]₁)
        cstrA≡B = (cstr₌ a' D' A≡B [a≡a'])
        ⊢Ka≡Ka' = ≅-eq (≅-cstr-cong KcodU A≡B)
      in cstrₜ₌ k k'
                 (PE.subst (λ x → Γ ⊢ t :⇒*: k ∷ x ⦂ s) Ka'≡K₁a₁ (convRed:*: d ⊢Ka≡Ka'))
                 (PE.subst (λ x → Γ ⊢ u :⇒*: k' ∷ x ⦂ s) Ka'≡K₁a₁ (convRed:*: d' ⊢Ka≡Ka'))
                 (PE.subst (λ x → Γ ⊢ k ≅ k' ∷ x ⦂ s) Ka'≡K₁a₁ (≅-conv k≡k' ⊢Ka≡Ka'))
                 (convTerm₁ cstrA cstrB cstrA≡B [k])
                 (convTerm₁ cstrA cstrB cstrA≡B [k'])
                 (PE.subst (λ a → [Cstr]-prop K₁ Γ _ a _ k k')  a'≡a₁
                           ([Cstr]-prop-ext K≡K₁ (λ ki kiK kiK' t t' d → irrelevanceEqTerm ([Yi] ki kiK) ([Yi]₁ ki kiK') d ) ⊢Ka≡Ka' [k≡k']))
  convEqTermT₁ {Γ = Γ} {s = s} (Πᵥ (Πᵣ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                           (Πᵣ sF₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
               (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
               (Πₜ₌ f g d d′ funcF funcG t≡u [t] [u] [t≡u]) =
    let [A] = Πᵣ′ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext
        [B] = Πᵣ′ sF₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁
        [A≡B] = Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]
        ΠF₁G₁≡ΠF′G′ = whrDet* (red D₁ , Πₙ) (D′ , Πₙ)
        ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ ⊢ Π F ⦂ sF ▹ G ≡ x ⦂ s)
                             (PE.sym ΠF₁G₁≡ΠF′G′) (≅-eq A≡B)
    in  Πₜ₌ f g (convRed:*: d ΠFG≡ΠF₁G₁) (convRed:*: d′ ΠFG≡ΠF₁G₁)
            funcF funcG (≅-conv t≡u ΠFG≡ΠF₁G₁)
            (convTerm₁ [A] [B] [A≡B] [t]) (convTerm₁ [A] [B] [A≡B] [u])
            (λ {ρ} [ρ] ⊢Δ [a] →
               let F₁≡F′ , sF₁≡sF′ , G₁≡G′ = Π-PE-injectivity (whrDet* (red D₁ , Πₙ) (D′ , Πₙ))
                   [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                            ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                   [a]₁ = convTerm₂′ PE.refl (PE.sym sF₁≡sF′) ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                   [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                                     (PE.sym G₁≡G′))
                                            ([G] [ρ] ⊢Δ [a]₁)
                                            ([G≡G′] [ρ] ⊢Δ [a]₁)
               in  convEqTerm₁ ([G] [ρ] ⊢Δ [a]₁) ([G]₁ [ρ] ⊢Δ [a])
                               [G≡G₁] ([t≡u] [ρ] ⊢Δ [a]₁))
  convEqTermT₁ {Γ = Γ} {s = s} {t = t} {u = u}
               (Boxᵥ (Boxᵣ F sF D ⊢F A≡A [F])
                     (Boxᵣ F' sF' D' ⊢F' A≡A' [F]'))
               (Box₌ F'' D'' A≡B [F≡F'])
               (boxₜ₌ b b' d d' b≡b' [b] [b'] [b≡b']) =
    let BF''≡BF' = whrDet* (red D'' , Boxₙ) (red D' , Boxₙ)
        sF≡sF' = Box-sort-inj BF''≡BF'
        F''≡F'   = Box-inj BF''≡BF'
        ⊢BF≡BF'' = ≅-eq A≡B
        BoxA     = Boxᵣ′ F sF D ⊢F A≡A [F]
        BoxB     = Boxᵣ′ F' sF' D' ⊢F' A≡A' [F]'
        BoxAB    = Box₌ F'' D'' A≡B [F≡F']
    in boxₜ₌ b b'
         (PE.subst (λ BF → Γ ⊢ t :⇒*: b ∷ BF ⦂ 𝕥y) BF''≡BF'
          (convRed:*: d ⊢BF≡BF''))
         (PE.subst (λ BF → Γ ⊢ u :⇒*: b' ∷ BF ⦂ 𝕥y) BF''≡BF'
          (convRed:*: d' ⊢BF≡BF''))
         (PE.subst (λ BF → Γ ⊢ b ≅ b' ∷ BF ⦂ 𝕥y) BF''≡BF'
          (≅-conv b≡b' ⊢BF≡BF''))
         (convTerm₁ BoxA BoxB BoxAB [b])
         (convTerm₁ BoxA BoxB BoxAB [b'])
         ([Box]-prop-ext
           (λ x x' d → convEqTerm₁′ (PE.cong ‼ sF≡sF') [F] [F]'
                                    (PE.subst (λ G → Γ ⊩⟨ _ ⟩ F ≡ G ⦂ _ / [F]) F''≡F' [F≡F']) d)
           sF≡sF' (PE.subst (λ BF → Γ ⊢ Box sF F ≡ BF ⦂ 𝕥y) BF''≡BF' ⊢BF≡BF'') [b≡b'])
  convEqTermT₁ (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) A≡B t≡u rewrite Univ-PE-injectivity A≡B = t≡u
  convEqTermT₁ (emb⁰¹ x) A≡B t≡u = convEqTermT₁ x A≡B t≡u
  convEqTermT₁ (emb¹⁰ x) A≡B t≡u = convEqTermT₁ x A≡B t≡u

  -- Helper function for conversion of term equality converting from right to left.
  convEqTermT₂ : ∀ {l l′ Γ A B t u s} {[A] : Γ ⊩⟨ l ⟩ A ⦂ s} {[B] : Γ ⊩⟨ l′ ⟩ B ⦂ s}
             → ShapeView Γ l l′ A B s s [A] [B]
             → Γ ⊩⟨ l ⟩  A ≡ B ⦂ s / [A]
             → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B ⦂ s / [B]
             → Γ ⊩⟨ l ⟩  t ≡ u ∷ A ⦂ s / [A]
  convEqTermT₂ (ℕᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₂ (Emptyᵥ D D′) A≡B t≡u = t≡u
  convEqTermT₂ (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
               (neₜ₌ k m d d′ (neNfₜ₌ neK₂ neM₁ k≡m)) =
    let K₁≡K = PE.subst (λ x → _ ⊢ x ≡ _ ⦂ _)
                        (whrDet* (red D′ , ne neM) (red D₁ , ne neK₁))
                        (sym (≅-eq (~-to-≅ K≡M)))
    in  neₜ₌ k m (convRed:*: d K₁≡K) (convRed:*: d′ K₁≡K)
                 (neNfₜ₌ neK₂ neM₁ (~-conv k≡m K₁≡K))
  convEqTermT₂ {Γ = Γ} {t = t} {u = u} {s = s}
         (cstrᵥ (cstrᵣ K KcodU a D ⊢a A≡A [domK] [a] [Yi])
                (cstrᵣ K₁ KcodU₁ a₁ D₁ ⊢a₁ A≡A₁ [domK]₁ [a]₁ [Yi]₁))
         (cstr₌ a' D' A≡B [a≡a'])
         (cstrₜ₌ k k' d d' k≡k' [k] [k'] [k≡k']) =
    let K₁a₁≡Ka' = whrDet* (red D₁ , cstrₙ) (red D' , cstrₙ)
        K₁≡K    = cstr-app-PE-injectivity K₁a₁≡Ka'
        a₁≡a'   = cstr-app-PE-arg-injectivity K₁a₁≡Ka'
        ⊢Ka'≡Ka  = ≅-eq (≅-sym (≅-cstr-cong KcodU A≡B))
        ⊢K₁a'≡K₁a  = PE.subst (λ k → Γ ⊢ cstr k ∘ a' ≡ cstr k ∘ a ⦂ s) (PE.sym K₁≡K) ⊢Ka'≡Ka
        cstrA   = (cstrᵣ K KcodU a D ⊢a A≡A [domK] [a] [Yi])
        cstrB   = (cstrᵣ K₁ KcodU₁ a₁ D₁ ⊢a₁ A≡A₁ [domK]₁ [a]₁ [Yi]₁)
        cstrA≡B = (cstr₌ a' D' A≡B [a≡a'])
        -- ⊢Ka≡Ka' = ≅-eq (≅-cstr-cong KcodU₁ (wfTerm ⊢a₁) (PE.subst (λ k → Γ ⊢ a ≅ a' ∷ wkAll Γ (cstr-dom k) ⦂ cstr-dom-sort k) (PE.sym K≡K₁) A≡B))
      in cstrₜ₌ k k'
               (convRed:*: (PE.subst (λ x → Γ ⊢ t :⇒*: k ∷ x ⦂ s) K₁a₁≡Ka' d) ⊢Ka'≡Ka)
               (convRed:*: (PE.subst (λ x → Γ ⊢ u :⇒*: k' ∷ x ⦂ s) K₁a₁≡Ka' d') ⊢Ka'≡Ka)
               (≅-conv (PE.subst (λ x → Γ ⊢ k ≅ k' ∷ x ⦂ s) K₁a₁≡Ka' k≡k') ⊢Ka'≡Ka)
               (convTermT₂ (cstrᵥ cstrA cstrB) cstrA≡B [k])
               (convTermT₂ (cstrᵥ cstrA cstrB) cstrA≡B [k'])
               ([Cstr]-prop-ext K₁≡K
                             (λ ki kiK kiK' t t' d → irrelevanceEqTerm ([Yi]₁ ki kiK) ([Yi] ki kiK') d)
                              ⊢K₁a'≡K₁a
                             (PE.subst (λ a → [Cstr]-prop K₁ Γ _ a _ k k') a₁≡a' [k≡k']))
  convEqTermT₂ {Γ = Γ} {s = s} (Πᵥ (Πᵣ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                           (Πᵣ sF₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
               (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
               (Πₜ₌ f g d d′ funcF funcG t≡u [t] [u] [t≡u]) =
    let [A] = Πᵣ′ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext
        [B] = Πᵣ′ sF₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁
        [A≡B] = Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]
        ΠF₁G₁≡ΠF′G′ = whrDet* (red D₁ , Πₙ) (D′ , Πₙ)
        ΠFG≡ΠF₁G₁ = PE.subst (λ x → Γ ⊢ Π F ⦂ sF ▹ G ≡ x ⦂ s)
                             (PE.sym ΠF₁G₁≡ΠF′G′) (≅-eq A≡B)
    in  Πₜ₌ f g (convRed:*: d (sym ΠFG≡ΠF₁G₁)) (convRed:*: d′ (sym ΠFG≡ΠF₁G₁))
            funcF funcG (≅-conv t≡u (sym ΠFG≡ΠF₁G₁))
            (convTerm₂ [A] [B] [A≡B] [t]) (convTerm₂ [A] [B] [A≡B] [u])
            (λ {ρ} [ρ] ⊢Δ [a] →
               let F₁≡F′ , sF₁≡sF′ , G₁≡G′ = Π-PE-injectivity (whrDet* (red D₁ , Πₙ) (D′ , Πₙ))
                   [F≡F₁] = irrelevanceEqR′ (PE.cong (wk ρ) (PE.sym F₁≡F′))
                                            ([F] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ)
                   [a]₁ = convTerm₁′ (PE.sym sF₁≡sF′) ([F] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [F≡F₁] [a]
                   [G≡G₁] = irrelevanceEqR′ (PE.cong (λ x → wk (lift ρ) x [ _ ])
                                                     (PE.sym G₁≡G′))
                                            ([G] [ρ] ⊢Δ [a])
                                            ([G≡G′] [ρ] ⊢Δ [a])
               in  convEqTerm₂ ([G] [ρ] ⊢Δ [a]) ([G]₁ [ρ] ⊢Δ [a]₁)
                               [G≡G₁] ([t≡u] [ρ] ⊢Δ [a]₁))
  convEqTermT₂ {Γ = Γ} {t = t} {u = u} {s = s}
               (Boxᵥ (Boxᵣ F sF D ⊢F A≡A [F])
                     (Boxᵣ F' sF' D' ⊢F' A≡A' [F]'))
               (Box₌ F'' D'' A≡B [F≡F'])
               (boxₜ₌ b b' d d' b≡b' [b] [b'] [b≡b']) =
    let BF''≡BF' = whrDet* (red D'' , Boxₙ) (red D' , Boxₙ)
        BF'≡BF'' = PE.sym BF''≡BF'
        sF≡sF'   = Box-sort-inj BF''≡BF'
        sF'≡sF   = PE.sym sF≡sF'
        F''≡F'   = Box-inj BF''≡BF'
        F'≡F''   = PE.sym F''≡F'
        ⊢BF''≡BF = ≅-eq (≅-sym A≡B)
        BoxA     = Boxᵣ′ F sF D ⊢F A≡A [F]
        BoxB     = Boxᵣ′ F' sF' D' ⊢F' A≡A' [F]'
        BoxAB    = Box₌ F'' D'' A≡B [F≡F']
    in boxₜ₌ b b'
         (convRed:*: (PE.subst (λ BF → Γ ⊢ t :⇒*: b ∷ BF ⦂ 𝕥y) BF'≡BF'' d) ⊢BF''≡BF)
         (convRed:*: (PE.subst (λ BF → Γ ⊢ u :⇒*: b' ∷ BF ⦂ 𝕥y) BF'≡BF'' d') ⊢BF''≡BF)
         (≅-conv (PE.subst (λ BF → Γ ⊢ b ≅ b' ∷ BF ⦂ 𝕥y) BF'≡BF'' b≡b') ⊢BF''≡BF)
         (convTerm₂ BoxA BoxB BoxAB [b])
         (convTerm₂ BoxA BoxB BoxAB [b'])
         ([Box]-prop-ext (λ x x' d → convEqTerm₂′ (PE.cong ‼ sF≡sF') [F] [F]' (PE.subst (λ G → Γ ⊩⟨ _ ⟩ F ≡ G ⦂ _ / [F]) F''≡F' [F≡F']) d)
           sF'≡sF (PE.subst (λ BF → Γ ⊢ BF ≡ Box sF F ⦂ 𝕥y) BF''≡BF' ⊢BF''≡BF) [b≡b'])
  convEqTermT₂ (Uᵥ (Uᵣ .⁰ 0<1 ⊢Γ) (Uᵣ .⁰ 0<1 ⊢Γ₁)) A≡B t≡u rewrite Univ-PE-injectivity A≡B = t≡u
  convEqTermT₂ (emb⁰¹ x) A≡B t≡u = convEqTermT₂ x A≡B t≡u
  convEqTermT₂ (emb¹⁰ x) A≡B t≡u = convEqTermT₂ x A≡B t≡u

  -- Conversion of term equality converting from left to right.
  convEqTerm₁ : ∀ {l l′ Γ A B t u s} ([A] : Γ ⊩⟨ l ⟩ A ⦂ s) ([B] : Γ ⊩⟨ l′ ⟩ B ⦂ s)
              → Γ ⊩⟨ l ⟩  A ≡ B ⦂ s / [A]
              → Γ ⊩⟨ l ⟩  t ≡ u ∷ A ⦂ s / [A]
              → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B ⦂ s / [B]
  convEqTerm₁ [A] [B] A≡B t≡u = convEqTermT₁ (goodCases [A] [B] A≡B) A≡B t≡u

  -- Conversion of term equality converting from left to right. with PE
  convEqTerm₁′ : ∀ {l l′ Γ A B t u s s'} (eq : s PE.≡ s') ([A] : Γ ⊩⟨ l ⟩ A ⦂ s) ([B] : Γ ⊩⟨ l′ ⟩ B ⦂ s')
              → Γ ⊩⟨ l ⟩  A ≡ B ⦂ s / [A]
              → Γ ⊩⟨ l ⟩  t ≡ u ∷ A ⦂ s / [A]
              → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B ⦂ s' / [B]
  convEqTerm₁′ PE.refl [A] [B] A≡B t≡u = convEqTerm₁ [A] [B] A≡B t≡u

  -- Conversion of term equality converting from right to left.
  convEqTerm₂ : ∀ {l l′ Γ A B t u s} ([A] : Γ ⊩⟨ l ⟩ A ⦂ s) ([B] : Γ ⊩⟨ l′ ⟩ B ⦂ s)
            → Γ ⊩⟨ l ⟩  A ≡ B ⦂ s / [A]
            → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B ⦂ s / [B]
            → Γ ⊩⟨ l ⟩  t ≡ u ∷ A ⦂ s / [A]
  convEqTerm₂ [A] [B] A≡B t≡u = convEqTermT₂ (goodCases [A] [B] A≡B) A≡B t≡u

  -- Conversion of term equality converting from right to left with PE
  convEqTerm₂′ : ∀ {l l′ Γ A B t u s s'} (eq : s PE.≡ s') ([A] : Γ ⊩⟨ l ⟩ A ⦂ s) ([B] : Γ ⊩⟨ l′ ⟩ B ⦂ s')
            → Γ ⊩⟨ l ⟩  A ≡ B ⦂ s / [A]
            → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B ⦂ s' / [B]
            → Γ ⊩⟨ l ⟩  t ≡ u ∷ A ⦂ s / [A]
  convEqTerm₂′ PE.refl [A] [B] A≡B t≡u = convEqTerm₂ [A] [B] A≡B t≡u
