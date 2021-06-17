{-# OPTIONS --without-K  #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Symmetry {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties.Conversion

open import Tools.Product
import Tools.PropositionalEquality as PE

symNeutralTerm : ∀ {t u A s Γ}
              → Γ ⊩neNf t ≡ u ∷ A ⦂ s
              → Γ ⊩neNf u ≡ t ∷ A ⦂ s
symNeutralTerm (neNfₜ₌ neK neM k≡m) = neNfₜ₌ neM neK (~-sym k≡m)

symNatural-prop : ∀ {Γ k k′}
                → [Natural]-prop Γ k k′
                → [Natural]-prop Γ k′ k
symNatural-prop (sucᵣ (ℕₜ₌ k k′ d d′ t≡u prop)) =
  sucᵣ (ℕₜ₌ k′ k d′ d (≅ₜ-sym t≡u) (symNatural-prop prop))
symNatural-prop zeroᵣ = zeroᵣ
symNatural-prop (ne prop) = ne (symNeutralTerm prop)

symEmpty-prop : ∀ {Γ k k′}
                → [Empty]-prop Γ k k′
                → [Empty]-prop Γ k′ k
symEmpty-prop (ne prop) = ne (symNeutralTerm prop)

[Cstr]-prop-sym : ∀ {K Γ Pi a s t t'}
                    (Pi-sym : ∀ ki kiK t t' → Pi ki kiK t t' → Pi ki kiK t' t)
                    (d : [Cstr]-prop K Γ Pi a s t t')
                  → [Cstr]-prop K Γ Pi a s t' t
[Cstr]-prop-sym Pi-sym (cstrᵣ kK x) = cstrᵣ kK (Pi-sym _ _ _ _ x)
[Cstr]-prop-sym Pi-sym (ne x) = ne (symNeutralTerm x)


[Box]-prop-sym : ∀ {P Γ sF F b b'}
                   (P-sym : ∀ b b' → P b b' → P b' b)
                   (d : [Box]-prop P Γ sF F b b')
                 → [Box]-prop P Γ sF F b' b
[Box]-prop-sym P-sym (boxᵣ x) = boxᵣ (P-sym _ _ x)
[Box]-prop-sym P-sym (ne x) = ne (symNeutralTerm x)

mutual
  -- Helper function for symmetry of type equality using shape views.
  {-# TERMINATING #-}
  symEqT : ∀ {Γ A B s l l′} {[A] : Γ ⊩⟨ l ⟩ A ⦂ s} {[B] : Γ ⊩⟨ l′ ⟩ B ⦂ s}
         → ShapeView Γ l l′ A B s s [A] [B]
         → Γ ⊩⟨ l  ⟩ A ≡ B ⦂ s / [A]
         → Γ ⊩⟨ l′ ⟩ B ≡ A ⦂ s / [B]
  symEqT (ℕᵥ D D′) A≡B = red D
  symEqT (Emptyᵥ D D′) A≡B = red D
  symEqT (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
         rewrite whrDet* (red D′ , ne neM) (red D₁ , ne neK₁) =
    ne₌ _ D neK
        (~-sym K≡M)
  symEqT {Γ} {s = s}
         (cstrᵥ (cstrᵣ K KcodU a D ⊢a A≡A [domK] [a] [Yi])
                (cstrᵣ K₁ KcodU₁ a₁ D₁ ⊢a₁ A≡A₁ [domK]₁ [a]₁ [Yi]₁))
         (cstr₌ a' D' A≡B [a≡a']) =
    let Ka≡K₁a₁ = PE.sym (whrDet* (red D₁ , cstrₙ) (red D' , cstrₙ))
        K≡K₁    = cstr-app-PE-injectivity Ka≡K₁a₁
        a≡a₁    = cstr-app-PE-arg-injectivity Ka≡K₁a₁
    in cstr₌ a
            (PE.subst (λ k → Γ ⊢ _ :⇒*: cstr k ∘ a ⦂ s) K≡K₁ D)
            (≅ₜ-sym (PE.subst₂ (λ a' k → Γ ⊢ a ≅ a' ∷ wkAll Γ (cstr-dom k) ⦂ _) a≡a₁ K≡K₁ A≡B))
            (symEqTerm [domK]₁
                       (PE.subst (λ a' → Γ ⊩⟨ _ ⟩ a ≡ a' ∷ _ ⦂ _ / [domK]₁) a≡a₁
                                 (irrelevanceEqTerm′ (PE.cong (λ k → wk (empty-wk Γ) (cstr-dom k)) K≡K₁)
                                                     (PE.cong cstr-dom-sort K≡K₁)
                                                     [domK]
                                                     [domK]₁
                                                     [a≡a'])))
  symEqT {Γ} {A = A} {s = s}
         (Boxᵥ (Boxᵣ F sF D ⊢F A≡A [F])
               (Boxᵣ F' sF' D' ⊢F' A≡A' [F]'))
         (Box₌ F'' D'' A≡B [F≡F']) =
    let BF''≡BF' = whrDet* (red D'' , Boxₙ) (red D' , Boxₙ)
        sF≡sF'   = Box-sort-inj BF''≡BF'
        F''≡F'   = Box-inj BF''≡BF'
    in Box₌ F (PE.subst (λ s → Γ ⊢ A :⇒*: Box s F ⦂ 𝕥y) sF≡sF' D)
              (≅-sym (PE.subst₂ (λ s G → Γ ⊢ Box s F ≅ Box s G ⦂ 𝕥y) sF≡sF' F''≡F' A≡B))
              (symEq′ (PE.cong ‼ sF≡sF') [F] [F]' (PE.subst (λ G → Γ ⊩⟨ _ ⟩ F ≡ G ⦂ _ / [F]) F''≡F' [F≡F']))
  symEqT {Γ = Γ} {s = s} (Πᵥ (Πᵣ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                     (Πᵣ sF₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
         (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
    let ΠF₁G₁≡ΠF′G′   = whrDet* (red D₁ , Πₙ) (D′ , Πₙ)
        F₁≡F′ , sF₁≡sF′ , G₁≡G′ = Π-PE-injectivity ΠF₁G₁≡ΠF′G′
        [F₁≡F] : ∀ {Δ} {ρ} [ρ] ⊢Δ → _
        [F₁≡F] {Δ} {ρ} [ρ] ⊢Δ =
          let ρF′≡ρF₁ ρ = PE.cong (wk ρ) (PE.sym F₁≡F′)
              [ρF′] {ρ} [ρ] ⊢Δ = PE.subst (λ x → Δ ⊩⟨ _ ⟩ wk ρ x ⦂ _) F₁≡F′ ([F]₁ [ρ] ⊢Δ)
          in  irrelevanceEq′ {Δ} (ρF′≡ρF₁ ρ) PE.refl
                             ([ρF′] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ)
                             (symEq′ (PE.sym sF₁≡sF′) ([F] [ρ] ⊢Δ) ([ρF′] [ρ] ⊢Δ)
                                    ([F≡F′] [ρ] ⊢Δ))
    in  Π₌ _ _ (red (PE.subst _ (PE.sym sF₁≡sF′) D)) (PE.subst _ (PE.sym sF₁≡sF′) (≅-sym (PE.subst (λ x → Γ ⊢ Π F ⦂ sF ▹ G ≅ x ⦂ s) (PE.sym ΠF₁G₁≡ΠF′G′) A≡B)))
          [F₁≡F]
          (λ {ρ} [ρ] ⊢Δ [a] →
               let ρG′a≡ρG₁′a = PE.cong (λ x → wk (lift ρ) x [ _ ]) (PE.sym G₁≡G′)
                   [ρG′a] = PE.subst (λ x → _ ⊩⟨ _ ⟩ wk (lift ρ) x [ _ ] ⦂ _) G₁≡G′
                                     ([G]₁ [ρ] ⊢Δ [a])
                   [a]₁ = convTerm₁′ sF₁≡sF′ ([F]₁ [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) ([F₁≡F] [ρ] ⊢Δ) [a]
               in  irrelevanceEq′ ρG′a≡ρG₁′a PE.refl
                                  [ρG′a]
                                  ([G]₁ [ρ] ⊢Δ [a])
                                  (symEq ([G] [ρ] ⊢Δ [a]₁) [ρG′a]
                                         ([G≡G′] [ρ] ⊢Δ [a]₁)))
  symEqT (Uᵥ (Uᵣ _ _ _) (Uᵣ _ _ _)) A≡B rewrite Univ-PE-injectivity A≡B = PE.refl
  symEqT (emb⁰¹ x) A≡B = symEqT x A≡B
  symEqT (emb¹⁰ x) A≡B = symEqT x A≡B

  -- Symmetry of type equality.
  symEq : ∀ {Γ A B s l l′} ([A] : Γ ⊩⟨ l ⟩ A ⦂ s) ([B] : Γ ⊩⟨ l′ ⟩ B ⦂ s)
        → Γ ⊩⟨ l ⟩ A ≡ B ⦂ s / [A]
        → Γ ⊩⟨ l′ ⟩ B ≡ A ⦂ s / [B]
  symEq [A] [B] A≡B = symEqT (goodCases [A] [B] A≡B) A≡B

  -- same but with PE
  symEq′ : ∀ {Γ A B s s' l l′} (eq : s PE.≡ s') ([A] : Γ ⊩⟨ l ⟩ A ⦂ s) ([B] : Γ ⊩⟨ l′ ⟩ B ⦂ s')
        → Γ ⊩⟨ l ⟩ A ≡ B ⦂ s / [A]
        → Γ ⊩⟨ l′ ⟩ B ≡ A ⦂ s' / [B]
  symEq′ PE.refl [A] [B] A≡B = symEq [A] [B] A≡B


  -- Symmetry of term equality.
  symEqTerm : ∀ {l Γ A t u s} ([A] : Γ ⊩⟨ l ⟩ A ⦂ s)
            → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ⦂ s / [A]
            → Γ ⊩⟨ l ⟩ u ≡ t ∷ A ⦂ s / [A]
  symEqTerm (Uᵣ′ _ .⁰ 0<1 ⊢Γ) (Uₜ₌ A B d d′ typeA typeB A≡B [A] [B] [A≡B]) =
    Uₜ₌ B A d′ d typeB typeA (≅ₜ-sym A≡B) [B] [A] (symEq [A] [B] [A≡B])
  symEqTerm (ℕᵣ D) (ℕₜ₌ k k′ d d′ t≡u prop) =
    ℕₜ₌ k′ k d′ d (≅ₜ-sym t≡u) (symNatural-prop prop)
  symEqTerm (Emptyᵣ D) (Emptyₜ₌ k k′ d d′ t≡u prop) =
    Emptyₜ₌ k′ k d′ d (≅ₜ-sym t≡u) (symEmpty-prop prop)
  symEqTerm (ne′ K D neK K≡K) (neₜ₌ k m d d′ nf) =
    neₜ₌ m k d′ d (symNeutralTerm nf)
  symEqTerm (Πᵣ′ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
            (Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g]) =
    Πₜ₌ g f d′ d funcG funcF (≅ₜ-sym f≡g) [g] [f]
        (λ ρ ⊢Δ [a] → symEqTerm ([G] ρ ⊢Δ [a]) ([f≡g] ρ ⊢Δ [a]))
  symEqTerm (cstrᵣ′ K KcodU a D ⊢a A≡A [domK] [a] [Yi])
            (cstrₜ₌ k k' d d' k≡k' [k] [k'] [k≡k']) =
    cstrₜ₌ k' k d' d (≅ₜ-sym k≡k') [k'] [k] ([Cstr]-prop-sym (λ ki kiK t t' x → symEqTerm ([Yi] ki kiK) x) [k≡k'])
  symEqTerm (Boxᵣ′ F sF D ⊢F A≡A [F])
            (boxₜ₌ b b' d d' b≡b' [b] [b'] [b≡b']) =
    boxₜ₌ b' b d' d (≅ₜ-sym b≡b') [b'] [b] ([Box]-prop-sym (λ b b' d → symEqTerm [F] d) [b≡b'])
  symEqTerm (emb 0<1 x) t≡u = symEqTerm x t≡u
