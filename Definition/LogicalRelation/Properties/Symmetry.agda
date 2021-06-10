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


mutual
  -- Helper function for symmetry of type equality using shape views.
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
symEqTerm (emb 0<1 x) t≡u = symEqTerm x t≡u
