{-# OPTIONS --safe #-}

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
  symEqT : ∀ {Γ A B r l l′} {[A] : Γ ⊩⟨ l ⟩ A ^ r} {[B] : Γ ⊩⟨ l′ ⟩ B ^ r}
         → ShapeView Γ l l′ A B r r [A] [B]
         → Γ ⊩⟨ l  ⟩ A ≡ B ^ r / [A]
         → Γ ⊩⟨ l′ ⟩ B ≡ A ^ r / [B]
  symEqT (ℕᵥ D D′) A≡B = red D
  symEqT (Emptyᵥ D D′) A≡B = red D
  symEqT (ne (ne K D neK K≡K) (ne K₁ D₁ neK₁ K≡K₁)) (ne₌ M D′ neM K≡M)
         rewrite whrDet* (red D′ , ne neM) (red D₁ , ne neK₁) =
    ne₌ _ D neK
        (~-sym K≡M)
  symEqT {Γ = Γ} {r = r} (Πᵥ (Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                     (Πᵣ rF₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
         (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
    let ΠF₁G₁≡ΠF′G′   = whrDet* (red D₁ , Πₙ) (D′ , Πₙ)
        F₁≡F′ , rF₁≡rF′ , G₁≡G′ = Π-PE-injectivity ΠF₁G₁≡ΠF′G′
        [F₁≡F] : ∀ {Δ} {ρ} [ρ] ⊢Δ → _
        [F₁≡F] {Δ} {ρ} [ρ] ⊢Δ =
          let ρF′≡ρF₁ ρ = PE.cong (wk ρ) (PE.sym F₁≡F′)
              [ρF′] {ρ} [ρ] ⊢Δ = PE.subst (λ x → Δ ⊩⟨ _ ⟩ wk ρ x ^ _) F₁≡F′ ([F]₁ [ρ] ⊢Δ)
          in  irrelevanceEq′ {Δ} (ρF′≡ρF₁ ρ) PE.refl
                             ([ρF′] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ)
                             (symEq′ (PE.sym rF₁≡rF′) ([F] [ρ] ⊢Δ) ([ρF′] [ρ] ⊢Δ)
                                    ([F≡F′] [ρ] ⊢Δ))
    in  Π₌ _ _ (red (PE.subst _ (PE.sym rF₁≡rF′) D)) (PE.subst _ (PE.sym rF₁≡rF′) (≅-sym (PE.subst (λ x → Γ ⊢ Π F ^ rF ▹ G ≅ x ^ r) (PE.sym ΠF₁G₁≡ΠF′G′) A≡B)))
          [F₁≡F]
          (λ {ρ} [ρ] ⊢Δ [a] →
               let ρG′a≡ρG₁′a = PE.cong (λ x → wk (lift ρ) x [ _ ]) (PE.sym G₁≡G′)
                   [ρG′a] = PE.subst (λ x → _ ⊩⟨ _ ⟩ wk (lift ρ) x [ _ ] ^ _) G₁≡G′
                                     ([G]₁ [ρ] ⊢Δ [a])
                   [a]₁ = convTerm₁′ rF₁≡rF′ ([F]₁ [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) ([F₁≡F] [ρ] ⊢Δ) [a]
               in  irrelevanceEq′ ρG′a≡ρG₁′a PE.refl
                                  [ρG′a]
                                  ([G]₁ [ρ] ⊢Δ [a])
                                  (symEq ([G] [ρ] ⊢Δ [a]₁) [ρG′a]
                                         ([G≡G′] [ρ] ⊢Δ [a]₁)))
  symEqT {Γ = Γ} (∃ᵥ (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                     (∃ᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
         (∃₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
    let ∃F₁G₁≡∃F′G′   = whrDet* (red D₁ , ∃ₙ) (D′ , ∃ₙ)
        F₁≡F′ , G₁≡G′ = ∃-PE-injectivity ∃F₁G₁≡∃F′G′
        [F₁≡F] : ∀ {Δ} {ρ} [ρ] ⊢Δ → _
        [F₁≡F] {Δ} {ρ} [ρ] ⊢Δ =
          let ρF′≡ρF₁ ρ = PE.cong (wk ρ) (PE.sym F₁≡F′)
              [ρF′] {ρ} [ρ] ⊢Δ = PE.subst (λ x → Δ ⊩⟨ _ ⟩ wk ρ x ^ _) F₁≡F′ ([F]₁ [ρ] ⊢Δ)
          in  irrelevanceEq′ {Δ} (ρF′≡ρF₁ ρ) PE.refl
                             ([ρF′] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ)
                             (symEq′ PE.refl ([F] [ρ] ⊢Δ) ([ρF′] [ρ] ⊢Δ)
                                    ([F≡F′] [ρ] ⊢Δ))
    in  ∃₌ _ _ (red D) (≅-sym (PE.subst (λ x → Γ ⊢ ∃ F ▹ G ≅ x ^ %) (PE.sym ∃F₁G₁≡∃F′G′) A≡B))
          [F₁≡F]
          (λ {ρ} [ρ] ⊢Δ [a] →
               let ρG′a≡ρG₁′a = PE.cong (λ x → wk (lift ρ) x [ _ ]) (PE.sym G₁≡G′)
                   [ρG′a] = PE.subst (λ x → _ ⊩⟨ _ ⟩ wk (lift ρ) x [ _ ] ^ _) G₁≡G′
                                     ([G]₁ [ρ] ⊢Δ [a])
                   [a]₁ = convTerm₁′ PE.refl ([F]₁ [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) ([F₁≡F] [ρ] ⊢Δ) [a]
               in  irrelevanceEq′ ρG′a≡ρG₁′a PE.refl
                                  [ρG′a]
                                  ([G]₁ [ρ] ⊢Δ [a])
                                  (symEq ([G] [ρ] ⊢Δ [a]₁) [ρG′a]
                                         ([G≡G′] [ρ] ⊢Δ [a]₁)))
  symEqT (Uᵥ (Uᵣ _ _ _) (Uᵣ _ _ _)) A≡B rewrite Univ-PE-injectivity A≡B = PE.refl
  symEqT (emb⁰¹ x) A≡B = symEqT x A≡B
  symEqT (emb¹⁰ x) A≡B = symEqT x A≡B

  -- Symmetry of type equality.
  symEq : ∀ {Γ A B r l l′} ([A] : Γ ⊩⟨ l ⟩ A ^ r) ([B] : Γ ⊩⟨ l′ ⟩ B ^ r)
        → Γ ⊩⟨ l ⟩ A ≡ B ^ r / [A]
        → Γ ⊩⟨ l′ ⟩ B ≡ A ^ r / [B]
  symEq [A] [B] A≡B = symEqT (goodCases [A] [B] A≡B) A≡B

  -- same but with PE
  symEq′ : ∀ {Γ A B r r' l l′} (eq : r PE.≡ r') ([A] : Γ ⊩⟨ l ⟩ A ^ r) ([B] : Γ ⊩⟨ l′ ⟩ B ^ r')
        → Γ ⊩⟨ l ⟩ A ≡ B ^ r / [A]
        → Γ ⊩⟨ l′ ⟩ B ≡ A ^ r' / [B]
  symEq′ PE.refl [A] [B] A≡B = symEq [A] [B] A≡B

symNeutralTerm : ∀ {t u A r Γ}
               → Γ ⊩neNf t ≡ u ∷ A ^ r
               → Γ ⊩neNf u ≡ t ∷ A ^ r
symNeutralTerm {r = !} (neNfₜ₌ neK neM k≡m) = neNfₜ₌ neM neK (~-sym k≡m)
symNeutralTerm {r = %} (neNfₜ₌ neK neM k≡m) = neNfₜ₌ neM neK (~-sym k≡m)

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
symEmpty-prop (ne t u ) = ne u t

-- Symmetry of term equality.
symEqTerm : ∀ {l Γ A t u r} ([A] : Γ ⊩⟨ l ⟩ A ^ r)
          → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ r / [A]
          → Γ ⊩⟨ l ⟩ u ≡ t ∷ A ^ r / [A]
symEqTerm (Uᵣ′ _ .⁰ 0<1 ⊢Γ) (Uₜ₌ A B d d′ typeA typeB A≡B [A] [B] [A≡B]) =
  Uₜ₌ B A d′ d typeB typeA (≅ₜ-sym A≡B) [B] [A] (symEq [A] [B] [A≡B])
symEqTerm (ℕᵣ D) (ℕₜ₌ k k′ d d′ t≡u prop) =
  ℕₜ₌ k′ k d′ d (≅ₜ-sym t≡u) (symNatural-prop prop)
symEqTerm (Emptyᵣ D) (Emptyₜ₌ prop) = Emptyₜ₌ (symEmpty-prop prop)
symEqTerm {r = !} (ne′ K D neK K≡K) (neₜ₌ k m d d′ nf) =
  neₜ₌ m k d′ d (symNeutralTerm nf)
symEqTerm {r = %} (ne′ K D neK K≡K) (neₜ₌ d d′) = neₜ₌ d′ d
symEqTerm {r = !} (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
          (Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g]) =
  Πₜ₌ g f d′ d funcG funcF (≅ₜ-sym f≡g) [g] [f]
      (λ ρ ⊢Δ [a] → symEqTerm ([G] ρ ⊢Δ [a]) ([f≡g] ρ ⊢Δ [a]))
symEqTerm {r = %} (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
          (d , d′) = d′ , d
symEqTerm {r = %} (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
          (d , d′) = d′ , d
symEqTerm (emb 0<1 x) t≡u = symEqTerm x t≡u
