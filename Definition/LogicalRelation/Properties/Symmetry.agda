{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Symmetry {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening hiding (wk)
open import Definition.Typed.Properties
open import Definition.Typed.EqualityRelation
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties.Escape
open import Definition.LogicalRelation.Properties.Conversion

open import Tools.Product
open import Tools.Empty
import Tools.PropositionalEquality as PE

import Data.Fin as Fin
import Data.Nat as Nat


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
  symEqT {Γ = Γ} {r = r} (Πᵥ (Πᵣ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                     (Πᵣ rF₁ lF₁ lG₁ _ _ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
         (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
    let ΠF₁G₁≡ΠF′G′   = whrDet* (red D₁ , Πₙ) (D′ , Πₙ)
        F₁≡F′ , rF₁≡rF′ , lF₁≡lF′ , G₁≡G′ , lG₁≡lG′ = Π-PE-injectivity ΠF₁G₁≡ΠF′G′
        [F₁≡F] : ∀ {Δ} {ρ} [ρ] ⊢Δ → _
        [F₁≡F] {Δ} {ρ} [ρ] ⊢Δ =
          let ρF′≡ρF₁ ρ = PE.cong (wk ρ) (PE.sym F₁≡F′)
              [ρF′] {ρ} [ρ] ⊢Δ = PE.subst (λ x → Δ ⊩⟨ _ ⟩ wk ρ x ^ _) F₁≡F′ ([F]₁ [ρ] ⊢Δ)
          in  irrelevanceEq′ {Δ} (ρF′≡ρF₁ ρ) PE.refl PE.refl
                             ([ρF′] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ)
                             (symEq′ (PE.sym rF₁≡rF′) (PE.cong ι (PE.sym lF₁≡lF′)) ([F] [ρ] ⊢Δ) ([ρF′] [ρ] ⊢Δ)
                                    ([F≡F′] [ρ] ⊢Δ))
    in  Π₌ _ _ (red (PE.subst₃ _ (PE.sym rF₁≡rF′) (PE.sym lF₁≡lF′) (PE.sym lG₁≡lG′) D))
           (PE.subst₃ _ (PE.sym rF₁≡rF′) (PE.sym lF₁≡lF′) (PE.sym lG₁≡lG′) (≅-sym (PE.subst (λ x → Γ ⊢ Π F ^ rF ° lF ▹ G ° lG ≅ x ^ r) (PE.sym ΠF₁G₁≡ΠF′G′) A≡B)))
           [F₁≡F]
           (λ {ρ} [ρ] ⊢Δ [a] →
               let ρG′a≡ρG₁′a = PE.cong (λ x → wk (lift ρ) x [ _ ]) (PE.sym G₁≡G′)
                   [ρG′a] = PE.subst (λ x → _ ⊩⟨ _ ⟩ wk (lift ρ) x [ _ ] ^ _) G₁≡G′
                                     ([G]₁ [ρ] ⊢Δ [a])
                   [a]₁ = convTerm₁′ rF₁≡rF′ (PE.cong ι lF₁≡lF′) ([F]₁ [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) ([F₁≡F] [ρ] ⊢Δ) [a]
               in  irrelevanceEq′ ρG′a≡ρG₁′a PE.refl PE.refl
                                  [ρG′a]
                                  ([G]₁ [ρ] ⊢Δ [a]) (symEq′ PE.refl (PE.sym (PE.cong ι lG₁≡lG′)) ([G] [ρ] ⊢Δ [a]₁) [ρG′a] ([G≡G′] [ρ] ⊢Δ [a]₁)))
  symEqT {Γ = Γ} {r = r} (∃ᵥ (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                     (∃ᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁))
         (∃₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
    let ∃F₁G₁≡∃F′G′   = whrDet* (red D₁ , ∃ₙ) (D′ , ∃ₙ)
        F₁≡F′ , G₁≡G′ = ∃-PE-injectivity ∃F₁G₁≡∃F′G′
        [F₁≡F] : ∀ {Δ} {ρ} [ρ] ⊢Δ → _
        [F₁≡F] {Δ} {ρ} [ρ] ⊢Δ =
          let ρF′≡ρF₁ ρ = PE.cong (wk ρ) (PE.sym F₁≡F′)
              [ρF′] {ρ} [ρ] ⊢Δ = PE.subst (λ x → Δ ⊩⟨ _ ⟩ wk ρ x ^ _) F₁≡F′ ([F]₁ [ρ] ⊢Δ)
          in  irrelevanceEq′ {Δ} (ρF′≡ρF₁ ρ) PE.refl PE.refl
                             ([ρF′] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ)
                             (symEq′ PE.refl PE.refl ([F] [ρ] ⊢Δ) ([ρF′] [ρ] ⊢Δ)
                                    ([F≡F′] [ρ] ⊢Δ))
    in  ∃₌ _ _ (red D) (≅-sym (PE.subst (λ x → Γ ⊢ ∃ F ▹ G ≅ x ^ r) (PE.sym ∃F₁G₁≡∃F′G′) A≡B))
          [F₁≡F]
          (λ {ρ} [ρ] ⊢Δ [a] →
               let ρG′a≡ρG₁′a = PE.cong (λ x → wk (lift ρ) x [ _ ]) (PE.sym G₁≡G′)
                   [ρG′a] = PE.subst (λ x → _ ⊩⟨ _ ⟩ wk (lift ρ) x [ _ ] ^ _) G₁≡G′
                                     ([G]₁ [ρ] ⊢Δ [a])
                   [a]₁ = convTerm₁′ PE.refl PE.refl ([F]₁ [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) ([F₁≡F] [ρ] ⊢Δ) [a]
               in  irrelevanceEq′ ρG′a≡ρG₁′a PE.refl PE.refl
                                  [ρG′a]
                                  ([G]₁ [ρ] ⊢Δ [a])
                                  (symEq ([G] [ρ] ⊢Δ [a]₁) [ρG′a]
                                         ([G≡G′] [ρ] ⊢Δ [a]₁)))
  symEqT (Uᵥ (Uᵣ r l l< el d) (Uᵣ r' l' l<' PE.refl d')) A≡B =
    let U≡U   = whrDet* (A≡B , Uₙ) (red d' , Uₙ)
        r≡r , l≡l = Univ-PE-injectivity (PE.sym U≡U)
    in PE.subst _ (PE.sym l≡l) (PE.subst _ (PE.sym r≡r) (red d))
  symEqT (emb⁰¹ X) A≡B = symEqT X A≡B
  symEqT (emb¹⁰ X) A≡B = symEqT X A≡B
  symEqT (emb¹∞ X) A≡B = symEqT X A≡B
  symEqT (emb∞¹ X) A≡B = symEqT X A≡B

  -- Symmetry of type equality.
  symEq : ∀ {Γ A B r l l′} ([A] : Γ ⊩⟨ l ⟩ A ^ r) ([B] : Γ ⊩⟨ l′ ⟩ B ^ r)
        → Γ ⊩⟨ l ⟩ A ≡ B ^ r / [A]
        → Γ ⊩⟨ l′ ⟩ B ≡ A ^ r / [B]
  symEq [A] [B] A≡B = symEqT (goodCases [A] [B] A≡B) A≡B

  -- same but with PE
  symEq′ : ∀ {Γ A B r r' l l′ ll ll'} (eq : r PE.≡ r') (eq' : ll PE.≡ ll')
             ([A] : Γ ⊩⟨ l ⟩ A ^ [ r , ll ]) ([B] : Γ ⊩⟨ l′ ⟩ B ^ [ r' , ll' ])
        → Γ ⊩⟨ l ⟩ A ≡ B ^ [ r , ll ] / [A]
        → Γ ⊩⟨ l′ ⟩ B ≡ A ^ [ r' , ll' ] / [B]
  symEq′ PE.refl PE.refl [A] [B] A≡B = symEq [A] [B] A≡B

symNeutralTerm : ∀ {t u A r Γ}
               → Γ ⊩neNf t ≡ u ∷ A ^ r
               → Γ ⊩neNf u ≡ t ∷ A ^ r
symNeutralTerm {r = [ ! , ll ]} (neNfₜ₌ neK neM k≡m) = neNfₜ₌ neM neK (~-sym k≡m)
symNeutralTerm {r = [ % , ll ]} (neNfₜ₌ neK neM k≡m) = neNfₜ₌ neM neK (~-sym k≡m)

symNatural-prop : ∀ {Γ k k′}
                → [Natural]-prop Γ k k′
                → [Natural]-prop Γ k′ k
symNatural-prop (sucᵣ (ℕₜ₌ k k′ d d′ t≡u prop)) =
  sucᵣ (ℕₜ₌ k′ k d′ d (≅ₜ-sym t≡u) (symNatural-prop prop))
symNatural-prop zeroᵣ = zeroᵣ
symNatural-prop (ne prop) = ne (symNeutralTerm prop)

symEmpty-prop : ∀ {Γ k k′ l}
                → [Empty]-prop Γ k k′ l
                → [Empty]-prop Γ k′ k l
symEmpty-prop (ne t u ) = ne u t


symEqTerm⁰ : ∀ {Γ A t u r} ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ r)
          → Γ ⊩⟨ ι ⁰ ⟩ t ≡ u ∷ A ^ r / [A]
          → Γ ⊩⟨ ι ⁰ ⟩ u ≡ t ∷ A ^ r / [A]
symEqTerm⁰ (ℕᵣ D) (ℕₜ₌ k k′ d d′ t≡u prop) =
  ℕₜ₌ k′ k d′ d (≅ₜ-sym t≡u) (symNatural-prop prop)
symEqTerm⁰ (Emptyᵣ D) (Emptyₜ₌ prop) = Emptyₜ₌ (symEmpty-prop prop)
symEqTerm⁰ {r = [ ! , ll ]} (ne′ K D neK K≡K) (neₜ₌ k m d d′ nf) =
  neₜ₌ m k d′ d (symNeutralTerm nf)
symEqTerm⁰ {r = [ % , ll ]} (ne′ K D neK K≡K) (neₜ₌ d d′) = neₜ₌ d′ d
symEqTerm⁰ {r = [ ! , ll ]} (Πᵣ′ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
          (Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g]) =
  Πₜ₌ g f d′ d funcG funcF (≅ₜ-sym f≡g) [g] [f]
      (λ ρ ⊢Δ [a] → symEqTerm⁰ ([G] ρ ⊢Δ [a]) ([f≡g] ρ ⊢Δ [a]))
symEqTerm⁰ {r = [ % , ll ]} (Πᵣ′ rF lF _ _ F lG G D ⊢F ⊢G A≡A [F] [G] G-ext)
          (d , d′) = d′ , d
symEqTerm⁰ {r = [ % , ll ]} (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
          (d , d′) = d′ , d


symEqTerm¹ : ∀ {Γ A t u r} ([A] : Γ ⊩⟨ ι ¹ ⟩ A ^ r)
          → Γ ⊩⟨ ι ¹ ⟩ t ≡ u ∷ A ^ r / [A]
          → Γ ⊩⟨ ι ¹ ⟩ u ≡ t ∷ A ^ r / [A]
symEqTerm¹ {Γ} {A} {t} {u} (Uᵣ (Uᵣ r ⁰ l< el D)) (Uₜ₌ [A] [B] A≡B [A≡B]) =
  let
    [B≡A] = λ {ρ} {Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) ⊢Δ →
      symEq (LogRel._⊩¹U_∷_^_/_.[t] [A] [ρ] ⊢Δ) (LogRel._⊩¹U_∷_^_/_.[t] [B] [ρ] ⊢Δ) ([A≡B] [ρ] ⊢Δ)
    u_to_t : ∀ {ρ Δ a} → ([ρ] : ρ ∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ)
      → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ u ^ [ r , ι ⁰ ] / (LogRel._⊩¹U_∷_^_/_.[t] [B] [ρ] ⊢Δ))
      → Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ t ^ [ r , ι ⁰ ] / (LogRel._⊩¹U_∷_^_/_.[t] [A] [ρ] ⊢Δ)
    u_to_t = λ [ρ] ⊢Δ [a] → convTerm₂ (LogRel._⊩¹U_∷_^_/_.[t] [A] [ρ] ⊢Δ) (LogRel._⊩¹U_∷_^_/_.[t] [B] [ρ] ⊢Δ) ([A≡B] [ρ] ⊢Δ) [a]
  in
  Uₜ₌ [B] [A] (≅ₜ-sym A≡B) [B≡A] 
symEqTerm¹ (ℕᵣ D) (ℕₜ₌ k k′ d d′ t≡u prop) =
  ℕₜ₌ k′ k d′ d (≅ₜ-sym t≡u) (symNatural-prop prop)
symEqTerm¹ (Emptyᵣ D) (Emptyₜ₌ prop) = Emptyₜ₌ (symEmpty-prop prop)
symEqTerm¹ {r = [ ! , ll ]} (ne′ K D neK K≡K) (neₜ₌ k m d d′ nf) =
  neₜ₌ m k d′ d (symNeutralTerm nf)
symEqTerm¹ {r = [ % , ll ]} (ne′ K D neK K≡K) (neₜ₌ d d′) = neₜ₌ d′ d
symEqTerm¹ {r = [ ! , ll ]} (Πᵣ′ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
          (Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g]) =
  Πₜ₌ g f d′ d funcG funcF (≅ₜ-sym f≡g) [g] [f]
      (λ ρ ⊢Δ [a] → symEqTerm¹ ([G] ρ ⊢Δ [a]) ([f≡g] ρ ⊢Δ [a]))
symEqTerm¹ {r = [ % , ll ]} (Πᵣ′ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
          (d , d′) = d′ , d
symEqTerm¹ {r = [ % , ll ]} (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
          (d , d′) = d′ , d
symEqTerm¹ (emb <l x) t≡u = symEqTerm⁰ x t≡u

-- Symmetry of term equality.
symEqTerm∞ : ∀ {Γ A t u r} ([A] : Γ ⊩⟨ ∞ ⟩ A ^ r)
          → Γ ⊩⟨ ∞ ⟩ t ≡ u ∷ A ^ r / [A]
          → Γ ⊩⟨ ∞ ⟩ u ≡ t ∷ A ^ r / [A]
symEqTerm∞ {Γ} {A} {t} {u} (Uᵣ (Uᵣ r ⁰ l< el D)) (Uₜ₌ [A] [B] A≡B [A≡B]) =
  let
    [B≡A] = λ {ρ} {Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) ⊢Δ →
      symEq (LogRel._⊩¹U_∷_^_/_.[t] [A] [ρ] ⊢Δ) (LogRel._⊩¹U_∷_^_/_.[t] [B] [ρ] ⊢Δ) ([A≡B] [ρ] ⊢Δ)
  in
  Uₜ₌ [B] [A] (≅ₜ-sym A≡B) [B≡A] 
symEqTerm∞ {Γ} {A} {t} {u} (Uᵣ (Uᵣ r ¹ l< el D)) (Uₜ₌ [A] [B] A≡B [A≡B]) =
  let
    [B≡A] = λ {ρ} {Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) ⊢Δ →
      symEq (LogRel._⊩¹U_∷_^_/_.[t] [A] [ρ] ⊢Δ) (LogRel._⊩¹U_∷_^_/_.[t] [B] [ρ] ⊢Δ) ([A≡B] [ρ] ⊢Δ)
  in
  Uₜ₌ [B] [A] (≅ₜ-sym A≡B) [B≡A]
symEqTerm∞ (ℕᵣ D) (ℕₜ₌ k k′ d d′ t≡u prop) =
  ℕₜ₌ k′ k d′ d (≅ₜ-sym t≡u) (symNatural-prop prop)
symEqTerm∞ (Emptyᵣ D) (Emptyₜ₌ prop) = Emptyₜ₌ (symEmpty-prop prop)
symEqTerm∞ {r = [ ! , ll ]} (ne′ K D neK K≡K) (neₜ₌ k m d d′ nf) =
  neₜ₌ m k d′ d (symNeutralTerm nf)
symEqTerm∞ {r = [ % , ll ]} (ne′ K D neK K≡K) (neₜ₌ d d′) = neₜ₌ d′ d
symEqTerm∞ {r = [ ! , ll ]} (Πᵣ′ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
          (Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g]) =
  Πₜ₌ g f d′ d funcG funcF (≅ₜ-sym f≡g) [g] [f]
      (λ ρ ⊢Δ [a] → symEqTerm∞ ([G] ρ ⊢Δ [a]) ([f≡g] ρ ⊢Δ [a]))
symEqTerm∞ {r = [ % , ll ]} (Πᵣ′ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
          (d , d′) = d′ , d
symEqTerm∞ {r = [ % , ll ]} (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
          (d , d′) = d′ , d
symEqTerm∞ (emb <l x) t≡u = symEqTerm¹ x t≡u

symEqTerm : ∀ {l Γ A t u r} ([A] : Γ ⊩⟨ l ⟩ A ^ r)
          → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ r / [A]
          → Γ ⊩⟨ l ⟩ u ≡ t ∷ A ^ r / [A]
symEqTerm {l = ι ⁰} = symEqTerm⁰
symEqTerm {l = ι ¹} = symEqTerm¹
symEqTerm {l = ∞} = symEqTerm∞
