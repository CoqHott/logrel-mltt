{-# OPTIONS --without-K  #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Reduction {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties.Reflexivity
open import Definition.LogicalRelation.Properties.Universe
open import Definition.LogicalRelation.Properties.Escape

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Weak head expansion of reducible types.
redSubst* : ∀ {A B s l Γ}
          → Γ ⊢ A ⇒* B ⦂ s
          → Γ ⊩⟨ l ⟩ B ⦂ s
          → ∃ λ ([A] : Γ ⊩⟨ l ⟩ A ⦂ s)
          → Γ ⊩⟨ l ⟩ A ≡ B ⦂ s / [A]
redSubst* D (Uᵣ′ sU l′ l< ⊢Γ) rewrite redU* D =
  Uᵣ′ sU l′ l< ⊢Γ , PE.refl
redSubst* D (ℕᵣ [ ⊢B , ⊢ℕ , D′ ]) =
  let ⊢A = redFirst* D
  in  ℕᵣ ([ ⊢A , ⊢ℕ , D ⇨* D′ ]) , D′
redSubst* D (Emptyᵣ [ ⊢B , ⊢Empty , D′ ]) =
  let ⊢A = redFirst* D
  in  Emptyᵣ ([ ⊢A , ⊢Empty , D ⇨* D′ ]) , D′
redSubst* D (ne′ K [ ⊢B , ⊢K , D′ ] neK K≡K) =
  let ⊢A = redFirst* D
  in  (ne′ K [ ⊢A , ⊢K , D ⇨* D′ ] neK K≡K)
  ,   (ne₌ _ [ ⊢B , ⊢K , D′ ] neK K≡K)
redSubst* D (Πᵣ′ sF F G [ ⊢B , ⊢ΠFG , D′ ] ⊢F ⊢G A≡A [F] [G] G-ext) =
  let ⊢A = redFirst* D
  in  (Πᵣ′ sF F G [ ⊢A , ⊢ΠFG , D ⇨* D′ ] ⊢F ⊢G A≡A [F] [G] G-ext)
  ,   (Π₌ _ _ D′ A≡A (λ ρ ⊢Δ → reflEq ([F] ρ ⊢Δ))
        (λ ρ ⊢Δ [a] → reflEq ([G] ρ ⊢Δ [a])))
redSubst* D (cstrᵣ′ K KcodU a [ ⊢B , ⊢cstr , D' ] ⊢a A≡A [domK] [a] [Yi]) =
  let ⊢A = redFirst* D
  in (cstrᵣ′ K KcodU a [ ⊢A , ⊢cstr , D ⇨* D' ] ⊢a A≡A [domK] [a] [Yi]),
     (cstr₌ a [ ⊢B , ⊢cstr , D' ] A≡A (reflEqTerm [domK] [a]))
redSubst* D (Boxᵣ′ F sF [ ⊢B , ⊢Box , D' ] ⊢F A≡A [F]) =
  let ⊢A = redFirst* D
  in Boxᵣ′ F sF [ ⊢A , ⊢Box , D ⇨* D' ] ⊢F A≡A [F] ,
     Box₌ F [ ⊢B , ⊢Box , D' ] A≡A (reflEq [F])
redSubst* D (emb 0<1 x) with redSubst* D x
redSubst* D (emb 0<1 x) | y , y₁ = emb 0<1 y , y₁

-- Weak head expansion of reducible terms.
redSubst*Term : ∀ {A t u s l Γ}
              → Γ ⊢ t ⇒* u ∷ A ⦂ s
              → ([A] : Γ ⊩⟨ l ⟩ A ⦂ s)
              → Γ ⊩⟨ l ⟩ u ∷ A ⦂ s / [A]
              → Γ ⊩⟨ l ⟩ t ∷ A ⦂ s / [A]
              × Γ ⊩⟨ l ⟩ t ≡ u ∷ A ⦂ s / [A]
redSubst*Term t⇒u (Uᵣ′ sU .⁰ 0<1 ⊢Γ) (Uₜ A [ ⊢t , ⊢u , d ] typeA A≡A [u]) =
  let [d]  = [ ⊢t , ⊢u , d ]
      [d′] = [ redFirst*Term t⇒u , ⊢u , t⇒u ⇨∷* d ]
      q = redSubst* (univ* t⇒u) (univEq (Uᵣ′ sU ⁰ 0<1 ⊢Γ) (Uₜ A [d] typeA A≡A [u]))
  in Uₜ A [d′] typeA A≡A (proj₁ q)
  ,  Uₜ₌ A A [d′] [d] typeA typeA A≡A (proj₁ q) [u] (proj₂ q)
redSubst*Term t⇒u (ℕᵣ D) (ℕₜ n [ ⊢u , ⊢n , d ] n≡n prop) =
  let A≡ℕ  = subset* (red D)
      ⊢t   = conv (redFirst*Term t⇒u) A≡ℕ
      t⇒u′ = conv* t⇒u A≡ℕ
  in  ℕₜ n [ ⊢t , ⊢n , t⇒u′ ⇨∷* d ] n≡n prop
  ,   ℕₜ₌ n n [ ⊢t , ⊢n , t⇒u′ ⇨∷* d ] [ ⊢u , ⊢n , d ]
          n≡n (reflNatural-prop prop)
redSubst*Term t⇒u (Emptyᵣ D) (Emptyₜ n [ ⊢u , ⊢n , d ] n≡n prop) =
  let A≡Empty  = subset* (red D)
      ⊢t   = conv (redFirst*Term t⇒u) A≡Empty
      t⇒u′ = conv* t⇒u A≡Empty
  in  Emptyₜ n [ ⊢t , ⊢n , t⇒u′ ⇨∷* d ] n≡n prop
  ,   Emptyₜ₌ n n [ ⊢t , ⊢n , t⇒u′ ⇨∷* d ] [ ⊢u , ⊢n , d ]
          n≡n (reflEmpty-prop prop)
redSubst*Term t⇒u (ne′ K D neK K≡K) (neₜ k [ ⊢t , ⊢u , d ] (neNfₜ neK₁ ⊢k k≡k)) =
  let A≡K  = subset* (red D)
      [d]  = [ ⊢t , ⊢u , d ]
      [d′] = [ conv (redFirst*Term t⇒u) A≡K , ⊢u , conv* t⇒u A≡K ⇨∷* d ]
  in  neₜ k [d′] (neNfₜ neK₁ ⊢k k≡k) , neₜ₌ k k [d′] [d] (neNfₜ₌ neK₁ neK₁ k≡k)
redSubst*Term {A} {t} {u} {l} {Γ} t⇒u (Πᵣ′ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                  (Πₜ f [ ⊢t , ⊢u , d ] funcF f≡f [f] [f]₁) =
  let A≡ΠFG = subset* (red D)
      t⇒u′  = conv* t⇒u A≡ΠFG
      [d]  = [ ⊢t , ⊢u , d ]
      [d′] = [ conv (redFirst*Term t⇒u) A≡ΠFG , ⊢u , conv* t⇒u A≡ΠFG ⇨∷* d ]
  in  Πₜ f [d′] funcF f≡f [f] [f]₁
  ,   Πₜ₌ f f [d′] [d] funcF funcF f≡f
          (Πₜ f [d′] funcF f≡f [f] [f]₁)
          (Πₜ f [d] funcF f≡f [f] [f]₁)
          (λ [ρ] ⊢Δ [a] → reflEqTerm ([G] [ρ] ⊢Δ [a]) ([f]₁ [ρ] ⊢Δ [a]))
redSubst*Term t⇒u (cstrᵣ′ K KcodU a D ⊢a A≡A [domK] [a] [Yi]) (cstrₜ k [ ⊢t , ⊢u , d ] k≡k [k]) =
  let A≡cstr = subset* (red D)
      t⇒u'   = conv* t⇒u A≡cstr
      [d]  = [ ⊢t , ⊢u , d ]
      [d'] = [ conv (redFirst*Term t⇒u) A≡cstr , ⊢u , conv* t⇒u A≡cstr ⇨∷* d ]
  in cstrₜ k [d'] k≡k [k]
  ,  cstrₜ₌ k k [d'] [d] k≡k
            (cstrₜ k [d'] k≡k [k]) (cstrₜ k [d] k≡k [k])
            (reflCstr-prop (λ ki kiK t₁ x → reflEqTerm ([Yi] ki kiK) x) [k])
redSubst*Term t⇒u (Boxᵣ′ F sF D ⊢F A≡A [F]) (boxₜ b [ ⊢t , ⊢u , d ] b≡b [b]) =
  let A≡Box = subset* (red D)
      t⇒u' = conv* t⇒u A≡Box
      [d]  = [ ⊢t , ⊢u , d ]
      [d'] = [ conv (redFirst*Term t⇒u) A≡Box , ⊢u , conv* t⇒u A≡Box ⇨∷* d ]
  in boxₜ b [d'] b≡b [b] ,
     boxₜ₌ b b [d'] [d] b≡b
           (boxₜ b [d'] b≡b [b]) (boxₜ b [d] b≡b [b])
           (reflBox-prop (λ x d → reflEqTerm [F] d) [b])
redSubst*Term t⇒u (emb 0<1 x) [u] = redSubst*Term t⇒u x [u]

-- Weak head expansion of reducible types with single reduction step.
redSubst : ∀ {A B s l Γ}
         → Γ ⊢ A ⇒ B ⦂ s
         → Γ ⊩⟨ l ⟩ B ⦂ s
         → ∃ λ ([A] : Γ ⊩⟨ l ⟩ A ⦂ s)
         → Γ ⊩⟨ l ⟩ A ≡ B ⦂ s / [A]
redSubst A⇒B [B] = redSubst* (A⇒B ⇨ id (escape [B])) [B]

-- Weak head expansion of reducible terms with single reduction step.
redSubstTerm : ∀ {A t u s l Γ}
             → Γ ⊢ t ⇒ u ∷ A ⦂ s
             → ([A] : Γ ⊩⟨ l ⟩ A ⦂ s)
             → Γ ⊩⟨ l ⟩ u ∷ A ⦂ s / [A]
             → Γ ⊩⟨ l ⟩ t ∷ A ⦂ s / [A]
             × Γ ⊩⟨ l ⟩ t ≡ u ∷ A ⦂ s / [A]
redSubstTerm t⇒u [A] [u] = redSubst*Term (t⇒u ⇨ id (escapeTerm [A] [u])) [A] [u]
