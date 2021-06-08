{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Reduction {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.Typed.Weakening
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties.Reflexivity
open import Definition.LogicalRelation.Properties.Transitivity
open import Definition.LogicalRelation.Properties.Symmetry
open import Definition.LogicalRelation.Properties.Universe
open import Definition.LogicalRelation.Properties.Escape
open import Definition.LogicalRelation.Properties.Conversion

open import Tools.Product
open import Tools.Empty
import Tools.PropositionalEquality as PE

import Data.Fin as Fin
import Data.Nat as Nat

-- Weak head expansion of reducible types.
redSubst* : ∀ {A B r l Γ}
          → Γ ⊢ A ⇒* B ^ r
          → Γ ⊩⟨ l ⟩ B ^ r
          → ∃ λ ([A] : Γ ⊩⟨ l ⟩ A ^ r)
          → Γ ⊩⟨ l ⟩ A ≡ B ^ r / [A]
redSubst* {A = A} D (Uᵣ′ B .(next l′) rU l′ l< PE.refl [[ ⊢A , ⊢B , D' ]]) =
  let ⊢A = redFirst* D
  in  Uᵣ′ A (next l′) rU l′ l< PE.refl [[ ⊢A , ⊢B , D ⇨* D' ]] , D'
redSubst* D (ℕᵣ [[ ⊢B , ⊢ℕ , D′ ]]) =
  let ⊢A = redFirst* D
  in  ℕᵣ ([[ ⊢A , ⊢ℕ , D ⇨* D′ ]]) , D′
redSubst* D (Emptyᵣ [[ ⊢B , ⊢Empty , D′ ]]) =
  let ⊢A = redFirst* D
  in  Emptyᵣ ([[ ⊢A , ⊢Empty , D ⇨* D′ ]]) , D′
redSubst* D (ne′ K [[ ⊢B , ⊢K , D′ ]] neK K≡K) =
  let ⊢A = redFirst* D
  in  (ne′ K [[ ⊢A , ⊢K , D ⇨* D′ ]] neK K≡K)
  ,   (ne₌ _ [[ ⊢B , ⊢K , D′ ]] neK K≡K)
redSubst* D (Πᵣ′ rF lF lG lF≤ lG≤ F G [[ ⊢B , ⊢ΠFG , D′ ]] ⊢F ⊢G A≡A [F] [G] G-ext) =
  let ⊢A = redFirst* D
  in  (Πᵣ′ rF lF lG lF≤ lG≤ F G [[ ⊢A , ⊢ΠFG , D ⇨* D′ ]] ⊢F ⊢G A≡A [F] [G] G-ext)
  ,   (Π₌ _ _ D′ A≡A (λ ρ ⊢Δ → reflEq ([F] ρ ⊢Δ))
        (λ ρ ⊢Δ [a] → reflEq ([G] ρ ⊢Δ [a])))
redSubst* D (∃ᵣ′ F G [[ ⊢B , ⊢ΠFG , D′ ]] ⊢F ⊢G A≡A [F] [G] G-ext) =
  let ⊢A = redFirst* D
  in  (∃ᵣ′ F G [[ ⊢A , ⊢ΠFG , D ⇨* D′ ]] ⊢F ⊢G A≡A [F] [G] G-ext)
  ,   (∃₌ _ _ D′ A≡A (λ ρ ⊢Δ → reflEq ([F] ρ ⊢Δ))
        (λ ρ ⊢Δ [a] → reflEq ([G] ρ ⊢Δ [a])))
redSubst* {l = ι ¹} D (emb l< X) with redSubst* D X
redSubst* {l = ι ¹} D (emb l< X) | y , y₁ = emb l< y , y₁
redSubst* {l = ∞} D (emb l< X) with redSubst* D X
redSubst* {l = ∞} D (emb ∞< X) | y , y₁ = emb {l′ = ι ¹} ∞< y , y₁


redSubst*Term⁰ : ∀ {A t u ll Γ} → let l = ι ⁰ in
                Γ ⊢ t ⇒* u ∷ A ^ ll
              → ([A] : Γ ⊩⟨ l ⟩ A ^ [ ! , ll ])
              → Γ ⊩⟨ l ⟩ u ∷ A ^ [ ! , ll ] / [A]
              → Γ ⊩⟨ l ⟩ t ∷ A ^ [ ! , ll ] / [A]
              × Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ [ ! , ll ] / [A]
redSubst*Term⁰ t⇒u (ℕᵣ D) (ℕₜ n [[ ⊢u , ⊢n , d ]] n≡n prop) =
  let A≡ℕ  = subset* (red D)
      ⊢t   = conv (redFirst*Term t⇒u) A≡ℕ
      t⇒u′ = conv* t⇒u A≡ℕ
  in  ℕₜ n [[ ⊢t , ⊢n , t⇒u′ ⇨∷* d ]] n≡n prop
  ,   ℕₜ₌ n n [[ ⊢t , ⊢n , t⇒u′ ⇨∷* d ]] [[ ⊢u , ⊢n , d ]]
          n≡n (reflNatural-prop prop)
redSubst*Term⁰ t⇒u (ne′ K D neK K≡K) (neₜ k [[ ⊢t , ⊢u , d ]] (neNfₜ neK₁ ⊢k k≡k)) =
  let A≡K  = subset* (red D)
      [d]  = [[ ⊢t , ⊢u , d ]]
      [d′] = [[ conv (redFirst*Term t⇒u) A≡K , ⊢u , conv* t⇒u A≡K ⇨∷* d ]]
  in  neₜ k [d′] (neNfₜ neK₁ ⊢k k≡k) , neₜ₌ k k [d′] [d] (neNfₜ₌ neK₁ neK₁ k≡k)
redSubst*Term⁰ {A} {t} {u} {l} {Γ} t⇒u (Πᵣ′ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                  (Πₜ f [[ ⊢t , ⊢u , d ]] funcF f≡f [f] [f]₁) =
  let A≡ΠFG = subset* (red D)
      t⇒u′  = conv* t⇒u A≡ΠFG
      [d]  = [[ ⊢t , ⊢u , d ]]
      [d′] = [[ conv (redFirst*Term t⇒u) A≡ΠFG , ⊢u , conv* t⇒u A≡ΠFG ⇨∷* d ]]
  in  Πₜ f [d′] funcF f≡f [f] [f]₁
  ,   Πₜ₌ f f [d′] [d] funcF funcF f≡f
          (Πₜ f [d′] funcF f≡f [f] [f]₁)
          (Πₜ f [d] funcF f≡f [f] [f]₁)
          (λ [ρ] ⊢Δ [a] → reflEqTerm ([G] [ρ] ⊢Δ [a]) ([f]₁ [ρ] ⊢Δ [a]))

-- Weak head expansion of reducible terms.
redSubst*Term : ∀ {A t u l ll Γ}
              → Γ ⊢ t ⇒* u ∷ A ^ ll
              → ([A] : Γ ⊩⟨ l ⟩ A ^ [ ! , ll ])
              → Γ ⊩⟨ l ⟩ u ∷ A ^ [ ! , ll ] / [A]
              → Γ ⊩⟨ l ⟩ t ∷ A ^ [ ! , ll ] / [A]
              × Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ [ ! , ll ] / [A]
redSubst*Term {t = t} {l = ι ¹} {Γ = Γ} t⇒u (Uᵣ′ A .(next ⁰) rU ⁰ l< PE.refl D) (Uₜ K [[ ⊢u , ⊢K , d ]] typeA A≡A [u]) =
  let
    A≡U  = subset* (red D)
    ⊢t   = conv (redFirst*Term t⇒u) A≡U
    t⇒u′ = conv* t⇒u A≡U
    [t] = λ {ρ} {Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) ⊢Δ → proj₁ (redSubst* {l = ι ⁰} (wkRed* [ρ] ⊢Δ (univ* t⇒u′)) ([u] [ρ] ⊢Δ))
    [t≡u] = λ {ρ} {Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) ⊢Δ → proj₂ (redSubst* {l = ι ⁰} (wkRed* [ρ] ⊢Δ (univ* t⇒u′)) ([u] [ρ] ⊢Δ))
    [[t]] = Uₜ K [[ ⊢t , ⊢K , t⇒u′ ⇨∷* d ]] typeA A≡A [t]
  in
  ([[t]] , Uₜ₌ [[t]] (Uₜ K [[ ⊢u , ⊢K , d ]] typeA A≡A [u]) A≡A [t≡u])
redSubst*Term {t = t} {l = ∞} {Γ = Γ} t⇒u (Uᵣ′ A .(next ¹) rU ¹ l< PE.refl D) (Uₜ K [[ ⊢u , ⊢K , d ]] typeA A≡A [u]) =
  let
    A≡U  = subset* (red D)
    ⊢t   = conv (redFirst*Term t⇒u) A≡U
    t⇒u′ = conv* t⇒u A≡U
    [t] = λ {ρ} {Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) ⊢Δ → proj₁ (redSubst* {l = ι ¹} (wkRed* [ρ] ⊢Δ (univ* t⇒u′)) ([u] [ρ] ⊢Δ))
    [t≡u] = λ {ρ} {Δ} ([ρ] : ρ ∷ Δ ⊆ Γ) ⊢Δ → proj₂ (redSubst* {l = ι ¹} (wkRed* [ρ] ⊢Δ (univ* t⇒u′)) ([u] [ρ] ⊢Δ))
    [[t]] = Uₜ K [[ ⊢t , ⊢K , t⇒u′ ⇨∷* d ]] typeA A≡A [t]
  in
  ([[t]] , Uₜ₌ [[t]] (Uₜ K [[ ⊢u , ⊢K , d ]] typeA A≡A [u]) A≡A [t≡u])
redSubst*Term t⇒u (ℕᵣ D) (ℕₜ n [[ ⊢u , ⊢n , d ]] n≡n prop) =
  let A≡ℕ  = subset* (red D)
      ⊢t   = conv (redFirst*Term t⇒u) A≡ℕ
      t⇒u′ = conv* t⇒u A≡ℕ
  in  ℕₜ n [[ ⊢t , ⊢n , t⇒u′ ⇨∷* d ]] n≡n prop
  ,   ℕₜ₌ n n [[ ⊢t , ⊢n , t⇒u′ ⇨∷* d ]] [[ ⊢u , ⊢n , d ]]
          n≡n (reflNatural-prop prop)
redSubst*Term t⇒u (ne′ K D neK K≡K) (neₜ k [[ ⊢t , ⊢u , d ]] (neNfₜ neK₁ ⊢k k≡k)) =
  let A≡K  = subset* (red D)
      [d]  = [[ ⊢t , ⊢u , d ]]
      [d′] = [[ conv (redFirst*Term t⇒u) A≡K , ⊢u , conv* t⇒u A≡K ⇨∷* d ]]
  in  neₜ k [d′] (neNfₜ neK₁ ⊢k k≡k) , neₜ₌ k k [d′] [d] (neNfₜ₌ neK₁ neK₁ k≡k)
redSubst*Term {A} {t} {u} {l} {Γ} t⇒u (Πᵣ′ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                  (Πₜ f [[ ⊢t , ⊢u , d ]] funcF f≡f [f] [f]₁) =
  let A≡ΠFG = subset* (red D)
      t⇒u′  = conv* t⇒u A≡ΠFG
      [d]  = [[ ⊢t , ⊢u , d ]]
      [d′] = [[ conv (redFirst*Term t⇒u) A≡ΠFG , ⊢u , conv* t⇒u A≡ΠFG ⇨∷* d ]]
  in  Πₜ f [d′] funcF f≡f [f] [f]₁
  ,   Πₜ₌ f f [d′] [d] funcF funcF f≡f
          (Πₜ f [d′] funcF f≡f [f] [f]₁)
          (Πₜ f [d] funcF f≡f [f] [f]₁)
          (λ [ρ] ⊢Δ [a] → reflEqTerm ([G] [ρ] ⊢Δ [a]) ([f]₁ [ρ] ⊢Δ [a]))
redSubst*Term {l = ι ¹} D (emb l< X) [u] = redSubst*Term D X [u]
redSubst*Term {l = ∞} D (emb l< X) [u] = redSubst*Term D X [u]

-- Weak head expansion of reducible types with single reduction step.
redSubst : ∀ {A B r l Γ}
         → Γ ⊢ A ⇒ B ^ r
         → Γ ⊩⟨ l ⟩ B ^ r
         → ∃ λ ([A] : Γ ⊩⟨ l ⟩ A ^ r)
         → Γ ⊩⟨ l ⟩ A ≡ B ^ r / [A]
redSubst A⇒B [B] = redSubst* (A⇒B ⇨ id (escape [B])) [B]

-- Weak head expansion of reducible terms with single reduction step.
redSubstTerm : ∀ {A t u l ll Γ}
             → Γ ⊢ t ⇒ u ∷ A ^ ll
             → ([A] : Γ ⊩⟨ l ⟩ A ^ [ ! , ll ])
             → Γ ⊩⟨ l ⟩ u ∷ A ^ [ ! , ll ] / [A]
             → Γ ⊩⟨ l ⟩ t ∷ A ^ [ ! , ll ] / [A]
             × Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ [ ! , ll ] / [A]
redSubstTerm t⇒u [A] [u] = redSubst*Term (t⇒u ⇨ id (escapeTerm [A] [u])) [A] [u]
