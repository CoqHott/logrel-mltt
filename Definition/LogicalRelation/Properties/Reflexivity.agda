{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Reflexivity {{eqrel : EqRelSet}} where

open import Definition.Untyped
open import Definition.Typed
open import Definition.LogicalRelation

open import Tools.Product
open import Tools.Empty
import Tools.PropositionalEquality as PE


import Data.Fin as Fin
import Data.Nat as Nat

-- Reflexivity of reducible types.
reflEq : ∀ {l Γ A r} ([A] : Γ ⊩⟨ l ⟩ A ^ r) → Γ ⊩⟨ l ⟩ A ≡ A ^ r / [A]
reflEq (Uᵣ′ _ _ _ _ l< PE.refl D) = red D
reflEq (ℕᵣ D) = red D
reflEq (Emptyᵣ D) = red D
reflEq (ne′ K [[ ⊢A , ⊢B , D ]] neK K≡K) =
  ne₌ _ [[ ⊢A , ⊢B , D ]] neK K≡K
reflEq (Πᵣ′ rF lF lG F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext) =
  Π₌ _ _ D A≡A
     (λ ρ ⊢Δ → reflEq ([F] ρ ⊢Δ))
     (λ ρ ⊢Δ [a] → reflEq ([G] ρ ⊢Δ [a]))
reflEq (∃ᵣ′ F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext) =
  ∃₌ _ _ D A≡A
    (λ ρ ⊢Δ → reflEq ([F] ρ ⊢Δ))
    (λ ρ ⊢Δ [a] → reflEq ([G] ρ ⊢Δ [a]))
reflEq {ι ¹} (emb {l′ = ι ⁰} (Nat.s≤s X) [A]) = reflEq [A]
reflEq {∞} (emb {l′ = ι ⁰} (Nat.s≤s X) [A]) = reflEq [A]
reflEq {∞} (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) [A]) = reflEq [A]
reflEq {∞} (emb {l′ = ∞} (Nat.s≤s (Nat.s≤s ())) [A])

reflNatural-prop : ∀ {Γ n}
                 → Natural-prop Γ n
                 → [Natural]-prop Γ n n
reflNatural-prop (sucᵣ (ℕₜ n d t≡t prop)) =
  sucᵣ (ℕₜ₌ n n d d t≡t
            (reflNatural-prop prop))
reflNatural-prop zeroᵣ = zeroᵣ
reflNatural-prop (ne (neNfₜ neK ⊢k k≡k)) = ne (neNfₜ₌ neK neK k≡k)

reflEmpty-prop : ∀ {Γ n l}
                 → Empty-prop Γ n l
                 → [Empty]-prop Γ n n l
reflEmpty-prop (ne x) = ne x x

-- Reflexivity of reducible terms.
-- We proceed in a layered way because agda does not understand our recursions are well founded
reflEqTerm⁰ : ∀ {Γ A t r} ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ r)
           → Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ r / [A]
           → Γ ⊩⟨ ι ⁰ ⟩ t ≡ t ∷ A ^ r / [A]
reflEqTerm⁰ (ℕᵣ D) (ℕₜ n [[ ⊢t , ⊢u , d ]] t≡t prop) =
  ℕₜ₌ n n [[ ⊢t , ⊢u , d ]] [[ ⊢t , ⊢u , d ]] t≡t
      (reflNatural-prop prop)
reflEqTerm⁰ (Emptyᵣ D) (Emptyₜ (ne x)) = Emptyₜ₌ (ne x x)
reflEqTerm⁰ {r = [ ! , l ]} (ne′ K D neK K≡K) (neₜ k d (neNfₜ neK₁ ⊢k k≡k)) =
  neₜ₌ k k d d (neNfₜ₌ neK₁ neK₁ k≡k)
reflEqTerm⁰ {r = [ % , l ]} (ne′ K D neK K≡K) (neₜ d) = neₜ₌ d d
reflEqTerm⁰ {r = [ ! , l ]} (Πᵣ′ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Πₜ f d funcF f≡f [f] [f]₁) =
  Πₜ₌ f f d d funcF funcF f≡f
      (Πₜ f d funcF f≡f [f] [f]₁)
      (Πₜ f d funcF f≡f [f] [f]₁)
      (λ ρ ⊢Δ [a] → [f] ρ ⊢Δ [a] [a] (reflEqTerm⁰ ([F] ρ ⊢Δ) [a]))
reflEqTerm⁰ {r = [ % , l ]} (Πᵣ′ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext) X = X , X
reflEqTerm⁰ (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) X = X , X

reflEqTerm¹ : ∀ {Γ A t r} ([A] : Γ ⊩⟨ ι ¹ ⟩ A ^ r)
           → Γ ⊩⟨ ι ¹ ⟩ t ∷ A ^ r / [A]
           → Γ ⊩⟨ ι ¹ ⟩ t ≡ t ∷ A ^ r / [A]
reflEqTerm¹ (Uᵣ (Uᵣ r ⁰ (Nat.s≤s Nat.z≤n) PE.refl D)) (Uₜ A d typeA A≡A [A] [IdA] IdAExt [castA] castAExt) =
  Uₜ₌ (Uₜ A d typeA A≡A [A] [IdA] IdAExt [castA] castAExt) (Uₜ A d typeA A≡A [A] [IdA] IdAExt [castA] castAExt)
    A≡A (λ [ρ] ⊢Δ → reflEq ([A] [ρ] ⊢Δ)) (λ x [ρ] ⊢Δ [a] [b] → reflEq ([IdA] x [ρ] ⊢Δ [a] [b]))
      (λ x x₁ [ρ] ⊢Δ [B] [e] [a] → reflEqTerm⁰ [B] ([castA] x x₁ [ρ] ⊢Δ [B] [e] [a]))
reflEqTerm¹ (Uᵣ (Uᵣ r ¹ (Nat.s≤s ()) PE.refl D)) (Uₜ A d typeA A≡A [A] [IdA] IdAExt [castA] castAExt)
reflEqTerm¹ (ℕᵣ D) (ℕₜ n [[ ⊢t , ⊢u , d ]] t≡t prop) =
  ℕₜ₌ n n [[ ⊢t , ⊢u , d ]] [[ ⊢t , ⊢u , d ]] t≡t
      (reflNatural-prop prop)
reflEqTerm¹ (Emptyᵣ D) (Emptyₜ (ne x)) = Emptyₜ₌ (ne x x)
reflEqTerm¹ {r = [ ! , l ]} (ne′ K D neK K≡K) (neₜ k d (neNfₜ neK₁ ⊢k k≡k)) =
  neₜ₌ k k d d (neNfₜ₌ neK₁ neK₁ k≡k)
reflEqTerm¹ {r = [ % , l ]} (ne′ K D neK K≡K) (neₜ d) = neₜ₌ d d
reflEqTerm¹ {r = [ ! , l ]} (Πᵣ′ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Πₜ f d funcF f≡f [f] [f]₁) =
  Πₜ₌ f f d d funcF funcF f≡f
      (Πₜ f d funcF f≡f [f] [f]₁)
      (Πₜ f d funcF f≡f [f] [f]₁)
      (λ ρ ⊢Δ [a] → [f] ρ ⊢Δ [a] [a] (reflEqTerm¹ ([F] ρ ⊢Δ) [a]))
reflEqTerm¹ {r = [ % , l ]} (Πᵣ′ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext) X = X , X
reflEqTerm¹ (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) X = X , X
reflEqTerm¹ (emb {l′ = ι ⁰} (Nat.s≤s X) [A]) = reflEqTerm⁰ [A]

reflEqTerm∞ : ∀ {Γ A t r} ([A] : Γ ⊩⟨ ∞ ⟩ A ^ r)
           → Γ ⊩⟨ ∞ ⟩ t ∷ A ^ r / [A]
           → Γ ⊩⟨ ∞ ⟩ t ≡ t ∷ A ^ r / [A]
reflEqTerm∞ (Uᵣ (Uᵣ r ⁰ (Nat.s≤s Nat.z≤n) eq D)) (Uₜ A d typeA A≡A [A] [IdA] IdAExt [castA] castAExt) =
  Uₜ₌ (Uₜ A d typeA A≡A [A] [IdA] IdAExt [castA] castAExt) (Uₜ A d typeA A≡A [A] [IdA] IdAExt [castA] castAExt) A≡A (λ [ρ] ⊢Δ → reflEq ([A] [ρ] ⊢Δ)) (λ x [ρ] ⊢Δ [a] [b] → reflEq ([IdA] x [ρ] ⊢Δ [a] [b])) (λ x x₁ [ρ] ⊢Δ [B] [e] [a] → reflEqTerm⁰ [B] ([castA] x x₁ [ρ] ⊢Δ [B] [e] [a]))
reflEqTerm∞ (Uᵣ (Uᵣ r ¹ (Nat.s≤s (Nat.s≤s Nat.z≤n)) eq D)) (Uₜ A d typeA A≡A [A] [IdA] IdAExt [castA] castAExt) =
  Uₜ₌ (Uₜ A d typeA A≡A [A] [IdA] IdAExt [castA] castAExt) (Uₜ A d typeA A≡A [A] [IdA] IdAExt [castA] castAExt) A≡A (λ [ρ] ⊢Δ → reflEq ([A] [ρ] ⊢Δ)) (λ x [ρ] ⊢Δ [a] [b] → reflEq ([IdA] x [ρ] ⊢Δ [a] [b])) (λ x x₁ [ρ] ⊢Δ [B] [e] [a] → ⊥-elim (⁰≢¹ (PE.sym x)))
reflEqTerm∞ (ℕᵣ D) (ℕₜ n [[ ⊢t , ⊢u , d ]] t≡t prop) =
  ℕₜ₌ n n [[ ⊢t , ⊢u , d ]] [[ ⊢t , ⊢u , d ]] t≡t
      (reflNatural-prop prop)
reflEqTerm∞ (Emptyᵣ D) (Emptyₜ (ne x)) = Emptyₜ₌ (ne x x)
reflEqTerm∞ {r = [ ! , l ]} (ne′ K D neK K≡K) (neₜ k d (neNfₜ neK₁ ⊢k k≡k)) =
  neₜ₌ k k d d (neNfₜ₌ neK₁ neK₁ k≡k)
reflEqTerm∞ {r = [ % , l ]} (ne′ K D neK K≡K) (neₜ d) = neₜ₌ d d
reflEqTerm∞ {r = [ ! , l ]} (Πᵣ′ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Πₜ f d funcF f≡f [f] [f]₁) =
  Πₜ₌ f f d d funcF funcF f≡f
      (Πₜ f d funcF f≡f [f] [f]₁)
      (Πₜ f d funcF f≡f [f] [f]₁)
      (λ ρ ⊢Δ [a] → [f] ρ ⊢Δ [a] [a] (reflEqTerm∞ ([F] ρ ⊢Δ) [a]))
reflEqTerm∞ {r = [ % , l ]} (Πᵣ′ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext) X = X , X
reflEqTerm∞ (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) X = X , X
reflEqTerm∞ (emb {l′ = ι ⁰} (Nat.s≤s X) [A]) = reflEqTerm⁰ [A]
reflEqTerm∞ (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) [A]) = reflEqTerm¹ [A]
reflEqTerm∞ (emb {l′ = ∞} (Nat.s≤s (Nat.s≤s ())) [A])

reflEqTerm : ∀ {l Γ A t r} ([A] : Γ ⊩⟨ l ⟩ A ^ r)
           → Γ ⊩⟨ l ⟩ t ∷ A ^ r / [A]
           → Γ ⊩⟨ l ⟩ t ≡ t ∷ A ^ r / [A]
reflEqTerm {l = ι ⁰} [A] [t] = reflEqTerm⁰ [A] [t]
reflEqTerm {l = ι ¹} [A] [t] = reflEqTerm¹ [A] [t]
reflEqTerm {l = ∞} [A] [t] = reflEqTerm∞ [A] [t]
