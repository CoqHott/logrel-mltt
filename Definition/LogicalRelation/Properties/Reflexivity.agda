{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Reflexivity {{eqrel : EqRelSet}} where

open import Definition.Untyped
open import Definition.Typed
open import Definition.LogicalRelation

open import Tools.Product
import Tools.PropositionalEquality as PE

import Data.Fin as Fin
import Data.Nat as Nat

-- Reflexivity of reducible types.
reflEq : ∀ {l Γ A r} ([A] : Γ ⊩⟨ l ⟩ A ^ r) → Γ ⊩⟨ l ⟩ A ≡ A ^ r / [A]
reflEq (Uᵣ′ _ _ _ l< D) = red D
reflEq (ℕᵣ D) = red D
reflEq (Emptyᵣ D) = red D
reflEq (ne′ K [[ ⊢A , ⊢B , D ]] neK K≡K) =
  ne₌ _ [[ ⊢A , ⊢B , D ]] neK K≡K
reflEq (Πᵣ′ rF F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext) =
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

reflEmpty-prop : ∀ {Γ n}
                 → Empty-prop Γ n
                 → [Empty]-prop Γ n n
reflEmpty-prop (ne x) = ne x x

-- Reflexivity of reducible terms.
reflEqTerm : ∀ {l Γ A t r} ([A] : Γ ⊩⟨ l ⟩ A ^ r)
           → Γ ⊩⟨ l ⟩ t ∷ A ^ r / [A]
           → Γ ⊩⟨ l ⟩ t ≡ t ∷ A ^ r / [A]
reflEqTerm {∞} (Uᵣ′ _ _ ⁰ <l D) (Uₜ A d typeA A≡A [A] IdA castA) = Uₜ₌ A A d d typeA typeA A≡A [A] [A] (reflEq [A]) 
reflEqTerm {∞} (Uᵣ′ _ _ ¹ <l D) (Uₜ A d typeA A≡A [A] IdA castA) = Uₜ₌ A A d d typeA typeA A≡A [A] [A] (reflEq [A]) 
reflEqTerm {ι ¹} (Uᵣ′ _ _ ⁰ <l D) (Uₜ A d typeA A≡A [A] IdA castA) = Uₜ₌ A A d d typeA typeA A≡A [A] [A] (reflEq [A]) 
reflEqTerm {ι ¹} (Uᵣ′ _ _ ¹ (Nat.s≤s ()) _) (Uₜ A d typeA A≡A [A] IdA castA)
reflEqTerm (ℕᵣ D) (ℕₜ n [[ ⊢t , ⊢u , d ]] t≡t prop) =
  ℕₜ₌ n n [[ ⊢t , ⊢u , d ]] [[ ⊢t , ⊢u , d ]] t≡t
      (reflNatural-prop prop)
reflEqTerm (Emptyᵣ D) (Emptyₜ (ne x)) = Emptyₜ₌ (ne x x)
reflEqTerm {r = [ ! , l ]} (ne′ K D neK K≡K) (neₜ k d (neNfₜ neK₁ ⊢k k≡k)) =
  neₜ₌ k k d d (neNfₜ₌ neK₁ neK₁ k≡k)
reflEqTerm {r = [ % , l ]} (ne′ K D neK K≡K) (neₜ d) = neₜ₌ d d
reflEqTerm {r = [ ! , l ]} (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Πₜ f d funcF f≡f [f] [f]₁) =
  Πₜ₌ f f d d funcF funcF f≡f
      (Πₜ f d funcF f≡f [f] [f]₁)
      (Πₜ f d funcF f≡f [f] [f]₁)
      (λ ρ ⊢Δ [a] → [f] ρ ⊢Δ [a] [a] (reflEqTerm ([F] ρ ⊢Δ) [a]))
reflEqTerm {r = [ % , l ]} (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) X = X , X
reflEqTerm (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) X = X , X
reflEqTerm {ι ¹} (emb {l′ = ι ⁰} (Nat.s≤s X) [A]) = reflEqTerm [A]
reflEqTerm {∞} (emb {l′ = ι ⁰} (Nat.s≤s X) [A]) = reflEqTerm [A]
reflEqTerm {∞} (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) [A]) = reflEqTerm [A]
reflEqTerm {∞} (emb {l′ = ∞} (Nat.s≤s (Nat.s≤s ())) [A]) 
