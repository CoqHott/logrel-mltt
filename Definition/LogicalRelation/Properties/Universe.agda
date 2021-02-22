{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Universe {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.Typed.Properties
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Empty using (⊥; ⊥-elim)

import Data.Fin as Fin
import Data.Nat as Nat

U-Relevance-Level : ∀ {l ll Γ A} ([U] : Γ ⊩⟨ l ⟩U A ^ ll) → Relevance × Level
U-Relevance-Level (noemb (Uᵣ r l′ l< eq d)) =  r , l′
U-Relevance-Level (emb x X) = U-Relevance-Level X

toTypeInfo : Relevance × Level → TypeInfo
toTypeInfo ( r , l ) = [ r , ι l ]

-- Helper function for reducible terms of type U for specific type derivations.
univEq′ : ∀ {l ll Γ A t} ([U] : Γ ⊩⟨ l ⟩U A ^ ll) → Γ ⊩⟨ l ⟩ t ∷ A ^ [ ! , ll ] / U-intr [U] → Γ ⊩⟨ l ⟩ t ^ toTypeInfo (U-Relevance-Level [U])
univEq′ (noemb (Uᵣ r l′ l< eq d)) (Uₜ K d₁ typeK K≡K [t] [IdK] [castK]) = emb l< [t]
univEq′ {ι ¹} (emb {ι ⁰} (Nat.s≤s Nat.z≤n) X) [A] = emb (Nat.s≤s Nat.z≤n) (univEq′ X [A])
univEq′ {ι ¹} (emb {ι ¹} (Nat.s≤s ()) X) [A]
univEq′ {ι ¹} (emb {∞} (Nat.s≤s ()) X) [A]
univEq′ {∞} (emb {ι ⁰} (Nat.s≤s Nat.z≤n) X) [A] = emb (Nat.s≤s Nat.z≤n) (univEq′ X [A])
univEq′ {∞} (emb {ι ¹} (Nat.s≤s (Nat.s≤s Nat.z≤n)) X) [A] = emb {l′ =  ι ¹} (Nat.s≤s (Nat.s≤s Nat.z≤n)) (univEq′ X [A])
univEq′ {∞} (emb {∞} (Nat.s≤s (Nat.s≤s ())) X) [A]


-- Reducible terms of type U are reducible types.
univEq : ∀ {l Γ A r l′ ll′} ([U] : Γ ⊩⟨ l ⟩ Univ r l′ ^ [ ! , ll′ ] ) → Γ ⊩⟨ l ⟩ A ∷ Univ r l′ ^ [ ! , ll′ ] / [U] → Γ ⊩⟨ l ⟩ A ^ toTypeInfo (U-Relevance-Level (U-elim [U]))
univEq [U] [A] = univEq′ (U-elim [U]) (irrelevanceTerm [U] (U-intr (U-elim [U])) [A])


-- Helper function for reducible term equality of type U for specific type derivations.
univEqEq′ : ∀ {l ll l′ Γ X A B} ([U] : Γ ⊩⟨ l ⟩U X ^ ll) →
            let r = toTypeInfo (U-Relevance-Level [U])
            in
              ([A] : Γ ⊩⟨ l′ ⟩ A ^ r)
              → Γ ⊩⟨ l ⟩ A ≡ B ∷ X ^ [ ! , ll ] / U-intr [U]
              → Γ ⊩⟨ l′ ⟩ A ≡ B  ^ r / [A]
univEqEq′ (noemb (Uᵣ r l′ l< eq D)) [A]
          (Uₜ₌ A₁ B₁ d d′ typeA typeB A≡B [t] [u] [t≡u]) = irrelevanceEq (emb l< [t]) [A] [t≡u]
univEqEq′ {ι ¹} (emb {ι ⁰} (Nat.s≤s Nat.z≤n) X) [A] [A≡B] = univEqEq′ X [A] [A≡B]
univEqEq′ {ι ¹} (emb {ι ¹} (Nat.s≤s ()) X) [A] [A≡B]
univEqEq′ {ι ¹} (emb {∞} (Nat.s≤s ()) X) [A] [A≡B]
univEqEq′ {∞} (emb {ι ⁰} (Nat.s≤s Nat.z≤n) X) [A] [A≡B] = univEqEq′ X [A] [A≡B]
univEqEq′ {∞} (emb {ι ¹} (Nat.s≤s (Nat.s≤s Nat.z≤n)) X) [A] [A≡B] = univEqEq′ X [A] [A≡B]
univEqEq′ {∞} (emb {∞} (Nat.s≤s (Nat.s≤s ())) X) [A] [A≡B]

UnivNotℕ : ∀ {Γ r ll} →  Γ ⊩ℕ Univ r ll → ⊥
UnivNotℕ {ll = ⁰} [[ ⊢A , ⊢B , D ]] = U≢ℕ (whrDet* (id (univ (univ 0<1 (wf ⊢A))) , Uₙ) (D , ℕₙ))
UnivNotℕ {ll = ¹} [[ ⊢A , ⊢B , D ]] = U≢ℕ (whrDet* (id (Uⱼ (wf ⊢A)) , Uₙ) (D , ℕₙ))

UnivNotΠ : ∀ {Γ r r' l ll} →  (l LogRel.⊩¹Π logRelRec l ^ Γ) (Univ r ll) r' → ⊥
UnivNotΠ {ll = ⁰} (Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) = U≢Π (whrDet* (id (univ (univ 0<1 (wf ⊢F))) , Uₙ) (red D , Πₙ))
UnivNotΠ {ll = ¹} (Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) = U≢Π (whrDet* (id (Uⱼ (wf ⊢F)) , Uₙ) (red D , Πₙ))

U-Relevance-Level-eq : ∀ {l Γ r ll ll'} ([U] : Γ ⊩⟨ l ⟩ Univ r ll ^ [ ! , ll' ]) → U-Relevance-Level (U-elim [U]) PE.≡ (r , ll)
U-Relevance-Level-eq {ll = ⁰} (Uᵣ (Uᵣ r ⁰ l< eq d)) = ×-eq (Univ-PE-injectivity (whrDet* (red d , Uₙ) (id (univ (univ 0<1 (wf (_⊢_:⇒*:_^_.⊢A d)))) , Uₙ)))
U-Relevance-Level-eq {ll = ¹} (Uᵣ (Uᵣ r ⁰ l< eq d)) = let _ , X = (Univ-PE-injectivity (whrDet* (red d , Uₙ) (id (Uⱼ (wf (_⊢_:⇒*:_^_.⊢A d))) , Uₙ))) in ⊥-elim (⁰≢¹ X)
U-Relevance-Level-eq {ll = ¹} (Uᵣ (Uᵣ r ¹ l< eq d)) = ×-eq (Univ-PE-injectivity (whrDet* (red d , Uₙ) (id (Uⱼ (wf (_⊢_:⇒*:_^_.⊢A d))) , Uₙ)))
U-Relevance-Level-eq (ℕᵣ X) = ⊥-elim (UnivNotℕ X)
U-Relevance-Level-eq (ne′ K D neK K≡K) = ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
U-Relevance-Level-eq (Πᵣ X) = ⊥-elim (UnivNotΠ X)
U-Relevance-Level-eq {ι ¹} (emb l< (ℕᵣ X)) = ⊥-elim (UnivNotℕ X)
U-Relevance-Level-eq {ι ¹} (emb l< (ne′ K D neK K≡K)) = ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
U-Relevance-Level-eq {ι ¹} (emb l< (Πᵣ X)) = ⊥-elim (UnivNotΠ X)
U-Relevance-Level-eq {∞} (emb {l′ = ι ⁰} l< (ℕᵣ X)) = ⊥-elim (UnivNotℕ X)
U-Relevance-Level-eq {∞} (emb {l′ = ι ⁰} l< (ne′ K D neK K≡K)) = ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
U-Relevance-Level-eq {∞} (emb {l′ = ι ⁰} l< (Πᵣ X)) = ⊥-elim (UnivNotΠ X)
U-Relevance-Level-eq {∞} {ll = ⁰} (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s Nat.z≤n)) (Uᵣ (Uᵣ r ⁰ l<₁ eq d))) = ×-eq (Univ-PE-injectivity (whrDet* (red d , Uₙ) (id (univ (univ 0<1 (wf (_⊢_:⇒*:_^_.⊢A d)))) , Uₙ)))
U-Relevance-Level-eq {∞} {ll = ¹} (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s Nat.z≤n)) (Uᵣ (Uᵣ r ⁰ l<₁ eq d))) = let _ , X = (Univ-PE-injectivity (whrDet* (red d , Uₙ) (id (Uⱼ (wf (_⊢_:⇒*:_^_.⊢A d))) , Uₙ))) in ⊥-elim (⁰≢¹ X)
U-Relevance-Level-eq {∞} {ll = ¹} (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s Nat.z≤n)) (Uᵣ (Uᵣ r ¹ l<₁ eq d))) = ×-eq (Univ-PE-injectivity (whrDet* (red d , Uₙ) (id (Uⱼ (wf (_⊢_:⇒*:_^_.⊢A d))) , Uₙ)))
U-Relevance-Level-eq {∞} (emb {l′ = ι ¹} l< (ℕᵣ X)) = ⊥-elim (UnivNotℕ X)
U-Relevance-Level-eq {∞} (emb {l′ = ι ¹} l< (ne′ K D neK K≡K)) = ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
U-Relevance-Level-eq {∞} (emb {l′ = ι ¹} l< (Πᵣ x)) = ⊥-elim (UnivNotΠ x)
U-Relevance-Level-eq {∞} (emb {l′ = ι ¹} l< (emb {l′ = ι ⁰} (Nat.s≤s Nat.z≤n) (ℕᵣ x))) = ⊥-elim (UnivNotℕ x)
U-Relevance-Level-eq {∞} (emb {l′ = ι ¹} l< (emb {l′ = ι ⁰} (Nat.s≤s Nat.z≤n) (ne′ K D neK K≡K))) = ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
U-Relevance-Level-eq {∞} (emb {l′ = ι ¹} l< (emb {l′ = ι ⁰} (Nat.s≤s Nat.z≤n) (Πᵣ x))) = ⊥-elim (UnivNotΠ x)
U-Relevance-Level-eq {∞} (emb {l′ = ∞} (Nat.s≤s (Nat.s≤s ())) [A])

helper-eq : ∀ {l Γ A B r r'} {[A] : Γ ⊩⟨ l ⟩ A ^ r} (e : r PE.≡ r' ) → Γ ⊩⟨ l ⟩ A ≡ B ^ r' / (PE.subst _ e [A]) → Γ ⊩⟨ l ⟩ A ≡ B ^ r / [A]
helper-eq PE.refl X = X

-- Reducible term equality of type U is reducible type equality.
univEqEq : ∀ {l l′ Γ A B r ll} ([U] : Γ ⊩⟨ l ⟩ Univ r ll ^ [ ! , next ll ]) ([A] : Γ ⊩⟨ l′ ⟩ A ^ [ r , ι ll ])
         → Γ ⊩⟨ l ⟩ A ≡ B ∷ Univ r ll ^ [ ! , next ll ] / [U]
         → Γ ⊩⟨ l′ ⟩ A ≡ B ^ [ r , ι ll ] / [A]
univEqEq {l} {l′} {Γ} {A} {B} {r} {ll} [U] [A] [A≡B] =
  let [A≡B]′ = irrelevanceEqTerm [U] (U-intr (U-elim [U])) [A≡B]
      X = univEqEq′ (U-elim [U]) (PE.subst (λ r → Γ ⊩⟨ l′ ⟩ A ^ r) (PE.sym (PE.cong toTypeInfo (U-Relevance-Level-eq [U]))) [A]) [A≡B]′
  in helper-eq (PE.sym (PE.cong toTypeInfo (U-Relevance-Level-eq [U]))) X
  
