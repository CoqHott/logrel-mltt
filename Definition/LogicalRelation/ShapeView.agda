{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.ShapeView {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties.Escape
open import Definition.LogicalRelation.Properties.Reflexivity

open import Tools.Product
open import Tools.Empty using (⊥; ⊥-elim)
import Tools.PropositionalEquality as PE

import Data.Fin as Fin
import Data.Nat as Nat

-- Type for maybe embeddings of reducible types
data MaybeEmb (l : TypeLevel) (⊩⟨_⟩ : TypeLevel → Set) : Set where
  noemb : ⊩⟨ l ⟩ → MaybeEmb l ⊩⟨_⟩
  emb   : ∀ {l′} → l′ <∞ l → MaybeEmb l′ ⊩⟨_⟩ → MaybeEmb l ⊩⟨_⟩

-- Specific reducible types with possible embedding

_⊩⟨_⟩U_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → Set
Γ ⊩⟨ l ⟩U A = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩U A)

_⊩⟨_⟩ℕ_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → Set
Γ ⊩⟨ l ⟩ℕ A = MaybeEmb l (λ l′ → Γ ⊩ℕ A)

_⊩⟨_⟩Empty_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → Set
Γ ⊩⟨ l ⟩Empty A = MaybeEmb l (λ l′ → Γ ⊩Empty A)

_⊩⟨_⟩ne_^[_,_] : (Γ : Con Term) (l : TypeLevel) (A : Term) (r : Relevance) (ll : Level) → Set
Γ ⊩⟨ l ⟩ne A ^[ r , ll ] = MaybeEmb l (λ l′ → Γ ⊩ne A ^[ r , ll ])

_⊩⟨_⟩Π_^_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → TypeInfo → Set
Γ ⊩⟨ l ⟩Π A ^ r = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩Π A ^ r)

_⊩⟨_⟩∃_^_ : (Γ : Con Term) (l : TypeLevel) (A : Term) (ll : TypeLevel) → Set
Γ ⊩⟨ l ⟩∃ A ^ ll = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩∃ A ^ ll)

-- Construct a general reducible type from a specific

U-level : ∀ {l Γ A} → (UA : Γ ⊩⟨ l ⟩U A) → Level
U-level (noemb (Uᵣ r l′ l< d)) = l′
U-level (emb x X) = U-level X


U-intr : ∀ {l Γ A} → (UA : Γ ⊩⟨ l ⟩U A) → Γ ⊩⟨ l ⟩ A ^ [ ! , next (U-level UA) ]
U-intr (noemb UA) = Uᵣ UA
U-intr {l = ι ¹} (emb {l′ = ι ⁰} (Nat.s≤s l<) x) = emb {l′ = ι ⁰} (Nat.s≤s l<) (U-intr x)
U-intr {l = ι ¹} (emb {l′ = ∞} (Nat.s≤s ()) x) 
U-intr {l = ∞} (emb {l′ = ι ⁰} (Nat.s≤s Nat.z≤n) x) = emb {l′ = ι ⁰} (Nat.s≤s Nat.z≤n) (U-intr x)
U-intr {l = ∞} (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s l<)) x) = emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s l<)) (U-intr x)
U-intr {l = ∞} (emb {l′ = ∞} (Nat.s≤s (Nat.s≤s ())) x)


ℕ-intr : ∀ {l A Γ} → Γ ⊩⟨ l ⟩ℕ A → Γ ⊩⟨ l ⟩ A ^ [ ! , ι ⁰ ]
ℕ-intr (noemb x) = ℕᵣ x
ℕ-intr {ι ¹} (emb {l′ = ι ⁰} (Nat.s≤s X) x) = emb (Nat.s≤s X) (ℕ-intr x)
ℕ-intr {∞} (emb {l′ = ι ⁰} (Nat.s≤s X) x) = emb (Nat.s≤s X) (ℕ-intr x)
ℕ-intr {∞} (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) x) = emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) (ℕ-intr x)
ℕ-intr {∞} (emb {∞} (Nat.s≤s (Nat.s≤s ())) x₁)

Empty-intr : ∀ {l A Γ} → Γ ⊩⟨ l ⟩Empty A → Γ ⊩⟨ l ⟩ A ^ [ % , ι ⁰ ]
Empty-intr (noemb x) = Emptyᵣ x
Empty-intr {ι ¹} (emb {l′ = ι ⁰} (Nat.s≤s X) x) = emb (Nat.s≤s X) (Empty-intr x)
Empty-intr {∞} (emb {l′ = ι ⁰} (Nat.s≤s X) x) = emb (Nat.s≤s X) (Empty-intr x)
Empty-intr {∞} (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) x) = emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) (Empty-intr x)
Empty-intr {∞} (emb {∞} (Nat.s≤s (Nat.s≤s ())) x₁)

ne-intr : ∀ {l A Γ r ll} → Γ ⊩⟨ l ⟩ne A ^[ r , ll ] → Γ ⊩⟨ l ⟩ A ^ [ r , ι ll ]
ne-intr (noemb x) = ne x
ne-intr {ι ¹} (emb {l′ = ι ⁰} (Nat.s≤s X) x) = emb (Nat.s≤s X) (ne-intr x)
ne-intr {∞} (emb {l′ = ι ⁰} (Nat.s≤s X) x) = emb (Nat.s≤s X) (ne-intr x)
ne-intr {∞} (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) x) = emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) (ne-intr x)
ne-intr {∞} (emb {∞} (Nat.s≤s (Nat.s≤s ())) x₁)

Π-intr : ∀ {l A Γ r} → Γ ⊩⟨ l ⟩Π A ^ r → Γ ⊩⟨ l ⟩ A ^ r
Π-intr (noemb x) = Πᵣ x
Π-intr {ι ¹} (emb {l′ = ι ⁰} (Nat.s≤s X) x) = emb (Nat.s≤s X) (Π-intr x)
Π-intr {∞} (emb {l′ = ι ⁰} (Nat.s≤s X) x) = emb (Nat.s≤s X) (Π-intr x)
Π-intr {∞} (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) x) = emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) (Π-intr x)
Π-intr {∞} (emb {∞} (Nat.s≤s (Nat.s≤s ())) x₁)

∃-intr : ∀ {l A Γ ll} → Γ ⊩⟨ l ⟩∃ A ^ ll → Γ ⊩⟨ l ⟩ A ^ [ % , ll ]
∃-intr (noemb x) = ∃ᵣ x
∃-intr {ι ¹} (emb {l′ = ι ⁰} (Nat.s≤s X) x) = emb (Nat.s≤s X) (∃-intr x)
∃-intr {∞} (emb {l′ = ι ⁰} (Nat.s≤s X) x) = emb (Nat.s≤s X) (∃-intr x)
∃-intr {∞} (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) x) = emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) (∃-intr x)
∃-intr {∞} (emb {∞} (Nat.s≤s (Nat.s≤s ())) x₁)


-- Construct a specific reducible type from a general with some criterion

U-elim′ : ∀ {l Γ A r l′ ll} → Γ ⊢ A ⇒* Univ r l′ ^ [ ! , ll ] → Γ ⊩⟨ l ⟩ A ^ [ ! , ll ] → Γ ⊩⟨ l ⟩U A
U-elim′ D (Uᵣ′ A r l l< D') = noemb (Uᵣ r l l< D')
U-elim′ D (ℕᵣ D') =  ⊥-elim (U≢ℕ (whrDet* (D ,  Uₙ) (red D' , ℕₙ)))
U-elim′ D (ne′ K D' neK K≡K) =  ⊥-elim (U≢ne neK (whrDet* (D ,  Uₙ) (red D' , ne neK))) 
U-elim′ D (Πᵣ′ rF F G D' ⊢F ⊢G A≡A [F] [G] G-ext) = ⊥-elim (U≢Π (whrDet* (D , Uₙ) (red D' , Πₙ)))
U-elim′ {ι ¹} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) with U-elim′ D x
U-elim′ {ι ¹} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) | noemb x₁ = emb (Nat.s≤s X) (noemb x₁)
U-elim′ {ι ¹} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) | emb () x₁
U-elim′ {∞} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) with U-elim′ D x
U-elim′ {∞} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) | noemb x₁ = emb (Nat.s≤s X) (noemb x₁)
U-elim′ {∞} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) | emb () x₁
U-elim′ {∞} D (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) x) with U-elim′ D x
U-elim′ {∞} D (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) x) | noemb x₁ = emb (Nat.s≤s (Nat.s≤s X)) (noemb x₁)
U-elim′ {∞} D (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) x) | emb <l x₁ = emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) (emb <l x₁)
U-elim′ {∞} D (emb {l′ = ∞} (Nat.s≤s (Nat.s≤s ())) x)

U-elim : ∀ {l Γ r l′} → Γ ⊩⟨ l ⟩ Univ r l′ ^ [ ! , next l′ ] → Γ ⊩⟨ l ⟩U Univ r l′
U-elim [U] = U-elim′ (id (escape [U])) [U]

ℕ-elim′ : ∀ {l A Γ ll} → Γ ⊢ A ⇒* ℕ ^ [ ! , ll ]  → Γ ⊩⟨ l ⟩ A ^ [ ! , ll ] → Γ ⊩⟨ l ⟩ℕ A
ℕ-elim′ D (Uᵣ′ _ _ _ l< [[ _ , _ , d ]]) = ⊥-elim (U≢ℕ (whrDet* (d , Uₙ) (D , ℕₙ)))
ℕ-elim′ D (ℕᵣ D′) = noemb D′
ℕ-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (ℕ≢ne neK (whrDet* (D , ℕₙ) (red D′ , ne neK)))
ℕ-elim′ D (Πᵣ′ rF F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (ℕ≢Π (whrDet* (D , ℕₙ) (red D′ , Πₙ)))
ℕ-elim′ {ι ¹} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) with ℕ-elim′ D x
ℕ-elim′ {ι ¹} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) | noemb x₁ = emb (Nat.s≤s X) (noemb x₁)
ℕ-elim′ {ι ¹} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) | emb () x₁
ℕ-elim′ {∞} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) with ℕ-elim′ D x
ℕ-elim′ {∞} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) | noemb x₁ = emb (Nat.s≤s X) (noemb x₁)
ℕ-elim′ {∞} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) | emb () x₁
ℕ-elim′ {∞} D (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) x) with ℕ-elim′ D x
ℕ-elim′ {∞} D (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) x) | noemb x₁ = emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) (noemb x₁)
ℕ-elim′ {∞} D (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) x) | emb <l x₁ = emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) (emb <l x₁)
ℕ-elim′ {∞} D (emb {l′ = ∞} (Nat.s≤s (Nat.s≤s ())) x)

ℕ-elim : ∀ {Γ l ll } → Γ ⊩⟨ l ⟩ ℕ ^ [ ! , ll ] → Γ ⊩⟨ l ⟩ℕ ℕ
ℕ-elim [ℕ] = ℕ-elim′ (id (escape [ℕ])) [ℕ]


Empty-elim′ : ∀ {l A ll Γ} → Γ ⊢ A ⇒* Empty ^ [ % , ll ] → Γ ⊩⟨ l ⟩ A ^ [ % , ll ] → Γ ⊩⟨ l ⟩Empty A
Empty-elim′ D (Emptyᵣ D′) = noemb D′
Empty-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (Empty≢ne neK (whrDet* (D , Emptyₙ) (red D′ , ne neK)))
Empty-elim′ D (Πᵣ′ rF F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (Empty≢Π (whrDet* (D , Emptyₙ) (red D′ , Πₙ)))
Empty-elim′ D (∃ᵣ′  F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (Empty≢∃ (whrDet* (D , Emptyₙ) (red D′ , ∃ₙ)))
Empty-elim′ {ι ¹} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) with Empty-elim′ D x
Empty-elim′ {ι ¹} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) | noemb x₁ = emb (Nat.s≤s X) (noemb x₁)
Empty-elim′ {ι ¹} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) | emb () x₁
Empty-elim′ {∞} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) with Empty-elim′ D x
Empty-elim′ {∞} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) | noemb x₁ = emb (Nat.s≤s X) (noemb x₁)
Empty-elim′ {∞} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) | emb () x₁
Empty-elim′ {∞} D (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) x) with Empty-elim′ D x
Empty-elim′ {∞} D (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) x) | noemb x₁ = emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) (noemb x₁)
Empty-elim′ {∞} D (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) x) | emb <l x₁ = emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) (emb <l x₁)
Empty-elim′ {∞} D (emb {l′ = ∞} (Nat.s≤s (Nat.s≤s ())) x)

Empty-elim : ∀ {Γ l ll } → Γ ⊩⟨ l ⟩ Empty ^ [ % , ll ] → Γ ⊩⟨ l ⟩Empty Empty
Empty-elim [Empty] = Empty-elim′ (id (escape [Empty])) [Empty]

ne-elim′ : ∀ {l A Γ K r ll ll'} → Γ ⊢ A ⇒* K ^ [ r , ι ll ] → Neutral K → Γ ⊩⟨ l ⟩ A ^ [ r , ll' ] → ι ll PE.≡  ll' → Γ ⊩⟨ l ⟩ne A ^[ r , ll ]
ne-elim′ D neK (Uᵣ′ _ _ _ l< [[ _ , _ , d ]]) e = ⊥-elim (U≢ne neK (whrDet* (d , Uₙ) (D , ne neK)))
ne-elim′ D neK (ℕᵣ D′) e = ⊥-elim (ℕ≢ne neK (whrDet* (red D′ , ℕₙ) (D , ne neK)))
ne-elim′ D neK (ne (ne K D′ neK′ K≡K)) PE.refl = noemb (ne K D′ neK′ K≡K) 
ne-elim′ D neK (Πᵣ′ rF F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) e =
  ⊥-elim (Π≢ne neK (whrDet* (red D′ , Πₙ) (D , ne neK)))
ne-elim′ D neK (∃ᵣ′ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) e =
  ⊥-elim (∃≢ne neK (whrDet* (red D′ , ∃ₙ) (D , ne neK)))
ne-elim′ D neK (Emptyᵣ D′) e = ⊥-elim (Empty≢ne neK (whrDet* (red D′ , Emptyₙ) (D , ne neK)))
ne-elim′ {ι ¹} D neK (emb {l′ = ι ⁰} (Nat.s≤s X) x) e with ne-elim′ D neK x e
ne-elim′ {ι ¹} D neK (emb {l′ = ι ⁰} (Nat.s≤s X) x) e | noemb x₁ = emb (Nat.s≤s X) (noemb x₁)
ne-elim′ {ι ¹} D neK (emb {l′ = ι ⁰} (Nat.s≤s X) x) e | emb () x₁
ne-elim′ {∞} D neK (emb {l′ = ι ⁰} (Nat.s≤s X) x) e with ne-elim′ D neK x e
ne-elim′ {∞} D neK (emb {l′ = ι ⁰} (Nat.s≤s X) x) e | noemb x₁ = emb (Nat.s≤s X) (noemb x₁)
ne-elim′ {∞} D neK (emb {l′ = ι ⁰} (Nat.s≤s X) x) e | emb () x₁
ne-elim′ {∞} D neK (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) x) e with ne-elim′ D neK x e
ne-elim′ {∞} D neK (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) x) e | noemb x₁ = emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) (noemb x₁)
ne-elim′ {∞} D neK (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) x) e | emb <l x₁ = emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) (emb <l x₁)
ne-elim′ {∞} D neK (emb {l′ = ∞} (Nat.s≤s (Nat.s≤s ())) x) e

ne-elim : ∀ {Γ l K r ll} → Neutral K  → Γ ⊩⟨ l ⟩ K ^ [ r , ι ll ] → Γ ⊩⟨ l ⟩ne K ^[ r , ll ]
ne-elim neK [K] = ne-elim′ (id (escape [K])) neK [K] PE.refl

Π-elim′ : ∀ {l A Γ F G rF rG} → Γ ⊢ A ⇒* Π F ^ rF ▹ G ^ rG → Γ ⊩⟨ l ⟩ A ^ rG → Γ ⊩⟨ l ⟩Π A ^ rG
Π-elim′ D (Uᵣ′ _ _ _ l< [[ _ , _ , d ]]) = ⊥-elim (U≢Π (whrDet* (d , Uₙ) (D , Πₙ)))
Π-elim′ D (ℕᵣ D′) = ⊥-elim (ℕ≢Π (whrDet* (red D′ , ℕₙ) (D , Πₙ)))
Π-elim′ D (Emptyᵣ D′) = ⊥-elim (Empty≢Π (whrDet* (red D′ , Emptyₙ) (D , Πₙ)))
Π-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (Π≢ne neK (whrDet* (D , Πₙ) (red D′ , ne neK)))
Π-elim′ D (Πᵣ′ rF F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  noemb (Πᵣ rF F G D′ ⊢F ⊢G A≡A [F] [G] G-ext)
Π-elim′ D (∃ᵣ′ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (Π≢∃ (whrDet* (D , Πₙ) (red D′ , ∃ₙ)))
Π-elim′ {ι ¹} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) with Π-elim′ D x
Π-elim′ {ι ¹} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) | noemb x₁ = emb (Nat.s≤s X) (noemb x₁)
Π-elim′ {ι ¹} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) | emb () x₁
Π-elim′ {∞} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) with Π-elim′ D x
Π-elim′ {∞} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) | noemb x₁ = emb (Nat.s≤s X) (noemb x₁)
Π-elim′ {∞} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) | emb () x₁
Π-elim′ {∞} D (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) x) with Π-elim′ D x
Π-elim′ {∞} D (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) x) | noemb x₁ = emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) (noemb x₁)
Π-elim′ {∞} D (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) x) | emb <l x₁ = emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) (emb <l x₁)
Π-elim′ {∞} D (emb {l′ = ∞} (Nat.s≤s (Nat.s≤s ())) x)

Π-elim : ∀ {Γ F G rF rG l} → Γ ⊩⟨ l ⟩ Π F ^ rF ▹ G ^ rG → Γ ⊩⟨ l ⟩Π Π F ^ rF ▹ G ^ rG
Π-elim [Π] = Π-elim′ (id (escape [Π])) [Π]

∃-elim′ : ∀ {l A Γ F G ll} → Γ ⊢ A ⇒* ∃ F ▹ G ^ [ % , ll ] → Γ ⊩⟨ l ⟩ A ^ [ % , ll ] → Γ ⊩⟨ l ⟩∃ A  ^ ll
∃-elim′ D (Emptyᵣ D′) = ⊥-elim (Empty≢∃ (whrDet* (red D′ , Emptyₙ) (D , ∃ₙ)))
∃-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (∃≢ne neK (whrDet* (D , ∃ₙ) (red D′ , ne neK)))
∃-elim′ D (Πᵣ′ rF F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (Π≢∃ (whrDet* (red D′ , Πₙ) (D , ∃ₙ)))
∃-elim′ D (∃ᵣ′ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  noemb (∃ᵣ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext)
∃-elim′ {ι ¹} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) with ∃-elim′ D x
∃-elim′ {ι ¹} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) | noemb x₁ = emb (Nat.s≤s X) (noemb x₁)
∃-elim′ {ι ¹} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) | emb () x₁
∃-elim′ {∞} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) with ∃-elim′ D x
∃-elim′ {∞} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) | noemb x₁ = emb (Nat.s≤s X) (noemb x₁)
∃-elim′ {∞} D (emb {l′ = ι ⁰} (Nat.s≤s X) x) | emb () x₁
∃-elim′ {∞} D (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) x) with ∃-elim′ D x
∃-elim′ {∞} D (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) x) | noemb x₁ = emb (Nat.s≤s (Nat.s≤s X)) (noemb x₁)
∃-elim′ {∞} D (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) x) | emb <l x₁ = emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) (emb <l x₁)
∃-elim′ {∞} D (emb {l′ = ∞} (Nat.s≤s (Nat.s≤s ())) x)

∃-elim : ∀ {Γ F G l ll} → Γ ⊩⟨ l ⟩ ∃ F ▹ G ^ [ % , ll ] → Γ ⊩⟨ l ⟩∃ (∃ F ▹ G) ^ ll
∃-elim [∃] = ∃-elim′ (id (escape [∃])) [∃]

-- Extract a type and a level from a maybe embedding
extractMaybeEmb : ∀ {l ⊩⟨_⟩} → MaybeEmb l ⊩⟨_⟩ → ∃ λ l′ → ⊩⟨ l′ ⟩
extractMaybeEmb (noemb x) = _ , x
extractMaybeEmb (emb <l x) = extractMaybeEmb x



-- A view for constructor equality of types where embeddings are ignored
data ShapeView Γ : ∀ l l′ A B r r' (p : Γ ⊩⟨ l ⟩ A ^ r) (q : Γ ⊩⟨ l′ ⟩ B ^ r') → Set where
  Uᵥ : ∀ {A B l l′} UA UB → ShapeView Γ l l′ A B [ ! , next (LogRel._⊩¹U_.l′ UA) ] [ ! , next (LogRel._⊩¹U_.l′ UB) ] (Uᵣ UA) (Uᵣ UB)
  ℕᵥ : ∀ {A B l l′} ℕA ℕB → ShapeView Γ l l′ A B [ ! , ι ⁰ ] [ ! , ι ⁰ ] (ℕᵣ ℕA) (ℕᵣ ℕB)
  Emptyᵥ : ∀ {A B l l′} EmptyA EmptyB → ShapeView Γ l l′ A B [ % , ι ⁰ ] [ % , ι ⁰ ] (Emptyᵣ EmptyA) (Emptyᵣ EmptyB)
  ne  : ∀ {A B l l′ r lr r' lr'} neA neB
      → ShapeView Γ l l′ A B [ r , ι lr ] [ r' , ι lr' ] (ne neA) (ne neB)
  Πᵥ : ∀ {A B l l′ r r'} ΠA ΠB
    → ShapeView Γ l l′ A B r r' (Πᵣ ΠA) (Πᵣ ΠB)
  ∃ᵥ : ∀ {A B l l′ ll ll'} ∃A ∃B
    → ShapeView Γ l l′ A B [ % , ll ] [ % , ll' ] (∃ᵣ ∃A) (∃ᵣ ∃B)
  emb⁰¹ : ∀ {A B r r' l p q} 
        → ShapeView Γ (ι ⁰) l A B r r' p q
        → ShapeView Γ (ι ¹) l A B r r' (emb (Nat.s≤s Nat.z≤n) p) q
  emb¹⁰ : ∀ {A B r r' l p q}
        → ShapeView Γ l (ι ⁰) A B r r' p q
        → ShapeView Γ l (ι ¹) A B r r' p (emb (Nat.s≤s Nat.z≤n) q)
  emb⁰∞ : ∀ {A B r r' l p q} 
        → ShapeView Γ (ι ⁰) l A B r r' p q
        → ShapeView Γ ∞ l A B r r' (emb (Nat.s≤s Nat.z≤n) p) q
  emb∞⁰ : ∀ {A B r r' l p q}
        → ShapeView Γ l (ι ⁰) A B r r' p q
        → ShapeView Γ l ∞ A B r r' p (emb (Nat.s≤s Nat.z≤n) q)
  emb¹∞ : ∀ {A B r r' l p q} 
        → ShapeView Γ (ι ¹) l A B r r' p q
        → ShapeView Γ ∞ l A B r r' (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s Nat.z≤n)) p) q
  emb∞¹ : ∀ {A B r r' l p q}
        → ShapeView Γ l (ι ¹) A B r r' p q
        → ShapeView Γ l ∞ A B r r' p (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s Nat.z≤n)) q)


-- Construct a shape view from an equality
goodCases : ∀ {l l′ Γ A B r r'} ([A] : Γ ⊩⟨ l ⟩ A ^ r) ([B] : Γ ⊩⟨ l′ ⟩ B ^ r')
          → Γ ⊩⟨ l ⟩ A ≡ B ^ r / [A] → ShapeView Γ l l′ A B r r' [A] [B]
goodCases (Uᵣ UA) (Uᵣ UB) A≡B = Uᵥ UA UB
goodCases (Uᵣ′ _ _ _ _ ⊢Γ) (ℕᵣ D) D' = ⊥-elim (U≢ℕ (whrDet* (D' ,  Uₙ) (red D , ℕₙ)))
goodCases (Uᵣ′ _ _ _ _ ⊢Γ) (Emptyᵣ D) D' =  ⊥-elim (U≢Empty (whrDet* (D' ,  Uₙ) (red D , Emptyₙ)))
goodCases (Uᵣ′ _ _ _ _ ⊢Γ) (ne′ K D neK K≡K) D' = ⊥-elim (U≢ne neK (whrDet* (D' ,  Uₙ) (red D , ne neK))) 
goodCases (Uᵣ′ _ _ _ _ ⊢Γ) (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) D' =
  ⊥-elim (U≢Π (whrDet* (D' , Uₙ) (red D , Πₙ)))
goodCases (Uᵣ′ _ _ _ _ ⊢Γ) (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) D' =
  ⊥-elim (U≢∃ (whrDet* (D' , Uₙ) (red D , ∃ₙ)))
goodCases (ℕᵣ D) (Uᵣ′ _ _ _ _ D') A≡B = ⊥-elim (U≢ℕ (whrDet* (red D' ,  Uₙ) (A≡B , ℕₙ)))
goodCases (ℕᵣ _) (Emptyᵣ D') D =
  ⊥-elim (ℕ≢Empty (whrDet* (D , ℕₙ) (red D' , Emptyₙ)))
goodCases (ℕᵣ ℕA) (ℕᵣ ℕB) A≡B = ℕᵥ ℕA ℕB
goodCases (ℕᵣ D) (ne′ K D₁ neK K≡K) A≡B =
  ⊥-elim (ℕ≢ne neK (whrDet* (A≡B , ℕₙ) (red D₁ , ne neK)))
goodCases (ℕᵣ D) (Πᵣ′ rF F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B =
  ⊥-elim (ℕ≢Π (whrDet* (A≡B , ℕₙ) (red D₁ , Πₙ)))
goodCases (ℕᵣ D) (∃ᵣ′ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B =
  ⊥-elim (ℕ≢∃ (whrDet* (A≡B , ℕₙ) (red D₁ , ∃ₙ)))
goodCases (Emptyᵣ D) (Uᵣ′ _ _ _ _ D') A≡B = ⊥-elim (U≢Empty (whrDet* (red D' ,  Uₙ) (A≡B , Emptyₙ)))
goodCases (Emptyᵣ _) (ℕᵣ D') D =
   ⊥-elim (ℕ≢Empty (whrDet* (red D' , ℕₙ) (D , Emptyₙ)))
goodCases (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) A≡B = Emptyᵥ EmptyA EmptyB
goodCases (Emptyᵣ D) (ne′ K D₁ neK K≡K) A≡B =
  ⊥-elim (Empty≢ne neK (whrDet* (A≡B , Emptyₙ) (red D₁ , ne neK)))
goodCases (Emptyᵣ D) (Πᵣ′ rF F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B =
  ⊥-elim (Empty≢Π (whrDet* (A≡B , Emptyₙ) (red D₁ , Πₙ)))
goodCases (Emptyᵣ D) (∃ᵣ′ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B =
  ⊥-elim (Empty≢∃ (whrDet* (A≡B , Emptyₙ) (red D₁ , ∃ₙ)))
goodCases (ne′ K D neK K≡K) (Uᵣ′ _ _ _ _ D') (ne₌ M D'' neM K≡M) =
  ⊥-elim (U≢ne neM (whrDet* (red D' ,  Uₙ) (red D'' , ne neM)))
goodCases (ne′ K D neK K≡K) (ℕᵣ D₁) (ne₌ M D′ neM K≡M) =
  ⊥-elim (ℕ≢ne neM (whrDet* (red D₁ , ℕₙ) (red D′ , ne neM)))
goodCases (ne′ K D neK K≡K) (Emptyᵣ D₁) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Empty≢ne neM (whrDet* (red D₁ , Emptyₙ) (red D′ , ne neM)))
goodCases (ne neA) (ne neB) A≡B = ne neA neB
goodCases (ne′ K D neK K≡K) (Πᵣ′ rF F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Π≢ne neM (whrDet* (red D₁ , Πₙ) (red D′ , ne neM)))
goodCases (ne′ K D neK K≡K) (∃ᵣ′ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (ne₌ M D′ neM K≡M) =
  ⊥-elim (∃≢ne neM (whrDet* (red D₁ , ∃ₙ) (red D′ , ne neM)))
goodCases (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ′ _ _ _ _ D')
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (U≢Π (whrDet* (red D' ,  Uₙ) (D′ , Πₙ)))
goodCases (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ D₁)
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (ℕ≢Π (whrDet* (red D₁ , ℕₙ) (D′ , Πₙ)))
goodCases (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ D₁)
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Empty≢Π (whrDet* (red D₁ , Emptyₙ) (D′ , Πₙ)))
goodCases (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne′ K D₁ neK K≡K)
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Π≢ne neK (whrDet* (D′ , Πₙ) (red D₁ , ne neK)))
goodCases (Πᵣ ΠA) (Πᵣ ΠB) A≡B = Πᵥ ΠA ΠB
goodCases (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
          (∃ᵣ′ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Π≢∃ (whrDet* (D′ , Πₙ) (red D₁ , ∃ₙ)))
goodCases (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ′ _ _ _ _ D')
          (∃₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (U≢∃ (whrDet* (red D' ,  Uₙ) (D′ , ∃ₙ)))
goodCases (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ D₁)
          (∃₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (ℕ≢∃ (whrDet* (red D₁ , ℕₙ) (D′ , ∃ₙ)))
goodCases (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ D₁)
          (∃₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Empty≢∃ (whrDet* (red D₁ , Emptyₙ) (D′ , ∃ₙ)))
goodCases (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne′ K D₁ neK K≡K)
          (∃₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (∃≢ne neK (whrDet* (D′ , ∃ₙ) (red D₁ , ne neK)))
goodCases (∃ᵣ′ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
          (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
          (∃₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Π≢∃ (whrDet* (red D , Πₙ) (D′ , ∃ₙ)))
goodCases (∃ᵣ ∃A) (∃ᵣ ∃B) A≡B = ∃ᵥ ∃A ∃B
goodCases {l} {ι ¹} [A] (emb {l′ = ι ⁰} (Nat.s≤s Nat.z≤n) x) A≡B = emb¹⁰ (goodCases {l} {ι ⁰} [A] x A≡B)
goodCases {l} {∞} [A] (emb {l′ = ι ⁰} (Nat.s≤s Nat.z≤n) x) A≡B = emb∞⁰ (goodCases {l} {ι ⁰} [A] x A≡B)
goodCases {l} {∞} [A] (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s Nat.z≤n)) x) A≡B = emb∞¹ (goodCases {l} {ι ¹} [A] x A≡B)
goodCases {ι ¹} {l} (emb {l′ = ι ⁰} (Nat.s≤s Nat.z≤n) x) [B] A≡B = emb⁰¹ (goodCases {ι ⁰} {l} x [B] A≡B)
goodCases {∞} {l} (emb {l′ = ι ⁰} (Nat.s≤s Nat.z≤n) x) [B] A≡B = emb⁰∞ (goodCases {ι ⁰} {l} x [B] A≡B)
goodCases {∞} {l} (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s Nat.z≤n)) x) [B] A≡B = emb¹∞ (goodCases {ι ¹} {l} x [B] A≡B)
goodCases {l′ = ∞} _ (emb {l′ = ∞} (Nat.s≤s (Nat.s≤s ())) [A]) _
goodCases {l = ∞} (emb {l′ = ∞} (Nat.s≤s (Nat.s≤s ())) [A]) _ _

-- Construct an shape view between two derivations of the same type
goodCasesRefl : ∀ {l l′ Γ A r r'} ([A] : Γ ⊩⟨ l ⟩ A ^ r) ([A′] : Γ ⊩⟨ l′ ⟩ A ^ r')
              → ShapeView Γ l l′ A A r r' [A] [A′]
goodCasesRefl [A] [A′] = goodCases [A] [A′] (reflEq [A])


-- A view for constructor equality between three types
data ShapeView₃ Γ : ∀ l l′ l″ A B C r1 r2 r3
                 (p : Γ ⊩⟨ l   ⟩ A ^ r1)
                 (q : Γ ⊩⟨ l′  ⟩ B ^ r2)
                 (r : Γ ⊩⟨ l″ ⟩ C ^ r3) → Set where
  Uᵥ : ∀ {A B C l l′ l″} UA UB UC → ShapeView₃ Γ l l′ l″ A B C 
                                              [ ! , next (LogRel._⊩¹U_.l′ UA) ] [ ! , next (LogRel._⊩¹U_.l′ UB) ] [ ! , next (LogRel._⊩¹U_.l′ UC) ]
                                              (Uᵣ UA) (Uᵣ UB) (Uᵣ UC)
  ℕᵥ : ∀ {A B C l l′ l″} ℕA ℕB ℕC
    → ShapeView₃ Γ l l′ l″ A B C [ ! , ι ⁰ ] [ ! , ι ⁰ ] [ ! , ι ⁰ ] (ℕᵣ ℕA) (ℕᵣ ℕB) (ℕᵣ ℕC)
  Emptyᵥ : ∀ {A B C l l′ l″} EmptyA EmptyB EmptyC
    → ShapeView₃ Γ l l′ l″ A B C [ % , ι ⁰ ] [ % , ι ⁰ ] [ % , ι ⁰ ] (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) (Emptyᵣ EmptyC)
  ne  : ∀ {A B C r1 r2 r3 l1 l2 l3 l l′ l″} neA neB neC
      → ShapeView₃ Γ l l′ l″ A B C [ r1 , ι l1 ] [ r2 , ι l2 ] [ r3 , ι l3 ] (ne neA) (ne neB) (ne neC)
  Πᵥ : ∀ {A B C r1 r2 r3 l l′ l″} ΠA ΠB ΠC
    → ShapeView₃ Γ l l′ l″ A B C r1 r2 r3 (Πᵣ ΠA) (Πᵣ ΠB) (Πᵣ ΠC)
  ∃ᵥ : ∀ {A B C l l′ l″ ll ll' ll''} ΠA ΠB ΠC
    → ShapeView₃ Γ l l′ l″ A B C [ % , ll ] [ % , ll' ] [ % , ll'' ] (∃ᵣ ΠA) (∃ᵣ ΠB) (∃ᵣ ΠC)
  emb⁰¹¹ : ∀ {A B C l l′ r1 r2 r3 p q r}
         → ShapeView₃ Γ (ι ⁰) l l′ A B C r1 r2 r3 p q r
         → ShapeView₃ Γ (ι ¹) l l′ A B C r1 r2 r3 (emb (Nat.s≤s Nat.z≤n) p) q r
  emb¹⁰¹ : ∀ {A B C l l′ r1 r2 r3  p q r}
         → ShapeView₃ Γ l (ι ⁰) l′ A B C r1 r2 r3 p q r
         → ShapeView₃ Γ l (ι ¹) l′ A B C r1 r2 r3 p (emb (Nat.s≤s Nat.z≤n) q) r
  emb¹¹⁰ : ∀ {A B C l l′ r1 r2 r3 p q r}
         → ShapeView₃ Γ l l′ (ι ⁰) A B C r1 r2 r3 p q r
         → ShapeView₃ Γ l l′ (ι ¹) A B C r1 r2 r3 p q (emb (Nat.s≤s Nat.z≤n) r)
  emb⁰∞∞ : ∀ {A B C l l′ r1 r2 r3 p q r}
         → ShapeView₃ Γ (ι ⁰) l l′ A B C r1 r2 r3 p q r
         → ShapeView₃ Γ ∞ l l′ A B C r1 r2 r3 (emb (Nat.s≤s Nat.z≤n) p) q r
  emb∞⁰∞ : ∀ {A B C l l′ r1 r2 r3  p q r}
         → ShapeView₃ Γ l (ι ⁰) l′ A B C r1 r2 r3 p q r
         → ShapeView₃ Γ l ∞ l′ A B C r1 r2 r3 p (emb (Nat.s≤s Nat.z≤n) q) r
  emb∞∞⁰ : ∀ {A B C l l′ r1 r2 r3 p q r}
         → ShapeView₃ Γ l l′ (ι ⁰) A B C r1 r2 r3 p q r
         → ShapeView₃ Γ l l′ ∞ A B C r1 r2 r3 p q (emb (Nat.s≤s Nat.z≤n) r)
  emb¹∞∞ : ∀ {A B C l l′ r1 r2 r3 p q r}
         → ShapeView₃ Γ (ι ¹) l l′ A B C r1 r2 r3 p q r
         → ShapeView₃ Γ ∞ l l′ A B C r1 r2 r3 (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s Nat.z≤n)) p) q r
  emb∞¹∞ : ∀ {A B C l l′ r1 r2 r3  p q r}
         → ShapeView₃ Γ l (ι ¹) l′ A B C r1 r2 r3 p q r
         → ShapeView₃ Γ l ∞ l′ A B C r1 r2 r3 p (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s Nat.z≤n)) q) r
  emb∞∞¹ : ∀ {A B C l l′ r1 r2 r3 p q r}
         → ShapeView₃ Γ l l′ (ι ¹) A B C r1 r2 r3 p q r
         → ShapeView₃ Γ l l′ ∞ A B C r1 r2 r3 p q (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s Nat.z≤n)) r)


-- Combines two two-way views into a three-way view
combine : ∀ {Γ l l′ l″ l‴ A B C r1 r2 r2' r3 [A] [B] [B]′ [C]}
        → ShapeView Γ l l′ A B r1 r2 [A] [B]
        → ShapeView Γ l″ l‴ B C r2' r3 [B]′ [C]
        → ShapeView₃ Γ l l′ l‴ A B C r1 r2 r3 [A] [B] [C]
combine (Uᵥ UA UB) (Uᵥ UB' UC) = Uᵥ UA UB UC
combine (Uᵥ UA (Uᵣ r l′ l< D)) (ℕᵥ ℕA ℕB) = 
 ⊥-elim (U≢ℕ (whrDet* (red D ,  Uₙ) (red  ℕA , ℕₙ))) 
combine (Uᵥ UA (Uᵣ r l′ l< D)) (Emptyᵥ EmptyA EmptyB) =
 ⊥-elim (U≢Empty (whrDet* (red D ,  Uₙ) (red  EmptyA , Emptyₙ))) 
combine (Uᵥ UA (Uᵣ r l′ l< D)) (ne (ne K D' neK K≡K) neB) = 
  ⊥-elim (U≢ne neK (whrDet* (red D ,  Uₙ) (red  D' , ne neK)))
combine (Uᵥ UA (Uᵣ r l′ l< D)) (Πᵥ (Πᵣ rF F G D' ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) =
 ⊥-elim (U≢Π (whrDet* (red D ,  Uₙ) (red  D' , Πₙ))) 
combine (Uᵥ UA (Uᵣ r l′ l< D)) (∃ᵥ (∃ᵣ F G D' ⊢F ⊢G A≡A [F] [G] G-ext) ∃B) =
 ⊥-elim (U≢∃ (whrDet* (red D ,  Uₙ) (red  D' , ∃ₙ))) 
combine  (ℕᵥ ℕA ℕB) (Uᵥ (Uᵣ r l′ l< D) UB) = 
 ⊥-elim (U≢ℕ (whrDet* (red D ,  Uₙ) (red  ℕB , ℕₙ))) 
combine  (ℕᵥ ℕA ℕB) (Emptyᵥ EmptyA EmptyB) =
   ⊥-elim (ℕ≢Empty (whrDet* (red ℕB , ℕₙ) (red EmptyA , Emptyₙ)))
combine  (ℕᵥ ℕA₁ ℕB₁) (ℕᵥ ℕA ℕB) = ℕᵥ ℕA₁ ℕB₁ ℕB
combine  (ℕᵥ ℕA ℕB) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (ℕ≢ne neK (whrDet* (red ℕB , ℕₙ) (red D , ne neK)))
combine  (ℕᵥ ℕA ℕB) (Πᵥ (Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) =
  ⊥-elim (ℕ≢Π (whrDet* (red ℕB , ℕₙ) (red D , Πₙ)))
combine  (ℕᵥ ℕA ℕB) (∃ᵥ (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) ∃B) =
  ⊥-elim (ℕ≢∃ (whrDet* (red ℕB , ℕₙ) (red D , ∃ₙ)))
combine  (Emptyᵥ EmptyA EmptyB) (Uᵥ (Uᵣ r l′ l< D) UB) = 
 ⊥-elim (U≢Empty (whrDet* (red D ,  Uₙ) (red  EmptyB , Emptyₙ))) 
combine  (Emptyᵥ EmptyA EmptyB) (ℕᵥ ℕA ℕB) =
   ⊥-elim (Empty≢ℕ (whrDet* (red EmptyB , Emptyₙ) (red ℕA , ℕₙ)))
combine  (Emptyᵥ EmptyA₁ EmptyB₁) (Emptyᵥ EmptyA EmptyB) = Emptyᵥ EmptyA₁ EmptyB₁ EmptyB
combine  (Emptyᵥ EmptyA EmptyB) (ne (ne K D neK K≡K) neB) =
   ⊥-elim (Empty≢ne neK (whrDet* (red EmptyB , Emptyₙ) (red D , ne neK)))
combine  (Emptyᵥ EmptyA EmptyB) (Πᵥ (Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) =
   ⊥-elim (Empty≢Π (whrDet* (red EmptyB , Emptyₙ) (red D , Πₙ)))
combine  (Emptyᵥ EmptyA EmptyB) (∃ᵥ (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) ∃B) =
   ⊥-elim (Empty≢∃ (whrDet* (red EmptyB , Emptyₙ) (red D , ∃ₙ)))
combine  (ne neA (ne K D' neK K≡K)) (Uᵥ (Uᵣ r l′ l< D) UB) =
  ⊥-elim (U≢ne neK (whrDet* (red D ,  Uₙ) (red  D' , ne neK)))
combine  (ne neA (ne K D neK K≡K)) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢ne neK (whrDet* (red ℕA , ℕₙ) (red D , ne neK)))
combine  (ne neA (ne K D neK K≡K)) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢ne neK (whrDet* (red EmptyA , Emptyₙ) (red D , ne neK)))
combine  (ne neA₁ neB₁) (ne neA neB) = ne neA₁ neB₁ neB
combine  (ne neA (ne K D₁ neK K≡K)) (Πᵥ (Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) =
  ⊥-elim (Π≢ne neK (whrDet* (red D , Πₙ) (red D₁ , ne neK)))
combine  (ne neA (ne K D₁ neK K≡K)) (∃ᵥ (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) ∃B) =
  ⊥-elim (∃≢ne neK (whrDet* (red D , ∃ₙ) (red D₁ , ne neK)))
combine  (Πᵥ ΠA (Πᵣ rF F G D' ⊢F ⊢G A≡A [F] [G] G-ext)) (Uᵥ (Uᵣ r l′ l< D) UB) =
 ⊥-elim (U≢Π (whrDet* (red D ,  Uₙ) (red  D' , Πₙ))) 
combine  (Πᵥ ΠA (Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢Π (whrDet* (red ℕA , ℕₙ) (red D , Πₙ)))
combine  (Πᵥ ΠA (Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢Π (whrDet* (red EmptyA , Emptyₙ) (red D , Πₙ)))
combine  (Πᵥ ΠA (Πᵣ rF F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext)) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (Π≢ne neK (whrDet* (red D₁ , Πₙ) (red D , ne neK)))
combine  (Πᵥ ΠA₁ ΠB₁) (Πᵥ ΠA ΠB) = Πᵥ ΠA₁ ΠB₁ ΠB
combine  (Πᵥ ΠA (Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext))
        (∃ᵥ (∃ᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) ∃B) =
  ⊥-elim (Π≢∃ (whrDet* (red D , Πₙ) (red D₁ , ∃ₙ)))
combine  (∃ᵥ ∃A (∃ᵣ F G D' ⊢F ⊢G A≡A [F] [G] G-ext)) (Uᵥ (Uᵣ r l′ l< D) UB) = 
 ⊥-elim (U≢∃ (whrDet* (red D ,  Uₙ) (red  D' , ∃ₙ))) 
combine  (∃ᵥ ∃A (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢∃ (whrDet* (red ℕA , ℕₙ) (red D , ∃ₙ)))
combine  (∃ᵥ ∃A (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢∃ (whrDet* (red EmptyA , Emptyₙ) (red D , ∃ₙ)))
combine  (∃ᵥ ∃A (∃ᵣ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext)) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (∃≢ne neK (whrDet* (red D₁ , ∃ₙ) (red D , ne neK)))
combine  (∃ᵥ ΠA (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext))
        (Πᵥ (Πᵣ rF₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) ∃B) =
  ⊥-elim (Π≢∃ (whrDet* (red D₁ , Πₙ) (red D , ∃ₙ)))
combine  (∃ᵥ ∃A ∃B) (∃ᵥ ∃A₁ ∃B₁) = ∃ᵥ ∃A ∃B ∃B₁
combine (emb⁰¹ [AB]) [BC] = emb⁰¹¹ (combine [AB] [BC])
combine (emb¹⁰ [AB]) [BC] = emb¹⁰¹ (combine [AB] [BC])
combine [AB] (emb⁰¹ [BC]) = combine [AB] [BC]
combine [AB] (emb¹⁰ [BC]) = emb¹¹⁰ (combine [AB] [BC])
combine (emb⁰∞ [AB]) [BC] = emb⁰∞∞ (combine [AB] [BC])
combine (emb∞⁰ [AB]) [BC] = emb∞⁰∞ (combine [AB] [BC])
combine [AB] (emb⁰∞ [BC]) = combine [AB] [BC]
combine [AB] (emb∞⁰ [BC]) = emb∞∞⁰ (combine [AB] [BC])
combine (emb¹∞ [AB]) [BC] = emb¹∞∞ (combine [AB] [BC])
combine (emb∞¹ [AB]) [BC] = emb∞¹∞ (combine [AB] [BC])
combine [AB] (emb¹∞ [BC]) = combine [AB] [BC]
combine [AB] (emb∞¹ [BC]) = emb∞∞¹ (combine [AB] [BC])
