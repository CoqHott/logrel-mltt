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

_⊩⟨_⟩U : (Γ : Con Term) (l : TypeLevel) → Set
Γ ⊩⟨ l ⟩U = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩U)

_⊩⟨_⟩ℕ_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → Set
Γ ⊩⟨ l ⟩ℕ A = MaybeEmb l (λ l′ → Γ ⊩ℕ A)

_⊩⟨_⟩Empty_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → Set
Γ ⊩⟨ l ⟩Empty A = MaybeEmb l (λ l′ → Γ ⊩Empty A)

_⊩⟨_⟩ne_^_ : (Γ : Con Term) (l : TypeLevel) (A : Term) (r : Relevance) → Set
Γ ⊩⟨ l ⟩ne A ^ r = MaybeEmb l (λ l′ → Γ ⊩ne A ^ r)

_⊩⟨_⟩Π_^_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → Relevance → Set
Γ ⊩⟨ l ⟩Π A ^ r = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩Π A ^ r)

_⊩⟨_⟩∃_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → Set
Γ ⊩⟨ l ⟩∃ A = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩∃ A)

-- Construct a general reducible type from a specific

U-intr : ∀ {l Γ r} → Γ ⊩⟨ l ⟩U → Σ Level (λ l′ → Γ ⊩⟨ l ⟩ Univ r l′ ^ !)
U-intr {l = Fin.suc Fin.zero} (noemb (Uᵣ Fin.zero l< ⊢Γ)) = ⁰ , Uᵣ (Uᵣ _ l< ⊢Γ)
U-intr {l = Fin.suc (Fin.suc l)} (noemb (Uᵣ Fin.zero l< ⊢Γ)) = ⁰ , Uᵣ (Uᵣ _ l< ⊢Γ)
U-intr {l = Fin.suc l} (noemb (Uᵣ (Fin.suc l′) l< ⊢Γ)) = ¹ , Uᵣ (Uᵣ _ l< ⊢Γ)
U-intr {Fin.suc Fin.zero} (emb {l′ = Fin.zero} (Nat.s≤s X) x) = let i , x = U-intr x in i , emb (Nat.s≤s X) x
U-intr {Fin.suc (Fin.suc l)} (emb {l′ = Fin.zero} (Nat.s≤s X) x) = let i , x = U-intr x in i , emb (Nat.s≤s X) x
U-intr {Fin.suc (Fin.suc Fin.zero)} (emb {l′ = Fin.suc Fin.zero} (Nat.s≤s (Nat.s≤s X)) x) = let i , x = U-intr x in i , emb (Nat.s≤s (Nat.s≤s X)) x


ℕ-intr : ∀ {l A Γ} → Γ ⊩⟨ l ⟩ℕ A → Γ ⊩⟨ l ⟩ A ^ !
ℕ-intr (noemb x) = ℕᵣ x
ℕ-intr {Fin.suc Fin.zero} (emb {l′ = Fin.zero} (Nat.s≤s X) x) = emb (Nat.s≤s X) (ℕ-intr x)
ℕ-intr {Fin.suc (Fin.suc l)} (emb {l′ = Fin.zero} (Nat.s≤s X) x) = emb (Nat.s≤s X) (ℕ-intr x)
ℕ-intr {Fin.suc (Fin.suc Fin.zero)} (emb {l′ = Fin.suc Fin.zero} (Nat.s≤s (Nat.s≤s X)) x) = emb (Nat.s≤s (Nat.s≤s X)) (ℕ-intr x)

Empty-intr : ∀ {l A Γ} → Γ ⊩⟨ l ⟩Empty A → Γ ⊩⟨ l ⟩ A ^ %
Empty-intr (noemb x) = Emptyᵣ x
Empty-intr {Fin.suc Fin.zero} (emb {l′ = Fin.zero} (Nat.s≤s X) x) = emb (Nat.s≤s X) (Empty-intr x)
Empty-intr {Fin.suc (Fin.suc l)} (emb {l′ = Fin.zero} (Nat.s≤s X) x) = emb (Nat.s≤s X) (Empty-intr x)
Empty-intr {Fin.suc (Fin.suc Fin.zero)} (emb {l′ = Fin.suc Fin.zero} (Nat.s≤s (Nat.s≤s X)) x) = emb (Nat.s≤s (Nat.s≤s X)) (Empty-intr x)

ne-intr : ∀ {l A Γ r} → Γ ⊩⟨ l ⟩ne A ^ r → Γ ⊩⟨ l ⟩ A ^ r
ne-intr (noemb x) = ne x
ne-intr {Fin.suc Fin.zero} (emb {l′ = Fin.zero} (Nat.s≤s X) x) = emb (Nat.s≤s X) (ne-intr x)
ne-intr {Fin.suc (Fin.suc l)} (emb {l′ = Fin.zero} (Nat.s≤s X) x) = emb (Nat.s≤s X) (ne-intr x)
ne-intr {Fin.suc (Fin.suc Fin.zero)} (emb {l′ = Fin.suc Fin.zero} (Nat.s≤s (Nat.s≤s X)) x) = emb (Nat.s≤s (Nat.s≤s X)) (ne-intr x)

Π-intr : ∀ {l A Γ r} → Γ ⊩⟨ l ⟩Π A ^ r → Γ ⊩⟨ l ⟩ A ^ r
Π-intr (noemb x) = Πᵣ x
Π-intr {Fin.suc Fin.zero} (emb {l′ = Fin.zero} (Nat.s≤s X) x) = emb (Nat.s≤s X) (Π-intr x)
Π-intr {Fin.suc (Fin.suc l)} (emb {l′ = Fin.zero} (Nat.s≤s X) x) = emb (Nat.s≤s X) (Π-intr x)
Π-intr {Fin.suc (Fin.suc Fin.zero)} (emb {l′ = Fin.suc Fin.zero} (Nat.s≤s (Nat.s≤s X)) x) = emb (Nat.s≤s (Nat.s≤s X)) (Π-intr x)

∃-intr : ∀ {l A Γ} → Γ ⊩⟨ l ⟩∃ A → Γ ⊩⟨ l ⟩ A ^ %
∃-intr (noemb x) = ∃ᵣ x
∃-intr {Fin.suc Fin.zero} (emb {l′ = Fin.zero} (Nat.s≤s X) x) = emb (Nat.s≤s X) (∃-intr x)
∃-intr {Fin.suc (Fin.suc l)} (emb {l′ = Fin.zero} (Nat.s≤s X) x) = emb (Nat.s≤s X) (∃-intr x)
∃-intr {Fin.suc (Fin.suc Fin.zero)} (emb {l′ = Fin.suc Fin.zero} (Nat.s≤s (Nat.s≤s X)) x) = emb (Nat.s≤s (Nat.s≤s X)) (∃-intr x)


-- Construct a specific reducible type from a general with some criterion

U-elim : ∀ {l Γ r r' l'} → Γ ⊩⟨ l ⟩ Univ r l' ^ r' → Γ ⊩⟨ l ⟩U
U-elim (Uᵣ′ _ l′ l< ⊢Γ) = noemb (Uᵣ l′ l< ⊢Γ)
U-elim (ℕᵣ D) = ⊥-elim (U≢ℕ (whnfRed* (red D) Uₙ))
U-elim (Emptyᵣ D) = ⊥-elim (U≢Empty (whnfRed* (red D) Uₙ))
U-elim (ne′ l K D neK K≡K) = ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
U-elim (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) = ⊥-elim (U≢Π (whnfRed* (red D) Uₙ))
U-elim (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) = ⊥-elim (U≢∃ (whnfRed* (red D) Uₙ))
U-elim {Fin.suc Fin.zero} (emb {l′ = Fin.zero} (Nat.s≤s X) x) with U-elim x
U-elim {Fin.suc Fin.zero} (emb {l′ = Fin.zero} (Nat.s≤s X) x) | noemb x₁ = emb (Nat.s≤s X) (noemb x₁)
U-elim {Fin.suc Fin.zero} (emb {l′ = Fin.zero} (Nat.s≤s X) x) | emb () x₁
U-elim {Fin.suc (Fin.suc l)} (emb {l′ = Fin.zero} (Nat.s≤s X) x) with U-elim x
U-elim {Fin.suc (Fin.suc l)} (emb {l′ = Fin.zero} (Nat.s≤s X) x) | noemb x₁ = emb (Nat.s≤s X) (noemb x₁)
U-elim {Fin.suc (Fin.suc l)} (emb {l′ = Fin.zero} (Nat.s≤s X) x) | emb () x₁
U-elim {Fin.suc (Fin.suc Fin.zero)} (emb {l′ = Fin.suc Fin.zero} (Nat.s≤s (Nat.s≤s X)) x) with U-elim x
U-elim {Fin.suc (Fin.suc Fin.zero)} (emb {l′ = Fin.suc Fin.zero} (Nat.s≤s (Nat.s≤s X)) x) | noemb x₁ = emb (Nat.s≤s (Nat.s≤s X)) (noemb x₁)
U-elim {Fin.suc (Fin.suc Fin.zero)} (emb {l′ = Fin.suc Fin.zero} (Nat.s≤s (Nat.s≤s X)) x) | emb <l x₁ = emb (Nat.s≤s (Nat.s≤s X)) (emb <l x₁)

ℕ-elim′ : ∀ {l A Γ} → Γ ⊢ A ⇒* ℕ ^ ! → Γ ⊩⟨ l ⟩ A ^ ! → Γ ⊩⟨ l ⟩ℕ A
ℕ-elim′ D (Uᵣ′ _ Fin.zero l< ⊢Γ) = ⊥-elim (U≢ℕ (whrDet* (id (univ (univ 0<1 ⊢Γ)) , Uₙ) (D , ℕₙ)))
ℕ-elim′ D (Uᵣ′ _ (Fin.suc l′) l< ⊢Γ) = ⊥-elim (U≢ℕ (whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , ℕₙ)))
ℕ-elim′ D (ℕᵣ D′) = noemb D′
ℕ-elim′ D (ne′ l K D′ neK K≡K) =
  ⊥-elim (ℕ≢ne neK (whrDet* (D , ℕₙ) (red D′ , ne neK)))
ℕ-elim′ D (Πᵣ′ rF F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (ℕ≢Π (whrDet* (D , ℕₙ) (red D′ , Πₙ)))
ℕ-elim′ {Fin.suc Fin.zero} D (emb {l′ = Fin.zero} (Nat.s≤s X) x) with ℕ-elim′ D x
ℕ-elim′ {Fin.suc Fin.zero} D (emb {l′ = Fin.zero} (Nat.s≤s X) x) | noemb x₁ = emb (Nat.s≤s X) (noemb x₁)
ℕ-elim′ {Fin.suc Fin.zero} D (emb {l′ = Fin.zero} (Nat.s≤s X) x) | emb () x₁
ℕ-elim′ {Fin.suc (Fin.suc l)} D (emb {l′ = Fin.zero} (Nat.s≤s X) x) with ℕ-elim′ D x
ℕ-elim′ {Fin.suc (Fin.suc l)} D (emb {l′ = Fin.zero} (Nat.s≤s X) x) | noemb x₁ = emb (Nat.s≤s X) (noemb x₁)
ℕ-elim′ {Fin.suc (Fin.suc l)} D (emb {l′ = Fin.zero} (Nat.s≤s X) x) | emb () x₁
ℕ-elim′ {Fin.suc (Fin.suc Fin.zero)} D (emb {l′ = Fin.suc Fin.zero} (Nat.s≤s (Nat.s≤s X)) x) with ℕ-elim′ D x
ℕ-elim′ {Fin.suc (Fin.suc Fin.zero)} D (emb {l′ = Fin.suc Fin.zero} (Nat.s≤s (Nat.s≤s X)) x) | noemb x₁ = emb (Nat.s≤s (Nat.s≤s X)) (noemb x₁)
ℕ-elim′ {Fin.suc (Fin.suc Fin.zero)} D (emb {l′ = Fin.suc Fin.zero} (Nat.s≤s (Nat.s≤s X)) x) | emb <l x₁ = emb (Nat.s≤s (Nat.s≤s X)) (emb <l x₁)

ℕ-elim : ∀ {Γ l} → Γ ⊩⟨ l ⟩ ℕ ^ ! → Γ ⊩⟨ l ⟩ℕ ℕ
ℕ-elim [ℕ] = ℕ-elim′ (id (escape [ℕ])) [ℕ]


Empty-elim′ : ∀ {l A Γ} → Γ ⊢ A ⇒* Empty ^ % → Γ ⊩⟨ l ⟩ A ^ % → Γ ⊩⟨ l ⟩Empty A
Empty-elim′ D (Emptyᵣ D′) = noemb D′
Empty-elim′ D (ne′ l K D′ neK K≡K) =
  ⊥-elim (Empty≢ne neK (whrDet* (D , Emptyₙ) (red D′ , ne neK)))
Empty-elim′ D (Πᵣ′ rF F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (Empty≢Π (whrDet* (D , Emptyₙ) (red D′ , Πₙ)))
Empty-elim′ D (∃ᵣ′  F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (Empty≢∃ (whrDet* (D , Emptyₙ) (red D′ , ∃ₙ)))
Empty-elim′ {Fin.suc Fin.zero} D (emb {l′ = Fin.zero} (Nat.s≤s X) x) with Empty-elim′ D x
Empty-elim′ {Fin.suc Fin.zero} D (emb {l′ = Fin.zero} (Nat.s≤s X) x) | noemb x₁ = emb (Nat.s≤s X) (noemb x₁)
Empty-elim′ {Fin.suc Fin.zero} D (emb {l′ = Fin.zero} (Nat.s≤s X) x) | emb () x₁
Empty-elim′ {Fin.suc (Fin.suc l)} D (emb {l′ = Fin.zero} (Nat.s≤s X) x) with Empty-elim′ D x
Empty-elim′ {Fin.suc (Fin.suc l)} D (emb {l′ = Fin.zero} (Nat.s≤s X) x) | noemb x₁ = emb (Nat.s≤s X) (noemb x₁)
Empty-elim′ {Fin.suc (Fin.suc l)} D (emb {l′ = Fin.zero} (Nat.s≤s X) x) | emb () x₁
Empty-elim′ {Fin.suc (Fin.suc Fin.zero)} D (emb {l′ = Fin.suc Fin.zero} (Nat.s≤s (Nat.s≤s X)) x) with Empty-elim′ D x
Empty-elim′ {Fin.suc (Fin.suc Fin.zero)} D (emb {l′ = Fin.suc Fin.zero} (Nat.s≤s (Nat.s≤s X)) x) | noemb x₁ = emb (Nat.s≤s (Nat.s≤s X)) (noemb x₁)
Empty-elim′ {Fin.suc (Fin.suc Fin.zero)} D (emb {l′ = Fin.suc Fin.zero} (Nat.s≤s (Nat.s≤s X)) x) | emb <l x₁ = emb (Nat.s≤s (Nat.s≤s X)) (emb <l x₁)

Empty-elim : ∀ {Γ l} → Γ ⊩⟨ l ⟩ Empty ^ % → Γ ⊩⟨ l ⟩Empty Empty
Empty-elim [Empty] = Empty-elim′ (id (escape [Empty])) [Empty]

ne-elim′ : ∀ {l A Γ K r} → Γ ⊢ A ⇒* K ^ r → Neutral K → Γ ⊩⟨ l ⟩ A ^ r → Γ ⊩⟨ l ⟩ne A ^ r
ne-elim′ D neK (Uᵣ′ _ Fin.zero l< ⊢Γ) = ⊥-elim (U≢ne neK (whrDet* (id (univ (univ 0<1 ⊢Γ)) , Uₙ) (D , ne neK)))
ne-elim′ D neK (Uᵣ′ _ (Fin.suc l′) l< ⊢Γ) = ⊥-elim (U≢ne neK (whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , ne neK)))
ne-elim′ D neK (ℕᵣ D′) = ⊥-elim (ℕ≢ne neK (whrDet* (red D′ , ℕₙ) (D , ne neK)))
ne-elim′ D neK (ne (ne l K D′ neK′ K≡K)) = noemb (ne l K D′ neK′ K≡K) 
ne-elim′ D neK (Πᵣ′ rF F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (Π≢ne neK (whrDet* (red D′ , Πₙ) (D , ne neK)))
ne-elim′ D neK (∃ᵣ′ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (∃≢ne neK (whrDet* (red D′ , ∃ₙ) (D , ne neK)))
ne-elim′ D neK (Emptyᵣ D′) = ⊥-elim (Empty≢ne neK (whrDet* (red D′ , Emptyₙ) (D , ne neK)))
ne-elim′ {Fin.suc Fin.zero} D neK (emb {l′ = Fin.zero} (Nat.s≤s X) x) with ne-elim′ D neK x
ne-elim′ {Fin.suc Fin.zero} D neK (emb {l′ = Fin.zero} (Nat.s≤s X) x) | noemb x₁ = emb (Nat.s≤s X) (noemb x₁)
ne-elim′ {Fin.suc Fin.zero} D neK (emb {l′ = Fin.zero} (Nat.s≤s X) x) | emb () x₁
ne-elim′ {Fin.suc (Fin.suc l)} D neK (emb {l′ = Fin.zero} (Nat.s≤s X) x) with ne-elim′ D neK x
ne-elim′ {Fin.suc (Fin.suc l)} D neK (emb {l′ = Fin.zero} (Nat.s≤s X) x) | noemb x₁ = emb (Nat.s≤s X) (noemb x₁)
ne-elim′ {Fin.suc (Fin.suc l)} D neK (emb {l′ = Fin.zero} (Nat.s≤s X) x) | emb () x₁
ne-elim′ {Fin.suc (Fin.suc Fin.zero)} D neK (emb {l′ = Fin.suc Fin.zero} (Nat.s≤s (Nat.s≤s X)) x) with ne-elim′ D neK x
ne-elim′ {Fin.suc (Fin.suc Fin.zero)} D neK (emb {l′ = Fin.suc Fin.zero} (Nat.s≤s (Nat.s≤s X)) x) | noemb x₁ = emb (Nat.s≤s (Nat.s≤s X)) (noemb x₁)
ne-elim′ {Fin.suc (Fin.suc Fin.zero)} D neK (emb {l′ = Fin.suc Fin.zero} (Nat.s≤s (Nat.s≤s X)) x) | emb <l x₁ = emb (Nat.s≤s (Nat.s≤s X)) (emb <l x₁)

ne-elim : ∀ {Γ l K r} → Neutral K  → Γ ⊩⟨ l ⟩ K ^ r → Γ ⊩⟨ l ⟩ne K ^ r
ne-elim neK [K] = ne-elim′ (id (escape [K])) neK [K]

Π-elim′ : ∀ {l A Γ F G rF rG} → Γ ⊢ A ⇒* Π F ^ rF ▹ G ^ rG → Γ ⊩⟨ l ⟩ A ^ rG → Γ ⊩⟨ l ⟩Π A ^ rG
Π-elim′ D (Uᵣ′ _ Fin.zero l< ⊢Γ) = ⊥-elim (U≢Π (whrDet* (id (univ (univ 0<1 ⊢Γ)) , Uₙ) (D , Πₙ)))
Π-elim′ D (Uᵣ′ _ (Fin.suc l′) l< ⊢Γ) = ⊥-elim (U≢Π (whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , Πₙ)))
Π-elim′ D (ℕᵣ D′) = ⊥-elim (ℕ≢Π (whrDet* (red D′ , ℕₙ) (D , Πₙ)))
Π-elim′ D (Emptyᵣ D′) = ⊥-elim (Empty≢Π (whrDet* (red D′ , Emptyₙ) (D , Πₙ)))
Π-elim′ D (ne′ l K D′ neK K≡K) =
  ⊥-elim (Π≢ne neK (whrDet* (D , Πₙ) (red D′ , ne neK)))
Π-elim′ D (Πᵣ′ rF F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  noemb (Πᵣ rF F G D′ ⊢F ⊢G A≡A [F] [G] G-ext)
Π-elim′ D (∃ᵣ′ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (Π≢∃ (whrDet* (D , Πₙ) (red D′ , ∃ₙ)))
Π-elim′ {Fin.suc Fin.zero} D (emb {l′ = Fin.zero} (Nat.s≤s X) x) with Π-elim′ D x
Π-elim′ {Fin.suc Fin.zero} D (emb {l′ = Fin.zero} (Nat.s≤s X) x) | noemb x₁ = emb (Nat.s≤s X) (noemb x₁)
Π-elim′ {Fin.suc Fin.zero} D (emb {l′ = Fin.zero} (Nat.s≤s X) x) | emb () x₁
Π-elim′ {Fin.suc (Fin.suc l)} D (emb {l′ = Fin.zero} (Nat.s≤s X) x) with Π-elim′ D x
Π-elim′ {Fin.suc (Fin.suc l)} D (emb {l′ = Fin.zero} (Nat.s≤s X) x) | noemb x₁ = emb (Nat.s≤s X) (noemb x₁)
Π-elim′ {Fin.suc (Fin.suc l)} D (emb {l′ = Fin.zero} (Nat.s≤s X) x) | emb () x₁
Π-elim′ {Fin.suc (Fin.suc Fin.zero)} D (emb {l′ = Fin.suc Fin.zero} (Nat.s≤s (Nat.s≤s X)) x) with Π-elim′ D x
Π-elim′ {Fin.suc (Fin.suc Fin.zero)} D (emb {l′ = Fin.suc Fin.zero} (Nat.s≤s (Nat.s≤s X)) x) | noemb x₁ = emb (Nat.s≤s (Nat.s≤s X)) (noemb x₁)
Π-elim′ {Fin.suc (Fin.suc Fin.zero)} D (emb {l′ = Fin.suc Fin.zero} (Nat.s≤s (Nat.s≤s X)) x) | emb <l x₁ = emb (Nat.s≤s (Nat.s≤s X)) (emb <l x₁)

Π-elim : ∀ {Γ F G rF rG l} → Γ ⊩⟨ l ⟩ Π F ^ rF ▹ G ^ rG → Γ ⊩⟨ l ⟩Π Π F ^ rF ▹ G ^ rG
Π-elim [Π] = Π-elim′ (id (escape [Π])) [Π]

∃-elim′ : ∀ {l A Γ F G} → Γ ⊢ A ⇒* ∃ F ▹ G ^ % → Γ ⊩⟨ l ⟩ A ^ % → Γ ⊩⟨ l ⟩∃ A 
∃-elim′ D (Emptyᵣ D′) = ⊥-elim (Empty≢∃ (whrDet* (red D′ , Emptyₙ) (D , ∃ₙ)))
∃-elim′ D (ne′ l K D′ neK K≡K) =
  ⊥-elim (∃≢ne neK (whrDet* (D , ∃ₙ) (red D′ , ne neK)))
∃-elim′ D (Πᵣ′ rF F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (Π≢∃ (whrDet* (red D′ , Πₙ) (D , ∃ₙ)))
∃-elim′ D (∃ᵣ′ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  noemb (∃ᵣ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext)
∃-elim′ {Fin.suc Fin.zero} D (emb {l′ = Fin.zero} (Nat.s≤s X) x) with ∃-elim′ D x
∃-elim′ {Fin.suc Fin.zero} D (emb {l′ = Fin.zero} (Nat.s≤s X) x) | noemb x₁ = emb (Nat.s≤s X) (noemb x₁)
∃-elim′ {Fin.suc Fin.zero} D (emb {l′ = Fin.zero} (Nat.s≤s X) x) | emb () x₁
∃-elim′ {Fin.suc (Fin.suc l)} D (emb {l′ = Fin.zero} (Nat.s≤s X) x) with ∃-elim′ D x
∃-elim′ {Fin.suc (Fin.suc l)} D (emb {l′ = Fin.zero} (Nat.s≤s X) x) | noemb x₁ = emb (Nat.s≤s X) (noemb x₁)
∃-elim′ {Fin.suc (Fin.suc l)} D (emb {l′ = Fin.zero} (Nat.s≤s X) x) | emb () x₁
∃-elim′ {Fin.suc (Fin.suc Fin.zero)} D (emb {l′ = Fin.suc Fin.zero} (Nat.s≤s (Nat.s≤s X)) x) with ∃-elim′ D x
∃-elim′ {Fin.suc (Fin.suc Fin.zero)} D (emb {l′ = Fin.suc Fin.zero} (Nat.s≤s (Nat.s≤s X)) x) | noemb x₁ = emb (Nat.s≤s (Nat.s≤s X)) (noemb x₁)
∃-elim′ {Fin.suc (Fin.suc Fin.zero)} D (emb {l′ = Fin.suc Fin.zero} (Nat.s≤s (Nat.s≤s X)) x) | emb <l x₁ = emb (Nat.s≤s (Nat.s≤s X)) (emb <l x₁)

∃-elim : ∀ {Γ F G l} → Γ ⊩⟨ l ⟩ ∃ F ▹ G ^ % → Γ ⊩⟨ l ⟩∃ (∃ F ▹ G)
∃-elim [∃] = ∃-elim′ (id (escape [∃])) [∃]

-- Extract a type and a level from a maybe embedding
extractMaybeEmb : ∀ {l ⊩⟨_⟩} → MaybeEmb l ⊩⟨_⟩ → ∃ λ l′ → ⊩⟨ l′ ⟩
extractMaybeEmb (noemb x) = _ , x
extractMaybeEmb (emb <l x) = extractMaybeEmb x

-- A view for constructor equality of types where embeddings are ignored
data ShapeView Γ : ∀ l l′ A B r r' (p : Γ ⊩⟨ l ⟩ A ^ r) (q : Γ ⊩⟨ l′ ⟩ B ^ r') → Set where
  Uᵥ : ∀ {r r' l l′} UA UB → ShapeView Γ l l′ (Univ r (toLevel (LogRel._⊩¹U.l< UA))) (Univ r' (toLevel (LogRel._⊩¹U.l< UB))) ! ! (Uᵣ UA) (Uᵣ UB)
  ℕᵥ : ∀ {A B l l′} ℕA ℕB → ShapeView Γ l l′ A B ! ! (ℕᵣ ℕA) (ℕᵣ ℕB)
  Emptyᵥ : ∀ {A B l l′} EmptyA EmptyB → ShapeView Γ l l′ A B % % (Emptyᵣ EmptyA) (Emptyᵣ EmptyB)
  ne  : ∀ {A B l l′ r r'} neA neB
      → ShapeView Γ l l′ A B r r' (ne neA) (ne neB)
  Πᵥ : ∀ {A B l l′ r r'} ΠA ΠB
    → ShapeView Γ l l′ A B r r' (Πᵣ ΠA) (Πᵣ ΠB)
  ∃ᵥ : ∀ {A B l l′} ∃A ∃B
    → ShapeView Γ l l′ A B % % (∃ᵣ ∃A) (∃ᵣ ∃B)
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
        → ShapeView Γ ∞ l A B r r' (emb (Nat.s≤s (Nat.s≤s Nat.z≤n)) p) q
  emb∞¹ : ∀ {A B r r' l p q}
        → ShapeView Γ l (ι ¹) A B r r' p q
        → ShapeView Γ l ∞ A B r r' p (emb (Nat.s≤s (Nat.s≤s Nat.z≤n)) q)



-- Construct a shape view from an equality
goodCases : ∀ {l l′ Γ A B r r'} ([A] : Γ ⊩⟨ l ⟩ A ^ r) ([B] : Γ ⊩⟨ l′ ⟩ B ^ r')
          → Γ ⊩⟨ l ⟩ A ≡ B ^ r / [A] → ShapeView Γ l l′ A B r r' [A] [B]
goodCases (Uᵣ UA) (Uᵣ UB) A≡B = Uᵥ UA UB
goodCases (Uᵣ′ _ _ _ ⊢Γ) (ℕᵣ D) PE.refl = ⊥-elim (U≢ℕ (whnfRed* (red D) Uₙ))
goodCases (Uᵣ′ _ _ _ ⊢Γ) (Emptyᵣ D) PE.refl = ⊥-elim (U≢Empty (whnfRed* (red D) Uₙ))
goodCases (Uᵣ′ _ _ _ ⊢Γ) (ne′ l K D neK K≡K) PE.refl = ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
goodCases (Uᵣ′ _ _ _ ⊢Γ) (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) PE.refl =
  ⊥-elim (U≢Π (whnfRed* (red D) Uₙ))
goodCases (Uᵣ′ _ _ _ ⊢Γ) (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) PE.refl =
  ⊥-elim (U≢∃ (whnfRed* (red D) Uₙ))
goodCases (ℕᵣ D) (Uᵣ ⊢Γ) A≡B = ⊥-elim (U≢ℕ (whnfRed* A≡B Uₙ))
goodCases (ℕᵣ _) (Emptyᵣ D') D =
  ⊥-elim (ℕ≢Empty (whrDet* (D , ℕₙ) (red D' , Emptyₙ)))
goodCases (ℕᵣ ℕA) (ℕᵣ ℕB) A≡B = ℕᵥ ℕA ℕB
goodCases (ℕᵣ D) (ne′ l K D₁ neK K≡K) A≡B =
  ⊥-elim (ℕ≢ne neK (whrDet* (A≡B , ℕₙ) (red D₁ , ne neK)))
goodCases (ℕᵣ D) (Πᵣ′ rF F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B =
  ⊥-elim (ℕ≢Π (whrDet* (A≡B , ℕₙ) (red D₁ , Πₙ)))
goodCases (ℕᵣ D) (∃ᵣ′ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B =
  ⊥-elim (ℕ≢∃ (whrDet* (A≡B , ℕₙ) (red D₁ , ∃ₙ)))
goodCases (Emptyᵣ D) (Uᵣ ⊢Γ) A≡B = ⊥-elim (U≢Empty (whnfRed* A≡B Uₙ))
goodCases (Emptyᵣ _) (ℕᵣ D') D =
   ⊥-elim (ℕ≢Empty (whrDet* (red D' , ℕₙ) (D , Emptyₙ)))
goodCases (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) A≡B = Emptyᵥ EmptyA EmptyB
goodCases (Emptyᵣ D) (ne′ l K D₁ neK K≡K) A≡B =
  ⊥-elim (Empty≢ne neK (whrDet* (A≡B , Emptyₙ) (red D₁ , ne neK)))
goodCases (Emptyᵣ D) (Πᵣ′ rF F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B =
  ⊥-elim (Empty≢Π (whrDet* (A≡B , Emptyₙ) (red D₁ , Πₙ)))
goodCases (Emptyᵣ D) (∃ᵣ′ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B =
  ⊥-elim (Empty≢∃ (whrDet* (A≡B , Emptyₙ) (red D₁ , ∃ₙ)))
goodCases (ne′ l K D neK K≡K) (Uᵣ ⊢Γ) (ne₌ M D′ neM K≡M) =
  ⊥-elim (U≢ne neM (whnfRed* (red D′) Uₙ))
goodCases (ne′ l K D neK K≡K) (ℕᵣ D₁) (ne₌ M D′ neM K≡M) =
  ⊥-elim (ℕ≢ne neM (whrDet* (red D₁ , ℕₙ) (red D′ , ne neM)))
goodCases (ne′ l K D neK K≡K) (Emptyᵣ D₁) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Empty≢ne neM (whrDet* (red D₁ , Emptyₙ) (red D′ , ne neM)))
goodCases (ne neA) (ne neB) A≡B = ne neA neB
goodCases (ne′ l K D neK K≡K) (Πᵣ′ rF F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Π≢ne neM (whrDet* (red D₁ , Πₙ) (red D′ , ne neM)))
goodCases (ne′ l K D neK K≡K) (∃ᵣ′ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (ne₌ M D′ neM K≡M) =
  ⊥-elim (∃≢ne neM (whrDet* (red D₁ , ∃ₙ) (red D′ , ne neM)))
goodCases (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ ⊢Γ)
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (U≢Π (whnfRed* D′ Uₙ))
goodCases (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ D₁)
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (ℕ≢Π (whrDet* (red D₁ , ℕₙ) (D′ , Πₙ)))
goodCases (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ D₁)
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Empty≢Π (whrDet* (red D₁ , Emptyₙ) (D′ , Πₙ)))
goodCases (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne′ l K D₁ neK K≡K)
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Π≢ne neK (whrDet* (D′ , Πₙ) (red D₁ , ne neK)))
goodCases (Πᵣ ΠA) (Πᵣ ΠB) A≡B = Πᵥ ΠA ΠB
goodCases (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
          (∃ᵣ′ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Π≢∃ (whrDet* (D′ , Πₙ) (red D₁ , ∃ₙ)))
goodCases (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ ⊢Γ)
          (∃₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (U≢∃ (whnfRed* D′ Uₙ))
goodCases (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ D₁)
          (∃₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (ℕ≢∃ (whrDet* (red D₁ , ℕₙ) (D′ , ∃ₙ)))
goodCases (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ D₁)
          (∃₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Empty≢∃ (whrDet* (red D₁ , Emptyₙ) (D′ , ∃ₙ)))
goodCases (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne′ l K D₁ neK K≡K)
          (∃₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (∃≢ne neK (whrDet* (D′ , ∃ₙ) (red D₁ , ne neK)))
goodCases (∃ᵣ′ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
          (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
          (∃₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Π≢∃ (whrDet* (red D , Πₙ) (D′ , ∃ₙ)))
goodCases (∃ᵣ ∃A) (∃ᵣ ∃B) A≡B = ∃ᵥ ∃A ∃B
goodCases {l} {Fin.suc Fin.zero} [A] (emb {l′ = Fin.zero} (Nat.s≤s Nat.z≤n) x) A≡B = emb¹⁰ (goodCases {l} {ι ⁰} [A] x A≡B)
goodCases {l} {Fin.suc (Fin.suc Fin.zero)} [A] (emb {l′ = Fin.zero} (Nat.s≤s Nat.z≤n) x) A≡B = emb∞⁰ (goodCases {l} {ι ⁰} [A] x A≡B)
goodCases {l} {Fin.suc (Fin.suc Fin.zero)} [A] (emb {l′ = Fin.suc Fin.zero} (Nat.s≤s (Nat.s≤s Nat.z≤n)) x) A≡B = emb∞¹ (goodCases {l} {ι ¹} [A] x A≡B)
goodCases {Fin.suc Fin.zero} {l} (emb {l′ = Fin.zero} (Nat.s≤s Nat.z≤n) x) [B] A≡B = emb⁰¹ (goodCases {ι ⁰} {l} x [B] A≡B)
goodCases {Fin.suc (Fin.suc Fin.zero)} {l} (emb {l′ = Fin.zero} (Nat.s≤s Nat.z≤n) x) [B] A≡B = emb⁰∞ (goodCases {ι ⁰} {l} x [B] A≡B)
goodCases {Fin.suc (Fin.suc Fin.zero)} {l} (emb {l′ = Fin.suc Fin.zero} (Nat.s≤s (Nat.s≤s Nat.z≤n)) x) [B] A≡B = emb¹∞ (goodCases {ι ¹} {l} x [B] A≡B)

-- Construct an shape view between two derivations of the same type
goodCasesRefl : ∀ {l l′ Γ A r r'} ([A] : Γ ⊩⟨ l ⟩ A ^ r) ([A′] : Γ ⊩⟨ l′ ⟩ A ^ r')
              → ShapeView Γ l l′ A A r r' [A] [A′]
goodCasesRefl [A] [A′] = goodCases [A] [A′] (reflEq [A])


-- A view for constructor equality between three types
data ShapeView₃ Γ : ∀ l l′ l″ A B C r1 r2 r3
                 (p : Γ ⊩⟨ l   ⟩ A ^ r1)
                 (q : Γ ⊩⟨ l′  ⟩ B ^ r2)
                 (r : Γ ⊩⟨ l″ ⟩ C ^ r3) → Set where
  Uᵥ : ∀ {l l′ l″ r1 r2 r3} UA UB UC → ShapeView₃ Γ l l′ l″ (Univ r1 (toLevel (LogRel._⊩¹U.l< UA))) (Univ r2 (toLevel (LogRel._⊩¹U.l< UB)))
                                                            (Univ r3 (toLevel (LogRel._⊩¹U.l< UC))) ! ! ! (Uᵣ UA) (Uᵣ UB) (Uᵣ UC)
  ℕᵥ : ∀ {A B C l l′ l″} ℕA ℕB ℕC
    → ShapeView₃ Γ l l′ l″ A B C ! ! ! (ℕᵣ ℕA) (ℕᵣ ℕB) (ℕᵣ ℕC)
  Emptyᵥ : ∀ {A B C l l′ l″} EmptyA EmptyB EmptyC
    → ShapeView₃ Γ l l′ l″ A B C % % % (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) (Emptyᵣ EmptyC)
  ne  : ∀ {A B C r1 r2 r3 l l′ l″} neA neB neC
      → ShapeView₃ Γ l l′ l″ A B C r1 r2 r3 (ne neA) (ne neB) (ne neC)
  Πᵥ : ∀ {A B C r1 r2 r3 l l′ l″} ΠA ΠB ΠC
    → ShapeView₃ Γ l l′ l″ A B C r1 r2 r3 (Πᵣ ΠA) (Πᵣ ΠB) (Πᵣ ΠC)
  ∃ᵥ : ∀ {A B C l l′ l″} ΠA ΠB ΠC
    → ShapeView₃ Γ l l′ l″ A B C % % % (∃ᵣ ΠA) (∃ᵣ ΠB) (∃ᵣ ΠC)
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
         → ShapeView₃ Γ ∞ l l′ A B C r1 r2 r3 (emb (Nat.s≤s (Nat.s≤s Nat.z≤n)) p) q r
  emb∞¹∞ : ∀ {A B C l l′ r1 r2 r3  p q r}
         → ShapeView₃ Γ l (ι ¹) l′ A B C r1 r2 r3 p q r
         → ShapeView₃ Γ l ∞ l′ A B C r1 r2 r3 p (emb (Nat.s≤s (Nat.s≤s Nat.z≤n)) q) r
  emb∞∞¹ : ∀ {A B C l l′ r1 r2 r3 p q r}
         → ShapeView₃ Γ l l′ (ι ¹) A B C r1 r2 r3 p q r
         → ShapeView₃ Γ l l′ ∞ A B C r1 r2 r3 p q (emb (Nat.s≤s (Nat.s≤s Nat.z≤n)) r)

combineUᵥ : ∀ {Γ l l′ l″ l‴ r1 r2 r4 UA UB UA' UB'}
        → (toLevel (LogRel._⊩¹U.l< UB)) PE.≡ (toLevel (LogRel._⊩¹U.l< UA'))
        → ShapeView Γ l l′  (Univ r1 (toLevel (LogRel._⊩¹U.l< UA))) (Univ r2 (toLevel (LogRel._⊩¹U.l< UB))) ! ! (Uᵣ UA) (Uᵣ UB)
        → ShapeView Γ l″ l‴ (Univ r2 (toLevel (LogRel._⊩¹U.l< UA'))) (Univ r4 (toLevel (LogRel._⊩¹U.l< UB'))) ! ! (Uᵣ UA') (Uᵣ UB')
        → ShapeView₃ Γ l l′ l‴ (Univ r1 (toLevel (LogRel._⊩¹U.l< UA))) (Univ r2 (toLevel (LogRel._⊩¹U.l< UB)))
                               (Univ r4 (toLevel (LogRel._⊩¹U.l< UB'))) ! ! ! (Uᵣ UA) (Uᵣ UB) (Uᵣ UB')
combineUᵥ {l′ = Fin.suc Fin.zero} {l″ = Fin.suc Fin.zero} e (Uᵥ UA (Uᵣ Fin.zero (Nat.s≤s Nat.z≤n) ⊢Γ)) (Uᵥ (Uᵣ Fin.zero (Nat.s≤s Nat.z≤n) ⊢Γ₁) UC) =
  Uᵥ UA (Uᵣ Fin.zero (Nat.s≤s Nat.z≤n) ⊢Γ) UC
combineUᵥ {l′ = Fin.suc (Fin.suc Fin.zero)} {l″ = Fin.suc (Fin.suc Fin.zero)} e (Uᵥ UA (Uᵣ Fin.zero (Nat.s≤s Nat.z≤n) ⊢Γ)) (Uᵥ (Uᵣ Fin.zero (Nat.s≤s Nat.z≤n) ⊢Γ₁) UC) =
  Uᵥ UA (Uᵣ Fin.zero (Nat.s≤s Nat.z≤n) ⊢Γ) UC
combineUᵥ {l′ = Fin.suc (Fin.suc Fin.zero)} {l″ = Fin.suc (Fin.suc Fin.zero)} e (Uᵥ UA (Uᵣ (Fin.suc Fin.zero) (Nat.s≤s (Nat.s≤s Nat.z≤n)) ⊢Γ))
                                                                              (Uᵥ (Uᵣ (Fin.suc Fin.zero) (Nat.s≤s (Nat.s≤s Nat.z≤n)) ⊢Γ₁) UC) =
  Uᵥ UA (Uᵣ (Fin.suc Fin.zero) (Nat.s≤s (Nat.s≤s Nat.z≤n)) ⊢Γ) UC
combineUᵥ {l′ = Fin.suc Fin.zero} {l″ = Fin.suc (Fin.suc l″)} e (Uᵥ UA (Uᵣ Fin.zero (Nat.s≤s Nat.z≤n) ⊢Γ)) (Uᵥ (Uᵣ Fin.zero (Nat.s≤s Nat.z≤n) ⊢Γ₁) UC) =
  Uᵥ UA (Uᵣ Fin.zero (Nat.s≤s Nat.z≤n) ⊢Γ) UC
combineUᵥ {l′ = Fin.suc (Fin.suc Fin.zero)} {Fin.suc Fin.zero} e (Uᵥ UA (Uᵣ Fin.zero (Nat.s≤s Nat.z≤n) ⊢Γ)) (Uᵥ (Uᵣ Fin.zero (Nat.s≤s Nat.z≤n) ⊢Γ₁) UC) =
  Uᵥ UA (Uᵣ Fin.zero (Nat.s≤s Nat.z≤n) ⊢Γ) UC

-- Combines two two-way views into a three-way view
combine : ∀ {Γ l l′ l″ l‴ A B B' C r1 r2 r2' r3 [A] [B] [B]′ [C]}
        → B PE.≡ B'
        → ShapeView Γ l l′ A B r1 r2 [A] [B]
        → ShapeView Γ l″ l‴ B' C r2' r3 [B]′ [C]
        → ShapeView₃ Γ l l′ l‴ A B C r1 r2 r3 [A] [B] [C]
combine e (Uᵥ UA UB) (Uᵥ UB' UC) = combineUᵥ (let _ , el = Univ-PE-injectivity e in el) (Uᵥ UA UB) (Uᵥ UB' UC)
combine PE.refl (Uᵥ UA UB) (ℕᵥ ℕA ℕB) = ⊥-elim (U≢ℕ (whnfRed* (red ℕA) Uₙ))
combine PE.refl (Uᵥ UA UB) (Emptyᵥ EmptyA EmptyB) = ⊥-elim (U≢Empty (whnfRed* (red EmptyA) Uₙ))
combine PE.refl (Uᵥ UA UB) (ne (ne l K D neK K≡K) neB) =
  ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
combine PE.refl (Uᵥ UA UB) (Πᵥ (Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) =
  ⊥-elim (U≢Π (whnfRed* (red D) Uₙ))
combine PE.refl (Uᵥ UA UB) (∃ᵥ (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) ∃B) =
  ⊥-elim (U≢∃ (whnfRed* (red D) Uₙ))
combine PE.refl  (ℕᵥ ℕA ℕB) (Uᵥ UA UB) = ⊥-elim (U≢ℕ (whnfRed* (red ℕB) Uₙ))
combine PE.refl  (ℕᵥ ℕA ℕB) (Emptyᵥ EmptyA EmptyB) =
   ⊥-elim (ℕ≢Empty (whrDet* (red ℕB , ℕₙ) (red EmptyA , Emptyₙ)))
combine PE.refl  (ℕᵥ ℕA₁ ℕB₁) (ℕᵥ ℕA ℕB) = ℕᵥ ℕA₁ ℕB₁ ℕB
combine PE.refl  (ℕᵥ ℕA ℕB) (ne (ne l K D neK K≡K) neB) =
  ⊥-elim (ℕ≢ne neK (whrDet* (red ℕB , ℕₙ) (red D , ne neK)))
combine PE.refl  (ℕᵥ ℕA ℕB) (Πᵥ (Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) =
  ⊥-elim (ℕ≢Π (whrDet* (red ℕB , ℕₙ) (red D , Πₙ)))
combine PE.refl  (ℕᵥ ℕA ℕB) (∃ᵥ (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) ∃B) =
  ⊥-elim (ℕ≢∃ (whrDet* (red ℕB , ℕₙ) (red D , ∃ₙ)))
combine PE.refl  (Emptyᵥ EmptyA EmptyB) (Uᵥ UA UB) = ⊥-elim (U≢Empty (whnfRed* (red EmptyB) Uₙ))
combine PE.refl  (Emptyᵥ EmptyA EmptyB) (ℕᵥ ℕA ℕB) =
   ⊥-elim (Empty≢ℕ (whrDet* (red EmptyB , Emptyₙ) (red ℕA , ℕₙ)))
combine PE.refl  (Emptyᵥ EmptyA₁ EmptyB₁) (Emptyᵥ EmptyA EmptyB) = Emptyᵥ EmptyA₁ EmptyB₁ EmptyB
combine PE.refl  (Emptyᵥ EmptyA EmptyB) (ne (ne l K D neK K≡K) neB) =
   ⊥-elim (Empty≢ne neK (whrDet* (red EmptyB , Emptyₙ) (red D , ne neK)))
combine PE.refl  (Emptyᵥ EmptyA EmptyB) (Πᵥ (Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) =
   ⊥-elim (Empty≢Π (whrDet* (red EmptyB , Emptyₙ) (red D , Πₙ)))
combine PE.refl  (Emptyᵥ EmptyA EmptyB) (∃ᵥ (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) ∃B) =
   ⊥-elim (Empty≢∃ (whrDet* (red EmptyB , Emptyₙ) (red D , ∃ₙ)))
combine PE.refl  (ne neA (ne l K D neK K≡K)) (Uᵥ UA UB) =
  ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
combine PE.refl  (ne neA (ne l K D neK K≡K)) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢ne neK (whrDet* (red ℕA , ℕₙ) (red D , ne neK)))
combine PE.refl  (ne neA (ne l K D neK K≡K)) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢ne neK (whrDet* (red EmptyA , Emptyₙ) (red D , ne neK)))
combine PE.refl  (ne neA₁ neB₁) (ne neA neB) = ne neA₁ neB₁ neB
combine PE.refl  (ne neA (ne l K D₁ neK K≡K)) (Πᵥ (Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) =
  ⊥-elim (Π≢ne neK (whrDet* (red D , Πₙ) (red D₁ , ne neK)))
combine PE.refl  (ne neA (ne l K D₁ neK K≡K)) (∃ᵥ (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) ∃B) =
  ⊥-elim (∃≢ne neK (whrDet* (red D , ∃ₙ) (red D₁ , ne neK)))
combine PE.refl  (Πᵥ ΠA (Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Uᵥ UA UB) =
  ⊥-elim (U≢Π (whnfRed* (red D) Uₙ))
combine PE.refl  (Πᵥ ΠA (Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢Π (whrDet* (red ℕA , ℕₙ) (red D , Πₙ)))
combine PE.refl  (Πᵥ ΠA (Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢Π (whrDet* (red EmptyA , Emptyₙ) (red D , Πₙ)))
combine PE.refl  (Πᵥ ΠA (Πᵣ rF F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext)) (ne (ne l K D neK K≡K) neB) =
  ⊥-elim (Π≢ne neK (whrDet* (red D₁ , Πₙ) (red D , ne neK)))
combine PE.refl  (Πᵥ ΠA₁ ΠB₁) (Πᵥ ΠA ΠB) = Πᵥ ΠA₁ ΠB₁ ΠB
combine PE.refl  (Πᵥ ΠA (Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext))
        (∃ᵥ (∃ᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) ∃B) =
  ⊥-elim (Π≢∃ (whrDet* (red D , Πₙ) (red D₁ , ∃ₙ)))
combine PE.refl  (∃ᵥ ∃A (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Uᵥ UA UB) =
  ⊥-elim (U≢∃ (whnfRed* (red D) Uₙ))
combine PE.refl  (∃ᵥ ∃A (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢∃ (whrDet* (red ℕA , ℕₙ) (red D , ∃ₙ)))
combine PE.refl  (∃ᵥ ∃A (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢∃ (whrDet* (red EmptyA , Emptyₙ) (red D , ∃ₙ)))
combine PE.refl  (∃ᵥ ∃A (∃ᵣ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext)) (ne (ne l K D neK K≡K) neB) =
  ⊥-elim (∃≢ne neK (whrDet* (red D₁ , ∃ₙ) (red D , ne neK)))
combine PE.refl  (∃ᵥ ΠA (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext))
        (Πᵥ (Πᵣ rF₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) ∃B) =
  ⊥-elim (Π≢∃ (whrDet* (red D₁ , Πₙ) (red D , ∃ₙ)))
combine PE.refl  (∃ᵥ ∃A ∃B) (∃ᵥ ∃A₁ ∃B₁) = ∃ᵥ ∃A ∃B ∃B₁
combine PE.refl (emb⁰¹ [AB]) [BC] = emb⁰¹¹ (combine PE.refl [AB] [BC])
combine PE.refl (emb¹⁰ [AB]) [BC] = emb¹⁰¹ (combine PE.refl [AB] [BC])
combine e [AB] (emb⁰¹ [BC]) = combine e [AB] [BC]
combine PE.refl [AB] (emb¹⁰ [BC]) = emb¹¹⁰ (combine PE.refl [AB] [BC])
combine PE.refl (emb⁰∞ [AB]) [BC] = emb⁰∞∞ (combine PE.refl [AB] [BC])
combine PE.refl (emb∞⁰ [AB]) [BC] = emb∞⁰∞ (combine PE.refl [AB] [BC])
combine e [AB] (emb⁰∞ [BC]) = combine e [AB] [BC]
combine PE.refl [AB] (emb∞⁰ [BC]) = emb∞∞⁰ (combine PE.refl [AB] [BC])
combine PE.refl (emb¹∞ [AB]) [BC] = emb¹∞∞ (combine PE.refl [AB] [BC])
combine PE.refl (emb∞¹ [AB]) [BC] = emb∞¹∞ (combine PE.refl [AB] [BC])
combine e [AB] (emb¹∞ [BC]) = combine e [AB] [BC]
combine PE.refl [AB] (emb∞¹ [BC]) = emb∞∞¹ (combine PE.refl [AB] [BC])
