{-# OPTIONS --without-K  #-}

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

-- Type for maybe embeddings of reducible types
data MaybeEmb (l : TypeLevel) (⊩⟨_⟩ : TypeLevel → Set) : Set where
  noemb : ⊩⟨ l ⟩ → MaybeEmb l ⊩⟨_⟩
  emb   : ∀ {l′} → l′ < l → MaybeEmb l′ ⊩⟨_⟩ → MaybeEmb l ⊩⟨_⟩

-- Specific reducible types with possible embedding

_⊩⟨_⟩U_ : (Γ : Con Term) (l : TypeLevel) (s : 𝕊) → Set
Γ ⊩⟨ l ⟩U s = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩U s)

_⊩⟨_⟩ℕ_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → Set
Γ ⊩⟨ l ⟩ℕ A = MaybeEmb l (λ l′ → Γ ⊩ℕ A)

_⊩⟨_⟩Empty_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → Set
Γ ⊩⟨ l ⟩Empty A = MaybeEmb l (λ l′ → Γ ⊩Empty A)

_⊩⟨_⟩ne_⦂_ : (Γ : Con Term) (l : TypeLevel) (A : Term) (s : 𝕊) → Set
Γ ⊩⟨ l ⟩ne A ⦂ s = MaybeEmb l (λ l′ → Γ ⊩ne A ⦂ s)

_⊩⟨_⟩Π_⦂_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → 𝕊 → Set
Γ ⊩⟨ l ⟩Π A ⦂ s = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩Π A ⦂ s)

_⊩⟨_⟩cstr_⦂_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → 𝕊 → Set
Γ ⊩⟨ l ⟩cstr A ⦂ s = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩cstr A ⦂ s)

_⊩⟨_⟩Box_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → Set
Γ ⊩⟨ l ⟩Box A = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩Box A)

-- Construct a general reducible type from a specific

U-intr : ∀ {Γ s l} → Γ ⊩⟨ l ⟩U s → Γ ⊩⟨ l ⟩ Univ s ⦂ 𝕥y
U-intr (noemb x) = Uᵣ x
U-intr (emb 0<1 x) = emb 0<1 (U-intr x)

ℕ-intr : ∀ {A Γ l} → Γ ⊩⟨ l ⟩ℕ A → Γ ⊩⟨ l ⟩ A ⦂ 𝕥y
ℕ-intr (noemb x) = ℕᵣ x
ℕ-intr (emb 0<1 x) = emb 0<1 (ℕ-intr x)

Empty-intr : ∀ {A Γ l} → Γ ⊩⟨ l ⟩Empty A → Γ ⊩⟨ l ⟩ A ⦂ 𝕥y
Empty-intr (noemb x) = Emptyᵣ x
Empty-intr (emb 0<1 x) = emb 0<1 (Empty-intr x)

ne-intr : ∀ {A Γ s l} → Γ ⊩⟨ l ⟩ne A ⦂ s → Γ ⊩⟨ l ⟩ A ⦂ s
ne-intr (noemb x) = ne x
ne-intr (emb 0<1 x) = emb 0<1 (ne-intr x)

Π-intr : ∀ {A Γ s l} → Γ ⊩⟨ l ⟩Π A ⦂ s → Γ ⊩⟨ l ⟩ A ⦂ s
Π-intr (noemb x) = Πᵣ x
Π-intr (emb 0<1 x) = emb 0<1 (Π-intr x)

-- Construct a specific reducible type from a general with some criterion

U-elim : ∀ {Γ s s' l} → Γ ⊩⟨ l ⟩ Univ s ⦂ s' → Γ ⊩⟨ l ⟩U s
U-elim (Uᵣ′ _ l′ l< ⊢Γ) = noemb (Uᵣ l′ l< ⊢Γ)
U-elim (ℕᵣ D) = ⊥-elim (U≢ℕ (whnfRed* (red D) Uₙ))
U-elim (Emptyᵣ D) = ⊥-elim (U≢Empty (whnfRed* (red D) Uₙ))
U-elim (ne′ K D neK K≡K) = ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
U-elim (Πᵣ′ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext) = ⊥-elim (U≢Π (whnfRed* (red D) Uₙ))
U-elim (cstrᵣ′ K KcodU a D ⊢a A≡A [domK] [a] [Yi]) = ⊥-elim (U≢cstr (whnfRed* (red D) Uₙ))
U-elim (Boxᵣ′ F sF D ⊢F A≡A [F]) = ⊥-elim (U≢Box (whnfRed* (red D) Uₙ))
U-elim (emb 0<1 x) with U-elim x
U-elim (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
U-elim (emb 0<1 x) | emb () x₁

ℕ-elim′ : ∀ {A Γ s s' l} → Γ ⊢ A ⇒* ℕ ⦂ s → Γ ⊩⟨ l ⟩ A ⦂ s' → Γ ⊩⟨ l ⟩ℕ A
ℕ-elim′ D (Uᵣ′ _ l′ l< ⊢Γ) = ⊥-elim (U≢ℕ (whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , ℕₙ)))
ℕ-elim′ D (ℕᵣ D′) = noemb D′
ℕ-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (ℕ≢ne neK (whrDet* (D , ℕₙ) (red D′ , ne neK)))
ℕ-elim′ D (Πᵣ′ sF F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (ℕ≢Π (whrDet* (D , ℕₙ) (red D′ , Πₙ)))
ℕ-elim′ D (Emptyᵣ D′) =
  ⊥-elim (ℕ≢Empty (whrDet* (D , ℕₙ) (red D′ , Emptyₙ)))
ℕ-elim′ D (cstrᵣ′ K KcodU a D' ⊢a A≡A [domK] [a] [Yi]) =
  ⊥-elim (ℕ≢cstr (whrDet* (D , ℕₙ) (red D' , cstrₙ)))
ℕ-elim′ D (Boxᵣ′ F sF D' ⊢F A≡A [F]) =
  ⊥-elim (ℕ≢Box (whrDet* (D , ℕₙ) (red D' , Boxₙ)))
ℕ-elim′ D (emb 0<1 x) with ℕ-elim′ D x
ℕ-elim′ D (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
ℕ-elim′ D (emb 0<1 x) | emb () x₂

ℕ-elim : ∀ {Γ s l} → Γ ⊩⟨ l ⟩ ℕ ⦂ s → Γ ⊩⟨ l ⟩ℕ ℕ
ℕ-elim [ℕ] = ℕ-elim′ (id (escape [ℕ])) [ℕ]

Empty-elim′ : ∀ {A Γ s s' l} → Γ ⊢ A ⇒* Empty ⦂ s → Γ ⊩⟨ l ⟩ A ⦂ s' → Γ ⊩⟨ l ⟩Empty A
Empty-elim′ D (Uᵣ′ _ l′ l< ⊢Γ) = ⊥-elim (U≢Empty (whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , Emptyₙ)))
Empty-elim′ D (Emptyᵣ D′) = noemb D′
Empty-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (Empty≢ne neK (whrDet* (D , Emptyₙ) (red D′ , ne neK)))
Empty-elim′ D (Πᵣ′ sF F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (Empty≢Π (whrDet* (D , Emptyₙ) (red D′ , Πₙ)))
Empty-elim′ D (ℕᵣ D′) =
  ⊥-elim (Empty≢ℕ (whrDet* (D , Emptyₙ) (red D′ , ℕₙ)))
Empty-elim′ D (cstrᵣ′ K KcodU a D' ⊢a A≡A [domK] [a] [Yi]) =
  ⊥-elim (Empty≢cstr (whrDet* (D , Emptyₙ) (red D' , cstrₙ)))
Empty-elim′ D (Boxᵣ′ F sF D' ⊢F A≡A [F]) =
  ⊥-elim (Empty≢Box (whrDet* (D , Emptyₙ) (red D' , Boxₙ)))
Empty-elim′ D (emb 0<1 x) with Empty-elim′ D x
Empty-elim′ D (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
Empty-elim′ D (emb 0<1 x) | emb () x₂

Empty-elim : ∀ {Γ l} → Γ ⊩⟨ l ⟩ Empty ⦂ 𝕥y → Γ ⊩⟨ l ⟩Empty Empty
Empty-elim [Empty] = Empty-elim′ (id (escape [Empty])) [Empty]

ne-elim′ : ∀ {A Γ l s s' K} → Γ ⊢ A ⇒* K ⦂ s → Neutral K → Γ ⊩⟨ l ⟩ A ⦂ s' → Γ ⊩⟨ l ⟩ne A ⦂ s'
ne-elim′ D neK (Uᵣ′ _ l′ l< ⊢Γ) =
  ⊥-elim (U≢ne neK (whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , ne neK)))
ne-elim′ D neK (ℕᵣ D′) = ⊥-elim (ℕ≢ne neK (whrDet* (red D′ , ℕₙ) (D , ne neK)))
ne-elim′ D neK (Emptyᵣ D′) = ⊥-elim (Empty≢ne neK (whrDet* (red D′ , Emptyₙ) (D , ne neK)))
ne-elim′ D neK (ne′ K D′ neK′ K≡K) = noemb (ne K D′ neK′ K≡K)
ne-elim′ D neK (Πᵣ′ sF F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (Π≢ne neK (whrDet* (red D′ , Πₙ) (D , ne neK)))
ne-elim′ D neK (cstrᵣ′ K KcodU a D' ⊢a A≡A [domK] [a] [Yi]) =
  ⊥-elim (cstr≢ne neK (whrDet* (red D' , cstrₙ) (D , ne neK)))
ne-elim′ D neK (Boxᵣ′ F sF D' ⊢F A≡A [F]) =
  ⊥-elim (Box≢ne neK (whrDet* (red D' , Boxₙ) (D , ne neK)))
ne-elim′ D neK (emb 0<1 x) with ne-elim′ D neK x
ne-elim′ D neK (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
ne-elim′ D neK (emb 0<1 x) | emb () x₂

ne-elim : ∀ {Γ l s K} → Neutral K  → Γ ⊩⟨ l ⟩ K ⦂ s → Γ ⊩⟨ l ⟩ne K ⦂ s
ne-elim neK [K] = ne-elim′ (id (escape [K])) neK [K]

Π-elim′ : ∀ {A Γ F G sF s s' l} → Γ ⊢ A ⇒* Π F ⦂ sF ▹ G ⦂ s → Γ ⊩⟨ l ⟩ A ⦂ s' → Γ ⊩⟨ l ⟩Π A ⦂ s'
Π-elim′ D (Uᵣ′ _ l′ l< ⊢Γ) = ⊥-elim (U≢Π (whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , Πₙ)))
Π-elim′ D (ℕᵣ D′) = ⊥-elim (ℕ≢Π (whrDet* (red D′ , ℕₙ) (D , Πₙ)))
Π-elim′ D (Emptyᵣ D′) = ⊥-elim (Empty≢Π (whrDet* (red D′ , Emptyₙ) (D , Πₙ)))
Π-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (Π≢ne neK (whrDet* (D , Πₙ) (red D′ , ne neK)))
Π-elim′ D (Πᵣ′ sF F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  noemb (Πᵣ sF F G D′ ⊢F ⊢G A≡A [F] [G] G-ext)
Π-elim′ D (cstrᵣ′ K KcodU a D' ⊢a A≡A [domK] [a] [Yi]) =
  ⊥-elim (cstr≢Π (whrDet* (red D' , cstrₙ) (D , Πₙ)))
Π-elim′ D (Boxᵣ′ F sF D' ⊢F A≡A [F]) =
  ⊥-elim (Box≢Π (whrDet* (red D' , Boxₙ) (D , Πₙ)))
Π-elim′ D (emb 0<1 x) with Π-elim′ D x
Π-elim′ D (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
Π-elim′ D (emb 0<1 x) | emb () x₂

Π-elim : ∀ {Γ F G sF s l} → Γ ⊩⟨ l ⟩ Π F ⦂ sF ▹ G ⦂ s → Γ ⊩⟨ l ⟩Π Π F ⦂ sF ▹ G ⦂ s
Π-elim [Π] = Π-elim′ (id (escape [Π])) [Π]


-- TODO
cstr-elim′ : ∀ {A Γ K a s s' l} → Γ ⊢ A ⇒* cstr K a ⦂ s → Γ ⊩⟨ l ⟩ A ⦂ s' → Γ ⊩⟨ l ⟩cstr A ⦂ s'
cstr-elim′ D (Uᵣ′ _ l′ l< ⊢Γ) = ⊥-elim (U≢cstr (whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , cstrₙ)))
cstr-elim′ D (Emptyᵣ D') =
  ⊥-elim (Empty≢cstr (whrDet* (red D' , Emptyₙ) (D , cstrₙ)))
cstr-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (cstr≢ne neK (whrDet* (D , cstrₙ) (red D′ , ne neK)))
cstr-elim′ D (Πᵣ′ sF F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (cstr≢Π (whrDet* (D , cstrₙ) (red D′ , Πₙ)))
cstr-elim′ D (ℕᵣ D′) =
  ⊥-elim (ℕ≢cstr (whrDet* (red D′ , ℕₙ) (D , cstrₙ) ))
cstr-elim′ D (cstrᵣ D′) = noemb D′
cstr-elim′ D (Boxᵣ′ F sF D' ⊢F A≡A [F]) =
  ⊥-elim (cstr≢Box (whrDet* (D , cstrₙ) (red D' , Boxₙ)))
cstr-elim′ D (emb 0<1 x) with cstr-elim′ D x
cstr-elim′ D (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
cstr-elim′ D (emb 0<1 x) | emb () x₂

cstr-elim : ∀ {Γ K a s l} → Γ ⊩⟨ l ⟩ cstr K a ⦂ s → Γ ⊩⟨ l ⟩cstr cstr K a ⦂ s
cstr-elim [cstr] = cstr-elim′ (id (escape [cstr])) [cstr]

Box-elim′ : ∀ {A Γ s s' s'' B l} → Γ ⊢ A ⇒* Box s B ⦂ s' → Γ ⊩⟨ l ⟩ A ⦂ s'' → Γ ⊩⟨ l ⟩Box A
Box-elim′ D (Uᵣ′ _ l′ l< ⊢Γ) = ⊥-elim (U≢Box (whrDet* (id (Uⱼ ⊢Γ) , Uₙ) (D , Boxₙ)))
Box-elim′ D (Emptyᵣ D') =
  ⊥-elim (Empty≢Box (whrDet* (red D' , Emptyₙ) (D , Boxₙ)))
Box-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (Box≢ne neK (whrDet* (D , Boxₙ) (red D′ , ne neK)))
Box-elim′ D (Πᵣ′ sF F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (Box≢Π (whrDet* (D , Boxₙ) (red D′ , Πₙ)))
Box-elim′ D (ℕᵣ D′) =
  ⊥-elim (ℕ≢Box (whrDet* (red D′ , ℕₙ) (D , Boxₙ) ))
Box-elim′ D (cstrᵣ′ K KcodU a D' ⊢a A≡A [domK] [a] [Yi]) =
  ⊥-elim (cstr≢Box (whrDet* (red D' , cstrₙ) (D , Boxₙ)))
Box-elim′ D (Boxᵣ D′) = noemb D′
Box-elim′ D (emb 0<1 x) with Box-elim′ D x
Box-elim′ D (emb 0<1 x) | noemb x₁ = emb 0<1 (noemb x₁)
Box-elim′ D (emb 0<1 x) | emb () x₂

-- automagically s' ≡ 𝕥y
Box-elim : ∀ {Γ s s' A l} → Γ ⊩⟨ l ⟩ Box s A ⦂ s' → Γ ⊩⟨ l ⟩Box (Box s A)
Box-elim [Box] = Box-elim′ (id (escape [Box])) [Box]

-- Extract a type and a level from a maybe embedding
extractMaybeEmb : ∀ {l ⊩⟨_⟩} → MaybeEmb l ⊩⟨_⟩ → ∃ λ l′ → ⊩⟨ l′ ⟩
extractMaybeEmb (noemb x) = _ , x
extractMaybeEmb (emb 0<1 x) = extractMaybeEmb x

-- A view for constructor equality of types where embeddings are ignored
data ShapeView Γ : ∀ l l′ A B s s' (p : Γ ⊩⟨ l ⟩ A ⦂ s) (q : Γ ⊩⟨ l′ ⟩ B ⦂ s') → Set where
  Uᵥ : ∀ {s s' l l′} UA UB → ShapeView Γ l l′ (Univ s) (Univ s') 𝕥y 𝕥y (Uᵣ UA) (Uᵣ UB)
  ℕᵥ : ∀ {A B l l′} ℕA ℕB → ShapeView Γ l l′ A B 𝕥y 𝕥y (ℕᵣ ℕA) (ℕᵣ ℕB)
  Emptyᵥ : ∀ {A B l l′} EmptyA EmptyB → ShapeView Γ l l′ A B 𝕥y 𝕥y (Emptyᵣ EmptyA) (Emptyᵣ EmptyB)
  ne  : ∀ {A B s s' l l′} neA neB
      → ShapeView Γ l l′ A B s s' (ne neA) (ne neB)
  Πᵥ : ∀ {A B s s' l l′} ΠA ΠB
    → ShapeView Γ l l′ A B s s' (Πᵣ ΠA) (Πᵣ ΠB)
  cstrᵥ : ∀ {A B s s' l l′} cstrA cstrB
    → ShapeView Γ l l′ A B s s' (cstrᵣ cstrA) (cstrᵣ cstrB)
  Boxᵥ : ∀ {A B l l′} BoxA BoxB
    → ShapeView Γ l l′ A B 𝕥y 𝕥y (Boxᵣ BoxA) (Boxᵣ BoxB)
  emb⁰¹ : ∀ {A B s s' l p q}
        → ShapeView Γ ⁰ l A B s s' p q
        → ShapeView Γ ¹ l A B s s' (emb 0<1 p) q
  emb¹⁰ : ∀ {A B s s' l p q}
        → ShapeView Γ l ⁰ A B s s' p q
        → ShapeView Γ l ¹ A B s s' p (emb 0<1 q)

-- Construct an shape view from an equality
goodCases : ∀ {l l′ Γ A B s s'} ([A] : Γ ⊩⟨ l ⟩ A ⦂ s) ([B] : Γ ⊩⟨ l′ ⟩ B ⦂ s')
          → Γ ⊩⟨ l ⟩ A ≡ B ⦂ s / [A] → ShapeView Γ l l′ A B s s' [A] [B]
goodCases (Uᵣ UA) (Uᵣ UB) A≡B = Uᵥ UA UB
goodCases (Uᵣ′ _ _ _ ⊢Γ) (ℕᵣ D) PE.refl = ⊥-elim (U≢ℕ (whnfRed* (red D) Uₙ))
goodCases (Uᵣ′ _ _ _ ⊢Γ) (Emptyᵣ D) PE.refl = ⊥-elim (U≢Empty (whnfRed* (red D) Uₙ))
goodCases (Uᵣ′ _ _ _ ⊢Γ) (ne′ K D neK K≡K) PE.refl = ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
goodCases (Uᵣ′ _ _ _ ⊢Γ) (Πᵣ′ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext) PE.refl =
  ⊥-elim (U≢Π (whnfRed* (red D) Uₙ))
goodCases (Uᵣ′ _ _ _ ⊢Γ) (cstrᵣ′ K KcodU a D ⊢a A≡A [domK] [a] [Yi]) PE.refl =
  ⊥-elim (U≢cstr (whnfRed* (red D) Uₙ))
goodCases (Uᵣ′ _ _ _ ⊢Γ)(Boxᵣ′ F sF D' ⊢F A≡A [F]) PE.refl =
  ⊥-elim (U≢Box (whnfRed* (red D') Uₙ))
goodCases (ℕᵣ D) (Uᵣ ⊢Γ) A≡B = ⊥-elim (U≢ℕ (whnfRed* A≡B Uₙ))
goodCases (ℕᵣ _) (Emptyᵣ D') D =
  ⊥-elim (ℕ≢Empty (whrDet* (D , ℕₙ) (red D' , Emptyₙ)))
goodCases (ℕᵣ ℕA) (ℕᵣ ℕB) A≡B = ℕᵥ ℕA ℕB
goodCases (ℕᵣ D) (ne′ K D₁ neK K≡K) A≡B =
  ⊥-elim (ℕ≢ne neK (whrDet* (A≡B , ℕₙ) (red D₁ , ne neK)))
goodCases (ℕᵣ D) (Πᵣ′ sF F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B =
  ⊥-elim (ℕ≢Π (whrDet* (A≡B , ℕₙ) (red D₁ , Πₙ)))
goodCases (ℕᵣ D) (cstrᵣ′ K KcodU a D' ⊢a A≡A [domK] [a] [Yi]) A≡B =
  ⊥-elim (ℕ≢cstr (whrDet* (A≡B , ℕₙ) (red D' , cstrₙ)))
goodCases (ℕᵣ D) (Boxᵣ′ F sF D' ⊢F A≡A [F]) A≡B =
  ⊥-elim (ℕ≢Box (whrDet* (A≡B , ℕₙ) (red D' , Boxₙ)))
goodCases (Emptyᵣ D) (Uᵣ ⊢Γ) A≡B = ⊥-elim (U≢Empty (whnfRed* A≡B Uₙ))
goodCases (Emptyᵣ _) (ℕᵣ D') D =
  ⊥-elim (ℕ≢Empty (whrDet* (red D' , ℕₙ) (D , Emptyₙ)))
goodCases (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) A≡B = Emptyᵥ EmptyA EmptyB
goodCases (Emptyᵣ D) (ne′ K D₁ neK K≡K) A≡B =
  ⊥-elim (Empty≢ne neK (whrDet* (A≡B , Emptyₙ) (red D₁ , ne neK)))
goodCases (Emptyᵣ D) (Πᵣ′ sF F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B =
  ⊥-elim (Empty≢Π (whrDet* (A≡B , Emptyₙ) (red D₁ , Πₙ)))
goodCases (Emptyᵣ D) (cstrᵣ′ K KcodU a D' ⊢a A≡A [domK] [a] [Yi]) A≡B =
  ⊥-elim (Empty≢cstr (whrDet* (A≡B , Emptyₙ) (red D' , cstrₙ)))
goodCases (Emptyᵣ D) (Boxᵣ′ F sF D' ⊢F A≡A [F]) A≡B =
  ⊥-elim (Empty≢Box (whrDet* (A≡B , Emptyₙ) (red D' , Boxₙ)))
goodCases (ne′ K D neK K≡K) (Uᵣ ⊢Γ) (ne₌ M D′ neM K≡M) =
  ⊥-elim (U≢ne neM (whnfRed* (red D′) Uₙ))
goodCases (ne′ K D neK K≡K) (ℕᵣ D₁) (ne₌ M D′ neM K≡M) =
  ⊥-elim (ℕ≢ne neM (whrDet* (red D₁ , ℕₙ) (red D′ , ne neM)))
goodCases (ne′ K D neK K≡K) (Emptyᵣ D₁) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Empty≢ne neM (whrDet* (red D₁ , Emptyₙ) (red D′ , ne neM)))
goodCases (ne neA) (ne neB) A≡B = ne neA neB
goodCases (ne′ K D neK K≡K) (Πᵣ′ sF F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Π≢ne neM (whrDet* (red D₁ , Πₙ) (red D′ , ne neM)))
goodCases (ne′ K D neK K≡K) (cstrᵣ′ _ KcodU a D₁ ⊢a A≡A [domK] [a] [Yi]) (ne₌ M D′ neM K≡M) =
  ⊥-elim (cstr≢ne neM (whrDet* (red D₁ , cstrₙ) (red D′ , ne neM)))
goodCases (ne′ K D neK K≡K) (Boxᵣ′ F sF D' ⊢F A≡A [F]) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Box≢ne neM (whrDet* (red D' , Boxₙ) (red D′ , ne neM)))
goodCases (Πᵣ′ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ ⊢Γ)
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (U≢Π (whnfRed* D′ Uₙ))
goodCases (Πᵣ′ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ D₁)
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (ℕ≢Π (whrDet* (red D₁ , ℕₙ) (D′ , Πₙ)))
goodCases (Πᵣ′ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ D₁)
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Empty≢Π (whrDet* (red D₁ , Emptyₙ) (D′ , Πₙ)))
goodCases (Πᵣ′ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext) (cstrᵣ′ K KcodU a D₁ ⊢a _ [domK] [a] [Yi])
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (cstr≢Π (whrDet* (red D₁ , cstrₙ) (D′ , Πₙ)))
goodCases (Πᵣ′ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Boxᵣ′ _ _ D₁ _ _ _)
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Box≢Π (whrDet* (red D₁ , Boxₙ) (D′ , Πₙ)))
goodCases (Πᵣ′ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne′ K D₁ neK K≡K)
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Π≢ne neK (whrDet* (D′ , Πₙ) (red D₁ , ne neK)))
goodCases (Πᵣ ΠA) (Πᵣ ΠB) A≡B = Πᵥ ΠA ΠB
goodCases (cstrᵣ′ K KcodU a D ⊢a _ [domK] [a] [Yi]) (Uᵣ x) (cstr₌ a' D' A≡B [a≡a']) =
  ⊥-elim (U≢cstr (whnfRed* (red D') Uₙ))
goodCases (cstrᵣ′ K KcodU a D ⊢a _ [domK] [a] [Yi]) (ℕᵣ D₁) (cstr₌ a' D' A≡B [a≡a']) =
  ⊥-elim (ℕ≢cstr (whrDet* (red D₁ , ℕₙ) (red D' , cstrₙ)))
goodCases (cstrᵣ′ K KcodU a D ⊢a _ [domK] [a] [Yi]) (Emptyᵣ D₁) (cstr₌ a' D' A≡B [a≡a']) =
  ⊥-elim (Empty≢cstr (whrDet* (red D₁ , Emptyₙ) (red D' , cstrₙ)))
goodCases (cstrᵣ′ K KcodU a D ⊢a _ [domK] [a] [Yi]) (ne′ _ D₁ neK K≡K) (cstr₌ a' D' A≡B [a≡a']) =
  ⊥-elim (cstr≢ne neK (whrDet* (red D' , cstrₙ) (red D₁ , ne neK) ))
goodCases (cstrᵣ′ K KcodU a D ⊢a _ [domK] [a] [Yi]) (Πᵣ′ sF F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (cstr₌ a' D' A≡B [a≡a']) =
  ⊥-elim (cstr≢Π (whrDet* (red D' , cstrₙ) (red D₁ , Πₙ) ))
goodCases (cstrᵣ cstrA) (cstrᵣ cstrB) (cstr₌ a' D' A≡B [a≡a']) = cstrᵥ cstrA cstrB
goodCases (cstrᵣ′ K KcodU a D ⊢a _ [domK] [a] [Yi]) (Boxᵣ′ F sF D₁ ⊢F A≡A [F]) (cstr₌ a' D' A≡B [a≡a']) =
  ⊥-elim (cstr≢Box (whrDet* (red D' , cstrₙ) (red D₁ , Boxₙ) ))

goodCases (Boxᵣ′ F sF D ⊢F A≡A [F]) (Uᵣ x) (Box₌ F' D' A≡B [F≡F']) =
  ⊥-elim (U≢Box (whnfRed* (red D') Uₙ))
goodCases (Boxᵣ′ F sF D ⊢F A≡A [F]) (ℕᵣ x) (Box₌ F' D' A≡B [F≡F']) =
  ⊥-elim (ℕ≢Box (whrDet* (red x , ℕₙ) (red D' , Boxₙ)))
goodCases (Boxᵣ′ F sF D ⊢F A≡A [F]) (Emptyᵣ x) (Box₌ F' D' A≡B [F≡F']) =
  ⊥-elim (Empty≢Box (whrDet* (red x , Emptyₙ) (red D' , Boxₙ)))
goodCases (Boxᵣ BoxA) (Boxᵣ BoxB) (Box₌ F' D' A≡B [F≡F']) =
  Boxᵥ BoxA BoxB
goodCases (Boxᵣ′ F sF D ⊢F A≡A [F]) (ne′ _ D₁ neK K≡K) (Box₌ F' D' A≡B [F≡F']) =
  ⊥-elim (Box≢ne neK (whrDet* (red D' , Boxₙ) (red D₁ , ne neK) ))
goodCases (Boxᵣ′ F sF D ⊢F A≡A [F]) (Πᵣ′ _ _ G D₁ _ ⊢G _ _ [G] G-ext) (Box₌ F' D' A≡B [F≡F']) =
  ⊥-elim (Box≢Π (whrDet* (red D' , Boxₙ) (red D₁ , Πₙ) ))
goodCases (Boxᵣ′ F sF D ⊢F A≡A [F]) (cstrᵣ′ K KcodU a D₁ ⊢a _ [domK] [a] [Yi]) (Box₌ F' D' A≡B [F≡F']) =
  ⊥-elim (cstr≢Box (whrDet* (red D₁ , cstrₙ) (red D' , Boxₙ) ))
goodCases {l} [A] (emb 0<1 x) A≡B =
  emb¹⁰ (goodCases {l} {⁰} [A] x A≡B)
goodCases {l′ = l} (emb 0<1 x) [B] A≡B =
  emb⁰¹ (goodCases {⁰} {l} x [B] A≡B)

-- Construct an shape view between two derivations of the same type
goodCasesRefl : ∀ {l l′ Γ A s s'} ([A] : Γ ⊩⟨ l ⟩ A ⦂ s) ([A′] : Γ ⊩⟨ l′ ⟩ A ⦂ s')
              → ShapeView Γ l l′ A A s s' [A] [A′]
goodCasesRefl [A] [A′] = goodCases [A] [A′] (reflEq [A])


-- A view for constructor equality between three types
data ShapeView₃ Γ : ∀ l l′ l″ A B C s1 s2 s3
                 (p : Γ ⊩⟨ l   ⟩ A ⦂ s1)
                 (q : Γ ⊩⟨ l′  ⟩ B ⦂ s2)
                 (s : Γ ⊩⟨ l″ ⟩ C ⦂ s3) → Set where
  Uᵥ : ∀ {l l′ l″ s1 s2 s3} UA UB UC → ShapeView₃ Γ l l′ l″ (Univ s1) (Univ s2) (Univ s3) 𝕥y 𝕥y 𝕥y (Uᵣ UA) (Uᵣ UB) (Uᵣ UC)
  ℕᵥ : ∀ {A B C l l′ l″} ℕA ℕB ℕC
    → ShapeView₃ Γ l l′ l″ A B C 𝕥y 𝕥y 𝕥y (ℕᵣ ℕA) (ℕᵣ ℕB) (ℕᵣ ℕC)
  Emptyᵥ : ∀ {A B C l l′ l″} EmptyA EmptyB EmptyC
    → ShapeView₃ Γ l l′ l″ A B C 𝕥y 𝕥y 𝕥y (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) (Emptyᵣ EmptyC)
  ne  : ∀ {A B C s1 s2 s3 l l′ l″} neA neB neC
      → ShapeView₃ Γ l l′ l″ A B C s1 s2 s3 (ne neA) (ne neB) (ne neC)
  Πᵥ : ∀ {A B C s1 s2 s3 l l′ l″} ΠA ΠB ΠC
    → ShapeView₃ Γ l l′ l″ A B C s1 s2 s3 (Πᵣ ΠA) (Πᵣ ΠB) (Πᵣ ΠC)
  cstrᵥ : ∀ {A B C s1 s2 s3 l l′ l″} cstrA cstrB cstrC
    → ShapeView₃ Γ l l′ l″ A B C s1 s2 s3 (cstrᵣ cstrA) (cstrᵣ cstrB) (cstrᵣ cstrC)
  Boxᵥ : ∀ {A B C l l′ l″} BoxA BoxB BoxC
    → ShapeView₃ Γ l l′ l″ A B C 𝕥y 𝕥y 𝕥y (Boxᵣ BoxA) (Boxᵣ BoxB) (Boxᵣ BoxC)
  emb⁰¹¹ : ∀ {A B C l l′ s1 s2 s3 p q s}
         → ShapeView₃ Γ ⁰ l l′ A B C s1 s2 s3 p q s
         → ShapeView₃ Γ ¹ l l′ A B C s1 s2 s3 (emb 0<1 p) q s
  emb¹⁰¹ : ∀ {A B C l l′ s1 s2 s3  p q s}
         → ShapeView₃ Γ l ⁰ l′ A B C s1 s2 s3 p q s
         → ShapeView₃ Γ l ¹ l′ A B C s1 s2 s3 p (emb 0<1 q) s
  emb¹¹⁰ : ∀ {A B C l l′ s1 s2 s3 p q s}
         → ShapeView₃ Γ l l′ ⁰ A B C s1 s2 s3 p q s
         → ShapeView₃ Γ l l′ ¹ A B C s1 s2 s3 p q (emb 0<1 s)

-- Combines two two-way views into a three-way view
combine : ∀ {Γ l l′ l″ l‴ A B C s1 s2 r2' s3 [A] [B] [B]′ [C]}
        → ShapeView Γ l l′ A B s1 s2 [A] [B]
        → ShapeView Γ l″ l‴ B C r2' s3 [B]′ [C]
        → ShapeView₃ Γ l l′ l‴ A B C s1 s2 s3 [A] [B] [C]
combine (Uᵥ UA₁ UB₁) (Uᵥ UA UB) = Uᵥ UA₁ UB₁ UB
combine (Uᵥ UA UB) (ℕᵥ ℕA ℕB) = ⊥-elim (U≢ℕ (whnfRed* (red ℕA) Uₙ))
combine (Uᵥ UA UB) (Emptyᵥ EmptyA EmptyB) = ⊥-elim (U≢Empty (whnfRed* (red EmptyA) Uₙ))
combine (Uᵥ UA UB) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
combine (Uᵥ UA UB) (Πᵥ (Πᵣ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) =
  ⊥-elim (U≢Π (whnfRed* (red D) Uₙ))
combine (Uᵥ UA UB) (cstrᵥ (cstrᵣ K KcodU [domK] [Yi] a D ⊢a A≡A [a]) cstrB) =
  ⊥-elim (U≢cstr (whnfRed* (red D) Uₙ))
combine (Uᵥ UA UB) (Boxᵥ (Boxᵣ F sF D ⊢F A≡A [F]) BoxB) =
  ⊥-elim (U≢Box (whnfRed* (red D) Uₙ))
combine (ℕᵥ ℕA ℕB) (Uᵥ UA UB) = ⊥-elim (U≢ℕ (whnfRed* (red ℕB) Uₙ))
combine (ℕᵥ ℕA ℕB) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (ℕ≢Empty (whrDet* (red ℕB , ℕₙ) (red EmptyA , Emptyₙ)))
combine (ℕᵥ ℕA₁ ℕB₁) (ℕᵥ ℕA ℕB) = ℕᵥ ℕA₁ ℕB₁ ℕB
combine (ℕᵥ ℕA ℕB) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (ℕ≢ne neK (whrDet* (red ℕB , ℕₙ) (red D , ne neK)))
combine (ℕᵥ ℕA ℕB) (Πᵥ (Πᵣ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) =
  ⊥-elim (ℕ≢Π (whrDet* (red ℕB , ℕₙ) (red D , Πₙ)))
combine (ℕᵥ ℕA ℕB) (cstrᵥ (cstrᵣ K KcodU [domK] [Yi] a D ⊢a A≡A [a]) cstrB) =
  ⊥-elim (ℕ≢cstr (whrDet* (red ℕB , ℕₙ) (red D , cstrₙ)))
combine (ℕᵥ ℕA ℕB) (Boxᵥ (Boxᵣ F sF D ⊢F A≡A [F]) BoxB) =
  ⊥-elim (ℕ≢Box (whrDet* (red ℕB , ℕₙ) (red D , Boxₙ)))
combine (Emptyᵥ EmptyA EmptyB) (Uᵥ UA UB) = ⊥-elim (U≢Empty (whnfRed* (red EmptyB) Uₙ))
combine (Emptyᵥ EmptyA EmptyB) (ℕᵥ ℕA ℕB) =
  ⊥-elim (Empty≢ℕ (whrDet* (red EmptyB , Emptyₙ) (red ℕA , ℕₙ)))
combine (Emptyᵥ EmptyA₁ EmptyB₁) (Emptyᵥ EmptyA EmptyB) = Emptyᵥ EmptyA₁ EmptyB₁ EmptyB
combine (Emptyᵥ EmptyA EmptyB) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (Empty≢ne neK (whrDet* (red EmptyB , Emptyₙ) (red D , ne neK)))
combine (Emptyᵥ EmptyA EmptyB) (Πᵥ (Πᵣ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) =
  ⊥-elim (Empty≢Π (whrDet* (red EmptyB , Emptyₙ) (red D , Πₙ)))
combine (Emptyᵥ EmptyA EmptyB) (cstrᵥ (cstrᵣ K KcodU [domK] [Yi] a D ⊢a A≡A [a]) cstrB) =
  ⊥-elim (Empty≢cstr (whrDet* (red EmptyB , Emptyₙ) (red D , cstrₙ)))
combine (Emptyᵥ EmptyA EmptyB) (Boxᵥ (Boxᵣ F sF D ⊢F A≡A [F]) BoxB) =
  ⊥-elim (Empty≢Box (whrDet* (red EmptyB , Emptyₙ) (red D , Boxₙ)))
combine (ne neA (ne K D neK K≡K)) (Uᵥ UA UB) =
  ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
combine (ne neA (ne K D neK K≡K)) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢ne neK (whrDet* (red ℕA , ℕₙ) (red D , ne neK)))
combine (ne neA (ne K D neK K≡K)) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢ne neK (whrDet* (red EmptyA , Emptyₙ) (red D , ne neK)))
combine (ne neA₁ neB₁) (ne neA neB) = ne neA₁ neB₁ neB
combine (ne neA (ne K D₁ neK K≡K)) (Πᵥ (Πᵣ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) =
  ⊥-elim (Π≢ne neK (whrDet* (red D , Πₙ) (red D₁ , ne neK)))
combine (ne neA (ne K D₁ neK K≡K)) (cstrᵥ (cstrᵣ _ KcodU [domK] [Yi] a D ⊢a A≡A [a]) cstrB) =
  ⊥-elim (cstr≢ne neK (whrDet* (red D , cstrₙ) (red D₁ , ne neK)))
combine (ne neA (ne K D₁ neK K≡K)) (Boxᵥ (Boxᵣ F sF D ⊢F A≡A [F]) BoxB) =
  ⊥-elim (Box≢ne neK (whrDet* (red D , Boxₙ) (red D₁ , ne neK)))
combine (Πᵥ ΠA (Πᵣ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Uᵥ UA UB) =
  ⊥-elim (U≢Π (whnfRed* (red D) Uₙ))
combine (Πᵥ ΠA (Πᵣ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢Π (whrDet* (red ℕA , ℕₙ) (red D , Πₙ)))
combine (Πᵥ ΠA (Πᵣ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢Π (whrDet* (red EmptyA , Emptyₙ) (red D , Πₙ)))
combine (Πᵥ ΠA (Πᵣ sF F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext)) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (Π≢ne neK (whrDet* (red D₁ , Πₙ) (red D , ne neK)))
combine (Πᵥ ΠA₁ ΠB₁) (Πᵥ ΠA ΠB) = Πᵥ ΠA₁ ΠB₁ ΠB
combine (Πᵥ ΠA (Πᵣ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (cstrᵥ (cstrᵣ K KcodU [domK] [Yi] a D' ⊢a _ [a]) constrB) =
  ⊥-elim (cstr≢Π (whrDet* (red D' , cstrₙ) (red D , Πₙ)))
combine (Πᵥ ΠA (Πᵣ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Boxᵥ (Boxᵣ _ _ D' _ _ _) constrB) =
  ⊥-elim (Box≢Π (whrDet* (red D' , Boxₙ) (red D , Πₙ)))
combine (cstrᵥ _ (cstrᵣ K KcodU [domK] [Yi] a D₁ ⊢a _ [a])) (Uᵥ UA UB) =
  ⊥-elim (U≢cstr (whnfRed* (red D₁) Uₙ))
combine (cstrᵥ _ (cstrᵣ K KcodU [domK] [Yi] a D₁ ⊢a _ [a])) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢cstr (whrDet* (red ℕA , ℕₙ) (red D₁ , cstrₙ)))
combine (cstrᵥ _ (cstrᵣ K KcodU [domK] [Yi] a D₁ ⊢a _ [a])) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢cstr (whrDet* (red EmptyA , Emptyₙ) (red D₁ , cstrₙ)))
combine (cstrᵥ _ (cstrᵣ K KcodU [domK] [Yi] a D₁ ⊢a _ [a])) (ne (ne _ D neK K≡K) neB) =
  ⊥-elim (cstr≢ne neK (whrDet* (red D₁ , cstrₙ) (red D , ne neK)))
combine (cstrᵥ _ (cstrᵣ K KcodU [domK] [Yi] a D₁ ⊢a _ [a])) (Πᵥ (Πᵣ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) =
  ⊥-elim (cstr≢Π (whrDet* (red D₁ , cstrₙ) (red D , Πₙ)))
combine (cstrᵥ cstrA  cstrB) (cstrᵥ _ cstrC) = cstrᵥ cstrA cstrB cstrC
combine (cstrᵥ _ (cstrᵣ K KcodU [domK] [Yi] a D₁ ⊢a _ [a])) (Boxᵥ (Boxᵣ F sF D ⊢F A≡A [F]) constrB) =
  ⊥-elim (cstr≢Box (whrDet* (red D₁ , cstrₙ) (red D , Boxₙ)))
combine (Boxᵥ _ (Boxᵣ _ _ D₁ _ _ _)) (Uᵥ UA UB) =
  ⊥-elim (U≢Box (whnfRed* (red D₁) Uₙ))
combine (Boxᵥ _ (Boxᵣ _ _ D₁ _ _ _)) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢Box (whrDet* (red ℕA , ℕₙ) (red D₁ , Boxₙ)))
combine (Boxᵥ _ (Boxᵣ _ _ D₁ _ _ _)) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢Box (whrDet* (red EmptyA , Emptyₙ) (red D₁ , Boxₙ)))
combine (Boxᵥ _ (Boxᵣ _ _ D₁ _ _ _)) (ne (ne _ D neK K≡K) neB) =
  ⊥-elim (Box≢ne neK (whrDet* (red D₁ , Boxₙ) (red D , ne neK)))
combine (Boxᵥ _ (Boxᵣ _ _ D₁ _ _ _)) (Πᵥ (Πᵣ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) =
  ⊥-elim (Box≢Π (whrDet* (red D₁ , Boxₙ) (red D , Πₙ)))
combine (Boxᵥ _ (Boxᵣ _ _ D₁ _ _ _))  (cstrᵥ (cstrᵣ K KcodU [domK] [Yi] a D' ⊢a _ [a]) constrB) =
  ⊥-elim (cstr≢Box (whrDet* (red D' , cstrₙ) (red D₁ , Boxₙ)))
combine (Boxᵥ BoxA  BoxB) (Boxᵥ _ BoxC) = Boxᵥ BoxA BoxB BoxC
combine (emb⁰¹ [AB]) [BC] = emb⁰¹¹ (combine [AB] [BC])
combine (emb¹⁰ [AB]) [BC] = emb¹⁰¹ (combine [AB] [BC])
combine [AB] (emb⁰¹ [BC]) = combine [AB] [BC]
combine [AB] (emb¹⁰ [BC]) = emb¹¹⁰ (combine [AB] [BC])
