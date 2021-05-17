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

_⊩⟨_⟩U_^_ : (Γ : Con Term) (l : TypeLevel) (A : Term) (ll : TypeLevel) → Set
Γ ⊩⟨ l ⟩U A ^ ll = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩U A ^ ll)

_⊩⟨_⟩ℕ_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → Set
Γ ⊩⟨ l ⟩ℕ A = MaybeEmb l (λ l′ → Γ ⊩ℕ A)

_⊩⟨_⟩Empty_^_ : (Γ : Con Term) (l : TypeLevel) (A : Term) (ll : Level) → Set
Γ ⊩⟨ l ⟩Empty A ^ ll = MaybeEmb l (λ l′ → Γ ⊩Empty A ^ ll)

_⊩⟨_⟩ne_^[_,_] : (Γ : Con Term) (l : TypeLevel) (A : Term) (r : Relevance) (ll : Level) → Set
Γ ⊩⟨ l ⟩ne A ^[ r , ll ] = MaybeEmb l (λ l′ → Γ ⊩ne A ^[ r , ll ])

_⊩⟨_⟩Π_^_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → TypeInfo → Set
Γ ⊩⟨ l ⟩Π A ^ r = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩Π A ^ r)

_⊩⟨_⟩∃_^_ : (Γ : Con Term) (l : TypeLevel) (A : Term) (ll : TypeLevel) → Set
Γ ⊩⟨ l ⟩∃ A ^ ll = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩∃ A ^ ll)

-- Construct a general reducible type from a specific

U-intr : ∀ {l Γ A ll } → (UA : Γ ⊩⟨ l ⟩U A ^ ll) → Γ ⊩⟨ l ⟩ A ^ [ ! , ll ]
U-intr (noemb UA) = Uᵣ UA
U-intr {l = ι ¹} (emb emb< x) = emb emb< (U-intr x)
U-intr {l = ∞}  (emb ∞< x) = emb ∞< (U-intr x)

ℕ-intr : ∀ {l A Γ} → Γ ⊩⟨ l ⟩ℕ A → Γ ⊩⟨ l ⟩ A ^ [ ! , ι ⁰ ]
ℕ-intr (noemb x) = ℕᵣ x
ℕ-intr {l = ι ¹} (emb emb< x) = emb emb< (ℕ-intr x)
ℕ-intr {l = ∞}  (emb ∞< x) = emb ∞< (ℕ-intr x)

Empty-intr : ∀ {l A Γ ll} → Γ ⊩⟨ l ⟩Empty A ^ ll → Γ ⊩⟨ l ⟩ A ^ [ % , ι ll ]
Empty-intr (noemb x) = Emptyᵣ x
Empty-intr {l = ι ¹} (emb emb< x) = emb emb< (Empty-intr x)
Empty-intr {l = ∞}  (emb ∞< x) = emb ∞< (Empty-intr x)

ne-intr : ∀ {l A Γ r ll} → Γ ⊩⟨ l ⟩ne A ^[ r , ll ] → Γ ⊩⟨ l ⟩ A ^ [ r , ι ll ]
ne-intr (noemb x) = ne x
ne-intr {l = ι ¹} (emb emb< x) = emb emb< (ne-intr x)
ne-intr {l = ∞}  (emb ∞< x) = emb ∞< (ne-intr x)

Π-intr : ∀ {l A Γ r} → Γ ⊩⟨ l ⟩Π A ^ r → Γ ⊩⟨ l ⟩ A ^ r
Π-intr (noemb x) = Πᵣ x
Π-intr {l = ι ¹} (emb emb< x) = emb emb< (Π-intr x)
Π-intr {l = ∞}  (emb ∞< x) = emb ∞< (Π-intr x)

∃-intr : ∀ {l A Γ ll} → Γ ⊩⟨ l ⟩∃ A ^ ll → Γ ⊩⟨ l ⟩ A ^ [ % , ll ]
∃-intr (noemb x) = ∃ᵣ x
∃-intr {l = ι ¹} (emb emb< x) = emb emb< (∃-intr x)
∃-intr {l = ∞}  (emb ∞< x) = emb ∞< (∃-intr x)


-- Construct a specific reducible type from a general with some criterion

U-elim′ : ∀ {l Γ A r l′ ll} → Γ ⊢ A ⇒* Univ r l′ ^ [ ! , ll ] → Γ ⊩⟨ l ⟩ A ^ [ ! , ll ] → Γ ⊩⟨ l ⟩U A ^ ll
U-elim′ D (Uᵣ′ A ll r l l< e D') = noemb (Uᵣ r l l< e D')
U-elim′ D (ℕᵣ D') =  ⊥-elim (U≢ℕ (whrDet* (D ,  Uₙ) (red D' , ℕₙ)))
U-elim′ D (ne′ K D' neK K≡K) =  ⊥-elim (U≢ne neK (whrDet* (D ,  Uₙ) (red D' , ne neK))) 
U-elim′ D (Πᵣ′ rF lF lG F G D' ⊢F ⊢G A≡A [F] [G] G-ext) = ⊥-elim (U≢Π (whrDet* (D , Uₙ) (red D' , Πₙ)))
U-elim′ {ι ¹} D (emb emb< x) with U-elim′ D x
U-elim′ {ι ¹} D (emb emb< x) | noemb x₁ = emb emb< (noemb x₁)
U-elim′ {ι ¹} D (emb emb< x) | emb () x₁
U-elim′ {∞} D (emb ∞< x) with U-elim′ D x
U-elim′ {∞} D (emb ∞< x) | noemb x₁ = emb ∞< (noemb x₁)
U-elim′ {∞} D (emb ∞< x) | emb <l x₁ = emb {l′ = ι ¹} ∞< (emb <l x₁)

U-elim : ∀ {l Γ r l′ ll′} → Γ ⊩⟨ l ⟩ Univ r l′ ^ [ ! , ll′ ] → Γ ⊩⟨ l ⟩U Univ r l′ ^ ll′
U-elim [U] = U-elim′ (id (escape [U])) [U]

ℕ-elim′ : ∀ {l A Γ ll} → Γ ⊢ A ⇒* ℕ ^ [ ! , ll ]  → Γ ⊩⟨ l ⟩ A ^ [ ! , ll ] → Γ ⊩⟨ l ⟩ℕ A
ℕ-elim′ D (Uᵣ′ _ _ _ _ l< PE.refl [[ _ , _ , d ]]) = ⊥-elim (U≢ℕ (whrDet* (d , Uₙ) (D , ℕₙ)))
ℕ-elim′ D (ℕᵣ D′) = noemb D′
ℕ-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (ℕ≢ne neK (whrDet* (D , ℕₙ) (red D′ , ne neK)))
ℕ-elim′ D (Πᵣ′ rF lF lG F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (ℕ≢Π (whrDet* (D , ℕₙ) (red D′ , Πₙ)))
ℕ-elim′ {ι ¹} D (emb emb< x) with ℕ-elim′ D x
ℕ-elim′ {ι ¹} D (emb emb< x) | noemb x₁ = emb emb< (noemb x₁)
ℕ-elim′ {ι ¹} D (emb emb< x) | emb () x₁
ℕ-elim′ {∞} D (emb ∞< x) with ℕ-elim′ D x
ℕ-elim′ {∞} D (emb ∞< x) | noemb x₁ = emb ∞< (noemb x₁)
ℕ-elim′ {∞} D (emb ∞< x) | emb <l x₁ = emb {l′ = ι ¹} ∞< (emb <l x₁)

ℕ-elim : ∀ {Γ l ll } → Γ ⊩⟨ l ⟩ ℕ ^ [ ! , ll ] → Γ ⊩⟨ l ⟩ℕ ℕ
ℕ-elim [ℕ] = ℕ-elim′ (id (escape [ℕ])) [ℕ]


Empty-elim′ : ∀ {l A ll Γ} → Γ ⊢ A ⇒* Empty ^ [ % , ι ll ] → Γ ⊩⟨ l ⟩ A ^ [ % , ι ll ] → Γ ⊩⟨ l ⟩Empty A ^ ll
Empty-elim′ D (Emptyᵣ D′) = noemb D′
Empty-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (Empty≢ne neK (whrDet* (D , Emptyₙ) (red D′ , ne neK)))
Empty-elim′ D (Πᵣ′ rF lF lG F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (Empty≢Π (whrDet* (D , Emptyₙ) (red D′ , Πₙ)))
Empty-elim′ D (∃ᵣ′  F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (Empty≢∃ (whrDet* (D , Emptyₙ) (red D′ , ∃ₙ)))
Empty-elim′ {ι ¹} D (emb emb< x) with Empty-elim′ D x
Empty-elim′ {ι ¹} D (emb emb< x) | noemb x₁ = emb emb< (noemb x₁)
Empty-elim′ {ι ¹} D (emb emb< x) | emb () x₁
Empty-elim′ {∞} D (emb ∞< x) with Empty-elim′ D x
Empty-elim′ {∞} D (emb ∞< x) | noemb x₁ = emb ∞< (noemb x₁)
Empty-elim′ {∞} D (emb ∞< x) | emb <l x₁ = emb {l′ = ι ¹} ∞< (emb <l x₁)

Empty-elim : ∀ {Γ l ll } → Γ ⊩⟨ l ⟩ Empty ^ [ % , ι ll ] → Γ ⊩⟨ l ⟩Empty Empty ^ ll
Empty-elim [Empty] = Empty-elim′ (id (escape [Empty])) [Empty]

ne-elim′ : ∀ {l A Γ K r ll ll'} → Γ ⊢ A ⇒* K ^ [ r , ι ll ] → Neutral K → Γ ⊩⟨ l ⟩ A ^ [ r , ll' ] → ι ll PE.≡  ll' → Γ ⊩⟨ l ⟩ne A ^[ r , ll ]
ne-elim′ D neK (Uᵣ′ _ _ _ _ l< PE.refl [[ _ , _ , d ]]) e = ⊥-elim (U≢ne neK (whrDet* (d , Uₙ) (D , ne neK)))
ne-elim′ D neK (ℕᵣ D′) e = ⊥-elim (ℕ≢ne neK (whrDet* (red D′ , ℕₙ) (D , ne neK)))
ne-elim′ D neK (ne (ne K D′ neK′ K≡K)) PE.refl = noemb (ne K D′ neK′ K≡K) 
ne-elim′ D neK (Πᵣ′ rF lF lG F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) e =
  ⊥-elim (Π≢ne neK (whrDet* (red D′ , Πₙ) (D , ne neK)))
ne-elim′ D neK (∃ᵣ′ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) e =
  ⊥-elim (∃≢ne neK (whrDet* (red D′ , ∃ₙ) (D , ne neK)))
ne-elim′ D neK (Emptyᵣ D′) e = ⊥-elim (Empty≢ne neK (whrDet* (red D′ , Emptyₙ) (D , ne neK)))
ne-elim′ {ι ¹} D neK (emb emb< x) e with ne-elim′ D neK x e
ne-elim′ {ι ¹} D neK (emb emb< x) e | noemb x₁ = emb emb< (noemb x₁)
ne-elim′ {ι ¹} D neK (emb emb< x) e | emb () x₁
ne-elim′ {∞} D neK (emb ∞< x) e with ne-elim′ D neK x e 
ne-elim′ {∞} D _ (emb ∞< x) e | noemb x₁ = emb ∞< (noemb x₁)
ne-elim′ {∞} D _ (emb ∞< x) e | emb <l x₁ = emb {l′ = ι ¹} ∞< (emb <l x₁)

ne-elim : ∀ {Γ l K r ll} → Neutral K  → Γ ⊩⟨ l ⟩ K ^ [ r , ι ll ] → Γ ⊩⟨ l ⟩ne K ^[ r , ll ]
ne-elim neK [K] = ne-elim′ (id (escape [K])) neK [K] PE.refl

Π-elim′ : ∀ {l A Γ F G rF lF lG r } → Γ ⊢ A ⇒* Π F ^ rF ° lF ▹ G ° lG ^ r → Γ ⊩⟨ l ⟩ A ^ r → Γ ⊩⟨ l ⟩Π A ^ r
Π-elim′ D (Uᵣ′ _ _ _ _ l< PE.refl [[ _ , _ , d ]]) = ⊥-elim (U≢Π (whrDet* (d , Uₙ) (D , Πₙ)))
Π-elim′ D (ℕᵣ D′) = ⊥-elim (ℕ≢Π (whrDet* (red D′ , ℕₙ) (D , Πₙ)))
Π-elim′ D (Emptyᵣ D′) = ⊥-elim (Empty≢Π (whrDet* (red D′ , Emptyₙ) (D , Πₙ)))
Π-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (Π≢ne neK (whrDet* (D , Πₙ) (red D′ , ne neK)))
Π-elim′ D (Πᵣ′ rF lF lG F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  noemb (Πᵣ rF lF lG F G D′ ⊢F ⊢G A≡A [F] [G] G-ext)
Π-elim′ D (∃ᵣ′ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (Π≢∃ (whrDet* (D , Πₙ) (red D′ , ∃ₙ)))
Π-elim′ {ι ¹} D (emb emb< x) with Π-elim′ D x
Π-elim′ {ι ¹} D (emb emb< x) | noemb x₁ = emb emb< (noemb x₁)
Π-elim′ {ι ¹} D (emb emb< x) | emb () x₁
Π-elim′ {∞} D (emb ∞< x) with Π-elim′ D x
Π-elim′ {∞} D (emb ∞< x) | noemb x₁ = emb ∞< (noemb x₁)
Π-elim′ {∞} D (emb ∞< x) | emb <l x₁ = emb {l′ = ι ¹} ∞< (emb <l x₁)

Π-elim : ∀ {Γ F G rF lF lG r l} → Γ ⊩⟨ l ⟩ Π F ^ rF ° lF ▹ G ° lG ^ r → Γ ⊩⟨ l ⟩Π Π F ^ rF ° lF ▹ G ° lG ^ r
Π-elim [Π] = Π-elim′ (id (escape [Π])) [Π]

∃-elim′ : ∀ {l A Γ F G ll} → Γ ⊢ A ⇒* ∃ F ▹ G ^ [ % , ll ] → Γ ⊩⟨ l ⟩ A ^ [ % , ll ] → Γ ⊩⟨ l ⟩∃ A  ^ ll
∃-elim′ D (Emptyᵣ D′) = ⊥-elim (Empty≢∃ (whrDet* (red D′ , Emptyₙ) (D , ∃ₙ)))
∃-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (∃≢ne neK (whrDet* (D , ∃ₙ) (red D′ , ne neK)))
∃-elim′ D (Πᵣ′ rF lF lG F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  ⊥-elim (Π≢∃ (whrDet* (red D′ , Πₙ) (D , ∃ₙ)))
∃-elim′ D (∃ᵣ′ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext) =
  noemb (∃ᵣ F G D′ ⊢F ⊢G A≡A [F] [G] G-ext)
∃-elim′ {ι ¹} D (emb emb< x) with ∃-elim′ D x
∃-elim′ {ι ¹} D (emb emb< x) | noemb x₁ = emb emb< (noemb x₁)
∃-elim′ {ι ¹} D (emb emb< x) | emb () x₁
∃-elim′ {∞} D (emb ∞< x) with ∃-elim′ D x
∃-elim′ {∞} D (emb ∞< x) | noemb x₁ = emb ∞< (noemb x₁)
∃-elim′ {∞} D (emb ∞< x) | emb <l x₁ = emb {l′ = ι ¹} ∞< (emb <l x₁)

∃-elim : ∀ {Γ F G l ll} → Γ ⊩⟨ l ⟩ ∃ F ▹ G ^ [ % , ll ] → Γ ⊩⟨ l ⟩∃ (∃ F ▹ G) ^ ll
∃-elim [∃] = ∃-elim′ (id (escape [∃])) [∃]

-- Extract a type and a level from a maybe embedding
extractMaybeEmb : ∀ {l ⊩⟨_⟩} → MaybeEmb l ⊩⟨_⟩ → ∃ λ l′ → ⊩⟨ l′ ⟩
extractMaybeEmb (noemb x) = _ , x
extractMaybeEmb (emb <l x) = extractMaybeEmb x



-- A view for constructor equality of types where embeddings are ignored
data ShapeView Γ : ∀ l l′ A B r r' (p : Γ ⊩⟨ l ⟩ A ^ r) (q : Γ ⊩⟨ l′ ⟩ B ^ r') → Set where
  Uᵥ : ∀ {A B l l′ ll ll′} UA UB → ShapeView Γ l l′ A B [ ! , ll ] [ ! , ll′ ] (Uᵣ UA) (Uᵣ UB)
  ℕᵥ : ∀ {A B l l′} ℕA ℕB → ShapeView Γ l l′ A B [ ! , ι ⁰ ] [ ! , ι ⁰ ] (ℕᵣ ℕA) (ℕᵣ ℕB)
  Emptyᵥ : ∀ {A B l l′ ll ll'} EmptyA EmptyB → ShapeView Γ l l′ A B [ % , ι ll ] [ % , ι ll' ] (Emptyᵣ EmptyA) (Emptyᵣ EmptyB)
  ne  : ∀ {A B l l′ r lr r' lr'} neA neB
      → ShapeView Γ l l′ A B [ r , ι lr ] [ r' , ι lr' ] (ne neA) (ne neB)
  Πᵥ : ∀ {A B l l′ r r'} ΠA ΠB
    → ShapeView Γ l l′ A B r r' (Πᵣ ΠA) (Πᵣ ΠB)
  ∃ᵥ : ∀ {A B l l′ ll ll'} ∃A ∃B
    → ShapeView Γ l l′ A B [ % , ll ] [ % , ll' ] (∃ᵣ ∃A) (∃ᵣ ∃B)
  emb⁰¹ : ∀ {A B r r' l p q} 
        → ShapeView Γ (ι ⁰) l A B r r' p q
        → ShapeView Γ (ι ¹) l A B r r' (emb emb< p) q
  emb¹⁰ : ∀ {A B r r' l p q}
        → ShapeView Γ l (ι ⁰) A B r r' p q
        → ShapeView Γ l (ι ¹) A B r r' p (emb emb< q)
  emb¹∞ : ∀ {A B r r' l p q} 
        → ShapeView Γ (ι ¹) l A B r r' p q
        → ShapeView Γ ∞ l A B r r' (emb ∞< p) q
  emb∞¹ : ∀ {A B r r' l p q}
        → ShapeView Γ l (ι ¹) A B r r' p q
        → ShapeView Γ l ∞ A B r r' p (emb ∞< q)


-- Construct a shape view from an equality
goodCases : ∀ {l l′ Γ A B r r'} ([A] : Γ ⊩⟨ l ⟩ A ^ r) ([B] : Γ ⊩⟨ l′ ⟩ B ^ r')
          → Γ ⊩⟨ l ⟩ A ≡ B ^ r / [A] → ShapeView Γ l l′ A B r r' [A] [B]
goodCases (Uᵣ UA) (Uᵣ UB) A≡B = Uᵥ UA UB
goodCases (Uᵣ′ _ _ _ _ _ _ ⊢Γ) (ℕᵣ D) D' = ⊥-elim (U≢ℕ (whrDet* (D' ,  Uₙ) (red D , ℕₙ)))
goodCases (Uᵣ′ _ _ _ _ _ _ ⊢Γ) (Emptyᵣ D) D' =  ⊥-elim (U≢Empty (whrDet* (D' ,  Uₙ) (red D , Emptyₙ)))
goodCases (Uᵣ′ _ _ _ _ _ _ ⊢Γ) (ne′ K D neK K≡K) D' = ⊥-elim (U≢ne neK (whrDet* (D' ,  Uₙ) (red D , ne neK))) 
goodCases (Uᵣ′ _ _ _ _ _ _ ⊢Γ) (Πᵣ′ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext) D' =
  ⊥-elim (U≢Π (whrDet* (D' , Uₙ) (red D , Πₙ)))
goodCases (Uᵣ′ _ _ _ _ _ _ ⊢Γ) (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) D' =
  ⊥-elim (U≢∃ (whrDet* (D' , Uₙ) (red D , ∃ₙ)))
goodCases (ℕᵣ D) (Uᵣ′ _ _ _ _ _ _ D') A≡B = ⊥-elim (U≢ℕ (whrDet* (red D' ,  Uₙ) (A≡B , ℕₙ)))
goodCases (ℕᵣ _) (Emptyᵣ D') D =
  ⊥-elim (ℕ≢Empty (whrDet* (D , ℕₙ) (red D' , Emptyₙ)))
goodCases (ℕᵣ ℕA) (ℕᵣ ℕB) A≡B = ℕᵥ ℕA ℕB
goodCases (ℕᵣ D) (ne′ K D₁ neK K≡K) A≡B =
  ⊥-elim (ℕ≢ne neK (whrDet* (A≡B , ℕₙ) (red D₁ , ne neK)))
goodCases (ℕᵣ D) (Πᵣ′ rF lF lG F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B =
  ⊥-elim (ℕ≢Π (whrDet* (A≡B , ℕₙ) (red D₁ , Πₙ)))
goodCases (ℕᵣ D) (∃ᵣ′ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B =
  ⊥-elim (ℕ≢∃ (whrDet* (A≡B , ℕₙ) (red D₁ , ∃ₙ)))
goodCases (Emptyᵣ D) (Uᵣ′ _ _ _ _ _ _ D') A≡B = ⊥-elim (U≢Empty (whrDet* (red D' ,  Uₙ) (A≡B , Emptyₙ)))
goodCases (Emptyᵣ _) (ℕᵣ D') D =
   ⊥-elim (ℕ≢Empty (whrDet* (red D' , ℕₙ) (D , Emptyₙ)))
goodCases (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) A≡B = Emptyᵥ EmptyA EmptyB
goodCases (Emptyᵣ D) (ne′ K D₁ neK K≡K) A≡B =
  ⊥-elim (Empty≢ne neK (whrDet* (A≡B , Emptyₙ) (red D₁ , ne neK)))
goodCases (Emptyᵣ D) (Πᵣ′ rF lF lG F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B =
  ⊥-elim (Empty≢Π (whrDet* (A≡B , Emptyₙ) (red D₁ , Πₙ)))
goodCases (Emptyᵣ D) (∃ᵣ′ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) A≡B =
  ⊥-elim (Empty≢∃ (whrDet* (A≡B , Emptyₙ) (red D₁ , ∃ₙ)))
goodCases (ne′ K D neK K≡K) (Uᵣ′ _ _ _ _ _ _ D') (ne₌ M D'' neM K≡M) =
  ⊥-elim (U≢ne neM (whrDet* (red D' ,  Uₙ) (red D'' , ne neM)))
goodCases (ne′ K D neK K≡K) (ℕᵣ D₁) (ne₌ M D′ neM K≡M) =
  ⊥-elim (ℕ≢ne neM (whrDet* (red D₁ , ℕₙ) (red D′ , ne neM)))
goodCases (ne′ K D neK K≡K) (Emptyᵣ D₁) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Empty≢ne neM (whrDet* (red D₁ , Emptyₙ) (red D′ , ne neM)))
goodCases (ne neA) (ne neB) A≡B = ne neA neB
goodCases (ne′ K D neK K≡K) (Πᵣ′ rF lF lG F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Π≢ne neM (whrDet* (red D₁ , Πₙ) (red D′ , ne neM)))
goodCases (ne′ K D neK K≡K) (∃ᵣ′ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext) (ne₌ M D′ neM K≡M) =
  ⊥-elim (∃≢ne neM (whrDet* (red D₁ , ∃ₙ) (red D′ , ne neM)))
goodCases (Πᵣ′ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ′ _ _ _ _ _ _ D')
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (U≢Π (whrDet* (red D' ,  Uₙ) (D′ , Πₙ)))
goodCases (Πᵣ′ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ℕᵣ D₁)
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (ℕ≢Π (whrDet* (red D₁ , ℕₙ) (D′ , Πₙ)))
goodCases (Πᵣ′ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Emptyᵣ D₁)
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Empty≢Π (whrDet* (red D₁ , Emptyₙ) (D′ , Πₙ)))
goodCases (Πᵣ′ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext) (ne′ K D₁ neK K≡K)
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Π≢ne neK (whrDet* (D′ , Πₙ) (red D₁ , ne neK)))
goodCases (Πᵣ ΠA) (Πᵣ ΠB) A≡B = Πᵥ ΠA ΠB
goodCases (Πᵣ′ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext)
          (∃ᵣ′ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Π≢∃ (whrDet* (D′ , Πₙ) (red D₁ , ∃ₙ)))
goodCases (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Uᵣ′ _ _ _ _ _ _ D')
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
          (Πᵣ′ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext)
          (∃₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Π≢∃ (whrDet* (red D , Πₙ) (D′ , ∃ₙ)))
goodCases (∃ᵣ ∃A) (∃ᵣ ∃B) A≡B = ∃ᵥ ∃A ∃B
goodCases {l} {ι ¹} [A] (emb emb< x) A≡B = emb¹⁰ (goodCases {l} {ι ⁰} [A] x A≡B)
goodCases {l} {∞} [A] (emb ∞< x) A≡B = emb∞¹ (goodCases {l} {ι ¹} [A] x A≡B)
goodCases {ι ¹} {l} (emb emb< x) [B] A≡B = emb⁰¹ (goodCases {ι ⁰} {l} x [B] A≡B)
goodCases {∞} {l} (emb ∞< x) [B] A≡B = emb¹∞ (goodCases {ι ¹} {l} x [B] A≡B)

-- Construct an shape view between two derivations of the same type
goodCasesRefl : ∀ {l l′ Γ A r r'} ([A] : Γ ⊩⟨ l ⟩ A ^ r) ([A′] : Γ ⊩⟨ l′ ⟩ A ^ r')
              → ShapeView Γ l l′ A A r r' [A] [A′]
goodCasesRefl [A] [A′] = goodCases [A] [A′] (reflEq [A])


-- A view for constructor equality between three types
data ShapeView₃ Γ : ∀ l l′ l″ A B C r1 r2 r3
                 (p : Γ ⊩⟨ l   ⟩ A ^ r1)
                 (q : Γ ⊩⟨ l′  ⟩ B ^ r2)
                 (r : Γ ⊩⟨ l″ ⟩ C ^ r3) → Set where
  Uᵥ : ∀ {A B C l l′ l″ ll ll′ ll″ } UA UB UC → ShapeView₃ Γ l l′ l″ A B C [ ! , ll ] [ ! , ll′ ] [ ! , ll″ ]
                                               (Uᵣ UA) (Uᵣ UB) (Uᵣ UC)
  ℕᵥ : ∀ {A B C l l′ l″} ℕA ℕB ℕC
    → ShapeView₃ Γ l l′ l″ A B C [ ! , ι ⁰ ] [ ! , ι ⁰ ] [ ! , ι ⁰ ] (ℕᵣ ℕA) (ℕᵣ ℕB) (ℕᵣ ℕC)
  Emptyᵥ : ∀ {A B C l l′ l″ ll ll′ ll″} EmptyA EmptyB EmptyC
    → ShapeView₃ Γ l l′ l″ A B C [ % , ι ll ] [ % , ι ll′ ] [ % , ι ll″ ] (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) (Emptyᵣ EmptyC)
  ne  : ∀ {A B C r1 r2 r3 l1 l2 l3 l l′ l″} neA neB neC
      → ShapeView₃ Γ l l′ l″ A B C [ r1 , ι l1 ] [ r2 , ι l2 ] [ r3 , ι l3 ] (ne neA) (ne neB) (ne neC)
  Πᵥ : ∀ {A B C r1 r2 r3 l l′ l″} ΠA ΠB ΠC
    → ShapeView₃ Γ l l′ l″ A B C r1 r2 r3 (Πᵣ ΠA) (Πᵣ ΠB) (Πᵣ ΠC)
  ∃ᵥ : ∀ {A B C l l′ l″ ll ll' ll''} ΠA ΠB ΠC
    → ShapeView₃ Γ l l′ l″ A B C [ % , ll ] [ % , ll' ] [ % , ll'' ] (∃ᵣ ΠA) (∃ᵣ ΠB) (∃ᵣ ΠC)
  emb⁰¹¹ : ∀ {A B C l l′ r1 r2 r3 p q r}
         → ShapeView₃ Γ (ι ⁰) l l′ A B C r1 r2 r3 p q r
         → ShapeView₃ Γ (ι ¹) l l′ A B C r1 r2 r3 (emb emb< p) q r
  emb¹⁰¹ : ∀ {A B C l l′ r1 r2 r3  p q r}
         → ShapeView₃ Γ l (ι ⁰) l′ A B C r1 r2 r3 p q r
         → ShapeView₃ Γ l (ι ¹) l′ A B C r1 r2 r3 p (emb emb< q) r
  emb¹¹⁰ : ∀ {A B C l l′ r1 r2 r3 p q r}
         → ShapeView₃ Γ l l′ (ι ⁰) A B C r1 r2 r3 p q r
         → ShapeView₃ Γ l l′ (ι ¹) A B C r1 r2 r3 p q (emb emb< r)
  emb¹∞∞ : ∀ {A B C l l′ r1 r2 r3 p q r}
         → ShapeView₃ Γ (ι ¹) l l′ A B C r1 r2 r3 p q r
         → ShapeView₃ Γ ∞ l l′ A B C r1 r2 r3 (emb ∞< p) q r
  emb∞¹∞ : ∀ {A B C l l′ r1 r2 r3  p q r}
         → ShapeView₃ Γ l (ι ¹) l′ A B C r1 r2 r3 p q r
         → ShapeView₃ Γ l ∞ l′ A B C r1 r2 r3 p (emb ∞< q) r
  emb∞∞¹ : ∀ {A B C l l′ r1 r2 r3 p q r}
         → ShapeView₃ Γ l l′ (ι ¹) A B C r1 r2 r3 p q r
         → ShapeView₃ Γ l l′ ∞ A B C r1 r2 r3 p q (emb ∞< r)


-- Combines two two-way views into a three-way view
combine : ∀ {Γ l l′ l″ l‴ A B C r1 r2 r2' r3 [A] [B] [B]′ [C]}
        → ShapeView Γ l l′ A B r1 r2 [A] [B]
        → ShapeView Γ l″ l‴ B C r2' r3 [B]′ [C]
        → ShapeView₃ Γ l l′ l‴ A B C r1 r2 r3 [A] [B] [C]
combine (Uᵥ UA UB) (Uᵥ UB' UC) = Uᵥ UA UB UC
combine (Uᵥ UA (Uᵣ r l′ l< PE.refl D)) (ℕᵥ ℕA ℕB) = 
 ⊥-elim (U≢ℕ (whrDet* (red D ,  Uₙ) (red  ℕA , ℕₙ))) 
combine (Uᵥ UA (Uᵣ r l′ l< PE.refl D)) (Emptyᵥ EmptyA EmptyB) =
 ⊥-elim (U≢Empty (whrDet* (red D ,  Uₙ) (red  EmptyA , Emptyₙ))) 
combine (Uᵥ UA (Uᵣ r l′ l< PE.refl D)) (ne (ne K D' neK K≡K) neB) = 
  ⊥-elim (U≢ne neK (whrDet* (red D ,  Uₙ) (red  D' , ne neK)))
combine (Uᵥ UA (Uᵣ r l′ l< PE.refl D)) (Πᵥ (Πᵣ rF lF lG F G D' ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) =
 ⊥-elim (U≢Π (whrDet* (red D ,  Uₙ) (red  D' , Πₙ))) 
combine (Uᵥ UA (Uᵣ r l′ l< PE.refl D)) (∃ᵥ (∃ᵣ F G D' ⊢F ⊢G A≡A [F] [G] G-ext) ∃B) =
 ⊥-elim (U≢∃ (whrDet* (red D ,  Uₙ) (red  D' , ∃ₙ))) 
combine  (ℕᵥ ℕA ℕB) (Uᵥ (Uᵣ r l′ l< PE.refl D) UB) = 
 ⊥-elim (U≢ℕ (whrDet* (red D ,  Uₙ) (red  ℕB , ℕₙ))) 
combine  (ℕᵥ ℕA ℕB) (Emptyᵥ EmptyA EmptyB) =
   ⊥-elim (ℕ≢Empty (whrDet* (red ℕB , ℕₙ) (red EmptyA , Emptyₙ)))
combine  (ℕᵥ ℕA₁ ℕB₁) (ℕᵥ ℕA ℕB) = ℕᵥ ℕA₁ ℕB₁ ℕB
combine  (ℕᵥ ℕA ℕB) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (ℕ≢ne neK (whrDet* (red ℕB , ℕₙ) (red D , ne neK)))
combine  (ℕᵥ ℕA ℕB) (Πᵥ (Πᵣ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) =
  ⊥-elim (ℕ≢Π (whrDet* (red ℕB , ℕₙ) (red D , Πₙ)))
combine  (ℕᵥ ℕA ℕB) (∃ᵥ (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) ∃B) =
  ⊥-elim (ℕ≢∃ (whrDet* (red ℕB , ℕₙ) (red D , ∃ₙ)))
combine  (Emptyᵥ EmptyA EmptyB) (Uᵥ (Uᵣ r l′ l< PE.refl D) UB) = 
 ⊥-elim (U≢Empty (whrDet* (red D ,  Uₙ) (red  EmptyB , Emptyₙ))) 
combine  (Emptyᵥ EmptyA EmptyB) (ℕᵥ ℕA ℕB) =
   ⊥-elim (Empty≢ℕ (whrDet* (red EmptyB , Emptyₙ) (red ℕA , ℕₙ)))
combine  (Emptyᵥ EmptyA₁ EmptyB₁) (Emptyᵥ EmptyA EmptyB) = Emptyᵥ EmptyA₁ EmptyB₁ EmptyB
combine  (Emptyᵥ EmptyA EmptyB) (ne (ne K D neK K≡K) neB) =
   ⊥-elim (Empty≢ne neK (whrDet* (red EmptyB , Emptyₙ) (red D , ne neK)))
combine  (Emptyᵥ EmptyA EmptyB) (Πᵥ (Πᵣ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) =
   ⊥-elim (Empty≢Π (whrDet* (red EmptyB , Emptyₙ) (red D , Πₙ)))
combine  (Emptyᵥ EmptyA EmptyB) (∃ᵥ (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) ∃B) =
   ⊥-elim (Empty≢∃ (whrDet* (red EmptyB , Emptyₙ) (red D , ∃ₙ)))
combine  (ne neA (ne K D' neK K≡K)) (Uᵥ (Uᵣ r l′ l< PE.refl D) UB) =
  ⊥-elim (U≢ne neK (whrDet* (red D ,  Uₙ) (red  D' , ne neK)))
combine  (ne neA (ne K D neK K≡K)) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢ne neK (whrDet* (red ℕA , ℕₙ) (red D , ne neK)))
combine  (ne neA (ne K D neK K≡K)) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢ne neK (whrDet* (red EmptyA , Emptyₙ) (red D , ne neK)))
combine  (ne neA₁ neB₁) (ne neA neB) = ne neA₁ neB₁ neB
combine  (ne neA (ne K D₁ neK K≡K)) (Πᵥ (Πᵣ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext) ΠB) =
  ⊥-elim (Π≢ne neK (whrDet* (red D , Πₙ) (red D₁ , ne neK)))
combine  (ne neA (ne K D₁ neK K≡K)) (∃ᵥ (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext) ∃B) =
  ⊥-elim (∃≢ne neK (whrDet* (red D , ∃ₙ) (red D₁ , ne neK)))
combine  (Πᵥ ΠA (Πᵣ rF lF lG F G D' ⊢F ⊢G A≡A [F] [G] G-ext)) (Uᵥ (Uᵣ r l′ l< PE.refl D) UB) =
 ⊥-elim (U≢Π (whrDet* (red D ,  Uₙ) (red  D' , Πₙ))) 
combine  (Πᵥ ΠA (Πᵣ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢Π (whrDet* (red ℕA , ℕₙ) (red D , Πₙ)))
combine  (Πᵥ ΠA (Πᵣ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢Π (whrDet* (red EmptyA , Emptyₙ) (red D , Πₙ)))
combine  (Πᵥ ΠA (Πᵣ rF lF lG F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext)) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (Π≢ne neK (whrDet* (red D₁ , Πₙ) (red D , ne neK)))
combine  (Πᵥ ΠA₁ ΠB₁) (Πᵥ ΠA ΠB) = Πᵥ ΠA₁ ΠB₁ ΠB
combine  (Πᵥ ΠA (Πᵣ rF lF lG F G D ⊢F ⊢G A≡A [F] [G] G-ext))
        (∃ᵥ (∃ᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) ∃B) =
  ⊥-elim (Π≢∃ (whrDet* (red D , Πₙ) (red D₁ , ∃ₙ)))
combine  (∃ᵥ ∃A (∃ᵣ F G D' ⊢F ⊢G A≡A [F] [G] G-ext)) (Uᵥ (Uᵣ r l′ l< PE.refl D) UB) = 
 ⊥-elim (U≢∃ (whrDet* (red D ,  Uₙ) (red  D' , ∃ₙ))) 
combine  (∃ᵥ ∃A (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢∃ (whrDet* (red ℕA , ℕₙ) (red D , ∃ₙ)))
combine  (∃ᵥ ∃A (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢∃ (whrDet* (red EmptyA , Emptyₙ) (red D , ∃ₙ)))
combine  (∃ᵥ ∃A (∃ᵣ F G D₁ ⊢F ⊢G A≡A [F] [G] G-ext)) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (∃≢ne neK (whrDet* (red D₁ , ∃ₙ) (red D , ne neK)))
combine  (∃ᵥ ΠA (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext))
        (Πᵥ (Πᵣ rF₁ lF₁ lG₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) ∃B) =
  ⊥-elim (Π≢∃ (whrDet* (red D₁ , Πₙ) (red D , ∃ₙ)))
combine  (∃ᵥ ∃A ∃B) (∃ᵥ ∃A₁ ∃B₁) = ∃ᵥ ∃A ∃B ∃B₁
combine (emb⁰¹ [AB]) [BC] = emb⁰¹¹ (combine [AB] [BC])
combine (emb¹⁰ [AB]) [BC] = emb¹⁰¹ (combine [AB] [BC])
combine [AB] (emb⁰¹ [BC]) = combine [AB] [BC]
combine [AB] (emb¹⁰ [BC]) = emb¹¹⁰ (combine [AB] [BC])
combine (emb¹∞ [AB]) [BC] = emb¹∞∞ (combine [AB] [BC])
combine (emb∞¹ [AB]) [BC] = emb∞¹∞ (combine [AB] [BC])
combine [AB] (emb¹∞ [BC]) = combine [AB] [BC]
combine [AB] (emb∞¹ [BC]) = emb∞∞¹ (combine [AB] [BC])
