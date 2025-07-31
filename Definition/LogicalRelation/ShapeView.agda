{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.ShapeView {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U
open import Definition.Typed
open import Definition.Typed.Weakening
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

_⊩⟨_⟩Empty_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → Set
Γ ⊩⟨ l ⟩Empty A = MaybeEmb l (λ l′ → Γ ⊩Empty A)

_⊩⟨_⟩ne_^[_,_] : (Γ : Con Term) (l : TypeLevel) (A : Term) (r : Relevance) (ll : Level) → Set
Γ ⊩⟨ l ⟩ne A ^[ r , ll ] = MaybeEmb l (λ l′ → Γ ⊩ne A ^[ r , ll ])

_⊩⟨_⟩Π_^[_] : (Γ : Con Term) (l : TypeLevel) (A : Term) → Level → Set
Γ ⊩⟨ l ⟩Π A ^[ lΠ ] = MaybeEmb l (λ l′ → Γ ⊩′⟨ l′ ⟩Π A ^[ lΠ ])

_⊩⟨_⟩Πirr_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → Set
Γ ⊩⟨ l ⟩Πirr A = MaybeEmb l (λ l′ → Γ ⊩Πirr A)

_⊩⟨_⟩Id_ : (Γ : Con Term) (l : TypeLevel) (A : Term) → Set
Γ ⊩⟨ l ⟩Id A = MaybeEmb l (λ l′ → Γ ⊩Id A)

-- Construct a general reducible type from a specific

U-intr : ∀ {l Γ A ll } → (UA : Γ ⊩⟨ l ⟩U A ^ ll) → Γ ⊩⟨ l ⟩ A ^ [ ! , ll ]
U-intr (noemb UA) = Uᵣ UA
U-intr {l = ι ¹} (emb emb< x) = emb emb< (U-intr x)
U-intr {l = ∞}  (emb ∞< x) = emb ∞< (U-intr x)

ℕ-intr : ∀ {l A Γ} → Γ ⊩⟨ l ⟩ℕ A → Γ ⊩⟨ l ⟩ A ^ [ ! , ι ⁰ ]
ℕ-intr (noemb x) = ℕᵣ x
ℕ-intr {l = ι ¹} (emb emb< x) = emb emb< (ℕ-intr x)
ℕ-intr {l = ∞}  (emb ∞< x) = emb ∞< (ℕ-intr x)

Empty-intr : ∀ {l A Γ} → Γ ⊩⟨ l ⟩Empty A → Γ ⊩⟨ l ⟩ A ^ [ % , ι ⁰ ]
Empty-intr (noemb x) = Emptyᵣ x
Empty-intr {l = ι ¹} (emb emb< x) = emb emb< (Empty-intr x)
Empty-intr {l = ∞}  (emb ∞< x) = emb ∞< (Empty-intr x)

ne-intr : ∀ {l A Γ r ll} → Γ ⊩⟨ l ⟩ne A ^[ r , ll ] → Γ ⊩⟨ l ⟩ A ^ [ r , ι ll ]
ne-intr (noemb x) = ne x
ne-intr {l = ι ¹} (emb emb< x) = emb emb< (ne-intr x)
ne-intr {l = ∞}  (emb ∞< x) = emb ∞< (ne-intr x)

Π-intr : ∀ {l A Γ ll} → Γ ⊩⟨ l ⟩Π A ^[ ll ]  → Γ ⊩⟨ l ⟩ A ^ [ ! , ι ll ]
Π-intr (noemb x) = Πᵣ x
Π-intr {l = ι ¹} (emb emb< x) = emb emb< (Π-intr x)
Π-intr {l = ∞}  (emb ∞< x) = emb ∞< (Π-intr x)

Πirr-intr : ∀ {l A Γ} → Γ ⊩⟨ l ⟩Πirr A → Γ ⊩⟨ l ⟩ A ^ [ % , ι ⁰ ]
Πirr-intr (noemb x) = Πirrᵣ x
Πirr-intr {l = ι ¹} (emb emb< x) = emb emb< (Πirr-intr x)
Πirr-intr {l = ∞}  (emb ∞< x) = emb ∞< (Πirr-intr x)

Id-intr : ∀ {l A Γ} → Γ ⊩⟨ l ⟩Id A → Γ ⊩⟨ l ⟩ A ^ [ % , ι ⁰ ]
Id-intr (noemb x) = Idᵣ x
Id-intr {l = ι ¹} (emb emb< x) = emb emb< (Id-intr x)
Id-intr {l = ∞}  (emb ∞< x) = emb ∞< (Id-intr x)


-- Construct a specific reducible type from a general with some criterion

U-elim′ : ∀ {l Γ A r l′ ll} → Γ ⊢ A ⇒* Univ r l′ ^ [ ! , ll ] → Γ ⊩⟨ l ⟩ A ^ [ ! , ll ] → Γ ⊩⟨ l ⟩U A ^ ll
U-elim′ D (Uᵣ′ A ll r l l< e D') = noemb (Uᵣ r l l< e D')
U-elim′ D (ℕᵣ D') =  ⊥-elim (U≢ℕ (whrDet* (D ,  Uₙ) (red D' , ℕₙ)))
U-elim′ D (ne′ K D' neK K≡K) =  ⊥-elim (U≢ne neK (whrDet* (D ,  Uₙ) (red D' , ne neK))) 
U-elim′ D (Πᵣ′ rF lF lG _ _ F G D' ⊢F ⊢G A≡A [F] [G]) = ⊥-elim (U≢Π (whrDet* (D , Uₙ) (red D' , Πₙ)))
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
ℕ-elim′ D (Πᵣ′ rF lF lG _ _ F G D′ ⊢F ⊢G A≡A [F] [G]) =
  ⊥-elim (ℕ≢Π (whrDet* (D , ℕₙ) (red D′ , Πₙ)))
ℕ-elim′ {ι ¹} D (emb emb< x) with ℕ-elim′ D x
ℕ-elim′ {ι ¹} D (emb emb< x) | noemb x₁ = emb emb< (noemb x₁)
ℕ-elim′ {ι ¹} D (emb emb< x) | emb () x₁
ℕ-elim′ {∞} D (emb ∞< x) with ℕ-elim′ D x
ℕ-elim′ {∞} D (emb ∞< x) | noemb x₁ = emb ∞< (noemb x₁)
ℕ-elim′ {∞} D (emb ∞< x) | emb <l x₁ = emb {l′ = ι ¹} ∞< (emb <l x₁)

ℕ-elim : ∀ {Γ l ll } → Γ ⊩⟨ l ⟩ ℕ ^ [ ! , ll ] → Γ ⊩⟨ l ⟩ℕ ℕ
ℕ-elim [ℕ] = ℕ-elim′ (id (escape [ℕ])) [ℕ]


Empty-elim′ : ∀ {l A Γ} → Γ ⊢ A ⇒* Empty ⁰ ^ [ % , ι ⁰ ] → Γ ⊩⟨ l ⟩ A ^ [ % , ι ⁰ ] → Γ ⊩⟨ l ⟩Empty A
Empty-elim′ D (Emptyᵣ D′) = noemb D′
Empty-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (Empty≢ne neK (whrDet* (D , Emptyₙ) (red D′ , ne neK)))
Empty-elim′ D (Πirrᵣ′ rF lF F G D′ ⊢F ⊢G A≡A) =
  ⊥-elim (Empty≢Π (whrDet* (D , Emptyₙ) (red D′ , Πₙ)))
Empty-elim′ D (Idᵣ′ F G _ _ D′ ⊢F ⊢G _ A≡A) =
  ⊥-elim (Empty≢Id (whrDet* (D , Emptyₙ) (red D′ , Idₙ)))
Empty-elim′ {ι ¹} D (emb emb< x) with Empty-elim′ D x
Empty-elim′ {ι ¹} D (emb emb< x) | noemb x₁ = emb emb< (noemb x₁)
Empty-elim′ {ι ¹} D (emb emb< x) | emb () x₁
Empty-elim′ {∞} D (emb ∞< x) with Empty-elim′ D x
Empty-elim′ {∞} D (emb ∞< x) | noemb x₁ = emb ∞< (noemb x₁)
Empty-elim′ {∞} D (emb ∞< x) | emb <l x₁ = emb {l′ = ι ¹} ∞< (emb <l x₁)

Empty-elim : ∀ {Γ l} → Γ ⊩⟨ l ⟩ Empty ⁰ ^ [ % , ι ⁰ ] → Γ ⊩⟨ l ⟩Empty Empty ⁰
Empty-elim [Empty] = Empty-elim′ (id (escape [Empty])) [Empty]

ne-elim′ : ∀ {l A Γ K r ll ll'} → Γ ⊢ A ⇒* K ^ [ r , ι ll ] → Neutral K → Γ ⊩⟨ l ⟩ A ^ [ r , ll' ] → ι ll PE.≡  ll' → Γ ⊩⟨ l ⟩ne A ^[ r , ll ]
ne-elim′ D neK (Uᵣ′ _ _ _ _ l< PE.refl [[ _ , _ , d ]]) e = ⊥-elim (U≢ne neK (whrDet* (d , Uₙ) (D , ne neK)))
ne-elim′ D neK (ℕᵣ D′) e = ⊥-elim (ℕ≢ne neK (whrDet* (red D′ , ℕₙ) (D , ne neK)))
ne-elim′ D neK (ne (ne K D′ neK′ K≡K)) PE.refl = noemb (ne K D′ neK′ K≡K) 
ne-elim′ D neK (Πᵣ′ rF lF lG _ _ F G D′ ⊢F ⊢G A≡A [F] [G]) e =
  ⊥-elim (Π≢ne neK (whrDet* (red D′ , Πₙ) (D , ne neK)))
ne-elim′ D neK (Πirrᵣ′ rF lF F G D′ ⊢F ⊢G A≡A) e =
  ⊥-elim (Π≢ne neK (whrDet* (red D′ , Πₙ) (D , ne neK)))
ne-elim′ D neK (Idᵣ′ F G _ _ D′ ⊢F ⊢G _ A≡A) e =
  ⊥-elim (Id≢ne neK (whrDet* (red D′ , Idₙ) (D , ne neK)))
ne-elim′ D neK (Emptyᵣ D′) e = ⊥-elim (Empty≢ne neK (whrDet* (red D′ , Emptyₙ) (D , ne neK)))
ne-elim′ {ι ¹} D neK (emb emb< x) e with ne-elim′ D neK x e
ne-elim′ {ι ¹} D neK (emb emb< x) e | noemb x₁ = emb emb< (noemb x₁)
ne-elim′ {ι ¹} D neK (emb emb< x) e | emb () x₁
ne-elim′ {∞} D neK (emb ∞< x) e with ne-elim′ D neK x e 
ne-elim′ {∞} D _ (emb ∞< x) e | noemb x₁ = emb ∞< (noemb x₁)
ne-elim′ {∞} D _ (emb ∞< x) e | emb <l x₁ = emb {l′ = ι ¹} ∞< (emb <l x₁)

ne-elim : ∀ {Γ l K r ll} → Neutral K  → Γ ⊩⟨ l ⟩ K ^ [ r , ι ll ] → Γ ⊩⟨ l ⟩ne K ^[ r , ll ]
ne-elim neK [K] = ne-elim′ (id (escape [K])) neK [K] PE.refl

Π-elim′ : ∀ {l A Γ F G rF lF lG lΠ} → Γ ⊢ A ⇒* Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ ! ^ [ ! , ι lΠ ] → Γ ⊩⟨ l ⟩ A ^ [ ! , ι lΠ ]  → Γ ⊩⟨ l ⟩Π A ^[ lΠ ]
Π-elim′ D (Uᵣ′ _ _ _ _ l< X [[ _ , _ , d ]]) = ⊥-elim (U≢Π (whrDet* (d , Uₙ) (D , Πₙ)))
Π-elim′ D (ℕᵣ D′) = ⊥-elim (ℕ≢Π (whrDet* (red D′ , ℕₙ) (D , Πₙ)))
Π-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (Π≢ne neK (whrDet* (D , Πₙ) (red D′ , ne neK)))
Π-elim′ D (Πᵣ′ rF lF lG lF≤ lG≤ F G D′ ⊢F ⊢G A≡A [F] [G]) =
  noemb (Πᵣ rF lF lG lF≤ lG≤ F G D′ ⊢F ⊢G A≡A [F] [G])
Π-elim′ {ι ¹} D (emb emb< x) with Π-elim′ D x
Π-elim′ {ι ¹} D (emb emb< x) | noemb x₁ = emb emb< (noemb x₁)
Π-elim′ {ι ¹} D (emb emb< x) | emb () x₁
Π-elim′ {∞} D (emb ∞< x) with Π-elim′ D x
Π-elim′ {∞} D (emb ∞< x) | noemb x₁ = emb ∞< (noemb x₁)
Π-elim′ {∞} D (emb ∞< x) | emb <l x₁ = emb {l′ = ι ¹} ∞< (emb <l x₁)

Π-elim : ∀ {Γ F G rF lF lG lΠ l} → Γ ⊩⟨ l ⟩ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ ! ^ [ ! , ι lΠ ] → Γ ⊩⟨ l ⟩Π Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ ! ^[ lΠ ]
Π-elim [Π] = Π-elim′ (id (escape [Π])) [Π]

Πirr-elim′ : ∀ {l A Γ F G rF lF} → Γ ⊢ A ⇒* Π F ^ rF ° lF ▹ G ° ⁰ ° ⁰  ^ % ^ [ % , ι ⁰ ] → Γ ⊩⟨ l ⟩ A ^ [ % , ι ⁰ ]  → Γ ⊩⟨ l ⟩Πirr A 
Πirr-elim′ D (Emptyᵣ D′) = ⊥-elim (Empty≢Π (whrDet* (red D′ , Emptyₙ) (D , Πₙ)))
Πirr-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (Π≢ne neK (whrDet* (D , Πₙ) (red D′ , ne neK)))
Πirr-elim′ D (Πirrᵣ′ rF lF F G D′ ⊢F ⊢G A≡A) =
  noemb (Πirrᵣ rF lF F G D′ ⊢F ⊢G A≡A)
Πirr-elim′ D (Idᵣ′ F G _ _ D′ ⊢F ⊢G _ A≡A) = ⊥-elim (Π≢Id (whrDet* (D , Πₙ) (red D′ , Idₙ)))
Πirr-elim′ {ι ¹} D (emb emb< x) with Πirr-elim′ D x
Πirr-elim′ {ι ¹} D (emb emb< x) | noemb x₁ = emb emb< (noemb x₁)
Πirr-elim′ {ι ¹} D (emb emb< x) | emb () x₁
Πirr-elim′ {∞} D (emb ∞< x) with Πirr-elim′ D x
Πirr-elim′ {∞} D (emb ∞< x) | noemb x₁ = emb ∞< (noemb x₁)
Πirr-elim′ {∞} D (emb ∞< x) | emb <l x₁ = emb {l′ = ι ¹} ∞< (emb <l x₁)

Πirr-elim : ∀ {Γ F G rF lF l} → Γ ⊩⟨ l ⟩ Π F ^ rF ° lF ▹ G ° ⁰ ° ⁰ ^ % ^ [ % , ι ⁰ ] → Γ ⊩⟨ l ⟩Πirr Π F ^ rF ° lF ▹ G ° ⁰ ° ⁰ ^ %
Πirr-elim [Π] = Πirr-elim′ (id (escape [Π])) [Π]


Id-elim′ : ∀ {l A Γ F t u} → Γ ⊢ A ⇒* Id F t u ^ [ % , ι ⁰ ] → Γ ⊩⟨ l ⟩ A ^ [ % , ι ⁰ ] → Γ ⊩⟨ l ⟩Id A
Id-elim′ D (Emptyᵣ D′) = ⊥-elim (Empty≢Id (whrDet* (red D′ , Emptyₙ) (D , Idₙ)))
Id-elim′ D (ne′ K D′ neK K≡K) =
  ⊥-elim (Id≢ne neK (whrDet* (D , Idₙ) (red D′ , ne neK)))
Id-elim′ D (Πirrᵣ′ rF lF F G D′ ⊢F ⊢G A≡A) =
  ⊥-elim (Π≢Id (whrDet* (red D′ , Πₙ) (D , Idₙ)))
Id-elim′ D (Idᵣ′ F t u l D′ ⊢F ⊢t ⊢u A≡A) = noemb (Idᵣ F t u l D′ ⊢F ⊢t ⊢u A≡A)
Id-elim′ {ι ¹} D (emb emb< x) with Id-elim′ D x
Id-elim′ {ι ¹} D (emb emb< x) | noemb x₁ = emb emb< (noemb x₁)
Id-elim′ {ι ¹} D (emb emb< x) | emb () x₁
Id-elim′ {∞} D (emb ∞< x) with Id-elim′ D x
Id-elim′ {∞} D (emb ∞< x) | noemb x₁ = emb ∞< (noemb x₁)
Id-elim′ {∞} D (emb ∞< x) | emb <l x₁ = emb {l′ = ι ¹} ∞< (emb <l x₁)

Id-elim : ∀ {Γ F t u l} → Γ ⊩⟨ l ⟩ Id F t u ^ [ % , ι ⁰ ] → Γ ⊩⟨ l ⟩Id (Id F t u)
Id-elim [Id] = Id-elim′ (id (escape [Id])) [Id]

-- Extract a type and a level from a maybe embedding
extractMaybeEmb : ∀ {l ⊩⟨_⟩} → MaybeEmb l ⊩⟨_⟩ → ∃ λ l′ → ⊩⟨ l′ ⟩
extractMaybeEmb (noemb x) = _ , x
extractMaybeEmb (emb <l x) = extractMaybeEmb x



-- A view for constructor equality of types where embeddings are ignored
data ShapeView Γ : ∀ l l′ A B r r' (p : Γ ⊩⟨ l ⟩ A ^ r) (q : Γ ⊩⟨ l′ ⟩ B ^ r') → Set where
  Uᵥ : ∀ {A B l l′ ll ll′} UA UB → ShapeView Γ l l′ A B [ ! , ll ] [ ! , ll′ ] (Uᵣ UA) (Uᵣ UB)
  ℕᵥ : ∀ {A B l l′} ℕA ℕB → ShapeView Γ l l′ A B [ ! , ι ⁰ ] [ ! , ι ⁰ ] (ℕᵣ ℕA) (ℕᵣ ℕB)
  Emptyᵥ : ∀ {A B l l′} EmptyA EmptyB → ShapeView Γ l l′ A B [ % , ι ⁰ ] [ % , ι ⁰ ] (Emptyᵣ EmptyA) (Emptyᵣ EmptyB)
  ne  : ∀ {A B l l′ r lr r' lr'} neA neB
      → ShapeView Γ l l′ A B [ r , ι lr ] [ r' , ι lr' ] (ne neA) (ne neB)
  Πᵥ : ∀ {A B l l′ lΠ lΠ' } ΠA ΠB
    → ShapeView Γ l l′ A B [ ! , ι lΠ ] [ ! , ι lΠ' ] (Πᵣ ΠA) (Πᵣ ΠB)
  ΠΠirrᵥ : ∀ {A B l l′ lΠ } ΠA ΠB
    → ShapeView Γ l l′ A B [ ! , ι lΠ ] [ % , ι ⁰ ] (Πᵣ ΠA) (Πirrᵣ ΠB)
  ΠirrΠᵥ : ∀ {A B l l′ lΠ } ΠA ΠB
    → ShapeView Γ l l′ A B [ % , ι ⁰ ] [ ! , ι lΠ ] (Πirrᵣ ΠA) (Πᵣ ΠB)
  Πirrᵥ : ∀ {A B l l′} ΠA ΠB
    → ShapeView Γ l l′ A B [ % , ι ⁰ ] [ % , ι ⁰ ] (Πirrᵣ ΠA) (Πirrᵣ ΠB)
  Idᵥ : ∀ {A B l l′} IdA IdB
    → ShapeView Γ l l′ A B [ % , ι ⁰ ] [ % , ι ⁰ ] (Idᵣ IdA) (Idᵣ IdB)
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
goodCases (Uᵣ′ _ _ _ _ _ _ ⊢Γ) (Πᵣ′ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G]) D' =
  ⊥-elim (U≢Π (whrDet* (D' , Uₙ) (red D , Πₙ)))
goodCases (Uᵣ′ _ _ _ _ _ _ ⊢Γ) (Πirrᵣ′ rF lF F G D ⊢F ⊢G A≡A) D' =
  ⊥-elim (U≢Π (whrDet* (D' , Uₙ) (red D , Πₙ)))
goodCases (Uᵣ′ _ _ _ _ _ _ ⊢Γ) (Idᵣ′ F G _ _ D ⊢F ⊢G _ A≡A) D' =
  ⊥-elim (U≢Id (whrDet* (D' , Uₙ) (red D , Idₙ)))
goodCases (ℕᵣ D) (Uᵣ′ _ _ _ _ _ _ D') A≡B = ⊥-elim (U≢ℕ (whrDet* (red D' ,  Uₙ) (A≡B , ℕₙ)))
goodCases (ℕᵣ _) (Emptyᵣ D') D =
  ⊥-elim (ℕ≢Empty (whrDet* (D , ℕₙ) (red D' , Emptyₙ)))
goodCases (ℕᵣ ℕA) (ℕᵣ ℕB) A≡B = ℕᵥ ℕA ℕB
goodCases (ℕᵣ D) (ne′ K D₁ neK K≡K) A≡B =
  ⊥-elim (ℕ≢ne neK (whrDet* (A≡B , ℕₙ) (red D₁ , ne neK)))
goodCases (ℕᵣ D) (Πᵣ′ rF lF lG _ _ F G D₁ ⊢F ⊢G A≡A [F] [G]) A≡B =
  ⊥-elim (ℕ≢Π (whrDet* (A≡B , ℕₙ) (red D₁ , Πₙ)))
goodCases (ℕᵣ D) (Πirrᵣ′ rF lF F G D₁ ⊢F ⊢G A≡A) A≡B =
  ⊥-elim (ℕ≢Π (whrDet* (A≡B , ℕₙ) (red D₁ , Πₙ)))
goodCases (ℕᵣ D) (Idᵣ′ F G _ _ D₁ ⊢F ⊢G _ A≡A) A≡B =
  ⊥-elim (ℕ≢Id (whrDet* (A≡B , ℕₙ) (red D₁ , Idₙ)))
goodCases (Emptyᵣ D) (Uᵣ′ _ _ _ _ _ _ D') A≡B = ⊥-elim (U≢Empty (whrDet* (red D' ,  Uₙ) (A≡B , Emptyₙ)))
goodCases (Emptyᵣ _) (ℕᵣ D') D =
   ⊥-elim (ℕ≢Empty (whrDet* (red D' , ℕₙ) (D , Emptyₙ)))
goodCases (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) A≡B = Emptyᵥ EmptyA EmptyB
goodCases (Emptyᵣ D) (ne′ K D₁ neK K≡K) A≡B =
  ⊥-elim (Empty≢ne neK (whrDet* (A≡B , Emptyₙ) (red D₁ , ne neK)))
goodCases (Emptyᵣ D) (Πᵣ′ rF lF lG _ _ F G D₁ ⊢F ⊢G A≡A [F] [G]) A≡B =
  ⊥-elim (Empty≢Π (whrDet* (A≡B , Emptyₙ) (red D₁ , Πₙ)))
goodCases (Emptyᵣ D) (Πirrᵣ′ rF lF F G D₁ ⊢F ⊢G A≡A) A≡B =
  ⊥-elim (Empty≢Π (whrDet* (A≡B , Emptyₙ) (red D₁ , Πₙ)))
goodCases (Emptyᵣ D) (Idᵣ′ F G _ _ D₁ ⊢F ⊢G _ A≡A) A≡B =
  ⊥-elim (Empty≢Id (whrDet* (A≡B , Emptyₙ) (red D₁ , Idₙ)))
goodCases (ne′ K D neK K≡K) (Uᵣ′ _ _ _ _ _ _ D') (ne₌ M D'' neM K≡M) =
  ⊥-elim (U≢ne neM (whrDet* (red D' ,  Uₙ) (red D'' , ne neM)))
goodCases (ne′ K D neK K≡K) (ℕᵣ D₁) (ne₌ M D′ neM K≡M) =
  ⊥-elim (ℕ≢ne neM (whrDet* (red D₁ , ℕₙ) (red D′ , ne neM)))
goodCases (ne′ K D neK K≡K) (Emptyᵣ D₁) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Empty≢ne neM (whrDet* (red D₁ , Emptyₙ) (red D′ , ne neM)))
goodCases (ne neA) (ne neB) A≡B = ne neA neB
goodCases (ne′ K D neK K≡K) (Πᵣ′ rF lF lG _ _ F G D₁ ⊢F ⊢G A≡A [F] [G]) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Π≢ne neM (whrDet* (red D₁ , Πₙ) (red D′ , ne neM)))
goodCases (ne′ K D neK K≡K) (Πirrᵣ′ rF lF F G D₁ ⊢F ⊢G A≡A) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Π≢ne neM (whrDet* (red D₁ , Πₙ) (red D′ , ne neM)))
goodCases (ne′ K D neK K≡K) (Idᵣ′ F G _ _ D₁ ⊢F ⊢G _ A≡A) (ne₌ M D′ neM K≡M) =
  ⊥-elim (Id≢ne neM (whrDet* (red D₁ , Idₙ) (red D′ , ne neM)))
goodCases (Πᵣ′ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G]) (Uᵣ′ _ _ _ _ _ _ D')
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (U≢Π (whrDet* (red D' ,  Uₙ) (D′ , Πₙ)))
goodCases (Πᵣ′ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G]) (ℕᵣ D₁)
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (ℕ≢Π (whrDet* (red D₁ , ℕₙ) (D′ , Πₙ)))
goodCases (Πᵣ′ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G]) (Emptyᵣ D₁)
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Empty≢Π (whrDet* (red D₁ , Emptyₙ) (D′ , Πₙ)))
goodCases (Πᵣ′ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G]) (ne′ K D₁ neK K≡K)
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Π≢ne neK (whrDet* (D′ , Πₙ) (red D₁ , ne neK)))
goodCases (Πᵣ ΠA) (Πᵣ ΠB) A≡B = Πᵥ ΠA ΠB
goodCases (Πᵣ ΠA) (Πirrᵣ ΠB) A≡B = ΠΠirrᵥ ΠA ΠB
goodCases (Πirrᵣ ΠA) (Πᵣ ΠB) A≡B = ΠirrΠᵥ ΠA ΠB
goodCases (Πᵣ′ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G])
          (Idᵣ′ F₁ G₁ _ _ D₁ ⊢F₁ ⊢G₁ _ A≡A₁)
          (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ⊥-elim (Π≢Id (whrDet* (D′ , Πₙ) (red D₁ , Idₙ)))
goodCases (Πirrᵣ′ rF lF F G D ⊢F ⊢G A≡A) (Uᵣ′ _ _ _ _ _ _ D')
          (Πirr₌ F′ G′ D′ A≡B) =
  ⊥-elim (U≢Π (whrDet* (red D' ,  Uₙ) (D′ , Πₙ)))
goodCases (Πirrᵣ′ rF lF F G D ⊢F ⊢G A≡A) (ℕᵣ D₁)
          (Πirr₌ F′ G′ D′ A≡B) =
  ⊥-elim (ℕ≢Π (whrDet* (red D₁ , ℕₙ) (D′ , Πₙ)))
goodCases (Πirrᵣ′ rF lF F G D ⊢F ⊢G A≡A) (Emptyᵣ D₁)
          (Πirr₌ F′ G′ D′ A≡B) =
  ⊥-elim (Empty≢Π (whrDet* (red D₁ , Emptyₙ) (D′ , Πₙ)))
goodCases (Πirrᵣ′ rF lF F G D ⊢F ⊢G A≡A) (ne′ K D₁ neK K≡K)
          (Πirr₌ F′ G′ D′ A≡B) =
  ⊥-elim (Π≢ne neK (whrDet* (D′ , Πₙ) (red D₁ , ne neK)))
goodCases (Πirrᵣ ΠA) (Πirrᵣ ΠB) A≡B = Πirrᵥ ΠA ΠB
goodCases (Πirrᵣ′ rF lF F G D ⊢F ⊢G A≡A)
          (Idᵣ′ F₁ G₁ _ _ D₁ ⊢F₁ ⊢G₁ _ A≡A₁)
          (Πirr₌ F′ G′ D′ A≡B) =
  ⊥-elim (Π≢Id (whrDet* (D′ , Πₙ) (red D₁ , Idₙ)))
goodCases (Idᵣ′ F G _ _ D ⊢F ⊢G _ A≡A) (Uᵣ′ _ _ _ _ _ _ D')
          (Id₌ F′ G′ _ D′ A≡B) =
  ⊥-elim (U≢Id (whrDet* (red D' ,  Uₙ) (D′ , Idₙ)))
goodCases (Idᵣ′ F G _ _ D ⊢F ⊢G _ A≡A) (ℕᵣ D₁)
          (Id₌ F′ G′ _ D′ A≡B) =
  ⊥-elim (ℕ≢Id (whrDet* (red D₁ , ℕₙ) (D′ , Idₙ)))
goodCases (Idᵣ′ F G _ _ D ⊢F ⊢G _ A≡A) (Emptyᵣ D₁)
          (Id₌ F′ G′ _ D′ A≡B) =
  ⊥-elim (Empty≢Id (whrDet* (red D₁ , Emptyₙ) (D′ , Idₙ)))
goodCases (Idᵣ′ F G _ _ D ⊢F ⊢G _ A≡A) (ne′ K D₁ neK K≡K)
          (Id₌ F′ G′ _ D′ A≡B) =
  ⊥-elim (Id≢ne neK (whrDet* (D′ , Idₙ) (red D₁ , ne neK)))
goodCases (Idᵣ′ F' G' _ _ D' ⊢F' ⊢G' _ A≡A')
          (Πᵣ′ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G])
          (Id₌ F′ G′ _ D′ A≡B) =
  ⊥-elim (Π≢Id (whrDet* (red D , Πₙ) (D′ , Idₙ)))
goodCases (Idᵣ′ F₁ G₁ _ _ D₁ ⊢F₁ ⊢G₁ _ A≡A₁)
          (Πirrᵣ′ rF lF F G D ⊢F ⊢G A≡A)
          (Id₌ F′ G′ _ D′ A≡B) =
  ⊥-elim (Π≢Id (whrDet* (red D , Πₙ) (D′ , Idₙ)))
goodCases (Idᵣ IdA) (Idᵣ IdB) A≡B = Idᵥ IdA IdB
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
  Emptyᵥ : ∀ {A B C l l′ l″} EmptyA EmptyB EmptyC
    → ShapeView₃ Γ l l′ l″ A B C [ % , ι ⁰ ] [ % , ι ⁰ ] [ % , ι ⁰ ] (Emptyᵣ EmptyA) (Emptyᵣ EmptyB) (Emptyᵣ EmptyC)
  ne  : ∀ {A B C r1 r2 r3 l1 l2 l3 l l′ l″} neA neB neC
      → ShapeView₃ Γ l l′ l″ A B C [ r1 , ι l1 ] [ r2 , ι l2 ] [ r3 , ι l3 ] (ne neA) (ne neB) (ne neC)
  Πᵥ : ∀ {A B C lΠ1 lΠ2 lΠ3 l l′ l″} ΠA ΠB ΠC
    → ShapeView₃ Γ l l′ l″ A B C [ ! , ι lΠ1 ] [ ! , ι lΠ2 ] [ ! , ι lΠ3 ] (Πᵣ ΠA) (Πᵣ ΠB) (Πᵣ ΠC)
  ΠΠirrΠᵥ : ∀ {A B C l l′ l″ lΠ lΠ3} ΠA ΠB ΠC
    → ShapeView₃ Γ l l′ l″ A B C [ ! , ι lΠ ] [ % , ι ⁰ ] [ ! , ι lΠ3 ] (Πᵣ ΠA) (Πirrᵣ ΠB) (Πᵣ ΠC)
  ΠirrΠΠᵥ : ∀ {A B C l l′ l″ lΠ lΠ3 } ΠA ΠB ΠC
    → ShapeView₃ Γ l l′ l″ A B C [ % , ι ⁰ ] [ ! , ι lΠ ] [ ! , ι lΠ3 ] (Πirrᵣ ΠA) (Πᵣ ΠB) (Πᵣ ΠC)
  ΠirrΠirrΠᵥ : ∀ {A B C l l′ l″ lΠ3} ΠA ΠB ΠC
    → ShapeView₃ Γ l l′ l″ A B C [ % , ι ⁰ ] [ % , ι ⁰ ] [ ! , ι lΠ3 ] (Πirrᵣ ΠA) (Πirrᵣ ΠB) (Πᵣ ΠC)
  ΠΠΠirrᵥ : ∀ {A B C lΠ1 lΠ2 l l′ l″} ΠA ΠB ΠC
    → ShapeView₃ Γ l l′ l″ A B C [ ! , ι lΠ1 ] [ ! , ι lΠ2 ] [ % , ι ⁰ ] (Πᵣ ΠA) (Πᵣ ΠB) (Πirrᵣ ΠC)
  ΠΠirrΠirrᵥ : ∀ {A B C l l′ l″ lΠ } ΠA ΠB ΠC
    → ShapeView₃ Γ l l′ l″ A B C [ ! , ι lΠ ] [ % , ι ⁰ ] [ % , ι ⁰ ] (Πᵣ ΠA) (Πirrᵣ ΠB) (Πirrᵣ ΠC)
  ΠirrΠΠirrᵥ : ∀ {A B C l l′ l″ lΠ } ΠA ΠB ΠC
    → ShapeView₃ Γ l l′ l″ A B C [ % , ι ⁰ ] [ ! , ι lΠ ] [ % , ι ⁰ ] (Πirrᵣ ΠA) (Πᵣ ΠB) (Πirrᵣ ΠC)
  Πirrᵥ : ∀ {A B C l l′ l″ } ΠA ΠB ΠC
    → ShapeView₃ Γ l l′ l″ A B C [ % , ι ⁰ ] [ % , ι ⁰ ] [ % , ι ⁰ ] (Πirrᵣ ΠA) (Πirrᵣ ΠB) (Πirrᵣ ΠC)
  Idᵥ : ∀ {A B C l l′ l″} ΠA ΠB ΠC
    → ShapeView₃ Γ l l′ l″ A B C [ % , ι ⁰ ] [ % , ι ⁰ ] [ % , ι ⁰ ] (Idᵣ ΠA) (Idᵣ ΠB) (Idᵣ ΠC)
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
combine (Uᵥ UA (Uᵣ r l′ l< PE.refl D)) (Πᵥ (Πᵣ rF lF lG _ _ F G D' ⊢F ⊢G A≡A [F] [G]) ΠB) =
 ⊥-elim (U≢Π (whrDet* (red D ,  Uₙ) (red  D' , Πₙ))) 
combine (Uᵥ UA (Uᵣ r l′ l< PE.refl D)) (ΠΠirrᵥ (Πᵣ rF lF lG _ _ F G D' ⊢F ⊢G A≡A [F] [G]) ΠB) =
 ⊥-elim (U≢Π (whrDet* (red D ,  Uₙ) (red  D' , Πₙ))) 
combine (Uᵥ UA (Uᵣ r l′ l< PE.refl D)) (ΠirrΠᵥ (Πirrᵣ rF lF F G D' ⊢F ⊢G A≡A) ΠB) =
 ⊥-elim (U≢Π (whrDet* (red D ,  Uₙ) (red  D' , Πₙ))) 
combine (Uᵥ UA (Uᵣ r l′ l< PE.refl D)) (Πirrᵥ (Πirrᵣ rF lF F G D' ⊢F ⊢G A≡A) ΠB) =
 ⊥-elim (U≢Π (whrDet* (red D ,  Uₙ) (red  D' , Πₙ))) 
combine (Uᵥ UA (Uᵣ r l′ l< PE.refl D)) (Idᵥ (Idᵣ F G _ _ D' ⊢F ⊢G _ A≡A) IdB) =
 ⊥-elim (U≢Id (whrDet* (red D ,  Uₙ) (red  D' , Idₙ))) 
combine  (ℕᵥ ℕA ℕB) (Uᵥ (Uᵣ r l′ l< PE.refl D) UB) = 
 ⊥-elim (U≢ℕ (whrDet* (red D ,  Uₙ) (red  ℕB , ℕₙ))) 
combine  (ℕᵥ ℕA ℕB) (Emptyᵥ EmptyA EmptyB) =
   ⊥-elim (ℕ≢Empty (whrDet* (red ℕB , ℕₙ) (red EmptyA , Emptyₙ)))
combine  (ℕᵥ ℕA₁ ℕB₁) (ℕᵥ ℕA ℕB) = ℕᵥ ℕA₁ ℕB₁ ℕB
combine  (ℕᵥ ℕA ℕB) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (ℕ≢ne neK (whrDet* (red ℕB , ℕₙ) (red D , ne neK)))
combine  (ℕᵥ ℕA ℕB) (Πᵥ (Πᵣ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G]) ΠB) =
  ⊥-elim (ℕ≢Π (whrDet* (red ℕB , ℕₙ) (red D , Πₙ)))
combine  (ℕᵥ ℕA ℕB) (Πirrᵥ (Πirrᵣ rF lF F G D ⊢F ⊢G A≡A) ΠB) =
  ⊥-elim (ℕ≢Π (whrDet* (red ℕB , ℕₙ) (red D , Πₙ)))
combine  (ℕᵥ ℕA ℕB) (ΠΠirrᵥ (Πᵣ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G]) ΠB) =
  ⊥-elim (ℕ≢Π (whrDet* (red ℕB , ℕₙ) (red D , Πₙ)))
combine  (ℕᵥ ℕA ℕB) (ΠirrΠᵥ (Πirrᵣ rF lF F G D ⊢F ⊢G A≡A) ΠB) =
  ⊥-elim (ℕ≢Π (whrDet* (red ℕB , ℕₙ) (red D , Πₙ)))
combine  (ℕᵥ ℕA ℕB) (Idᵥ (Idᵣ F G _ _ D ⊢F ⊢G _ A≡A) IdB) =
  ⊥-elim (ℕ≢Id (whrDet* (red ℕB , ℕₙ) (red D , Idₙ)))
combine  (Emptyᵥ EmptyA EmptyB) (Uᵥ (Uᵣ r l′ l< PE.refl D) UB) = 
 ⊥-elim (U≢Empty (whrDet* (red D ,  Uₙ) (red  EmptyB , Emptyₙ))) 
combine  (Emptyᵥ EmptyA EmptyB) (ℕᵥ ℕA ℕB) =
   ⊥-elim (Empty≢ℕ (whrDet* (red EmptyB , Emptyₙ) (red ℕA , ℕₙ)))
combine  (Emptyᵥ EmptyA₁ EmptyB₁) (Emptyᵥ EmptyA EmptyB) = Emptyᵥ EmptyA₁ EmptyB₁ EmptyB
combine  (Emptyᵥ EmptyA EmptyB) (ne (ne K D neK K≡K) neB) =
   ⊥-elim (Empty≢ne neK (whrDet* (red EmptyB , Emptyₙ) (red D , ne neK)))
combine  (Emptyᵥ EmptyA EmptyB) (Πᵥ (Πᵣ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G]) ΠB) =
   ⊥-elim (Empty≢Π (whrDet* (red EmptyB , Emptyₙ) (red D , Πₙ)))
combine  (Emptyᵥ EmptyA EmptyB) (Πirrᵥ (Πirrᵣ rF lF F G D ⊢F ⊢G A≡A) ΠB) =
   ⊥-elim (Empty≢Π (whrDet* (red EmptyB , Emptyₙ) (red D , Πₙ)))
combine  (Emptyᵥ EmptyA EmptyB) (ΠΠirrᵥ (Πᵣ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G]) ΠB) =
   ⊥-elim (Empty≢Π (whrDet* (red EmptyB , Emptyₙ) (red D , Πₙ)))
combine  (Emptyᵥ EmptyA EmptyB) (ΠirrΠᵥ (Πirrᵣ rF lF F G D ⊢F ⊢G A≡A) ΠB) =
   ⊥-elim (Empty≢Π (whrDet* (red EmptyB , Emptyₙ) (red D , Πₙ)))
combine  (Emptyᵥ EmptyA EmptyB) (Idᵥ (Idᵣ F G _ _ D ⊢F ⊢G _ A≡A) IdB) =
   ⊥-elim (Empty≢Id (whrDet* (red EmptyB , Emptyₙ) (red D , Idₙ)))
combine  (ne neA (ne K D' neK K≡K)) (Uᵥ (Uᵣ r l′ l< PE.refl D) UB) =
  ⊥-elim (U≢ne neK (whrDet* (red D ,  Uₙ) (red  D' , ne neK)))
combine  (ne neA (ne K D neK K≡K)) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢ne neK (whrDet* (red ℕA , ℕₙ) (red D , ne neK)))
combine  (ne neA (ne K D neK K≡K)) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢ne neK (whrDet* (red EmptyA , Emptyₙ) (red D , ne neK)))
combine  (ne neA₁ neB₁) (ne neA neB) = ne neA₁ neB₁ neB
combine  (ne neA (ne K D₁ neK K≡K)) (Πᵥ (Πᵣ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G]) ΠB) =
  ⊥-elim (Π≢ne neK (whrDet* (red D , Πₙ) (red D₁ , ne neK)))
combine  (ne neA (ne K D₁ neK K≡K)) (Πirrᵥ (Πirrᵣ rF lF F G D ⊢F ⊢G A≡A) ΠB) =
  ⊥-elim (Π≢ne neK (whrDet* (red D , Πₙ) (red D₁ , ne neK)))
combine  (ne neA (ne K D₁ neK K≡K)) (ΠΠirrᵥ (Πᵣ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G]) ΠB) =
  ⊥-elim (Π≢ne neK (whrDet* (red D , Πₙ) (red D₁ , ne neK)))
combine  (ne neA (ne K D₁ neK K≡K)) (ΠirrΠᵥ (Πirrᵣ rF lF F G D ⊢F ⊢G A≡A) ΠB) =
  ⊥-elim (Π≢ne neK (whrDet* (red D , Πₙ) (red D₁ , ne neK)))
combine  (ne neA (ne K D₁ neK K≡K)) (Idᵥ (Idᵣ F G _ _ D ⊢F ⊢G _ A≡A) IdB) =
  ⊥-elim (Id≢ne neK (whrDet* (red D , Idₙ) (red D₁ , ne neK)))
combine  (Πᵥ ΠA (Πᵣ rF lF lG _ _ F G D' ⊢F ⊢G A≡A [F] [G])) (Uᵥ (Uᵣ r l′ l< PE.refl D) UB) =
 ⊥-elim (U≢Π (whrDet* (red D ,  Uₙ) (red  D' , Πₙ))) 
combine  (Πᵥ ΠA (Πᵣ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G])) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢Π (whrDet* (red ℕA , ℕₙ) (red D , Πₙ)))
combine  (Πᵥ ΠA (Πᵣ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G])) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢Π (whrDet* (red EmptyA , Emptyₙ) (red D , Πₙ)))
combine  (Πᵥ ΠA (Πᵣ rF lF lG _ _ F G D₁ ⊢F ⊢G A≡A [F] [G])) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (Π≢ne neK (whrDet* (red D₁ , Πₙ) (red D , ne neK)))
combine  (Πᵥ ΠA (Πᵣ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G]))
        (Idᵥ (Idᵣ F₁ G₁ _ _ D₁ ⊢F₁ ⊢G₁ _ A≡A₁) IdB) =
  ⊥-elim (Π≢Id (whrDet* (red D , Πₙ) (red D₁ , Idₙ)))
combine  (ΠirrΠᵥ ΠA (Πᵣ rF lF lG _ _ F G D' ⊢F ⊢G A≡A [F] [G])) (Uᵥ (Uᵣ r l′ l< PE.refl D) UB) =
 ⊥-elim (U≢Π (whrDet* (red D ,  Uₙ) (red  D' , Πₙ))) 
combine  (ΠirrΠᵥ ΠA (Πᵣ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G])) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢Π (whrDet* (red ℕA , ℕₙ) (red D , Πₙ)))
combine  (ΠirrΠᵥ ΠA (Πᵣ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G])) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢Π (whrDet* (red EmptyA , Emptyₙ) (red D , Πₙ)))
combine  (ΠirrΠᵥ ΠA (Πᵣ rF lF lG _ _ F G D₁ ⊢F ⊢G A≡A [F] [G])) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (Π≢ne neK (whrDet* (red D₁ , Πₙ) (red D , ne neK)))
combine  (ΠirrΠᵥ ΠA (Πᵣ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G]))
        (Idᵥ (Idᵣ F₁ G₁ _ _ D₁ ⊢F₁ ⊢G₁ _ A≡A₁) IdB) =
  ⊥-elim (Π≢Id (whrDet* (red D , Πₙ) (red D₁ , Idₙ)))
combine  (Πirrᵥ ΠA (Πirrᵣ rF lF F G D' ⊢F ⊢G A≡A)) (Uᵥ (Uᵣ r l′ l< PE.refl D) UB) =
 ⊥-elim (U≢Π (whrDet* (red D ,  Uₙ) (red  D' , Πₙ))) 
combine  (Πirrᵥ ΠA (Πirrᵣ rF lF F G D ⊢F ⊢G A≡A)) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢Π (whrDet* (red ℕA , ℕₙ) (red D , Πₙ)))
combine  (Πirrᵥ ΠA (Πirrᵣ rF lF F G D ⊢F ⊢G A≡A)) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢Π (whrDet* (red EmptyA , Emptyₙ) (red D , Πₙ)))
combine  (Πirrᵥ ΠA (Πirrᵣ rF lF F G D₁ ⊢F ⊢G A≡A)) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (Π≢ne neK (whrDet* (red D₁ , Πₙ) (red D , ne neK)))
combine  (Πirrᵥ ΠA (Πirrᵣ rF lF F G D ⊢F ⊢G A≡A))
        (Idᵥ (Idᵣ F₁ G₁ _ _ D₁ ⊢F₁ ⊢G₁ _ A≡A₁) IdB) =
  ⊥-elim (Π≢Id (whrDet* (red D , Πₙ) (red D₁ , Idₙ)))
combine  (ΠΠirrᵥ ΠA (Πirrᵣ rF lF F G D' ⊢F ⊢G A≡A)) (Uᵥ (Uᵣ r l′ l< PE.refl D) UB) =
 ⊥-elim (U≢Π (whrDet* (red D ,  Uₙ) (red  D' , Πₙ))) 
combine  (ΠΠirrᵥ ΠA (Πirrᵣ rF lF F G D ⊢F ⊢G A≡A)) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢Π (whrDet* (red ℕA , ℕₙ) (red D , Πₙ)))
combine  (ΠΠirrᵥ ΠA (Πirrᵣ rF lF F G D ⊢F ⊢G A≡A)) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢Π (whrDet* (red EmptyA , Emptyₙ) (red D , Πₙ)))
combine  (ΠΠirrᵥ ΠA (Πirrᵣ rF lF F G D₁ ⊢F ⊢G A≡A)) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (Π≢ne neK (whrDet* (red D₁ , Πₙ) (red D , ne neK)))
combine  (ΠΠirrᵥ ΠA (Πirrᵣ rF lF F G D ⊢F ⊢G A≡A))
        (Idᵥ (Idᵣ F₁ G₁ _ _ D₁ ⊢F₁ ⊢G₁ _ A≡A₁) IdB) =
  ⊥-elim (Π≢Id (whrDet* (red D , Πₙ) (red D₁ , Idₙ)))
combine  (Πᵥ ΠA₁ ΠB₁) (Πᵥ ΠA ΠB) = Πᵥ ΠA₁ ΠB₁ ΠB
combine  (Πᵥ ΠA₁ ΠB₁) (ΠΠirrᵥ ΠA ΠB) = ΠΠΠirrᵥ ΠA₁ ΠB₁ ΠB
combine  (ΠirrΠᵥ ΠA₁ ΠB₁) (Πᵥ ΠA ΠB) = ΠirrΠΠᵥ ΠA₁ ΠB₁ ΠB
combine  (ΠirrΠᵥ ΠA₁ ΠB₁) (ΠΠirrᵥ ΠA ΠB) = ΠirrΠΠirrᵥ ΠA₁ ΠB₁ ΠB
combine  (Πirrᵥ ΠA₁ ΠB₁) (Πirrᵥ ΠA ΠB) = Πirrᵥ ΠA₁ ΠB₁ ΠB
combine  (Πirrᵥ ΠA₁ ΠB₁) (ΠirrΠᵥ ΠA ΠB) = ΠirrΠirrΠᵥ ΠA₁ ΠB₁ ΠB
combine  (ΠΠirrᵥ ΠA₁ ΠB₁) (ΠirrΠᵥ ΠA ΠB) = ΠΠirrΠᵥ ΠA₁ ΠB₁ ΠB
combine  (ΠΠirrᵥ ΠA₁ ΠB₁) (Πirrᵥ ΠA ΠB) = ΠΠirrΠirrᵥ ΠA₁ ΠB₁ ΠB
combine  (Πᵥ ΠA₁ ΠB₁) (ΠirrΠᵥ ΠA ΠB) = Πᵥ ΠA₁ ΠB₁ ΠB
combine  (Πᵥ ΠA₁ ΠB₁) (Πirrᵥ ΠA ΠB) = ΠΠΠirrᵥ ΠA₁ ΠB₁ ΠB
combine  (ΠirrΠᵥ ΠA₁ ΠB₁) (ΠirrΠᵥ ΠA ΠB) = ΠirrΠΠᵥ ΠA₁ ΠB₁ ΠB
combine  (ΠirrΠᵥ ΠA₁ ΠB₁) (Πirrᵥ ΠA ΠB) = ΠirrΠΠirrᵥ ΠA₁ ΠB₁ ΠB
combine  (Πirrᵥ ΠA₁ ΠB₁) (ΠΠirrᵥ ΠA ΠB) = Πirrᵥ ΠA₁ ΠB₁ ΠB
combine  (Πirrᵥ ΠA₁ ΠB₁) (Πᵥ ΠA ΠB) = ΠirrΠirrΠᵥ ΠA₁ ΠB₁ ΠB
combine  (ΠΠirrᵥ ΠA₁ ΠB₁) (Πᵥ ΠA ΠB) = ΠΠirrΠᵥ ΠA₁ ΠB₁ ΠB
combine  (ΠΠirrᵥ ΠA₁ ΠB₁) (ΠΠirrᵥ ΠA ΠB) = ΠΠirrΠirrᵥ ΠA₁ ΠB₁ ΠB
combine  (Idᵥ IdA (Idᵣ F G _ _ D' ⊢F ⊢G _ A≡A)) (Uᵥ (Uᵣ r l′ l< PE.refl D) UB) = 
 ⊥-elim (U≢Id (whrDet* (red D ,  Uₙ) (red  D' , Idₙ))) 
combine  (Idᵥ IdA (Idᵣ F G _ _ D ⊢F ⊢G _ A≡A)) (ℕᵥ ℕA ℕB) =
  ⊥-elim (ℕ≢Id (whrDet* (red ℕA , ℕₙ) (red D , Idₙ)))
combine  (Idᵥ IdA (Idᵣ F G _ _ D ⊢F ⊢G _ A≡A)) (Emptyᵥ EmptyA EmptyB) =
  ⊥-elim (Empty≢Id (whrDet* (red EmptyA , Emptyₙ) (red D , Idₙ)))
combine  (Idᵥ IdA (Idᵣ F G _ _ D₁ ⊢F ⊢G _ A≡A)) (ne (ne K D neK K≡K) neB) =
  ⊥-elim (Id≢ne neK (whrDet* (red D₁ , Idₙ) (red D , ne neK)))
combine  (Idᵥ ΠA (Idᵣ F G _ _ D ⊢F ⊢G _ A≡A))
        (Πᵥ (Πᵣ rF₁ lF₁ lG₁ _ _ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁₁) IdB) =
  ⊥-elim (Π≢Id (whrDet* (red D₁ , Πₙ) (red D , Idₙ)))
combine  (Idᵥ ΠA (Idᵣ F G _ _ D ⊢F ⊢G _ A≡A))
        (Πirrᵥ (Πirrᵣ rF₁ lF₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁) IdB) =
  ⊥-elim (Π≢Id (whrDet* (red D₁ , Πₙ) (red D , Idₙ)))
combine  (Idᵥ ΠA (Idᵣ F G _ _ D ⊢F ⊢G _ A≡A))
        (ΠΠirrᵥ (Πᵣ rF₁ lF₁ lG₁ _ _ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁₁) IdB) =
  ⊥-elim (Π≢Id (whrDet* (red D₁ , Πₙ) (red D , Idₙ)))
combine  (Idᵥ ΠA (Idᵣ F G _ _ D ⊢F ⊢G _ A≡A))
        (ΠirrΠᵥ (Πirrᵣ rF₁ lF₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁) IdB) =
  ⊥-elim (Π≢Id (whrDet* (red D₁ , Πₙ) (red D , Idₙ)))
combine  (Idᵥ IdA IdB) (Idᵥ IdA₁ IdB₁) = Idᵥ IdA IdB IdB₁
combine (emb⁰¹ [AB]) [BC] = emb⁰¹¹ (combine [AB] [BC])
combine (emb¹⁰ [AB]) [BC] = emb¹⁰¹ (combine [AB] [BC])
combine [AB] (emb⁰¹ [BC]) = combine [AB] [BC]
combine [AB] (emb¹⁰ [BC]) = emb¹¹⁰ (combine [AB] [BC])
combine (emb¹∞ [AB]) [BC] = emb¹∞∞ (combine [AB] [BC])
combine (emb∞¹ [AB]) [BC] = emb∞¹∞ (combine [AB] [BC])
combine [AB] (emb¹∞ [BC]) = combine [AB] [BC]
combine [AB] (emb∞¹ [BC]) = emb∞∞¹ (combine [AB] [BC])



