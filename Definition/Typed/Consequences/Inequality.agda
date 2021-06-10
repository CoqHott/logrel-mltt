{-# OPTIONS --without-K  #-}

module Definition.Typed.Consequences.Inequality where

open import Definition.Untyped hiding (U≢ℕ; U≢Π; U≢ne; ℕ≢Π; ℕ≢ne; Π≢ne; U≢Empty; ℕ≢Empty; Empty≢Π; Empty≢ne)
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.EqRelInstance
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Fundamental.Reducibility
open import Definition.Typed.Consequences.Syntactic

open import Tools.Product
open import Tools.Empty
import Tools.PropositionalEquality as PE

A≢B : ∀ {A B sA sB Γ} (_⊩′⟨_⟩A_ _⊩′⟨_⟩B_ : Con Term → TypeLevel → Term → Set)
      (A-intr : ∀ {l} → Γ ⊩′⟨ l ⟩A A → Γ ⊩⟨ l ⟩ A ⦂ sA)
      (B-intr : ∀ {l} → Γ ⊩′⟨ l ⟩B B → Γ ⊩⟨ l ⟩ B ⦂ sB)
      (A-elim : ∀ {l} → Γ ⊩⟨ l ⟩ A ⦂ sA → ∃ λ l′ → Γ ⊩′⟨ l′ ⟩A A)
      (B-elim : ∀ {l} → Γ ⊩⟨ l ⟩ B ⦂ sA → ∃ λ l′ → Γ ⊩′⟨ l′ ⟩B B)
      (A≢B′ : ∀ {l l′} ([A] : Γ ⊩′⟨ l ⟩A A) ([B] : Γ ⊩′⟨ l′ ⟩B B)
            → ShapeView Γ l l′ A B sA sB (A-intr [A]) (B-intr [B]) → ⊥)
    → Γ ⊢ A ≡ B ⦂ sA → ⊥
A≢B {A} {B} _ _ A-intr B-intr A-elim B-elim A≢B′ A≡B with reducibleEq A≡B
A≢B {A} {B} _ _ A-intr B-intr A-elim B-elim A≢B′ A≡B | [A] , [B] , [A≡B] =
  let _ , [A]′ = A-elim ([A])
      _ , [B]′ = B-elim ([B])
      [A≡B]′ = irrelevanceEq [A] (A-intr [A]′) [A≡B]
  in  A≢B′ [A]′ [B]′ (goodCases (A-intr [A]′) (B-intr [B]′) [A≡B]′)

U≢ℕ′ : ∀ {Γ s B l l′}
       ([U] : Γ ⊩′⟨ l ⟩U)
       ([ℕ] : Γ ⊩ℕ B)
     → ShapeView Γ l l′ _ _ 𝕥y 𝕥y (Uᵣ {s = s} [U]) (ℕᵣ [ℕ]) → ⊥
U≢ℕ′ a b ()

U≢ℕ-red : ∀ {s B Γ} → Γ ⊢ B ⇒* ℕ ⦂ 𝕥y → Γ ⊢ Univ s ≡ B ⦂ 𝕥y → ⊥
U≢ℕ-red D = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩U) (λ Γ l B → Γ ⊩ℕ B) Uᵣ ℕᵣ
                (λ x → extractMaybeEmb (U-elim x))
                (λ x → extractMaybeEmb (ℕ-elim′ D x))
                U≢ℕ′

-- U and ℕ cannot be judgmentally equal.
U≢ℕ𝕥y : ∀ {s Γ} → Γ ⊢ Univ s ≡ ℕ ⦂ 𝕥y → ⊥
U≢ℕ𝕥y U≡ℕ =
  let _ , ⊢ℕ = syntacticEq U≡ℕ
  in  U≢ℕ-red (id ⊢ℕ) U≡ℕ


-- U vs Pi
U≢Π′ : ∀ {sU B sB Γ l l′}
       ([U] : Γ ⊩′⟨ l ⟩U)
       ([Π] : Γ ⊩′⟨ l′ ⟩Π B ⦂ sB)
     → ShapeView Γ l l′ _ _ _ _ (Uᵣ {s = sU} [U]) (Πᵣ [Π]) → ⊥
U≢Π′ a b ()

U≢Π-red : ∀ {B F G sB sF sU Γ} → Γ ⊢ B ⇒* Π F ⦂ sF ▹ G ⦂ sB → Γ ⊢ Univ sU ≡ B ⦂ 𝕥y → ⊥
U≢Π-red {sB = sB} D = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩U)
                (λ Γ l A → Γ ⊩′⟨ l ⟩Π A ⦂ 𝕥y) Uᵣ Πᵣ
                (λ x → extractMaybeEmb (U-elim x))
                (λ x → extractMaybeEmb (Π-elim′ D x))
                U≢Π′

-- U and Π F ▹ G for any F and G cannot be judgmentally equal.
U≢Π𝕥y : ∀ {sU F sF G Γ} → Γ ⊢ Univ sU ≡ Π F ⦂ sF ▹ G ⦂ 𝕥y → ⊥
U≢Π𝕥y U≡Π =
  let _ , ⊢Π = syntacticEq U≡Π
  in  U≢Π-red (id ⊢Π) U≡Π

U≢ne′ : ∀ {s s' K Γ l l′}
       ([U] : Γ ⊩′⟨ l ⟩U)
       ([K] : Γ ⊩ne K ⦂ s')
     → ShapeView Γ l l′ _ _ _ _ (Uᵣ {s = s} [U]) (ne [K]) → ⊥
U≢ne′ a b ()

U≢ne-red : ∀ {sU s B K Γ} → Γ ⊢ B ⇒* K ⦂ s → Neutral K → Γ ⊢ Univ sU ≡ B ⦂ 𝕥y → ⊥
U≢ne-red D neK = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩U) (λ Γ l B → Γ ⊩ne B ⦂ 𝕥y) Uᵣ ne
                     (λ x → extractMaybeEmb (U-elim x))
                     (λ x → extractMaybeEmb (ne-elim′ D neK x))
                     U≢ne′

-- U and K for any neutral K cannot be judgmentally equal.
U≢ne𝕥y : ∀ {s K Γ} → Neutral K → Γ ⊢ Univ s ≡ K ⦂ 𝕥y → ⊥
U≢ne𝕥y neK U≡K =
  let _ , ⊢K = syntacticEq U≡K
  in  U≢ne-red (id ⊢K) neK U≡K

ℕ≢Π′ : ∀ {A B Γ l l′}
       ([ℕ] : Γ ⊩ℕ A)
       ([Π] : Γ ⊩′⟨ l′ ⟩Π B ⦂ 𝕥y)
     → ShapeView Γ l l′ _ _ _ _ (ℕᵣ [ℕ]) (Πᵣ [Π]) → ⊥
ℕ≢Π′ a b ()

ℕ≢Π-red : ∀ {A B F sF G Γ} → Γ ⊢ A ⇒* ℕ ⦂ 𝕥y → Γ ⊢ B ⇒* Π F ⦂ sF ▹ G ⦂ 𝕥y → Γ ⊢ A ≡ B ⦂ 𝕥y → ⊥
ℕ≢Π-red D D′ = A≢B (λ Γ l A → Γ ⊩ℕ A)
                   (λ Γ l A → Γ ⊩′⟨ l ⟩Π A ⦂ 𝕥y) ℕᵣ Πᵣ
                   (λ x → extractMaybeEmb (ℕ-elim′ D x))
                   (λ x → extractMaybeEmb (Π-elim′ D′ x))
                   ℕ≢Π′

-- ℕ and Π F ▹ G for any F and G cannot be judgmentally equal.
ℕ≢Π𝕥y : ∀ {F sF G Γ} → Γ ⊢ ℕ ≡ Π F ⦂ sF ▹ G ⦂ 𝕥y → ⊥
ℕ≢Π𝕥y ℕ≡Π =
  let ⊢ℕ , ⊢Π = syntacticEq ℕ≡Π
  in  ℕ≢Π-red (id ⊢ℕ) (id ⊢Π) ℕ≡Π


-- Empty and Π
Empty≢Π′ : ∀ {A B Γ l l′}
       ([Empty] : Γ ⊩Empty A)
       ([Π] : Γ ⊩′⟨ l′ ⟩Π B ⦂ 𝕥y)
     → ShapeView Γ l l′ _ _ _ _ (Emptyᵣ [Empty]) (Πᵣ [Π]) → ⊥
Empty≢Π′ a b ()

Empty≢Π-red : ∀ {A B F sF G Γ} → Γ ⊢ A ⇒* Empty ⦂ 𝕥y → Γ ⊢ B ⇒* Π F ⦂ sF ▹ G ⦂ 𝕥y → Γ ⊢ A ≡ B ⦂ 𝕥y → ⊥
Empty≢Π-red D D′ = A≢B (λ Γ l A → Γ ⊩Empty A)
                   (λ Γ l A → Γ ⊩′⟨ l ⟩Π A ⦂ 𝕥y) Emptyᵣ Πᵣ
                   (λ x → extractMaybeEmb (Empty-elim′ D x))
                   (λ x → extractMaybeEmb (Π-elim′ D′ x))
                   Empty≢Π′

Empty≢Π𝕥y : ∀ {F sF G Γ} → Γ ⊢ Empty ≡ Π F ⦂ sF ▹ G ⦂ 𝕥y → ⊥
Empty≢Π𝕥y Empty≡Π =
  let ⊢Empty , ⊢Π = syntacticEq Empty≡Π
  in  Empty≢Π-red (id ⊢Empty) (id ⊢Π) Empty≡Π

ℕ≢ne′ : ∀ {A K Γ l l′}
       ([ℕ] : Γ ⊩ℕ A)
       ([K] : Γ ⊩ne K ⦂ 𝕥y)
     → ShapeView Γ l l′ _ _ _ _ (ℕᵣ [ℕ]) (ne [K]) → ⊥
ℕ≢ne′ a b ()

ℕ≢ne-red : ∀ {A B K Γ} → Γ ⊢ A ⇒* ℕ ⦂ 𝕥y → Γ ⊢ B ⇒* K ⦂ 𝕥y → Neutral K → Γ ⊢ A ≡ B ⦂ 𝕥y → ⊥
ℕ≢ne-red D D′ neK = A≢B (λ Γ l A → Γ ⊩ℕ A) (λ Γ l B → Γ ⊩ne B ⦂ 𝕥y) ℕᵣ ne
                        (λ x → extractMaybeEmb (ℕ-elim′ D x))
                        (λ x → extractMaybeEmb (ne-elim′ D′ neK x))
                        ℕ≢ne′

-- ℕ and K for any neutral K cannot be judgmentally equal.
ℕ≢ne𝕥y : ∀ {K Γ} → Neutral K → Γ ⊢ ℕ ≡ K ⦂ 𝕥y → ⊥
ℕ≢ne𝕥y neK ℕ≡K =
  let ⊢ℕ , ⊢K = syntacticEq ℕ≡K
  in  ℕ≢ne-red (id ⊢ℕ) (id ⊢K) neK ℕ≡K

-- Empty and neutral
Empty≢ne′ : ∀ {A K Γ l l′}
       ([Empty] : Γ ⊩Empty A)
       ([K] : Γ ⊩ne K ⦂ 𝕥y)
     → ShapeView Γ l l′ _ _ _ _ (Emptyᵣ [Empty]) (ne [K]) → ⊥
Empty≢ne′ a b ()

Empty≢ne-red : ∀ {A B K Γ} → Γ ⊢ A ⇒* Empty ⦂ 𝕥y → Γ ⊢ B ⇒* K ⦂ 𝕥y → Neutral K → Γ ⊢ A ≡ B ⦂ 𝕥y → ⊥
Empty≢ne-red D D′ neK = A≢B (λ Γ l A → Γ ⊩Empty A) (λ Γ l B → Γ ⊩ne B ⦂ 𝕥y) Emptyᵣ ne
                        (λ x → extractMaybeEmb (Empty-elim′ D x))
                        (λ x → extractMaybeEmb (ne-elim′ D′ neK x))
                        Empty≢ne′

Empty≢ne𝕥y : ∀ {K Γ} → Neutral K → Γ ⊢ Empty ≡ K ⦂ 𝕥y → ⊥
Empty≢ne𝕥y neK Empty≡K =
  let ⊢Empty , ⊢K = syntacticEq Empty≡K
  in  Empty≢ne-red (id ⊢Empty) (id ⊢K) neK Empty≡K

Π≢ne′ : ∀ {A K s Γ l l′}
       ([Π] : Γ ⊩′⟨ l ⟩Π A ⦂ s)
       ([K] : Γ ⊩ne K ⦂ s)
     → ShapeView Γ l l′ _ _ _ _ (Πᵣ [Π]) (ne [K]) → ⊥
Π≢ne′ a b ()

Π≢ne-red : ∀ {A B F sF G K s Γ} → Γ ⊢ A ⇒* Π F ⦂ sF ▹ G ⦂ s → Γ ⊢ B ⇒* K ⦂ s → Neutral K
     → Γ ⊢ A ≡ B ⦂ s → ⊥
Π≢ne-red {s = s} D D′ neK = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩Π A ⦂ s)
                        (λ Γ l B → Γ ⊩ne B ⦂ s) Πᵣ ne
                        (λ x → extractMaybeEmb (Π-elim′ D x))
                        (λ x → extractMaybeEmb (ne-elim′ D′ neK x))
                        Π≢ne′

-- Π F ▹ G and K for any F and G and neutral K cannot be judgmentally equal.
Π≢ne : ∀ {F sF G K s Γ} → Neutral K → Γ ⊢ Π F ⦂ sF ▹ G ≡ K ⦂ s → ⊥
Π≢ne neK Π≡K =
  let ⊢Π , ⊢K = syntacticEq Π≡K
  in  Π≢ne-red (id ⊢Π) (id ⊢K) neK Π≡K
