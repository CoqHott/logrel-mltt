{-# OPTIONS --without-K --safe #-}

module Definition.Typed.Consequences.Inequality where

open import Definition.Untyped hiding (U≢ℕ; U≢Π; U≢ne; ℕ≢Π; ℕ≢ne; Π≢ne)
open import Definition.Typed
open import Definition.Typed.EqRelInstance
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Fundamental.Reducibility
open import Definition.Typed.Consequences.Syntactic

open import Tools.Product
open import Tools.Empty


A≢B : ∀ {A B rA rB Γ} (_⊩′⟨_⟩A_ _⊩′⟨_⟩B_ : Con Term → TypeLevel → Term → Set)
      (A-intr : ∀ {l} → Γ ⊩′⟨ l ⟩A A → Γ ⊩⟨ l ⟩ A ^ rA)
      (B-intr : ∀ {l} → Γ ⊩′⟨ l ⟩B B → Γ ⊩⟨ l ⟩ B ^ rB)
      (A-elim : ∀ {l} → Γ ⊩⟨ l ⟩ A ^ rA → ∃ λ l′ → Γ ⊩′⟨ l′ ⟩A A)
      (B-elim : ∀ {l} → Γ ⊩⟨ l ⟩ B ^ rA → ∃ λ l′ → Γ ⊩′⟨ l′ ⟩B B)
      (A≢B′ : ∀ {l l′} ([A] : Γ ⊩′⟨ l ⟩A A) ([B] : Γ ⊩′⟨ l′ ⟩B B)
            → ShapeView Γ l l′ A B rA rB (A-intr [A]) (B-intr [B]) → ⊥)
    → Γ ⊢ A ≡ B ^ rA → ⊥
A≢B {A} {B} _ _ A-intr B-intr A-elim B-elim A≢B′ A≡B with reducibleEq A≡B
A≢B {A} {B} _ _ A-intr B-intr A-elim B-elim A≢B′ A≡B | [A] , [B] , [A≡B] =
  let _ , [A]′ = A-elim ([A])
      _ , [B]′ = B-elim ([B])
      [A≡B]′ = irrelevanceEq [A] (A-intr [A]′) [A≡B]
  in  A≢B′ [A]′ [B]′ (goodCases (A-intr [A]′) (B-intr [B]′) [A≡B]′)

U≢ℕ′ : ∀ {Γ r B l l′}
       ([U] : Γ ⊩′⟨ l ⟩U)
       ([ℕ] : Γ ⊩ℕ B)
     → ShapeView Γ l l′ _ _ ! ! (Uᵣ {r = r} [U]) (ℕᵣ [ℕ]) → ⊥
U≢ℕ′ a b ()

U≢ℕ-red : ∀ {r B Γ} → Γ ⊢ B ⇒* ℕ ^ ! → Γ ⊢ Univ r ≡ B ^ ! → ⊥
U≢ℕ-red D = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩U) (λ Γ l B → Γ ⊩ℕ B) Uᵣ ℕᵣ
                (λ x → extractMaybeEmb (U-elim x))
                (λ x → extractMaybeEmb (ℕ-elim′ D x))
                U≢ℕ′

-- U and ℕ cannot be judgmentally equal.
U≢ℕ : ∀ {r Γ} → Γ ⊢ Univ r ≡ ℕ ^ ! → ⊥
U≢ℕ U≡ℕ =
  let _ , ⊢ℕ = syntacticEq U≡ℕ
  in  U≢ℕ-red (id ⊢ℕ) U≡ℕ

-- U and Empty
U≢Empty′ : ∀ {Γ r B l l′}
       ([U] : Γ ⊩′⟨ l ⟩U)
       ([Empty] : Γ ⊩Empty B)
     → ShapeView Γ l l′ _ _ ! % (Uᵣ {r = r} [U]) (Emptyᵣ [Empty]) → ⊥
U≢Empty′ a b ()

-- it's interesting here that we need r₁ free but the ! on the univ equality isn't free
U≢Empty-red : ∀ {r B Γ r₁} → Γ ⊢ B ⇒* Empty ^ r₁ → Γ ⊢ Univ r ≡ B ^ ! → ⊥
U≢Empty-red D = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩U) (λ Γ l B → Γ ⊩Empty B) Uᵣ Emptyᵣ
                (λ x → extractMaybeEmb (U-elim x))
                (λ x → extractMaybeEmb (Empty-elim′ D x))
                U≢Empty′

U≢Emptyⱼ : ∀ {Γ r} → Γ ⊢ Univ r ≡ Empty ^ ! → ⊥
U≢Emptyⱼ U≡Empty =
  let _ , ⊢Empty = syntacticEq U≡Empty
  in  U≢Empty-red (id ⊢Empty) U≡Empty

-- ℕ and Empty

ℕ≢Empty′ : ∀ {Γ B l l'}
           ([ℕ] : Γ ⊩ℕ ℕ)
           ([Empty] : Γ ⊩Empty B)
           → ShapeView Γ l l' _ _ _ _ (ℕᵣ [ℕ]) (Emptyᵣ [Empty]) → ⊥
ℕ≢Empty′ a b ()

ℕ≢Empty-red : ∀ {B Γ rB} → Γ ⊢ B ⇒* Empty ^ rB → Γ ⊢ ℕ ≡ B ^ ! → ⊥
ℕ≢Empty-red D = A≢B (λ Γ l A → Γ ⊩ℕ A) (λ Γ l B → Γ ⊩Empty B) ℕᵣ Emptyᵣ
                (λ x → extractMaybeEmb (ℕ-elim x))
                (λ x → extractMaybeEmb (Empty-elim′ D x))
                ℕ≢Empty′

-- ℕ≢Emptyⱼ : ∀ {Γ} → Γ ⊢ ℕ ≡ Empty → ⊥
-- ℕ≢Emptyⱼ ℕ≡Empty =
--   let _ , ⊢Empty = syntacticEq ℕ≡Empty
--   in  ℕ≢Empty-red (id ⊢Empty) ℕ≡Empty



U≢Π′ : ∀ {rU B rB Γ l l′}
       ([U] : Γ ⊩′⟨ l ⟩U)
       ([Π] : Γ ⊩′⟨ l′ ⟩Π B ^ rB)
     → ShapeView Γ l l′ _ _ _ _ (Uᵣ {r = rU} [U]) (Πᵣ [Π]) → ⊥
U≢Π′ a b ()

U≢Π-red : ∀ {B F G rB rF rU Γ} → Γ ⊢ B ⇒* Π F ^ rF ▹ G ^ rB → Γ ⊢ Univ rU ≡ B ^ ! → ⊥
U≢Π-red {rB = rB} D = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩U)
                (λ Γ l A → Γ ⊩′⟨ l ⟩Π A ^ !) Uᵣ Πᵣ
                (λ x → extractMaybeEmb (U-elim x))
                (λ x → extractMaybeEmb (Π-elim′ D x))
                U≢Π′

-- U and Π F ▹ G for any F and G cannot be judgmentally equal.
U≢Π : ∀ {rU F rF G Γ} → Γ ⊢ Univ rU ≡ Π F ^ rF ▹ G ^ ! → ⊥
U≢Π U≡Π =
  let _ , ⊢Π = syntacticEq U≡Π
  in  U≢Π-red (id ⊢Π) U≡Π

U≢ne′ : ∀ {r r' K Γ l l′}
       ([U] : Γ ⊩′⟨ l ⟩U)
       ([K] : Γ ⊩ne K ^ r')
     → ShapeView Γ l l′ _ _ _ _ (Uᵣ {r = r} [U]) (ne [K]) → ⊥
U≢ne′ a b ()

U≢ne-red : ∀ {rU r B K Γ} → Γ ⊢ B ⇒* K ^ r → Neutral K → Γ ⊢ Univ rU ≡ B ^ ! → ⊥
U≢ne-red D neK = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩U) (λ Γ l B → Γ ⊩ne B ^ !) Uᵣ ne
                     (λ x → extractMaybeEmb (U-elim x))
                     (λ x → extractMaybeEmb (ne-elim′ D neK x))
                     U≢ne′

-- U and K for any neutral K cannot be judgmentally equal.
U≢ne : ∀ {r K Γ} → Neutral K → Γ ⊢ Univ r ≡ K ^ ! → ⊥
U≢ne neK U≡K =
  let _ , ⊢K = syntacticEq U≡K
  in  U≢ne-red (id ⊢K) neK U≡K

-- ℕ≢Π′ : ∀ {A B Γ l l′}
--        ([ℕ] : Γ ⊩ℕ A)
--        ([Π] : Γ ⊩′⟨ l′ ⟩Π B)
--      → ShapeView Γ l l′ _ _ (ℕᵣ [ℕ]) (Πᵣ [Π]) → ⊥
-- ℕ≢Π′ a b ()

-- ℕ≢Π-red : ∀ {A B F G Γ} → Γ ⊢ A ⇒* ℕ → Γ ⊢ B ⇒* Π F ▹ G → Γ ⊢ A ≡ B → ⊥
-- ℕ≢Π-red D D′ = A≢B (λ Γ l A → Γ ⊩ℕ A)
--                    (λ Γ l A → Γ ⊩′⟨ l ⟩Π A) ℕᵣ Πᵣ
--                    (λ x → extractMaybeEmb (ℕ-elim′ D x))
--                    (λ x → extractMaybeEmb (Π-elim′ D′ x))
--                    ℕ≢Π′

-- -- ℕ and Π F ▹ G for any F and G cannot be judgmentally equal.
-- ℕ≢Π : ∀ {F G Γ} → Γ ⊢ ℕ ≡ Π F ▹ G → ⊥
-- ℕ≢Π ℕ≡Π =
--   let ⊢ℕ , ⊢Π = syntacticEq ℕ≡Π
--   in  ℕ≢Π-red (id ⊢ℕ) (id ⊢Π) ℕ≡Π

-- -- Empty and Π
-- Empty≢Π′ : ∀ {A B Γ l l′}
--        ([Empty] : Γ ⊩Empty A)
--        ([Π] : Γ ⊩′⟨ l′ ⟩Π B)
--      → ShapeView Γ l l′ _ _ (Emptyᵣ [Empty]) (Πᵣ [Π]) → ⊥
-- Empty≢Π′ a b ()

-- Empty≢Π-red : ∀ {A B F G Γ} → Γ ⊢ A ⇒* Empty → Γ ⊢ B ⇒* Π F ▹ G → Γ ⊢ A ≡ B → ⊥
-- Empty≢Π-red D D′ = A≢B (λ Γ l A → Γ ⊩Empty A)
--                    (λ Γ l A → Γ ⊩′⟨ l ⟩Π A) Emptyᵣ Πᵣ
--                    (λ x → extractMaybeEmb (Empty-elim′ D x))
--                    (λ x → extractMaybeEmb (Π-elim′ D′ x))
--                    Empty≢Π′

-- Empty≢Πⱼ : ∀ {F G Γ} → Γ ⊢ Empty ≡ Π F ▹ G → ⊥
-- Empty≢Πⱼ Empty≡Π =
--   let ⊢Empty , ⊢Π = syntacticEq Empty≡Π
--   in  Empty≢Π-red (id ⊢Empty) (id ⊢Π) Empty≡Π


-- ℕ≢ne′ : ∀ {A K Γ l l′}
--        ([ℕ] : Γ ⊩ℕ A)
--        ([K] : Γ ⊩ne K)
--      → ShapeView Γ l l′ _ _ (ℕᵣ [ℕ]) (ne [K]) → ⊥
-- ℕ≢ne′ a b ()

-- ℕ≢ne-red : ∀ {A B K Γ} → Γ ⊢ A ⇒* ℕ → Γ ⊢ B ⇒* K → Neutral K → Γ ⊢ A ≡ B → ⊥
-- ℕ≢ne-red D D′ neK = A≢B (λ Γ l A → Γ ⊩ℕ A) (λ Γ l B → Γ ⊩ne B) ℕᵣ ne
--                         (λ x → extractMaybeEmb (ℕ-elim′ D x))
--                         (λ x → extractMaybeEmb (ne-elim′ D′ neK x))
--                         ℕ≢ne′

-- -- ℕ and K for any neutral K cannot be judgmentally equal.
-- ℕ≢ne : ∀ {K Γ} → Neutral K → Γ ⊢ ℕ ≡ K → ⊥
-- ℕ≢ne neK ℕ≡K =
--   let ⊢ℕ , ⊢K = syntacticEq ℕ≡K
--   in  ℕ≢ne-red (id ⊢ℕ) (id ⊢K) neK ℕ≡K

-- -- Empty and neutral
-- Empty≢ne′ : ∀ {A K Γ l l′}
--        ([Empty] : Γ ⊩Empty A)
--        ([K] : Γ ⊩ne K)
--      → ShapeView Γ l l′ _ _ (Emptyᵣ [Empty]) (ne [K]) → ⊥
-- Empty≢ne′ a b ()

-- Empty≢ne-red : ∀ {A B K Γ} → Γ ⊢ A ⇒* Empty → Γ ⊢ B ⇒* K → Neutral K → Γ ⊢ A ≡ B → ⊥
-- Empty≢ne-red D D′ neK = A≢B (λ Γ l A → Γ ⊩Empty A) (λ Γ l B → Γ ⊩ne B) Emptyᵣ ne
--                         (λ x → extractMaybeEmb (Empty-elim′ D x))
--                         (λ x → extractMaybeEmb (ne-elim′ D′ neK x))
--                         Empty≢ne′

-- Empty≢neⱼ : ∀ {K Γ} → Neutral K → Γ ⊢ Empty ≡ K → ⊥
-- Empty≢neⱼ neK Empty≡K =
--   let ⊢Empty , ⊢K = syntacticEq Empty≡K
--   in  Empty≢ne-red (id ⊢Empty) (id ⊢K) neK Empty≡K


-- Π≢ne′ : ∀ {A K Γ l l′}
--        ([Π] : Γ ⊩′⟨ l ⟩Π A)
--        ([K] : Γ ⊩ne K)
--      → ShapeView Γ l l′ _ _ (Πᵣ [Π]) (ne [K]) → ⊥
-- Π≢ne′ a b ()

-- Π≢ne-red : ∀ {A B F G K Γ} → Γ ⊢ A ⇒* Π F ▹ G → Γ ⊢ B ⇒* K → Neutral K
--      → Γ ⊢ A ≡ B → ⊥
-- Π≢ne-red D D′ neK = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩Π A)
--                         (λ Γ l B → Γ ⊩ne B) Πᵣ ne
--                         (λ x → extractMaybeEmb (Π-elim′ D x))
--                         (λ x → extractMaybeEmb (ne-elim′ D′ neK x))
--                         Π≢ne′

-- -- Π F ▹ G and K for any F and G and neutral K cannot be judgmentally equal.
-- Π≢ne : ∀ {F G K Γ} → Neutral K → Γ ⊢ Π F ▹ G ≡ K → ⊥
-- Π≢ne neK Π≡K =
--   let ⊢Π , ⊢K = syntacticEq Π≡K
--   in  Π≢ne-red (id ⊢Π) (id ⊢K) neK Π≡K
