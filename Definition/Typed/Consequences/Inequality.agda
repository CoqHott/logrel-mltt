{-# OPTIONS --safe #-}

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

A≢B : ∀ {A B rA rB Γ} (_⊩′⟨_⟩A_ _⊩′⟨_⟩B_ : Con Term → TypeLevel → Term → Set)
      (A-intr : ∀ {l} → Γ ⊩′⟨ l ⟩A A → Γ ⊩⟨ l ⟩ A ^ rA)
      (B-intr : ∀ {l} → Γ ⊩′⟨ l ⟩B B → Γ ⊩⟨ l ⟩ B ^ rB)
      (A-elim : ∀ {l} → Γ ⊩⟨ l ⟩ A ^ rA → ∃ λ l′ → Γ ⊩′⟨ l′ ⟩A A)
      (B-elim : ∀ {l} → Γ ⊩⟨ l ⟩ B ^ rA → ∃ λ l′ → Γ ⊩′⟨ l′ ⟩B B)
      (A≢B′ : ∀ {l l′} ([A] : Γ ⊩′⟨ l ⟩A A) ([B] : Γ ⊩′⟨ l′ ⟩B B)
            → ShapeView Γ l l′ A B rA rB (A-intr [A]) (B-intr [B]) → ⊥)
    → Γ ⊢ A ≡ B ^ rA → ⊥
A≢B {A} {B} _ _ A-intr B-intr A-elim B-elim A≢B′ A≡B =
  let X = reducibleEq A≡B
      [A] = proj₁ X
      [B] = proj₁ (proj₂ X)
      [A≡B] = proj₂ (proj₂ X)
      _ , [A]′ = A-elim ([A])
      _ , [B]′ = B-elim ([B])
      [A≡B]′ = irrelevanceEq [A] (A-intr [A]′) [A≡B]
  in  A≢B′ [A]′ [B]′ (goodCases (A-intr [A]′) (B-intr [B]′) [A≡B]′)


U≢ℕ′ : ∀ {Γ A ll B l l′}
       ([U] : Γ ⊩′⟨ l ⟩U A ^ ll)
       ([ℕ] : Γ ⊩ℕ B)
     → ShapeView Γ l l′ _ _ [ ! , _ ] [ ! , _ ] (Uᵣ {ll = ll} [U]) (ℕᵣ [ℕ]) → ⊥
U≢ℕ′ a b ()

U≢ℕ-red : ∀ {ll r lU B Γ} → Γ ⊢ B ⇒* ℕ ^ [ ! , ll ] → Γ ⊢ Univ r lU ≡ B ^ [ ! , ll ] → ⊥
U≢ℕ-red {ll} D = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩U A ^ ll) (λ Γ l B → Γ ⊩ℕ B) Uᵣ ℕᵣ
                (λ x → extractMaybeEmb (U-elim x))
                (λ x → extractMaybeEmb (ℕ-elim′ D x))
                U≢ℕ′

-- U and ℕ cannot be judgmentally equal.
U≢ℕ! : ∀ {r l ll Γ} → Γ ⊢ Univ r l ≡ ℕ ^ [ ! , ll ] → ⊥
U≢ℕ! U≡ℕ =
  let _ , ⊢ℕ = syntacticEq U≡ℕ
  in  U≢ℕ-red (id ⊢ℕ) U≡ℕ

-- U vs Pi
U≢Π′ : ∀ {A lA B rB lB Γ l l′}
       ([U] : Γ ⊩′⟨ l ⟩U A ^ lA)
       ([Π] : Γ ⊩′⟨ l′ ⟩Π B ^[ rB , lB ])
     → ShapeView Γ l l′ _ _ _ _ (Uᵣ {ll = lA} [U]) (Πᵣ [Π]) → ⊥
U≢Π′ a b ()

U≢Π-red : ∀ {ll B F G rF lF lG rU lU Γ} → Γ ⊢ B ⇒* Π F ^ rF ° lF ▹ G ° lG ^ [ ! , ι ll ]
            → Γ ⊢ Univ rU lU ≡ B ^ [ ! , ι ll ] → ⊥
U≢Π-red {ll} D = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩U A ^ ι ll)
                (λ Γ l A → Γ ⊩′⟨ l ⟩Π A ^[ ! , ll ]) Uᵣ Πᵣ
                (λ x → extractMaybeEmb (U-elim x))
                (λ x → extractMaybeEmb (Π-elim′ D x))
                U≢Π′

-- U and Π F ▹ G for any F and G cannot be judgmentally equal.
U≢Π! : ∀ {rU lU F rF lF lG G l Γ} → Γ ⊢ Univ rU lU ≡ Π F ^ rF ° lF ▹ G  ° lG ^ [ ! , ι l ] → ⊥
U≢Π! U≡Π =
  let _ , ⊢Π = syntacticEq U≡Π
  in  U≢Π-red (id ⊢Π) U≡Π

U≢ne′ : ∀ {A lU r lK K Γ l l′}
       ([U] : Γ ⊩′⟨ l ⟩U A ^ lU)
       ([K] : Γ ⊩ne K ^[ r , lK ] )
     → ShapeView Γ l l′ _ _ _ _ (Uᵣ {ll = lU} [U]) (ne [K]) → ⊥
U≢ne′ a b ()


U≢ne-red : ∀ {ll rU lU B K Γ} → Γ ⊢ B ⇒* K ^ [ ! , ι ll ] → Neutral K → Γ ⊢ Univ rU lU ≡ B ^ [ ! , ι ll ] → ⊥
U≢ne-red {ll} D neK = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩U A ^ ι ll) (λ Γ l B → Γ ⊩ne B ^[ ! , ll ]) Uᵣ ne
                     (λ x → extractMaybeEmb (U-elim x))
                     (λ x → extractMaybeEmb (ne-elim′ D neK x PE.refl))
                     U≢ne′

-- U and K for any neutral K cannot be judgmentally equal.
U≢ne! : ∀ {r l ll K Γ} → Neutral K → Γ ⊢ Univ r l ≡ K ^ [ ! , ι ll ] → ⊥
U≢ne! neK U≡K =
  let _ , ⊢K = syntacticEq U≡K
  in  U≢ne-red (id ⊢K) neK U≡K

ℕ≢Π′ : ∀ {A B Γ ll l l′}
       ([ℕ] : Γ ⊩ℕ A)
       ([Π] : Γ ⊩′⟨ l′ ⟩Π B ^[ ! , ll ])
     → ShapeView Γ l l′ _ _ _ _ (ℕᵣ [ℕ]) (Πᵣ [Π]) → ⊥
ℕ≢Π′ a b ()


ℕ≢Π-red : ∀ {A B F rF lF lG G Γ} → Γ ⊢ A ⇒* ℕ ^ [ ! , ι ⁰ ] → Γ ⊢ B ⇒* Π F ^ rF ° lF ▹ G ° lG ^ [ ! , ι ⁰ ] → Γ ⊢ A ≡ B ^ [ ! , ι ⁰ ] → ⊥
ℕ≢Π-red D D′ = A≢B (λ Γ l A → Γ ⊩ℕ A)
                   (λ Γ l A → Γ ⊩′⟨ l ⟩Π A ^[ ! , ⁰ ]) ℕᵣ Πᵣ
                   (λ x → extractMaybeEmb (ℕ-elim′ D x))
                   (λ x → extractMaybeEmb (Π-elim′ D′ x))
                   ℕ≢Π′

-- ℕ and Π F ▹ G for any F and G cannot be judgmentally equal.
ℕ≢Π! : ∀ {F rF G lF lG  Γ} → Γ ⊢ ℕ ≡ Π F ^ rF ° lF ▹ G ° lG ^ [ ! , ι ⁰ ]  → ⊥
ℕ≢Π! ℕ≡Π =
  let ⊢ℕ , ⊢Π = syntacticEq ℕ≡Π
  in  ℕ≢Π-red (id ⊢ℕ) (id ⊢Π) ℕ≡Π

-- Empty and Π
Empty≢Π′ : ∀ {ll A B Γ l l′}
       ([Empty] : Γ ⊩Empty A ^ ll)
       ([Π] : Γ ⊩′⟨ l′ ⟩Π B ^[ % , ll ])
     → ShapeView Γ l l′ _ _ _ _ (Emptyᵣ [Empty]) (Πᵣ [Π]) → ⊥
Empty≢Π′ a b ()

Empty≢Π-red : ∀ {ll A B F rF lF lG G Γ} → Γ ⊢ A ⇒* Empty ^ [ % , ι ll ] → Γ ⊢ B ⇒* Π F ^ rF ° lF ▹ G ° lG ^ [ % , ι ll ]
                → Γ ⊢ A ≡ B ^ [ % , ι ll ] → ⊥
Empty≢Π-red {ll} D D′ = A≢B (λ Γ l A → Γ ⊩Empty A ^ ll)
                   (λ Γ l A → Γ ⊩′⟨ l ⟩Π A ^[ % , ll ]) Emptyᵣ Πᵣ
                   (λ x → extractMaybeEmb (Empty-elim′ D x))
                   (λ x → extractMaybeEmb (Π-elim′ D′ x))
                   Empty≢Π′

Empty≢Π% : ∀ {F rF lF lG l G Γ} → Γ ⊢ Empty ≡ Π F ^ rF ° lF ▹ G ° lG ^ [ % , ι l ] → ⊥
Empty≢Π% Empty≡Π =
  let ⊢Empty , ⊢Π = syntacticEq Empty≡Π
  in  Empty≢Π-red (id ⊢Empty) (id ⊢Π) Empty≡Π

ℕ≢ne′ : ∀ {ll A K Γ l l′}
       ([ℕ] : Γ ⊩ℕ A)
       ([K] : Γ ⊩ne K ^[ ! , ll ])
     → ShapeView Γ l l′ _ _ _ _ (ℕᵣ [ℕ]) (ne [K]) → ⊥
ℕ≢ne′ a b ()

ℕ≢ne-red : ∀ {A B K Γ} → Γ ⊢ A ⇒* ℕ ^ [ ! , ι ⁰ ] → Γ ⊢ B ⇒* K ^ [ ! , ι ⁰ ] → Neutral K → Γ ⊢ A ≡ B ^ [ ! , ι ⁰ ] → ⊥
ℕ≢ne-red D D′ neK = A≢B (λ Γ l A → Γ ⊩ℕ A) (λ Γ l B → Γ ⊩ne B ^[ ! , ⁰ ]) ℕᵣ ne
                        (λ x → extractMaybeEmb (ℕ-elim′ D x))
                        (λ x → extractMaybeEmb (ne-elim′ D′ neK x PE.refl ))
                        ℕ≢ne′

-- ℕ and K for any neutral K cannot be judgmentally equal.
ℕ≢ne! : ∀ {K Γ} → Neutral K → Γ ⊢ ℕ ≡ K ^ [ ! , ι ⁰ ] → ⊥
ℕ≢ne! neK ℕ≡K =
  let ⊢ℕ , ⊢K = syntacticEq ℕ≡K
  in  ℕ≢ne-red (id ⊢ℕ) (id ⊢K) neK ℕ≡K

-- Empty and neutral
Empty≢ne′ : ∀ {ll A K Γ l l′}
       ([Empty] : Γ ⊩Empty A ^ ll)
       ([K] : Γ ⊩ne K ^[ % , ll ])
     → ShapeView Γ l l′ _ _ _ _ (Emptyᵣ [Empty]) (ne [K]) → ⊥
Empty≢ne′ a b ()


Empty≢ne-red : ∀ {ll A B K Γ} → Γ ⊢ A ⇒* Empty ^ [ % , ι ll ] → Γ ⊢ B ⇒* K ^ [ % , ι ll ] →
                                Neutral K → Γ ⊢ A ≡ B ^ [ % , ι ll ] → ⊥
Empty≢ne-red {ll} D D′ neK = A≢B (λ Γ l A → Γ ⊩Empty A ^ ll) (λ Γ l B → Γ ⊩ne B ^[ % , ll ]) Emptyᵣ ne
                        (λ x → extractMaybeEmb (Empty-elim′ D x))
                        (λ x → extractMaybeEmb (ne-elim′ D′ neK x PE.refl))
                        Empty≢ne′

Empty≢ne% : ∀ {l K Γ} → Neutral K → Γ ⊢ Empty ≡ K ^ [ % , ι l ]  → ⊥
Empty≢ne% neK Empty≡K =
  let ⊢Empty , ⊢K = syntacticEq Empty≡K
  in  Empty≢ne-red (id ⊢Empty) (id ⊢K) neK Empty≡K

Π≢ne′ : ∀ {ll A K r Γ l l′}
       ([Π] : Γ ⊩′⟨ l ⟩Π A ^[ r , ll ])
       ([K] : Γ ⊩ne K ^[ r , ll ])
     → ShapeView Γ l l′ _ _ _ _ (Πᵣ [Π]) (ne [K]) → ⊥
Π≢ne′ a b ()

Π≢ne-red : ∀ {ll r A B F rF lF lG G K Γ} → Γ ⊢ A ⇒* Π F ^ rF ° lF ▹ G ° lG ^ [ r , ι ll ]
                                         → Γ ⊢ B ⇒* K ^ [ r , ι ll ] → Neutral K
                                         → Γ ⊢ A ≡ B ^ [ r , ι ll ] → ⊥
Π≢ne-red {ll} {r} D D′ neK = A≢B (λ Γ l A → Γ ⊩′⟨ l ⟩Π A ^[ r , ll ])
                        (λ Γ l B → Γ ⊩ne B ^[ r , ll ]) Πᵣ ne
                        (λ x → extractMaybeEmb (Π-elim′ D x))
                        (λ x → extractMaybeEmb (ne-elim′ D′ neK x PE.refl))
                        Π≢ne′

-- Π F ▹ G and K for any F and G and neutral K cannot be judgmentally equal.
Π≢ne : ∀ {F rF lF lG G K r l Γ} → Neutral K → Γ ⊢ Π F ^ rF ° lF ▹ G ° lG ≡ K ^ [ r , ι l ] → ⊥
Π≢ne neK Π≡K =
  let ⊢Π , ⊢K = syntacticEq Π≡K
  in  Π≢ne-red (id ⊢Π) (id ⊢K) neK Π≡K
