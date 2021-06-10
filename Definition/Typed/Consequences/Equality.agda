{-# OPTIONS --without-K  #-}

module Definition.Typed.Consequences.Equality where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.EqRelInstance
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Fundamental.Reducibility

open import Tools.Product
import Tools.PropositionalEquality as PE


U≡A′ : ∀ {A sU Γ l} ([U] : Γ ⊩⟨ l ⟩U)
    → Γ ⊩⟨ l ⟩ Univ sU ≡ A ⦂ 𝕥y / (U-intr [U])
    → A PE.≡ Univ sU
U≡A′ (noemb [U]) [U≡A] = [U≡A]
U≡A′ (emb 0<1 [U]) [U≡A] = U≡A′ [U] [U≡A]

-- If A is judgmentally equal to U, then A is propsitionally equal to U.
U≡A : ∀ {A sU Γ}
    → Γ ⊢ Univ sU ≡ A ⦂ 𝕥y
    → A PE.≡ Univ sU
U≡A {A} U≡A with reducibleEq U≡A
U≡A {A} U≡A | [U] , [A] , [U≡A] =
  U≡A′ (U-elim [U]) (irrelevanceEq [U] (U-intr (U-elim [U])) [U≡A])

ℕ≡A′ : ∀ {A Γ l} ([ℕ] : Γ ⊩⟨ l ⟩ℕ ℕ)
    → Γ ⊩⟨ l ⟩ ℕ ≡ A ⦂ 𝕥y / (ℕ-intr [ℕ])
    → Whnf A
    → A PE.≡ ℕ
ℕ≡A′ (noemb x) [ℕ≡A] whnfA = whnfRed* [ℕ≡A] whnfA
ℕ≡A′ (emb 0<1 [ℕ]) [ℕ≡A] whnfA = ℕ≡A′ [ℕ] [ℕ≡A] whnfA

-- If A in WHNF is judgmentally equal to ℕ, then A is propsitionally equal to ℕ.
ℕ≡A : ∀ {A Γ}
    → Γ ⊢ ℕ ≡ A ⦂ 𝕥y
    → Whnf A
    → A PE.≡ ℕ
ℕ≡A {A} ℕ≡A whnfA with reducibleEq ℕ≡A
ℕ≡A {A} ℕ≡A whnfA | [ℕ] , [A] , [ℕ≡A] =
  ℕ≡A′ (ℕ-elim [ℕ]) (irrelevanceEq [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [ℕ≡A]) whnfA

-- If A in WHNF is judgmentally equal to Empty, then A is propositionally equal to Empty.
Empty≡A′ : ∀ {A Γ l} ([Empty] : Γ ⊩⟨ l ⟩Empty Empty)
    → Γ ⊩⟨ l ⟩ Empty ≡ A ⦂ 𝕥y / (Empty-intr [Empty])
    → Whnf A
    → A PE.≡ Empty
Empty≡A′ (noemb x) [Empty≡A] whnfA = whnfRed* [Empty≡A] whnfA
Empty≡A′ (emb 0<1 [Empty]) [Empty≡A] whnfA = Empty≡A′ [Empty] [Empty≡A] whnfA

Empty≡A : ∀ {A Γ}
    → Γ ⊢ Empty ≡ A ⦂ 𝕥y
    → Whnf A
    → A PE.≡ Empty
Empty≡A {A} Empty≡A whnfA with reducibleEq Empty≡A
Empty≡A {A} Empty≡A whnfA | [Empty] , [A] , [Empty≡A] =
  Empty≡A′ (Empty-elim [Empty]) (irrelevanceEq [Empty] (Empty-intr (Empty-elim [Empty])) [Empty≡A]) whnfA

ne≡A′ : ∀ {A K s Γ l}
     → ([K] : Γ ⊩⟨ l ⟩ne K ⦂ s)
     → Γ ⊩⟨ l ⟩ K ≡ A ⦂ s / (ne-intr [K])
     → Whnf A
     → ∃ λ M → Neutral M × A PE.≡ M
ne≡A′ (noemb [K]) (ne₌ M D′ neM K≡M) whnfA =
  M , neM , (whnfRed* (red D′) whnfA)
ne≡A′ (emb 0<1 [K]) [K≡A] whnfA = ne≡A′ [K] [K≡A] whnfA

-- If A in WHNF is judgmentally equal to K, then there exists a M such that
-- A is propsitionally equal to M.
ne≡A : ∀ {A K s Γ}
    → Neutral K
    → Γ ⊢ K ≡ A ⦂ s
    → Whnf A
    → ∃ λ M → Neutral M × A PE.≡ M
ne≡A {A} neK ne≡A whnfA with reducibleEq ne≡A
ne≡A {A} neK ne≡A whnfA | [ne] , [A] , [ne≡A] =
  ne≡A′ (ne-elim neK [ne])
        (irrelevanceEq [ne] (ne-intr (ne-elim neK [ne])) [ne≡A]) whnfA

Π≡A′ : ∀ {A F G sF sG Γ l} ([Π] : Γ ⊩⟨ l ⟩Π Π F ⦂ sF ▹ G ⦂ sG)
    → Γ ⊩⟨ l ⟩ Π F ⦂ sF ▹ G ≡ A ⦂ sG / (Π-intr [Π])
    → Whnf A
    → ∃₂ λ H E → A PE.≡ Π H ⦂ sF ▹ E
Π≡A′ (noemb (Πᵣ sF′ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) whnfA =
    let _ , sF≡sF′ , _ = Π-PE-injectivity (whnfRed* (red D) Πₙ) in
    F′ , G′ , PE.subst (λ s → _ PE.≡ Π _ ⦂ s ▹ _) (PE.sym sF≡sF′) (whnfRed* D′ whnfA)
Π≡A′ (emb 0<1 [Π]) [Π≡A] whnfA = Π≡A′ [Π] [Π≡A] whnfA

-- If A is judgmentally equal to Π F ▹ G, then there exists H and E such that
-- A is propsitionally equal to  Π H ▹ E.
Π≡A : ∀ {A F G sF sG Γ}
    → Γ ⊢ Π F ⦂ sF ▹ G ≡ A ⦂ sG
    → Whnf A
    → ∃₂ λ H E → A PE.≡ Π H ⦂ sF ▹ E
Π≡A {A} Π≡A whnfA with reducibleEq Π≡A
Π≡A {A} Π≡A whnfA | [Π] , [A] , [Π≡A] =
  Π≡A′ (Π-elim [Π]) (irrelevanceEq [Π] (Π-intr (Π-elim [Π])) [Π≡A]) whnfA
