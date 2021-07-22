{-# OPTIONS --safe #-}

module Definition.Typed.Consequences.Equality where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.EqRelInstance
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties.Escape
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Fundamental.Reducibility
open import Definition.Typed.Consequences.Injectivity

open import Tools.Product
import Tools.PropositionalEquality as PE


{-


-- conversion is cumulative 

typeCumul′ : ∀ {A rA lA lA' Γ} → lA ≤∞ lA' →  Γ ⊩⟨ ∞ ⟩ A ^ [ rA , lA ] → Γ ⊩⟨ ∞ ⟩ A ^ [ rA , lA' ] 
typeCumul′ (≡is≤∞ PE.refl) [A] = [A]
typeCumul′ (<∞is≤∞ emb<) (Uᵣ (Uᵣ r l′ l<₁ eq d)) = emb ∞< (Uᵣ (Uᵣ r ⁰ emb< PE.refl {!!}))
typeCumul′ (<∞is≤∞ ∞<) (Uᵣ (Uᵣ r l′ l<₁ eq d)) = Uᵣ (Uᵣ r ¹ ∞< PE.refl {!!})
typeCumul′ (<∞is≤∞ emb<) (ℕᵣ [[ ⊢A , ⊢B , D ]]) = emb ∞< (emb emb< {!ℕᵣ ?!})
typeCumul′ (<∞is≤∞ l<) (Emptyᵣ x) = {!!}
typeCumul′ (<∞is≤∞ l<) (ne x) = {!!}
typeCumul′ (<∞is≤∞ l<) (Πᵣ x) = {!!}
typeCumul′ (<∞is≤∞ l<) (∃ᵣ x) = {!!}
typeCumul′ (<∞is≤∞ l<) (emb l<₁ [A]) = {!!}

convCumul′ : ∀ {A B rA lA lA' Γ} → (l< : lA ≤∞ lA') → ([A] : Γ ⊩⟨ ∞ ⟩ A ^ [ rA , lA ])
             → Γ ⊩⟨ ∞ ⟩ A ≡ B ^ [ rA , lA ] / [A] → Γ ⊩⟨ ∞ ⟩ A ≡ B ^ [ rA , lA' ] / typeCumul′ l< [A]
convCumul′ (<∞is≤∞ l<) [A] [A≡B] = {!!}
convCumul′ (≡is≤∞ PE.refl) [A] [A≡B] = [A≡B]


convCumul : ∀ {A B rA lA lA' Γ} → lA ≤∞ lA' → Γ ⊢ A ≡ B ^ [ rA , lA ] → Γ ⊢ A ≡ B ^ [ rA , lA' ]
convCumul {A} {B} {rA} {lA} {lA'} {Γ} (<∞is≤∞ l<) A≡B =
  let X = reducibleEq A≡B
      [A] = proj₁ X
      [B] = proj₁ (proj₂ X)
      [A≡B] = proj₂ (proj₂ X)
      [A]' : Γ ⊩⟨ ∞ ⟩ A ^ [ rA , lA' ]
      [A]' = emb l< {!!} -- [A]
  in {!escapeEq [A]' [A≡B]!}                        
-- convCumul (<∞is≤∞ ∞<) A≡B =
--   let X = reducibleEq A≡B
--       [A] = proj₁ X
--       [B] = proj₁ (proj₂ X)
--       [A≡B] = proj₂ (proj₂ X)
--   in {!!}                        
convCumul (≡is≤∞ PE.refl) A≡B = A≡B
-}



U≡A′ : ∀ {A rU Γ l lU nlU } ([U] : Γ ⊩⟨ l ⟩U Univ rU lU ^ nlU) 
    → Γ ⊩⟨ l ⟩ Univ rU lU ≡ A ^ [ ! , nlU ] / (U-intr [U])
    → Γ ⊢ A ⇒* Univ rU lU ^ [ ! , nlU ]
U≡A′ (noemb (Uᵣ r l′ l< eq d)) [U≡A] =
 let r≡r , l≡l  = Uinjectivity (subset* (red d))
 in PE.subst (λ r → _ ⊢ _ ⇒* Univ r _ ^ [ ! , _ ]) (PE.sym r≡r)
         (PE.subst (λ l → _ ⊢ _ ⇒* Univ _ l ^ [ ! , _ ]) (PE.sym l≡l) [U≡A])
U≡A′ (emb emb< [U]) [U≡A] = U≡A′ [U] [U≡A] 
U≡A′ (emb ∞< [U]) [U≡A] = U≡A′ [U] [U≡A] 

-- If A is judgmentally equal to U, then A reduces to U.
U≡A : ∀ {A rU Γ lU nlU }
    → Γ ⊢ Univ rU lU ≡ A ^ [ ! , nlU ]
    → Γ ⊢ A ⇒* Univ rU lU ^ [ ! , nlU ]
U≡A {A} U≡A =
  let X = reducibleEq U≡A
      [U] = proj₁ X
      [A] = proj₁ (proj₂ X)
      [U≡A] = proj₂ (proj₂ X)
  in U≡A′ (U-elim [U]) (irrelevanceEq [U] (U-intr (U-elim [U])) [U≡A])

-- If A is judgmentally equal to U, then A reduces to U.
U≡A-whnf : ∀ {A rU Γ lU nlU }
    → Γ ⊢ Univ rU lU ≡ A ^ [ ! , nlU ]
    → Whnf A
    → A PE.≡ Univ rU lU
U≡A-whnf {A} X whnfA = whnfRed* (U≡A X) whnfA

ℕ≡A′ : ∀ {A Γ l} ([ℕ] : Γ ⊩⟨ l ⟩ℕ ℕ)
    → Γ ⊩⟨ l ⟩ ℕ ≡ A ^ [ ! , ι ⁰ ] / (ℕ-intr [ℕ])
    → Whnf A
    → A PE.≡ ℕ
ℕ≡A′ (noemb x) [ℕ≡A] whnfA = whnfRed* [ℕ≡A] whnfA
ℕ≡A′ (emb emb< [ℕ]) [ℕ≡A] whnfA = ℕ≡A′ [ℕ] [ℕ≡A] whnfA
ℕ≡A′ (emb ∞< [ℕ]) [ℕ≡A] whnfA = ℕ≡A′ [ℕ] [ℕ≡A] whnfA

-- If A in WHNF is judgmentally equal to ℕ, then A is propsitionally equal to ℕ.
ℕ≡A : ∀ {A Γ}
    → Γ ⊢ ℕ ≡ A ^ [ ! , ι ⁰ ]
    → Whnf A
    → A PE.≡ ℕ
ℕ≡A {A} ℕ≡A whnfA =
  let X = reducibleEq ℕ≡A
      [ℕ] = proj₁ X
      [A] = proj₁ (proj₂ X)
      [ℕ≡A] = proj₂ (proj₂ X)
  in ℕ≡A′ (ℕ-elim [ℕ]) (irrelevanceEq [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [ℕ≡A]) whnfA

-- If A in WHNF is judgmentally equal to Empty, then A is propositionally equal to Empty.
Empty≡A′ : ∀ {A Γ l ll} ([Empty] : Γ ⊩⟨ l ⟩Empty Empty ^ ll)
    → Γ ⊩⟨ l ⟩ Empty ≡ A ^ [ % , ι ll ] / (Empty-intr [Empty])
    → Whnf A
    → A PE.≡ Empty
Empty≡A′ (noemb x) [Empty≡A] whnfA = whnfRed* [Empty≡A] whnfA
Empty≡A′ (emb emb< [Empty]) [Empty≡A] whnfA = Empty≡A′ [Empty] [Empty≡A] whnfA
Empty≡A′ (emb ∞< [Empty]) [Empty≡A] whnfA = Empty≡A′ [Empty] [Empty≡A] whnfA

Empty≡A : ∀ {A Γ l}
    → Γ ⊢ Empty ≡ A ^ [ % , ι l ]
    → Whnf A
    → A PE.≡ Empty
Empty≡A {A} Empty≡A whnfA =
  let X = reducibleEq Empty≡A
      [Empty] = proj₁ X
      [A] = proj₁ (proj₂ X)
      [Empty≡A] = proj₂ (proj₂ X)
  in Empty≡A′ (Empty-elim [Empty]) (irrelevanceEq [Empty] (Empty-intr (Empty-elim [Empty])) [Empty≡A]) whnfA

ne≡A′ : ∀ {A K r Γ l ll }
     → ([K] : Γ ⊩⟨ l ⟩ne K ^[ r , ll ] )
     → Γ ⊩⟨ l ⟩ K ≡ A ^ [ r , ι ll ] / (ne-intr [K])
     → Whnf A
     → ∃ λ M → Neutral M × A PE.≡ M
ne≡A′ (noemb [K]) (ne₌ M D′ neM K≡M) whnfA =
  M , neM , (whnfRed* (red D′) whnfA)
ne≡A′ (emb emb< [K]) [K≡A] whnfA = ne≡A′ [K] [K≡A] whnfA
ne≡A′ (emb ∞< [K]) [K≡A] whnfA = ne≡A′ [K] [K≡A] whnfA

-- If A in WHNF is judgmentally equal to K, then there exists a M such that
-- A is propsitionally equal to M.
ne≡A : ∀ {A K r l Γ}
    → Neutral K
    → Γ ⊢ K ≡ A ^ [ r , ι l ]
    → Whnf A
    → ∃ λ M → Neutral M × A PE.≡ M
ne≡A {A} neK ne≡A whnfA =
  let X = reducibleEq ne≡A
      [ne] = proj₁ X
      [A] = proj₁ (proj₂ X)
      [ne≡A] = proj₂ (proj₂ X)
  in ne≡A′ (ne-elim neK [ne])
        (irrelevanceEq [ne] (ne-intr (ne-elim neK [ne])) [ne≡A]) whnfA


Π≡A′ : ∀ {A F G rF lF lG rΠ lΠ Γ l} ([Π] : Γ ⊩⟨ l ⟩Π Π F ^ rF ° lF ▹ G ° lG ^[ rΠ , lΠ ] )
    → Γ ⊩⟨ l ⟩ Π F ^ rF ° lF ▹ G ° lG ≡ A ^ [ rΠ ,  ι lΠ ] / (Π-intr [Π])
    → Whnf A
    → ∃₂ λ H E → A PE.≡ Π H ^ rF ° lF ▹ E ° lG
Π≡A′ (noemb (Πᵣ rF′ lF′ lG′ lF≤ lG≤  F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) whnfA =
    let _ , rF≡rF′ , lF≡lF′ , _ , lG≡lG′ = Π-PE-injectivity (whnfRed* (red D) Πₙ)
        X = whnfRed* D′ whnfA
    in F′ , G′ ,
       PE.subst (λ r → _ PE.≡ Π _ ^ r ° _ ▹ _ ° _) (PE.sym rF≡rF′)
         (PE.subst (λ l → _ PE.≡ Π _ ^ _ ° l ▹ _ ° _) (PE.sym lF≡lF′)
           (PE.subst (λ l → _ PE.≡ Π _ ^ _ ° _ ▹ _ ° l) (PE.sym lG≡lG′) X))
Π≡A′ (emb emb< [Π]) [Π≡A] whnfA = Π≡A′ [Π] [Π≡A] whnfA
Π≡A′ (emb ∞< [Π]) [Π≡A] whnfA = Π≡A′ [Π] [Π≡A] whnfA

-- If A is judgmentally equal to Π F ▹ G, then there exists H and E such that
-- A is propositionally equal to Π H ▹ E.
Π≡A : ∀ {A F G rF lF lG rΠ lΠ Γ}
    → Γ ⊢ Π F ^ rF ° lF ▹ G ° lG ≡ A ^ [ rΠ ,  ι lΠ ]
    → Whnf A
    → ∃₂ λ H E → A PE.≡ Π H ^ rF ° lF ▹ E ° lG
Π≡A {A} Π≡A whnfA  =
  let X = reducibleEq Π≡A
      [Π] = proj₁ X
      [A] = proj₁ (proj₂ X)
      [Π≡A] = proj₂ (proj₂ X)
  in Π≡A′ (Π-elim [Π]) (irrelevanceEq [Π] (Π-intr (Π-elim [Π])) [Π≡A]) whnfA
