{-# OPTIONS --safe #-}

module Definition.Typed.Consequences.TypeUnicity where

open import Definition.Untyped hiding (U≢ℕ; U≢Π; U≢ne; ℕ≢Π; ℕ≢ne; Π≢ne; U≢Empty; ℕ≢Empty; Empty≢Π; Empty≢ne)
open import Definition.Untyped.Properties using (subst-Univ-either)
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.Typed.Consequences.Equality
import Definition.Typed.Consequences.Inequality as Ineq
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.NeTypeEq
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.RelevanceUnicity
open import Definition.Typed.Consequences.Substitution
open import Definition.Conversion.Stability

open import Tools.Product
open import Tools.Empty
open import Tools.Sum using (_⊎_; inj₁; inj₂)
import Tools.PropositionalEquality as PE

type-uniq : ∀ {Γ t T₁ T₂ r₁ r₂ l₁ l₂} → Γ ⊢ t ∷ T₁ ^ [ r₁ , l₁ ] → Γ ⊢ t ∷ T₂ ^ [ r₂ , l₂ ] →
                 r₁ PE.≡ r₂
type-uniq (univ 0<1 x) (univ 0<1 x') = PE.refl 
type-uniq (ℕⱼ x) (ℕⱼ x₁) = PE.refl 
type-uniq (Emptyⱼ x) (Emptyⱼ x₁) = PE.refl
type-uniq (Πⱼ x ▹ x₁ ▹ X ▹ X₁) (Πⱼ x₂ ▹ x₃ ▹ Y ▹ Y₁) =
          PE.refl 
type-uniq (∃ⱼ X ▹ X₁) (∃ⱼ Y ▹ Y₁) = PE.refl
type-uniq (var xx x) (var _ y) =
    let T≡T , e = varTypeEq′ x y
        er , el = typelevel-injectivity e
    in er
type-uniq (lamⱼ x x₁ x₂ X) (lamⱼ y y₁ y₂ Y) =
  let erF , elF  = relevance-unicity x₂ y₂
  in type-uniq X (PE.subst₂ (λ r l → _ ∙ _ ^ [ r , ι l ] ⊢ _ ∷ _ ^ _) (PE.sym erF) (PE.sym (ιinj elF)) Y)
type-uniq (_ ▹ _ ▹ _ ▹ X ∘ⱼ X₁) (_ ▹ _ ▹ _ ▹ Y ∘ⱼ Y₁) = type-uniq X Y
type-uniq {Γ} ⦅ x , x₁ , X , X₁ ⦆ⱼ (⦅_,_,_,_⦆ⱼ {F = F} {G = G} y y₁ Y Y₁)  = PE.refl 
type-uniq (fstⱼ X X₁ X₂) (fstⱼ Y Y₁ Y₂) =
    PE.refl 
type-uniq (sndⱼ X X₁ X₂) (sndⱼ Y Y₁ Y₂) = PE.refl
type-uniq (zeroⱼ x) (zeroⱼ x₁) = PE.refl 
type-uniq (sucⱼ X) (sucⱼ Y) = PE.refl 
type-uniq (natrecⱼ _ x X X₁ X₂) (natrecⱼ _ y Y Y₁ Y₂) = type-uniq X₁ Y₁
type-uniq (Emptyrecⱼ x X) (Emptyrecⱼ y Y) = let er , el = relevance-unicity x y in er
type-uniq (Idⱼ X X₁ X₂) (Idⱼ Y Y₁ Y₂) =
    PE.refl 
type-uniq (Idreflⱼ X) (Idreflⱼ Y) =
    PE.refl 
type-uniq (transpⱼ x x₁ X X₁ X₂ X₃) (transpⱼ x₂ x₃ Y Y₁ Y₂ Y₃) =
    PE.refl 
type-uniq (castⱼ X X₁ X₂ X₃) (castⱼ Y Y₁ Y₂ Y₃) = type-uniq X₃ Y₃
type-uniq (castreflⱼ X X₁) (castreflⱼ Y Y₁) = PE.refl 
type-uniq (conv X x) Y = type-uniq X Y
type-uniq X (conv Y y) = type-uniq X Y
  
