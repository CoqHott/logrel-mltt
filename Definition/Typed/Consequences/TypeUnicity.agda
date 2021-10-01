{-# OPTIONS --safe #-}

module Definition.Typed.Consequences.TypeUnicity where

open import Definition.Untyped hiding (U≢ℕ; U≢Π; U≢ne; ℕ≢Π; ℕ≢ne; Π≢ne; U≢Empty; ℕ≢Empty; Empty≢Π; Empty≢ne)
open import Definition.Untyped.Properties using (subst-Univ-either)
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.Typed.Consequences.Equality
import Definition.Typed.Consequences.Inequality as Ineq
open import Definition.Typed.Consequences.Inversion
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.NeTypeEq
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.PiNorm
open import Definition.Typed.Consequences.Substitution
open import Definition.Conversion.Stability

open import Tools.Product
open import Tools.Empty
open import Tools.Sum using (_⊎_; inj₁; inj₂)
import Tools.PropositionalEquality as PE

type-uniq : ∀ {Γ t T₁ T₂ r₁ r₂ l₁ l₂} → Γ ⊢ t ∷ T₁ ^ [ r₁ , l₁ ] → Γ ⊢ t ∷ T₂ ^ [ r₂ , l₂ ] →
                 r₁ PE.≡ r₂ × l₁ PE.≡ l₂ × Γ ⊢ T₁ ≡ T₂ ^ [ r₁ , l₁ ]
type-uniq (univ 0<1 x) (univ 0<1 x') = PE.refl , PE.refl , refl (Ugenⱼ x)
type-uniq (ℕⱼ x) (ℕⱼ x₁) = PE.refl , PE.refl , refl (Ugenⱼ x)
type-uniq (Emptyⱼ x) (Emptyⱼ x₁) = PE.refl , PE.refl , refl (Ugenⱼ x)
type-uniq (Πⱼ x ▹ x₁ ▹ X ▹ X₁) (Πⱼ x₂ ▹ x₃ ▹ Y ▹ Y₁) =
    let _ , _ , eU = type-uniq X₁ Y₁
        er , el = Uinjectivity eU
    in PE.refl , PE.refl , PE.subst (λ r → _ ⊢ _ ≡ Univ r _ ^ _ ) er (refl ((Ugenⱼ (wfTerm Y))) )
type-uniq (∃ⱼ X ▹ X₁) (∃ⱼ Y ▹ Y₁) =
    let _ , enextl , eU = type-uniq X Y
        el = next-inj enextl
    in PE.refl , enextl , PE.subst (λ l → _ ⊢ _ ≡ SProp l ^ _ ) el (refl ((Ugenⱼ (wfTerm Y))) )
type-uniq (var xx x) (var _ y) =
    let T≡T , e = varTypeEq′ x y
        er , el = typelevel-injectivity e
    in er , el , PE.subst (λ A → _ ⊢ _ ≡ A ^ _ ) T≡T (refl (syntacticTerm (var xx x)))
type-uniq (lamⱼ x x₁ x₂ X) (lamⱼ y y₁ y₂ Y) =
    let _ , _ , F≡F = type-uniq (un-univ x₂) (un-univ y₂)
        erF , elF = Uinjectivity F≡F
        erG , elG , G≡G = type-uniq X (PE.subst₂ (λ r l → _ ∙ _ ^ [ r , ι l ] ⊢ _ ∷ _ ^ _) (PE.sym erF) (PE.sym elF) Y)       
    in erG , PE.refl , PE.subst₃ (λ rF lF lG → _ ⊢ _ ≡  Π _ ^ rF ° lF ▹ _ ° lG ° _ ^ _) erF elF (ιinj elG)
                                 (univ (Π-cong x x₁ x₂ (refl (un-univ x₂)) (un-univ≡ G≡G)))
type-uniq (X ∘ⱼ X₁) (Y ∘ⱼ Y₁) =
    let er , _ , Π≡Π = type-uniq X Y
        F≡F , erF , elF , elG , G≡G = injectivity Π≡Π
    in er , PE.cong _ elG , (substitutionEq G≡G (substRefl (singleSubst X₁)) (wfTerm X₁))
type-uniq {Γ} ⦅ x , x₁ , X , X₁ ⦆ⱼ (⦅_,_,_,_⦆ⱼ {F = F} {G = G} y y₁ Y Y₁)  =
    let _ , el , F≡F = type-uniq X Y
        _ , el' , G≡G = type-uniq (un-univ x₁) (un-univ (stability (reflConEq (wf x) ∙ sym F≡F)
                                                         (PE.subst (λ l → Γ ∙ F ^ [ % , l ] ⊢ G ^ [ % , l ]) (PE.sym el) y₁)))
    in PE.refl , el , univ (∃-cong x (un-univ≡ F≡F) (un-univ≡ (refl x₁)))
type-uniq (fstⱼ X X₁ X₂) (fstⱼ Y Y₁ Y₂) =
    let er , el , ∃≡∃ = type-uniq X₂ Y₂
        F≡F , _ = ∃injectivity ∃≡∃ 
    in PE.refl , el , F≡F
type-uniq (sndⱼ X X₁ X₂) (sndⱼ Y Y₁ Y₂) =
    let er , el , ∃≡∃ = type-uniq X₂ Y₂
        F≡F , G≡G = ∃injectivity ∃≡∃ 
    in PE.refl , el , substitutionEq G≡G (substRefl (singleSubst (fstⱼ X X₁ X₂))) (wfTerm X)
type-uniq (zeroⱼ x) (zeroⱼ x₁) = PE.refl , PE.refl , refl (univ (ℕⱼ x))
type-uniq (sucⱼ X) (sucⱼ Y) = PE.refl , PE.refl , refl (univ (ℕⱼ (wfTerm X)))
type-uniq (natrecⱼ x X X₁ X₂) (natrecⱼ y Y Y₁ Y₂) =
    let _ , _ , U≡U = type-uniq (un-univ x) (un-univ y)
        er , _ = Uinjectivity U≡U
    in er , PE.refl , refl (substitution x (singleSubst X₂) (wfTerm X) ) 
type-uniq (Emptyrecⱼ x X) (Emptyrecⱼ y Y) =
    let _ , _ , U≡U = type-uniq (un-univ x) (un-univ y)
        er , _ = Uinjectivity U≡U
    in er , PE.refl , refl x
type-uniq (Idⱼ X X₁ X₂) (Idⱼ Y Y₁ Y₂) =
    let _ , enl , U≡U = type-uniq X Y
        el = next-inj enl
    in PE.refl , enl , PE.subst (λ l → _ ⊢ _ ≡ SProp l ^ _) el (refl (Ugenⱼ (wfTerm X))) 
type-uniq (Idreflⱼ X) (Idreflⱼ Y) =
    let _ , el , _ = type-uniq X Y
    in PE.refl , el , refl (syntacticTerm (Idreflⱼ X))
type-uniq (transpⱼ x x₁ X X₁ X₂ X₃) (transpⱼ x₂ x₃ Y Y₁ Y₂ Y₃) =
    let _ , el , _ = type-uniq X Y
    in PE.refl , el , refl (substitution x₁ (singleSubst X₂) (wfTerm X))
type-uniq (castⱼ X X₁ X₂ X₃) (castⱼ Y Y₁ Y₂ Y₃) =
    let er , _ , _ = type-uniq X₃ Y₃
    in er , PE.refl , refl (univ X₁)
type-uniq (castreflⱼ X X₁) (castreflⱼ Y Y₁) = PE.refl , PE.refl , refl (syntacticTerm (castreflⱼ X X₁))
type-uniq (conv X x) Y = let er , el , eA = type-uniq X Y in er , el , trans (sym x) eA 
type-uniq X (conv Y y) =
    let er , el , eA = type-uniq X Y
    in er , el , trans eA (PE.subst₂ (λ r l → _ ⊢ _ ≡ _ ^ [ r , l ]) (PE.sym er) (PE.sym el) y)
  
