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
open import Definition.Typed.Consequences.InjectivitySProp

open import Tools.Product
open import Tools.Empty
open import Tools.Sum using (_⊎_; inj₁; inj₂)
import Tools.PropositionalEquality as PE

type-uniq : ∀ {Γ t T₁ T₂ r₁ l₁ l₂} → Γ ⊢ t ∷ T₁ ^ [ r₁ , l₁ ] → Γ ⊢ t ∷ T₂ ^ [ r₁ , l₂ ] →
                 l₁ PE.≡ l₂ × Γ ⊢ T₁ ≡ T₂ ^ [ r₁ , l₁ ]
type-uniq (univ 0<1 x) (univ 0<1 x') = PE.refl , refl (Ugenⱼ x)
type-uniq (ℕⱼ x) (ℕⱼ x₁) = PE.refl , refl (Ugenⱼ x)
type-uniq (Emptyⱼ x) (Emptyⱼ x₁) = PE.refl , refl (Ugenⱼ x)
type-uniq (Πⱼ x ▹ x₁ ▹ X ▹ X₁) (Πⱼ x₂ ▹ x₃ ▹ Y ▹ Y₁) =
    let _ , eU = type-uniq X₁ Y₁
        er , el = Uinjectivity eU
    in PE.refl , refl ((Ugenⱼ (wfTerm Y)))
type-uniq (∃ⱼ X ▹ X₁) (∃ⱼ Y ▹ Y₁) =
    let enextl , eU = type-uniq X Y
        el = next-inj enextl
    in enextl , refl ((Ugenⱼ (wfTerm Y)))
type-uniq (var xx x) (var _ y) =
    let T≡T , e = varTypeEq′ x y
        er , el = typelevel-injectivity e
    in el , PE.subst (λ A → _ ⊢ _ ≡ A ^ _ ) T≡T (refl (syntacticTerm (var xx x)))
type-uniq (lamⱼ x x₁ x₂ X) (lamⱼ y y₁ y₂ Y) =
    let _ , F≡F = type-uniq (un-univ x₂) (un-univ y₂)
        erF , elF = Uinjectivity F≡F
        elG , G≡G = type-uniq X (PE.subst₂ (λ r l → _ ∙ _ ^ [ r , ι l ] ⊢ _ ∷ _ ^ _) (PE.sym erF) (PE.sym elF) Y)       
    in PE.refl , PE.subst₃ (λ rF lF lG → _ ⊢ _ ≡  Π _ ^ rF ° lF ▹ _ ° lG ° _ ^ _ ^ _) erF elF (ιinj elG)
                           (univ (Π-cong x x₁ x₂ (refl (un-univ x₂)) (un-univ≡ G≡G) )) 
type-uniq {r₁ = !} (_ ▹ _ ▹ _ ▹ X ∘ⱼ X₁) (_ ▹ _ ▹ _ ▹ Y ∘ⱼ Y₁) =
    let _ , Π≡Π = type-uniq X Y
        F≡F , erF , elF , elG , G≡G = injectivity Π≡Π
    in PE.cong _ elG , (substitutionEq G≡G (substRefl (singleSubst X₁)) (wfTerm X₁))
type-uniq {r₁ = %} (l% ▹ _ ▹ _ ▹ X ∘ⱼ X₁) (l%' ▹ _ ▹ _ ▹ Y ∘ⱼ Y₁)
  rewrite proj₁ (l% PE.refl) | proj₂ (l% PE.refl) |  proj₁ (l%' PE.refl) | proj₂ (l%' PE.refl) =   
    let _ , Π≡Π = type-uniq X Y
        F≡F , erF , elF , G≡G = injectivity-irr Π≡Π
    in PE.refl , (substitutionEq G≡G (substRefl (singleSubst X₁)) (wfTerm X₁))
type-uniq {Γ} ⦅ x , x₁ , X , X₁ ⦆ⱼ (⦅_,_,_,_⦆ⱼ {F = F} {G = G} y y₁ Y Y₁)  =
    let el , F≡F = type-uniq X Y
        el' , G≡G = type-uniq (un-univ x₁) (un-univ (stability (reflConEq (wf x) ∙ sym F≡F)
                                                         (PE.subst (λ l → Γ ∙ F ^ [ % , l ] ⊢ G ^ [ % , l ]) (PE.sym el) y₁)))
    in el , univ (∃-cong x (un-univ≡ F≡F) (un-univ≡ (refl x₁)))
type-uniq (fstⱼ X X₁ X₂) (fstⱼ Y Y₁ Y₂) =
    let _ , ∃≡∃ = type-uniq X₂ Y₂
        F≡F , _ = ∃injectivity ∃≡∃ 
    in PE.refl , F≡F
type-uniq (sndⱼ X X₁ X₂) (sndⱼ Y Y₁ Y₂) =
    let _ , ∃≡∃ = type-uniq X₂ Y₂
        F≡F , G≡G = ∃injectivity ∃≡∃ 
    in PE.refl , substitutionEq G≡G (substRefl (singleSubst (fstⱼ X X₁ X₂))) (wfTerm X)
type-uniq (zeroⱼ x) (zeroⱼ x₁) = PE.refl , refl (univ (ℕⱼ x))
type-uniq (sucⱼ X) (sucⱼ Y) = PE.refl , refl (univ (ℕⱼ (wfTerm X)))
type-uniq (natrecⱼ _ x X X₁ X₂) (natrecⱼ _ y Y Y₁ Y₂) =
    let _ , U≡U = type-uniq (un-univ x) (un-univ y)
        er , _ = Uinjectivity U≡U
    in PE.refl , refl (substitution x (singleSubst X₂) (wfTerm X) ) 
type-uniq (Emptyrecⱼ x X) (Emptyrecⱼ y Y) =
    let _ , U≡U = type-uniq (un-univ x) (un-univ y)
        er , _ = Uinjectivity U≡U
    in PE.refl , refl x
type-uniq (Idⱼ X X₁ X₂) (Idⱼ Y Y₁ Y₂) =
    PE.refl , refl (Ugenⱼ (wfTerm X))
type-uniq (Idreflⱼ X) (Idreflⱼ Y) =
    PE.refl , refl (syntacticTerm (Idreflⱼ X))
type-uniq (transpⱼ x x₁ X X₁ X₂ X₃) (transpⱼ x₂ x₃ Y Y₁ Y₂ Y₃) =
    PE.refl , refl (substitution x₁ (singleSubst X₂) (wfTerm X))
type-uniq (castⱼ X X₁ X₂ X₃) (castⱼ Y Y₁ Y₂ Y₃) =
    let _ , _ = type-uniq X₃ Y₃
    in PE.refl , refl (univ X₁)
type-uniq (castreflⱼ X X₁) (castreflⱼ Y Y₁) = PE.refl , refl (syntacticTerm (castreflⱼ X X₁))
type-uniq (conv X x) Y = let el , eA = type-uniq X Y in el , trans (sym x) eA 
type-uniq X (conv Y y) =
    let el , eA = type-uniq X Y
    in el , trans eA (PE.subst (λ l → _ ⊢ _ ≡ _ ^ [ _ , l ]) (PE.sym el) y)
