{-# OPTIONS --safe #-}

module Definition.Typed.Consequences.NeTypeEq where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.Substitution

open import Tools.Product
import Tools.PropositionalEquality as PE

ιinj : ∀ {l l'} → ι l PE.≡ ι l' → l PE.≡ l'
ιinj {⁰} {⁰} e = PE.refl
ιinj {¹} {¹} e = PE.refl


-- to be moved in Untyped

typelevel-injectivity : ∀ {r r' l l'} → [ r , l ] PE.≡ [ r' , l' ] → r PE.≡ r' × l PE.≡ l'
typelevel-injectivity PE.refl = PE.refl , PE.refl

-- Helper function for the same variable instance of a context have equal types.
varTypeEq′ : ∀ {n R rR T rT Γ} → n ∷ R ^ rR ∈ Γ → n ∷ T ^ rT ∈ Γ → R PE.≡ T × rR PE.≡ rT
varTypeEq′ here here = PE.refl , PE.refl
varTypeEq′ (there n∷R) (there n∷T) with varTypeEq′ n∷R n∷T
... | PE.refl , PE.refl = PE.refl , PE.refl

-- The same variable instance of a context have equal types.
varTypeEq : ∀ {x A B rA rB Γ} → Γ ⊢ A ^ rA → Γ ⊢ B ^ rB
          → x ∷ A ^ rA ∈ Γ
          → x ∷ B ^ rB ∈ Γ
          → Γ ⊢ A ≡ B ^ rA × rA PE.≡ rB
varTypeEq A B x∷A x∷B with varTypeEq′ x∷A x∷B
... | PE.refl , PE.refl = refl A , PE.refl



-- The same neutral term have equal types.
-- to use this with different relevances rA rB we need unicity of relevance for types
neTypeEq : ∀ {t A B rA lA lA' Γ} → Neutral t → Γ ⊢ t ∷ A ^ [ rA , lA ] → Γ ⊢ t ∷ B ^ [ rA , lA' ] →
  lA PE.≡ lA' × Γ ⊢ A ≡ B ^ [ rA , lA ]
neTypeEq (var x) (var x₁ x₂) (var x₃ x₄) =
  let V , e = varTypeEq (syntacticTerm (var x₃ x₂)) (syntacticTerm (var x₃ x₄)) x₂ x₄
      _ , el = typelevel-injectivity e
  in el , V 
neTypeEq (∘ₙ neT) (t∷A ∘ⱼ t∷A₁) (t∷B ∘ⱼ t∷B₁) with neTypeEq neT t∷A t∷B
... | e , q = let _ , _ , _ , elG , w = injectivity q
              in PE.cong _ elG , substTypeEq w (genRefl t∷A₁)
neTypeEq (natrecₙ neT) (natrecⱼ x t∷A t∷A₁ t∷A₂) (natrecⱼ x₁ t∷B t∷B₁ t∷B₂) =
  PE.refl , refl (substType x₁ t∷B₂)
neTypeEq Emptyrecₙ (Emptyrecⱼ x t∷A) (Emptyrecⱼ x₁ t∷B) =
  PE.refl , refl x₁
neTypeEq (Idₙ X) (Idⱼ Y Y₁ Y₂) (Idⱼ Z Z₁ Z₂) =
  let e , q = neTypeEq X Y Z
      el = next-inj e
  in e , PE.subst (λ l → _ ⊢ _ ≡ SProp l ^ _) el (refl (Ugenⱼ (wfTerm Y) ) )
neTypeEq (Idℕₙ X) (Idⱼ Y Y₁ Y₂) (Idⱼ Z Z₁ Z₂) =
  let e , q = neTypeEq X Y₁ Z₁
      el = ιinj e
  in PE.cong next el , PE.subst (λ l → _ ⊢ _ ≡ SProp l ^ _) el (refl (Ugenⱼ (wfTerm Y) ) )
neTypeEq (Idℕ0ₙ X) (Idⱼ Y Y₁ Y₂) (Idⱼ Z Z₁ Z₂) =
  let e , q = neTypeEq X Y₂ Z₂
      el = ιinj e
  in PE.cong next el , PE.subst (λ l → _ ⊢ _ ≡ SProp l ^ _) el (refl (Ugenⱼ (wfTerm Y) ) )
neTypeEq (IdℕSₙ X) (Idⱼ Y Y₁ Y₂) (Idⱼ Z Z₁ Z₂) =
  let e , q = neTypeEq X Y₂ Z₂
      el = ιinj e
  in PE.cong next el , PE.subst (λ l → _ ⊢ _ ≡ SProp l ^ _) el (refl (Ugenⱼ (wfTerm Y) ) )
neTypeEq (IdUₙ X) (Idⱼ Y Y₁ Y₂) (Idⱼ Z Z₁ Z₂) =
  let e , q = neTypeEq X Y₁ Z₁
      el = ιinj e
  in PE.cong next el , PE.subst (λ l → _ ⊢ _ ≡ SProp l ^ _) el (refl (Ugenⱼ (wfTerm Y) ) )
neTypeEq (IdUℕₙ X) (Idⱼ Y Y₁ Y₂) (Idⱼ Z Z₁ Z₂) =
  let e , q = neTypeEq X Y₂ Z₂
      el = ιinj e
  in PE.cong next el , PE.subst (λ l → _ ⊢ _ ≡ SProp l ^ _) el (refl (Ugenⱼ (wfTerm Y) ) )
neTypeEq (IdUΠₙ X) (Idⱼ Y Y₁ Y₂) (Idⱼ Z Z₁ Z₂) =
  let e , q = neTypeEq X Y₂ Z₂
      el = ιinj e
  in PE.cong next el , PE.subst (λ l → _ ⊢ _ ≡ SProp l ^ _) el (refl (Ugenⱼ (wfTerm Y) ) )
neTypeEq X (castⱼ Y Y₁ Y₂ Y₃)  (castⱼ Z Z₁ Z₂ Z₃) = PE.refl , refl (univ Y₁) 
neTypeEq x (conv t∷A x₁) t∷B = 
  let e , q = neTypeEq x t∷A t∷B
  in e , trans (sym x₁) q 
neTypeEq x t∷A (conv t∷B x₃) =
  let e , q = neTypeEq x t∷A t∷B
  in e , trans q (PE.subst (λ l → _ ⊢ _ ≡ _ ^ [ _ , l ]) (PE.sym e) x₃) 


natTypeEq : ∀ {A rA lA Γ} → Γ ⊢ ℕ ∷ A ^ [ rA , lA ] → rA PE.≡ ! × lA PE.≡ ι ¹ × Γ ⊢ A ≡ U ⁰ ^ [ ! , ι ¹ ]
natTypeEq (ℕⱼ x) = PE.refl , PE.refl , refl (univ (univ 0<1 x))
natTypeEq (conv X x) = let eqrA , eqlA , eqAU = natTypeEq X in eqrA , eqlA ,
  trans (sym (PE.subst (λ l → _ ⊢ _ ≡ _ ^ [ _ , l ] ) eqlA (PE.subst (λ r → _ ⊢ _ ≡ _ ^ [ r , _ ]) eqrA x))) eqAU 

emptyTypeEq : ∀ {A rA lA Γ l} → Γ ⊢ Empty l ∷ A ^ [ rA , lA ] →
  rA PE.≡ ! × lA PE.≡ next l × Γ ⊢ A ≡ SProp l ^ [ ! , next l ]
emptyTypeEq (Emptyⱼ x) = PE.refl , PE.refl , refl (Ugenⱼ x) 
emptyTypeEq (conv X x) = let eqrA , eqlA , eqAU = emptyTypeEq X in eqrA , eqlA , 
 trans (sym (PE.subst (λ l → _ ⊢ _ ≡ _ ^ [ _ , l ] ) eqlA (PE.subst (λ r → _ ⊢ _ ≡ _ ^ [ r , _ ]) eqrA x))) eqAU 

