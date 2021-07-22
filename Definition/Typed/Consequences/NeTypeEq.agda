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
neTypeEq : ∀ {t A B rA lA lA' Γ} → Neutral t → lA PE.≡ lA' → Γ ⊢ t ∷ A ^ [ rA , lA ] → Γ ⊢ t ∷ B ^ [ rA , lA' ] →
  Γ ⊢ A ≡ B ^ [ rA , lA ]
neTypeEq (var x) PE.refl (var x₁ x₂) (var x₃ x₄) =
  let V , e = varTypeEq (syntacticTerm (var x₃ x₂)) (syntacticTerm (var x₃ x₄)) x₂ x₄
  in V 
neTypeEq (∘ₙ neT) PE.refl (t∷A ∘ⱼ t∷A₁) (t∷B ∘ⱼ t∷B₁) with neTypeEq neT PE.refl t∷A t∷B
... | q = let _ , _ , _ , elG , w = injectivity q
              in substTypeEq (PE.subst (λ x → _ ⊢ _ ≡ _ ^ [ _ , ι x ]) elG w) (genRefl t∷A₁)
neTypeEq (natrecₙ neT) PE.refl (natrecⱼ x t∷A t∷A₁ t∷A₂) (natrecⱼ x₁ t∷B t∷B₁ t∷B₂) =
  refl (substType x₁ t∷B₂)
neTypeEq Emptyrecₙ PE.refl  (Emptyrecⱼ x t∷A) (Emptyrecⱼ x₁ t∷B) =
  refl x₁
neTypeEq (Idₙ X) el (Idⱼ Y Y₁ Y₂) (Idⱼ Z Z₁ Z₂) =
  let l≡l = next-inj el
  in PE.subst (λ l → _ ⊢ _ ≡ SProp l ^ _) l≡l (refl (Ugenⱼ (wfTerm Y) ) )
neTypeEq (Idℕₙ X) el (Idⱼ Y Y₁ Y₂) (Idⱼ Z Z₁ Z₂) =
  let l≡l = next-inj el
  in PE.subst (λ l → _ ⊢ _ ≡ SProp l ^ _) l≡l (refl (Ugenⱼ (wfTerm Y) ) )
neTypeEq (Idℕ0ₙ X) el (Idⱼ Y Y₁ Y₂) (Idⱼ Z Z₁ Z₂) =
  let l≡l = next-inj el
  in PE.subst (λ l → _ ⊢ _ ≡ SProp l ^ _) l≡l (refl (Ugenⱼ (wfTerm Y) ) )
neTypeEq (IdℕSₙ X) el (Idⱼ Y Y₁ Y₂) (Idⱼ Z Z₁ Z₂) =
  let l≡l = next-inj el
  in PE.subst (λ l → _ ⊢ _ ≡ SProp l ^ _) l≡l (refl (Ugenⱼ (wfTerm Y) ) )
neTypeEq (IdUₙ X) el (Idⱼ Y Y₁ Y₂) (Idⱼ Z Z₁ Z₂) =
  let l≡l = next-inj el
  in PE.subst (λ l → _ ⊢ _ ≡ SProp l ^ _) l≡l (refl (Ugenⱼ (wfTerm Y) ) )
neTypeEq (IdUℕₙ X) el (Idⱼ Y Y₁ Y₂) (Idⱼ Z Z₁ Z₂) =
  let l≡l = next-inj el
  in PE.subst (λ l → _ ⊢ _ ≡ SProp l ^ _) l≡l (refl (Ugenⱼ (wfTerm Y) ) )
neTypeEq (IdUΠₙ X) el (Idⱼ Y Y₁ Y₂) (Idⱼ Z Z₁ Z₂) =
  let l≡l = next-inj el
  in PE.subst (λ l → _ ⊢ _ ≡ SProp l ^ _) l≡l (refl (Ugenⱼ (wfTerm Y) ) )
neTypeEq X el (castⱼ Y Y₁ Y₂ Y₃)  (castⱼ Z Z₁ Z₂ Z₃) = refl (univ Y₁)
neTypeEq x PE.refl (conv t∷A x₁) t∷B = let q = neTypeEq x PE.refl t∷A t∷B
                               in trans (sym x₁) q
neTypeEq x PE.refl t∷A (conv t∷B x₃) = let q = neTypeEq x PE.refl t∷A t∷B
                               in trans q x₃


natTypeEq : ∀ {A rA lA Γ} → Γ ⊢ ℕ ∷ A ^ [ rA , lA ] → rA PE.≡ ! × lA PE.≡ ι ¹ × Γ ⊢ A ≡ U ⁰ ^ [ ! , ι ¹ ]
natTypeEq (ℕⱼ x) = PE.refl , PE.refl , refl (univ (univ 0<1 x))
natTypeEq (conv X x) = let eqrA , eqlA , eqAU = natTypeEq X in eqrA , eqlA ,
  trans (sym (PE.subst (λ l → _ ⊢ _ ≡ _ ^ [ _ , l ] ) eqlA (PE.subst (λ r → _ ⊢ _ ≡ _ ^ [ r , _ ]) eqrA x))) eqAU 

emptyTypeEq : ∀ {A rA lA Γ} → Γ ⊢ Empty ∷ A ^ [ rA , lA ] →
  Σ Level (λ l → rA PE.≡ ! × lA PE.≡ next l × Γ ⊢ A ≡ SProp l ^ [ ! , next l ])
emptyTypeEq (Emptyⱼ {l} x) = l , PE.refl , PE.refl , refl (Ugenⱼ x) 
emptyTypeEq (conv X x) = let l , eqrA , eqlA , eqAU = emptyTypeEq X in l , eqrA , eqlA , 
 trans (sym (PE.subst (λ l → _ ⊢ _ ≡ _ ^ [ _ , l ] ) eqlA (PE.subst (λ r → _ ⊢ _ ≡ _ ^ [ r , _ ]) eqrA x))) eqAU 

