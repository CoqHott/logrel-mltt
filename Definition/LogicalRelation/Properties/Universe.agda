{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Universe {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.Typed.Properties
open import Definition.LogicalRelation.Properties.MaybeEmb
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Empty using (⊥; ⊥-elim)

import Data.Fin as Fin
import Data.Nat as Nat

U-Relevance-Level : ∀ {l ll Γ A} ([U] : Γ ⊩⟨ l ⟩U A ^ ll) → Relevance × Level
U-Relevance-Level (noemb (Uᵣ r l′ l< eq d)) =  r , l′
U-Relevance-Level (emb x X) = U-Relevance-Level X

toTypeInfo : Relevance × Level → TypeInfo
toTypeInfo ( r , l ) = [ r , ι l ]

univRedTerm : ∀ {Γ r l u t ti}
        → Γ ⊢ Univ r l ⇒ u ∷ t ^ ti
        → ⊥
univRedTerm (conv d′ A≡t) = univRedTerm d′

univRed* : ∀ {Γ r l r′ l′ ti}
         → Γ ⊢ Univ r l ⇒* Univ r′ l′ ^ ti
         → (r PE.≡ r′) × (l PE.≡ l′)
univRed* (id x) = PE.refl , PE.refl
univRed* (univ x ⇨ D) = ⊥-elim (univRedTerm x)

-- Reducible terms of type U are reducible types.
univEq : ∀ {l Γ A r l′ ll′}
       → ([U] : Γ ⊩⟨ l ⟩ Univ r l′ ^ [ ! , ll′ ] )
       → Γ ⊩⟨ l ⟩ A ∷ Univ r l′ ^ [ ! , ll′ ] / [U]
       → Γ ⊩⟨ ι l′ ⟩ A ^ [ r , ι l′ ]
univEq {ι ⁰} {Γ} {A} {r} {l′} (Uᵣ (Uᵣ r₁ l′₁ () eq [[ ⊢A , ⊢B , D ]])) (Uₜ K d₁ typeK K≡K [t])
univEq {ι ¹} {Γ} {A} {r} {l′} (Uᵣ (Uᵣ r₁ ⁰ emb< eq [[ ⊢A , ⊢B , D ]])) (Uₜ K d₁ typeK K≡K [t]) =
  let
    ⊢Γ = wf ⊢A
    r≡r₁ , l′≡l′₁ = univRed* D
    [t]′ : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ r₁ , ι ⁰ ]
    [t]′ = PE.subst (λ X → Γ ⊩⟨ _ ⟩ X ^ [ _ , _ ])
      (Definition.Untyped.Properties.wk-id A) ([t] Definition.Typed.Weakening.id ⊢Γ)
  in
  PE.subst₂ (λ X Y → Γ ⊩⟨ ι Y ⟩ A ^ [ X , ι Y ]) (PE.sym r≡r₁) (PE.sym l′≡l′₁) [t]′
univEq {∞} {Γ} {A} {r} {l′} (Uᵣ (Uᵣ r₁ ¹ _ eq [[ ⊢A , ⊢B , D ]])) (Uₜ K d₁ typeK K≡K [t]) =
  let
    ⊢Γ = wf ⊢A
    r≡r₁ , l′≡l′₁ = univRed* D
    [t]′ : Γ ⊩⟨ ι ¹ ⟩ A ^ [ r₁ , ι ¹ ]
    [t]′ = PE.subst (λ X → Γ ⊩⟨ _ ⟩ X ^ [ _ , _ ])
      (Definition.Untyped.Properties.wk-id A) ([t] Definition.Typed.Weakening.id ⊢Γ)
  in
  PE.subst₂ (λ X Y → Γ ⊩⟨ ι Y ⟩ A ^ [ X , ι Y ]) (PE.sym r≡r₁) (PE.sym l′≡l′₁) [t]′
univEq (ℕᵣ [[ ⊢A , ⊢B , univ x ⇨ D ]]) [A] = ⊥-elim (univRedTerm x)
univEq (ne′ K [[ ⊢A , ⊢B , univ x ⇨ D ]] neK K≡K) [A] = ⊥-elim (univRedTerm x)
univEq (Πᵣ′ rF lF lG _ _ F G [[ ⊢A , ⊢B , univ x ⇨ D ]] ⊢F ⊢G A≡A [F] [G] G-ext) [A] =
  ⊥-elim (univRedTerm x)
univEq {ι ¹} (emb _ [U]′) [A] = univEq [U]′ [A]
univEq {∞} (emb _ [U]′) [A] = univEq [U]′ [A]


univ⊩ : ∀ {A Γ rU lU lU' l} 
        ([U] : Γ ⊩⟨ l ⟩ Univ rU lU ^ [ ! , lU' ])
      → Γ ⊩⟨ l ⟩ A ∷ Univ rU lU ^ [ ! , lU' ] / [U]
      → Γ ⊩⟨ ι lU ⟩ A ^ [ rU , ι lU ] 
univ⊩ {lU = lU} {l = l} [U] [A] = irrelevance-≤ (≡is≤ PE.refl) (univEq [U] [A])
  
univEqTerm : ∀ {Γ A t r l′ ll′}
       → ([U] : Γ ⊩⟨ ∞ ⟩ Univ r l′ ^ [ ! , ll′ ] )
       → ([A] : Γ ⊩⟨ ∞ ⟩ A ∷ Univ r l′ ^ [ ! , ll′ ] / [U])
       → Γ ⊩⟨ ∞ ⟩ t ∷ A ^ [ r , ι l′ ] / maybeEmb (univ⊩ [U] [A])
       → Γ ⊩⟨ ι l′ ⟩ t ∷ A ^ [ r , ι l′ ] / univEq [U] [A]
univEqTerm {Γ} {A} {t} {r} {⁰} [U] [A] [t] = [t]
univEqTerm {Γ} {A} {t} {r} {¹} [U] [A] [t] = [t]

-- Helper function for reducible term equality of type U for specific type derivations.
univEqEq′ : ∀ {l ll l′ Γ X A B} ([U] : Γ ⊩⟨ l ⟩U X ^ ll) →
            let r = toTypeInfo (U-Relevance-Level [U])
            in
              ([A] : Γ ⊩⟨ l′ ⟩ A ^ r)
              → Γ ⊩⟨ l ⟩ A ≡ B ∷ X ^ [ ! , ll ] / U-intr [U]
              → Γ ⊩⟨ l′ ⟩ A ≡ B  ^ r / [A]
univEqEq′ {l} {ll} {l″} {Γ} {X} {A} {B} (noemb (Uᵣ r l′ l< eq [[ ⊢A , ⊢B , D ]])) [A]
          (Uₜ₌ (Uₜ K d typeK K≡K [t]) [u] A≡B [t≡u]) =
  let ⊢Γ = wf ⊢A in
  irrelevanceEq″ (Definition.Untyped.Properties.wk-id A) (Definition.Untyped.Properties.wk-id B) PE.refl PE.refl
    (emb l< ([t] Definition.Typed.Weakening.id ⊢Γ)) [A]
    ([t≡u] Definition.Typed.Weakening.id ⊢Γ)
univEqEq′ (emb emb< X) [A] [A≡B] = univEqEq′ X [A] [A≡B]
univEqEq′ (emb ∞< X) [A] [A≡B] = univEqEq′ X [A] [A≡B]

UnivNotℕ : ∀ {Γ r ll} →  Γ ⊩ℕ Univ r ll → ⊥
UnivNotℕ {ll = ⁰} [[ ⊢A , ⊢B , D ]] = U≢ℕ (whrDet* (id (univ (univ 0<1 (wf ⊢A))) , Uₙ) (D , ℕₙ))
UnivNotℕ {ll = ¹} [[ ⊢A , ⊢B , D ]] = U≢ℕ (whrDet* (id (Uⱼ (wf ⊢A)) , Uₙ) (D , ℕₙ))

UnivNotΠ : ∀ {Γ r r' lΠ l ll} → (l LogRel.⊩¹Π logRelRec l ^[ Γ , Univ r ll ]) r' lΠ → ⊥ 
UnivNotΠ {ll = ⁰} (Πᵣ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G] G-ext) = U≢Π (whrDet* (id (univ (univ 0<1 (wf ⊢F))) , Uₙ) (red D , Πₙ))
UnivNotΠ {ll = ¹} (Πᵣ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G] G-ext) = U≢Π (whrDet* (id (Uⱼ (wf ⊢F)) , Uₙ) (red D , Πₙ))

U-Relevance-Level-eq : ∀ {l Γ r ll ll'} ([U] : Γ ⊩⟨ l ⟩ Univ r ll ^ [ ! , ll' ]) → U-Relevance-Level (U-elim [U]) PE.≡ (r , ll)
U-Relevance-Level-eq {ll = ⁰} (Uᵣ (Uᵣ r ⁰ l< eq d)) = ×-eq (Univ-PE-injectivity (whrDet* (red d , Uₙ) (id (univ (univ 0<1 (wf (_⊢_:⇒*:_^_.⊢A d)))) , Uₙ)))
U-Relevance-Level-eq {ll = ¹} (Uᵣ (Uᵣ r ⁰ l< eq d)) = let _ , X = (Univ-PE-injectivity (whrDet* (red d , Uₙ) (id (Uⱼ (wf (_⊢_:⇒*:_^_.⊢A d))) , Uₙ))) in ⊥-elim (⁰≢¹ X)
U-Relevance-Level-eq {ll = ¹} (Uᵣ (Uᵣ r ¹ l< eq d)) = ×-eq (Univ-PE-injectivity (whrDet* (red d , Uₙ) (id (Uⱼ (wf (_⊢_:⇒*:_^_.⊢A d))) , Uₙ)))
U-Relevance-Level-eq (ℕᵣ X) = ⊥-elim (UnivNotℕ X)
U-Relevance-Level-eq (ne′ K D neK K≡K) = ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
U-Relevance-Level-eq (Πᵣ X) = ⊥-elim (UnivNotΠ X)
U-Relevance-Level-eq {ι ¹} (emb l< (ℕᵣ X)) = ⊥-elim (UnivNotℕ X)
U-Relevance-Level-eq {ι ¹} (emb l< (ne′ K D neK K≡K)) = ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
U-Relevance-Level-eq {ι ¹} (emb l< (Πᵣ X)) = ⊥-elim (UnivNotΠ X)
U-Relevance-Level-eq {∞} {ll = ⁰} (emb ∞< (Uᵣ (Uᵣ r ⁰ l<₁ eq d))) = ×-eq (Univ-PE-injectivity (whrDet* (red d , Uₙ) (id (univ (univ 0<1 (wf (_⊢_:⇒*:_^_.⊢A d)))) , Uₙ)))
U-Relevance-Level-eq {∞} {ll = ¹} (emb ∞< (Uᵣ (Uᵣ r ⁰ l<₁ eq d))) = let _ , X = (Univ-PE-injectivity (whrDet* (red d , Uₙ) (id (Uⱼ (wf (_⊢_:⇒*:_^_.⊢A d))) , Uₙ))) in ⊥-elim (⁰≢¹ X)
U-Relevance-Level-eq {∞} {ll = ¹} (emb ∞< (Uᵣ (Uᵣ r ¹ l<₁ eq d))) = ×-eq (Univ-PE-injectivity (whrDet* (red d , Uₙ) (id (Uⱼ (wf (_⊢_:⇒*:_^_.⊢A d))) , Uₙ)))
U-Relevance-Level-eq {∞} (emb {l′ = ι ¹} l< (ℕᵣ X)) = ⊥-elim (UnivNotℕ X)
U-Relevance-Level-eq {∞} (emb {l′ = ι ¹} l< (ne′ K D neK K≡K)) = ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
U-Relevance-Level-eq {∞} (emb {l′ = ι ¹} l< (Πᵣ x)) = ⊥-elim (UnivNotΠ x)
U-Relevance-Level-eq {∞} (emb {l′ = ι ¹} l< (emb {l′ = ι ⁰} emb< (ℕᵣ x))) = ⊥-elim (UnivNotℕ x)
U-Relevance-Level-eq {∞} (emb {l′ = ι ¹} l< (emb {l′ = ι ⁰} emb< (ne′ K D neK K≡K))) = ⊥-elim (U≢ne neK (whnfRed* (red D) Uₙ))
U-Relevance-Level-eq {∞} (emb {l′ = ι ¹} l< (emb {l′ = ι ⁰} emb< (Πᵣ x))) = ⊥-elim (UnivNotΠ x)

helper-eq : ∀ {l Γ A B r r'} {[A] : Γ ⊩⟨ l ⟩ A ^ r} (e : r PE.≡ r' ) → Γ ⊩⟨ l ⟩ A ≡ B ^ r' / (PE.subst _ e [A]) → Γ ⊩⟨ l ⟩ A ≡ B ^ r / [A]
helper-eq PE.refl X = X

-- Reducible term equality of type U is reducible type equality.
univEqEq : ∀ {l l′ Γ A B r ll} ([U] : Γ ⊩⟨ l ⟩ Univ r ll ^ [ ! , next ll ]) ([A] : Γ ⊩⟨ l′ ⟩ A ^ [ r , ι ll ])
         → Γ ⊩⟨ l ⟩ A ≡ B ∷ Univ r ll ^ [ ! , next ll ] / [U]
         → Γ ⊩⟨ l′ ⟩ A ≡ B ^ [ r , ι ll ] / [A]
univEqEq {l} {l′} {Γ} {A} {B} {r} {ll} [U] [A] [A≡B] =
  let [A≡B]′ = irrelevanceEqTerm [U] (U-intr (U-elim [U])) [A≡B]
      X = univEqEq′ (U-elim [U]) (PE.subst (λ r → Γ ⊩⟨ l′ ⟩ A ^ r) (PE.sym (PE.cong toTypeInfo (U-Relevance-Level-eq [U]))) [A]) [A≡B]′
  in helper-eq (PE.sym (PE.cong toTypeInfo (U-Relevance-Level-eq [U]))) X

univEqEqTerm : ∀ {Γ A t u r l′ ll}
             → ([U] : Γ ⊩⟨ ∞ ⟩ Univ r l′ ^ [ ! , ll ] )
             → ([A] : Γ ⊩⟨ ∞ ⟩ A ∷ Univ r l′ ^ [ ! , ll ] / [U])
             → Γ ⊩⟨ ∞ ⟩ t ∷ A ^ [ r , ι l′ ] / maybeEmb (univ⊩ [U] [A])
             → Γ ⊩⟨ ∞ ⟩ t ≡ u ∷ A ^ [ r , ι l′ ] / maybeEmb (univ⊩ [U] [A])
             → Γ ⊩⟨ ι l′ ⟩ t ≡ u ∷ A ^ [ r , ι l′ ] / univEq [U] [A]
univEqEqTerm {Γ} {A} {t} {u} {r} {⁰} [U] [A] [t] [t≡u] = [t≡u]
univEqEqTerm {Γ} {A} {t} {u} {r} {¹} [U] [A] [t] [t≡u] = [t≡u]
