{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Universe {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Weakening as Lwk
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance as Irr
open import Definition.Typed.Properties
open import Definition.LogicalRelation.Properties.MaybeEmb
open import Definition.LogicalRelation.Properties.Escape
open import Definition.LogicalRelation.Properties.Reduction
open import Definition.LogicalRelation.Properties.Conversion
open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Empty using (⊥; ⊥-elim)

import Data.Fin as Fin
import Data.Nat as Nat

Ugen : ∀ {Γ rU l} → (⊢Γ : ⊢ Γ) →  Γ ⊩⟨ next l ⟩ Univ rU l ^ [ ! , next l ] 
Ugen {Γ} {rU} {⁰} ⊢Γ = Uᵣ′ (Univ rU ⁰) (ι ¹) rU ⁰ emb< PE.refl ((idRed:*: (Ugenⱼ ⊢Γ)))
Ugen {Γ} {rU} {¹} ⊢Γ = Uᵣ′ (Univ rU ¹) ∞ rU ¹ ∞< PE.refl (idRed:*: (Uⱼ ⊢Γ))

U-Relevance-Level : ∀ {l ll Γ A} ([U] : Γ ⊩⟨ l ⟩U A ^ ll) → Relevance × Level
U-Relevance-Level (noemb (Uᵣ r l′ l< eq d)) =  r , l′
U-Relevance-Level (emb x X) = U-Relevance-Level X


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

univEqGen : ∀ {Γ UA A l′}
       → ([U] : ((next l′) LogRel.⊩¹U logRelRec (next l′) ^ Γ) UA (next l′))
       → Γ ⊩⟨ next l′ ⟩ A ∷ UA ^ [ ! , next l′ ] / Uᵣ [U]
       → Γ ⊩⟨ ι l′ ⟩ A ^ [ LogRel._⊩¹U_^_.r [U] , ι l′ ]
univEqGen {Γ} {UA} {A} {l′} [UA] [A] =
  let (Uᵣ r l′₁ l< e [[ ⊢A , ⊢B , D ]]) = [UA]
      [U] = Ugen {l = l′} (wf ⊢A)
      [UA]' , [UAeq] = redSubst* (PE.subst (λ X →  Γ ⊢ UA ⇒* Univ r X ^ [ ! , next X ]) (next-inj e) D) [U]
  in univEq [U] (convTerm₁ {t = A} [UA]' [U] [UAeq] (irrelevanceTerm (Uᵣ [UA]) [UA]' [A]))

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



un-univEq : ∀ {l Γ A r }
          → ([A] : Γ ⊩⟨ ι l ⟩ A ^ [ r , ι l ])
          → let [U] : Γ ⊩⟨ next l ⟩ Univ r l ^ [ ! , next l ]
                [U] = Ugen (wf (escape [A]))
            in Γ ⊩⟨ next l ⟩ A ∷ Univ r l ^ [ ! , next l ] / [U]
un-univEq {⁰} {Γ} {A} {.!} (ℕᵣ [[ ⊢A , ⊢ℕ , D ]] ) = Uₜ ℕ (un-univ:⇒*: [[ ⊢A , ⊢ℕ , D ]]) ℕₙ (≅ₜ-ℕrefl (wf ⊢A)) (λ [ρ] ⊢Δ → Lwk.wk [ρ] ⊢Δ (ℕᵣ [[ ⊢A , ⊢ℕ , D ]] ))
un-univEq {⁰} {Γ} {A} {.%} (Emptyᵣ [[ ⊢A , ⊢Empty , D ]]) = Uₜ Empty (un-univ:⇒*: [[ ⊢A , ⊢Empty , D ]]) Emptyₙ (≅ₜ-Emptyrefl (wf ⊢A))
                                                                                (λ [ρ] ⊢Δ → Lwk.wk [ρ] ⊢Δ (Emptyᵣ [[ ⊢A , ⊢Empty , D ]] ))
un-univEq {⁰} {Γ} {A} {r} (ne′ K D neK K≡K) = Uₜ K (un-univ:⇒*: D) (ne neK) (~-to-≅ₜ K≡K) (λ [ρ] ⊢Δ → Lwk.wk [ρ] ⊢Δ (ne′ K D neK K≡K))
un-univEq {⁰} {Γ} {A} {r} (Πᵣ′ rF .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D ⊢F ⊢G A≡A [F] [G] G-ext) =
  Uₜ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰) (un-univ:⇒*: D) Πₙ (≅-un-univ A≡A) λ [ρ] ⊢Δ → Lwk.wk [ρ] ⊢Δ (Πᵣ′ rF ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D ⊢F ⊢G A≡A [F] [G] G-ext)
un-univEq {⁰}  {Γ} {A} {.%} (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) =
  Uₜ (∃ F ▹ G) (un-univ:⇒*: D) ∃ₙ (≅-un-univ A≡A) λ [ρ] ⊢Δ → Lwk.wk [ρ] ⊢Δ (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
un-univEq {¹} {Γ} {A} {.!} (Uᵣ (Uᵣ r .⁰ emb< eq [[ ⊢A , ⊢B , D ]])) = Uₜ (Univ r ⁰) (un-univ:⇒*: [[ ⊢A , ⊢B , D ]]) Uₙ (≅-U⁰refl (wf ⊢A))
                                                                              (λ [ρ] ⊢Δ → Lwk.wk [ρ] ⊢Δ (Uᵣ (Uᵣ r ⁰ emb< eq [[ ⊢A , ⊢B , D ]] )))
un-univEq {¹} {Γ} {A} {.%} (Emptyᵣ [[ ⊢A , ⊢Empty , D ]]) = Uₜ Empty (un-univ:⇒*: [[ ⊢A , ⊢Empty , D ]]) Emptyₙ (≅ₜ-Emptyrefl (wf ⊢A))
                                                                                (λ [ρ] ⊢Δ → Lwk.wk [ρ] ⊢Δ (Emptyᵣ [[ ⊢A , ⊢Empty , D ]] ))
un-univEq {¹} {Γ} {A} {r} (ne′ K D neK K≡K) = Uₜ K (un-univ:⇒*: D) (ne neK) (~-to-≅ₜ K≡K) (λ [ρ] ⊢Δ → Lwk.wk [ρ] ⊢Δ (ne′ K D neK K≡K))
un-univEq {¹} {Γ} {A} {r} (Πᵣ′ rF lF lG lF< lG< F G D ⊢F ⊢G A≡A [F] [G] G-ext) = 
  Uₜ (Π F ^ rF ° lF ▹ G ° lG ° ¹ ) (un-univ:⇒*: D) Πₙ (≅-un-univ A≡A) λ [ρ] ⊢Δ → Lwk.wk [ρ] ⊢Δ (Πᵣ′ rF lF lG lF< lG< F G D ⊢F ⊢G A≡A [F] [G] G-ext)
un-univEq {¹} {Γ} {A} {.%} (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) =
  Uₜ (∃ F ▹ G) (un-univ:⇒*: D) ∃ₙ (≅-un-univ A≡A) λ [ρ] ⊢Δ → Lwk.wk [ρ] ⊢Δ (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
un-univEq {¹} {Γ} {A} {.%} (emb emb< (Emptyᵣ [[ ⊢A , ⊢Empty , D ]])) = Uₜ Empty (un-univ:⇒*: [[ ⊢A , ⊢Empty , D ]]) Emptyₙ (≅ₜ-Emptyrefl (wf ⊢A))
                                                                                (λ [ρ] ⊢Δ → Lwk.wk [ρ] ⊢Δ (Emptyᵣ [[ ⊢A , ⊢Empty , D ]] ))
un-univEq {¹} {Γ} {A} {r} (emb emb< (ne′ K D neK K≡K)) = Uₜ K (un-univ:⇒*: D) (ne neK) (~-to-≅ₜ K≡K) (λ [ρ] ⊢Δ → Lwk.wk [ρ] ⊢Δ (ne′ K D neK K≡K))
un-univEq {¹} {Γ} {A} {r} (emb emb< (Πᵣ′ rF lF lG lF≤ lG≤ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) =
  Uₜ (Π F ^ rF ° lF ▹ G ° lG ° ¹) (un-univ:⇒*: D) Πₙ (≅-un-univ A≡A) λ [ρ] ⊢Δ → let X = Lwk.wk [ρ] ⊢Δ (Πᵣ′ rF lF lG lF≤ lG≤ F G D ⊢F ⊢G A≡A [F] [G] G-ext) in maybeEmb′ (<is≤ 0<1) X
un-univEq {¹} {Γ} {A} {.%} (emb emb< (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext)) =
  Uₜ (∃ F ▹ G) (un-univ:⇒*: D) ∃ₙ (≅-un-univ A≡A) λ [ρ] ⊢Δ → let X = Lwk.wk [ρ] ⊢Δ (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) in maybeEmb′ (<is≤ 0<1) X


un-univEqEq-Shape : ∀ {l Γ A B r }
          ([A] : Γ ⊩⟨ ι l ⟩ A ^ [ r , ι l ]) ([B] : Γ ⊩⟨ ι l ⟩ B ^ [ r , ι l ])
          (ShapeA : ShapeView Γ (ι l) (ι l) A B [ r , ι l ] [ r , ι l ] [A] [B])
          ([A≡B] : Γ ⊩⟨ ι l ⟩ A ≡ B ^ [ r , ι l ] / [A])
          → let [U] : Γ ⊩⟨ next l ⟩ Univ r l ^ [ ! , next l ]
                [U] = Ugen (wf (escape [A]))
            in Γ ⊩⟨ next l ⟩ A ≡ B ∷ Univ r l ^ [ ! , next l ] / [U]
un-univEqEq-Shape {⁰} {Γ} {A} {B} {.!} _ _ (ℕᵥ [[ ⊢A , ⊢ℕ , D ]] ℕB) [A≡B] =
  let [A] = ℕᵣ [[ ⊢A , ⊢ℕ , D ]]
      [B] = ℕᵣ [[ redFirst* [A≡B] , ⊢ℕ , [A≡B] ]]
  in Uₜ₌ (un-univEq [A]) (irrelevanceTerm {l = next ⁰} (Ugen (wf (escape [B]))) (Ugen (wf (escape [A]))) (un-univEq [B]))
         (≅ₜ-ℕrefl (wf ⊢A)) λ [ρ] ⊢Δ → Lwk.wkEq [ρ] ⊢Δ [A] [A≡B]
un-univEqEq-Shape {⁰} {Γ} {A} {B} {.%} _ _ (Emptyᵥ [[ ⊢A , ⊢Empty , D ]] EmptyB) [A≡B] =
  let [A] = Emptyᵣ [[ ⊢A , ⊢Empty , D ]]
      [B] = Emptyᵣ [[ redFirst* [A≡B] , ⊢Empty , [A≡B] ]]
  in Uₜ₌ (un-univEq [A]) (irrelevanceTerm {l = next ⁰} (Ugen (wf (escape [B]))) (Ugen (wf (escape [A]))) (un-univEq [B]))
         (≅ₜ-Emptyrefl (wf ⊢A)) λ [ρ] ⊢Δ → Lwk.wkEq [ρ] ⊢Δ [A] [A≡B]
un-univEqEq-Shape {⁰} {Γ} {A} {B} {r} _ _  (ne (ne K D neK K≡K) neB) (ne₌ M D′ neM K≡M) =
  let [A] = ne′ K D neK K≡K
      [B] = ne′ M D′ neM (~-trans (~-sym K≡M) K≡M)
      [A≡B] = ne₌ M D′ neM K≡M
  in Uₜ₌ (un-univEq [A]) (irrelevanceTerm {l = next ⁰} (Ugen (wf (escape [B]))) (Ugen (wf (escape [A]))) (un-univEq [B]))
         (~-to-≅ₜ K≡M) λ [ρ] ⊢Δ → Lwk.wkEq [ρ] ⊢Δ [A] [A≡B]
un-univEqEq-Shape {⁰} {Γ} {A} {B} {r} _ _ (Πᵥ (Πᵣ rF .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                        (Πᵣ rF' .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext'))
                                    (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  let [A] = Πᵣ′ rF ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D ⊢F ⊢G A≡A [F] [G] G-ext
      [B] = Πᵣ′ rF' ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext'
      [A≡B] = Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]
      F≡F , rF≡rF , _ , G≡G , _ = Π-PE-injectivity (whrDet* (D′ , Whnf.Πₙ) (red D' , Whnf.Πₙ))
  in Uₜ₌ (un-univEq [A]) (irrelevanceTerm {l = next ⁰} (Ugen (wf (escape [B]))) (Ugen (wf (escape [A]))) (un-univEq [B]))
         (≅-un-univ (
           PE.subst (λ X → _ ⊢ Π F ^ rF ° ⁰ ▹ G ° ⁰ ° _ ≅  Π F' ^ rF' ° ⁰ ▹ X ° ⁰ ° _ ^ _ ) G≡G
           (PE.subst (λ X → _ ⊢ Π F ^ rF ° ⁰ ▹ G ° ⁰ ° _ ≅  Π X ^ rF' ° ⁰ ▹ G′ ° ⁰ ° _ ^ _ ) F≡F
             (PE.subst (λ X → _ ⊢ Π F ^ rF ° ⁰ ▹ G ° ⁰ ° _ ≅  Π F′ ^ X ° ⁰ ▹ G′ ° ⁰ ° _ ^ _ ) rF≡rF A≡B)))) λ [ρ] ⊢Δ → Lwk.wkEq [ρ] ⊢Δ [A] [A≡B]

un-univEqEq-Shape {⁰} {Γ} {A} {B} {.%} _ _ (∃ᵥ (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                        (∃ᵣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext'))
                                    (∃₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  let [A] = ∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext
      [B] = ∃ᵣ′ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext'
      [A≡B] = ∃₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]
      F≡F , G≡G  = ∃-PE-injectivity (whrDet* (D′ , Whnf.∃ₙ) (red D' , Whnf.∃ₙ))
  in Uₜ₌ (un-univEq [A]) (irrelevanceTerm {l = next ⁰} (Ugen (wf (escape [B]))) (Ugen (wf (escape [A]))) (un-univEq [B]))
         (≅-un-univ (
           PE.subst (λ X → _ ⊢ ∃ F ▹ G ≅  ∃ F' ▹ X ^ _ ) G≡G
           (PE.subst (λ X → _ ⊢ ∃ F ▹ G ≅  ∃ X ▹ G′ ^ _ ) F≡F A≡B))) λ [ρ] ⊢Δ → Lwk.wkEq [ρ] ⊢Δ [A] [A≡B]
un-univEqEq-Shape {¹} {Γ} {A} {B} {.!} _ _ (Uᵥ (Uᵣ r .⁰ emb< eq d) (Uᵣ r₁ .⁰ emb< eq₁ d₁)) [A≡B] =
  let [A] = Uᵣ (Uᵣ r ⁰ emb< eq d)
      [B] = Uᵣ (Uᵣ r₁ ⁰ emb< eq₁ d₁)
      [[ ⊢A , _ , _ ]] = d
      r≡r , _ = Univ-PE-injectivity (whrDet* (red d₁ , Whnf.Uₙ) ([A≡B] , Whnf.Uₙ))
  in Uₜ₌ (un-univEq [A]) (irrelevanceTerm {l = next ¹} (Ugen (wf (escape [B]))) (Ugen (wf (escape [A]))) (un-univEq [B]))
         (PE.subst (λ X → _ ⊢  Univ r ⁰ ≅ Univ X ⁰ ∷ U _ ^ _ ) (PE.sym r≡r) (≅-U⁰refl (wf ⊢A))) λ [ρ] ⊢Δ → Lwk.wkEq [ρ] ⊢Δ [A] [A≡B]
un-univEqEq-Shape {¹} {Γ} {A} {B} {.%} _ _ (Emptyᵥ [[ ⊢A , ⊢Empty , D ]] EmptyB) [A≡B] =
  let [A] = Emptyᵣ [[ ⊢A , ⊢Empty , D ]]
      [B] = Emptyᵣ [[ redFirst* [A≡B] , ⊢Empty , [A≡B] ]]
  in Uₜ₌ (un-univEq [A]) (irrelevanceTerm {l = next ¹} (Ugen (wf (escape [B]))) (Ugen (wf (escape [A]))) (un-univEq [B]))
         (≅ₜ-Emptyrefl (wf ⊢A)) λ [ρ] ⊢Δ → Lwk.wkEq [ρ] ⊢Δ [A] [A≡B]
un-univEqEq-Shape {¹} {Γ} {A} {B} {r} _ _  (ne (ne K D neK K≡K) neB) (ne₌ M D′ neM K≡M) =
  let [A] = ne′ K D neK K≡K
      [B] = ne′ M D′ neM (~-trans (~-sym K≡M) K≡M)
      [A≡B] = ne₌ M D′ neM K≡M
  in Uₜ₌ (un-univEq [A]) (irrelevanceTerm {l = next ¹} (Ugen (wf (escape [B]))) (Ugen (wf (escape [A]))) (un-univEq [B]))
         (~-to-≅ₜ K≡M) λ [ρ] ⊢Δ → Lwk.wkEq [ρ] ⊢Δ [A] [A≡B]
un-univEqEq-Shape {¹} {Γ} {A} {B} {r} _ _ (Πᵥ (Πᵣ rF lF lG lF< lG< F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                        (Πᵣ rF' lF' lG' lF<' lG<' F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext'))
                                    (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  let [A] = Πᵣ′ rF lF lG lF< lG< F G D ⊢F ⊢G A≡A [F] [G] G-ext
      [B] = Πᵣ′ rF' lF' lG' lF<' lG<' F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext'
      [A≡B] = Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]
      F≡F , rF≡rF , lF≡lF , G≡G , lG≡lG , _ = Π-PE-injectivity (whrDet* (D′ , Whnf.Πₙ) (red D' , Whnf.Πₙ))
  in Uₜ₌ (un-univEq [A]) (irrelevanceTerm {l = next ¹} (Ugen (wf (escape [B]))) (Ugen (wf (escape [A]))) (un-univEq [B]))
         (≅-un-univ (
           PE.subst (λ X → _ ⊢ Π F ^ rF ° lF ▹ G ° lG ° _ ≅  Π F' ^ rF' ° lF' ▹ X ° lG' ° _ ^ _ ) G≡G
           (PE.subst (λ X → _ ⊢ Π F ^ rF ° lF ▹ G ° lG ° _ ≅  Π X ^ rF' ° lF' ▹ G′ ° lG' ° _ ^ _ ) F≡F
             (PE.subst (λ X → _ ⊢ Π F ^ rF ° lF ▹ G ° lG ° _ ≅  Π F′ ^ rF' ° lF' ▹ G′ ° X ° _ ^ _ ) lG≡lG
             (PE.subst (λ X → _ ⊢ Π F ^ rF ° lF ▹ G ° lG ° _ ≅  Π F′ ^ rF' ° X ▹ G′ ° lG ° _ ^ _ ) lF≡lF
             (PE.subst (λ X → _ ⊢ Π F ^ rF ° lF ▹ G ° lG ° _ ≅  Π F′ ^ X ° lF ▹ G′ ° lG ° _ ^ _ ) rF≡rF A≡B)))))) λ [ρ] ⊢Δ → Lwk.wkEq [ρ] ⊢Δ [A] [A≡B]
un-univEqEq-Shape {¹} {Γ} {A} {B} {.%} _ _ (∃ᵥ (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                        (∃ᵣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext'))
                                    (∃₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  let [A] = ∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext
      [B] = ∃ᵣ′ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext'
      [A≡B] = ∃₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]
      F≡F , G≡G  = ∃-PE-injectivity (whrDet* (D′ , Whnf.∃ₙ) (red D' , Whnf.∃ₙ))
  in Uₜ₌ (un-univEq [A]) (irrelevanceTerm {l = next ¹} (Ugen (wf (escape [B]))) (Ugen (wf (escape [A]))) (un-univEq [B]))
         (≅-un-univ (
           PE.subst (λ X → _ ⊢ ∃ F ▹ G ≅  ∃ F' ▹ X ^ _ ) G≡G
           (PE.subst (λ X → _ ⊢ ∃ F ▹ G ≅  ∃ X ▹ G′ ^ _ ) F≡F A≡B))) λ [ρ] ⊢Δ → Lwk.wkEq [ρ] ⊢Δ [A] [A≡B]
un-univEqEq-Shape {¹} {Γ} {A} {B} {.%} _ _ (emb⁰¹ (Emptyᵥ [[ ⊢A , ⊢Empty , D ]] EmptyB)) [A≡B] =
  let [A] = Emptyᵣ [[ ⊢A , ⊢Empty , D ]]
      [B] = Emptyᵣ [[ redFirst* [A≡B] , ⊢Empty , [A≡B] ]]
  in Uₜ₌ (un-univEq [A]) (irrelevanceTerm {l = next ¹} (Ugen (wf (escape [B]))) (Ugen (wf (escape [A]))) (un-univEq [B]))
         (≅ₜ-Emptyrefl (wf ⊢A)) λ [ρ] ⊢Δ → Lwk.wkEq [ρ] ⊢Δ [A] [A≡B]
un-univEqEq-Shape {¹} {Γ} {A} {B} {r} _ _ (emb⁰¹ (ne (ne K D neK K≡K) neB)) (ne₌ M D′ neM K≡M) =
  let [A] = ne′ K D neK K≡K
      [B] = ne′ M D′ neM (~-trans (~-sym K≡M) K≡M)
      [A≡B] = ne₌ M D′ neM K≡M
  in Uₜ₌ (un-univEq [A]) (irrelevanceTerm {l = next ¹} (Ugen (wf (escape [B]))) (Ugen (wf (escape [A]))) (un-univEq [B]))
         (~-to-≅ₜ K≡M) λ [ρ] ⊢Δ → Lwk.wkEq [ρ] ⊢Δ [A] [A≡B]
un-univEqEq-Shape {¹} {Γ} {A} {B} {r} _ _ (emb⁰¹ (Πᵥ (Πᵣ rF lF lG lF< lG< F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                        (Πᵣ rF' lF' lG' lF<' lG<' F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext')))
                                    (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  let [A] = Πᵣ′ rF lF lG lF< lG< F G D ⊢F ⊢G A≡A [F] [G] G-ext
      [B] = Πᵣ′ rF' lF' lG' lF<' lG<' F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext'
      [A≡B] = Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]
      F≡F , rF≡rF , lF≡lF , G≡G , lG≡lG , _ = Π-PE-injectivity (whrDet* (D′ , Whnf.Πₙ) (red D' , Whnf.Πₙ))
  in Uₜ₌ (un-univEq (maybeEmb′ (<is≤ 0<1) [A])) (irrelevanceTerm {l = next ¹} (Ugen (wf (escape [B]))) (Ugen (wf (escape [A]))) (un-univEq [B]))
         (≅-un-univ (
           PE.subst (λ X → _ ⊢ Π F ^ rF ° lF ▹ G ° lG ° _ ≅  Π F' ^ rF' ° lF' ▹ X ° lG' ° _ ^ _ ) G≡G
           (PE.subst (λ X → _ ⊢ Π F ^ rF ° lF ▹ G ° lG ° _ ≅  Π X ^ rF' ° lF' ▹ G′ ° lG' ° _ ^ _ ) F≡F
             (PE.subst (λ X → _ ⊢ Π F ^ rF ° lF ▹ G ° lG ° _ ≅  Π F′ ^ rF' ° lF' ▹ G′ ° X ° _ ^ _ ) lG≡lG
             (PE.subst (λ X → _ ⊢ Π F ^ rF ° lF ▹ G ° lG ° _ ≅  Π F′ ^ rF' ° X ▹ G′ ° lG ° _ ^ _ ) lF≡lF
             (PE.subst (λ X → _ ⊢ Π F ^ rF ° lF ▹ G ° lG ° _ ≅  Π F′ ^ X ° lF ▹ G′ ° lG ° _ ^ _ ) rF≡rF A≡B)))))) λ [ρ] ⊢Δ → Lwk.wkEq [ρ] ⊢Δ [A] [A≡B]
un-univEqEq-Shape {¹} {Γ} {A} {B} {.%} _ _ (emb⁰¹ (∃ᵥ (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                        (∃ᵣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext')))
                                    (∃₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  let [A] = ∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext
      [B] = ∃ᵣ′ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext'
      [A≡B] = ∃₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]
      F≡F , G≡G  = ∃-PE-injectivity (whrDet* (D′ , Whnf.∃ₙ) (red D' , Whnf.∃ₙ))
  in Uₜ₌ (un-univEq (maybeEmb′ (<is≤ 0<1) [A])) (irrelevanceTerm {l = next ¹} (Ugen (wf (escape [B]))) (Ugen (wf (escape [A]))) (un-univEq [B]))
         (≅-un-univ (
           PE.subst (λ X → _ ⊢ ∃ F ▹ G ≅  ∃ F' ▹ X ^ _ ) G≡G
           (PE.subst (λ X → _ ⊢ ∃ F ▹ G ≅  ∃ X ▹ G′ ^ _ ) F≡F A≡B))) λ [ρ] ⊢Δ → Lwk.wkEq [ρ] ⊢Δ [A] [A≡B]
un-univEqEq-Shape {¹} {Γ} {A} {B} {.%} _ _ (emb⁰¹ (emb¹⁰ (Emptyᵥ [[ ⊢A , ⊢Empty , D ]] EmptyB))) [A≡B] =
  let [A] = Emptyᵣ [[ ⊢A , ⊢Empty , D ]]
      [B] = Emptyᵣ [[ redFirst* [A≡B] , ⊢Empty , [A≡B] ]]
  in Uₜ₌ (un-univEq [A]) (irrelevanceTerm {l = next ¹} (Ugen (wf (escape [B]))) (Ugen (wf (escape [A]))) (un-univEq [B]))
         (≅ₜ-Emptyrefl (wf ⊢A)) λ [ρ] ⊢Δ → Lwk.wkEq [ρ] ⊢Δ [A] [A≡B]
un-univEqEq-Shape {¹} {Γ} {A} {B} {r} _ _ (emb⁰¹ (emb¹⁰ (ne (ne K D neK K≡K) neB))) (ne₌ M D′ neM K≡M) =
  let [A] = ne′ K D neK K≡K
      [B] = ne′ M D′ neM (~-trans (~-sym K≡M) K≡M)
      [A≡B] = ne₌ M D′ neM K≡M
  in Uₜ₌ (un-univEq [A]) (irrelevanceTerm {l = next ¹} (Ugen (wf (escape [B]))) (Ugen (wf (escape [A]))) (un-univEq [B]))
         (~-to-≅ₜ K≡M) λ [ρ] ⊢Δ → Lwk.wkEq [ρ] ⊢Δ [A] [A≡B]
un-univEqEq-Shape {¹} {Γ} {A} {B} {r} _ _ (emb⁰¹ (emb¹⁰ (Πᵥ (Πᵣ rF lF lG lF< lG< F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                        (Πᵣ rF' lF' lG' lF<' lG<' F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext'))))
                                    (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  let [A] = Πᵣ′ rF lF lG lF< lG< F G D ⊢F ⊢G A≡A [F] [G] G-ext
      [B] = Πᵣ′ rF' lF' lG' lF<' lG<' F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext'
      [A≡B] = Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]
      F≡F , rF≡rF , lF≡lF , G≡G , lG≡lG , _ = Π-PE-injectivity (whrDet* (D′ , Whnf.Πₙ) (red D' , Whnf.Πₙ))
  in Uₜ₌ (un-univEq (maybeEmb′ (<is≤ 0<1) [A])) (irrelevanceTerm {l = next ¹} (Ugen (wf (escape [B]))) (Ugen (wf (escape [A]))) (un-univEq (maybeEmb′ (<is≤ 0<1) [B])))
         (≅-un-univ (
           PE.subst (λ X → _ ⊢ Π F ^ rF ° lF ▹ G ° lG ° _ ≅  Π F' ^ rF' ° lF' ▹ X ° lG' ° _ ^ _ ) G≡G
           (PE.subst (λ X → _ ⊢ Π F ^ rF ° lF ▹ G ° lG ° _ ≅  Π X ^ rF' ° lF' ▹ G′ ° lG' ° _ ^ _ ) F≡F
             (PE.subst (λ X → _ ⊢ Π F ^ rF ° lF ▹ G ° lG ° _ ≅  Π F′ ^ rF' ° lF' ▹ G′ ° X ° _ ^ _ ) lG≡lG
             (PE.subst (λ X → _ ⊢ Π F ^ rF ° lF ▹ G ° lG ° _ ≅  Π F′ ^ rF' ° X ▹ G′ ° lG ° _ ^ _ ) lF≡lF
             (PE.subst (λ X → _ ⊢ Π F ^ rF ° lF ▹ G ° lG ° _ ≅  Π F′ ^ X ° lF ▹ G′ ° lG ° _ ^ _ ) rF≡rF A≡B)))))) λ [ρ] ⊢Δ → Lwk.wkEq [ρ] ⊢Δ [A] [A≡B]
un-univEqEq-Shape {¹} {Γ} {A} {B} {.%} _ _ (emb⁰¹ (emb¹⁰ (∃ᵥ (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                        (∃ᵣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext'))))
                                    (∃₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  let [A] = ∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext
      [B] = ∃ᵣ′ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext'
      [A≡B] = ∃₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]
      F≡F , G≡G  = ∃-PE-injectivity (whrDet* (D′ , Whnf.∃ₙ) (red D' , Whnf.∃ₙ))
  in Uₜ₌ (un-univEq (maybeEmb′ (<is≤ 0<1) [A])) (irrelevanceTerm {l = next ¹} (Ugen (wf (escape [B]))) (Ugen (wf (escape [A]))) (un-univEq (maybeEmb′ (<is≤ 0<1) [B])))
         (≅-un-univ (
           PE.subst (λ X → _ ⊢ ∃ F ▹ G ≅  ∃ F' ▹ X ^ _ ) G≡G
           (PE.subst (λ X → _ ⊢ ∃ F ▹ G ≅  ∃ X ▹ G′ ^ _ ) F≡F A≡B))) λ [ρ] ⊢Δ → Lwk.wkEq [ρ] ⊢Δ [A] [A≡B]
un-univEqEq-Shape {¹} {Γ} {A} {B} {.%} _ _ (emb¹⁰ (Emptyᵥ [[ ⊢A , ⊢Empty , D ]] EmptyB)) [A≡B] =
  let [A] = Emptyᵣ [[ ⊢A , ⊢Empty , D ]]
      [B] = Emptyᵣ [[ redFirst* [A≡B] , ⊢Empty , [A≡B] ]]
  in Uₜ₌ (un-univEq [A]) (irrelevanceTerm {l = next ¹} (Ugen (wf (escape [B]))) (Ugen (wf (escape [A]))) (un-univEq [B]))
         (≅ₜ-Emptyrefl (wf ⊢A)) λ [ρ] ⊢Δ → Lwk.wkEq [ρ] ⊢Δ [A] [A≡B]
un-univEqEq-Shape {¹} {Γ} {A} {B} {r} _ _ (emb¹⁰ (ne (ne K D neK K≡K) neB)) (ne₌ M D′ neM K≡M) =
  let [A] = ne′ K D neK K≡K
      [B] = ne′ M D′ neM (~-trans (~-sym K≡M) K≡M)
      [A≡B] = ne₌ M D′ neM K≡M
  in Uₜ₌ (un-univEq [A]) (irrelevanceTerm {l = next ¹} (Ugen (wf (escape [B]))) (Ugen (wf (escape [A]))) (un-univEq [B]))
         (~-to-≅ₜ K≡M) λ [ρ] ⊢Δ → Lwk.wkEq [ρ] ⊢Δ [A] [A≡B]
un-univEqEq-Shape {¹} {Γ} {A} {B} {r} _ _ (emb¹⁰ (Πᵥ (Πᵣ rF lF lG lF< lG< F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                        (Πᵣ rF' lF' lG' lF<' lG<' F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext')))
                                    (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  let [A] = Πᵣ′ rF lF lG lF< lG< F G D ⊢F ⊢G A≡A [F] [G] G-ext
      [B] = Πᵣ′ rF' lF' lG' lF<' lG<' F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext'
      [A≡B] = Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]
      F≡F , rF≡rF , lF≡lF , G≡G , lG≡lG , _ = Π-PE-injectivity (whrDet* (D′ , Whnf.Πₙ) (red D' , Whnf.Πₙ))
  in Uₜ₌ (un-univEq [A] ) (irrelevanceTerm {l = next ¹} (Ugen (wf (escape [B]))) (Ugen (wf (escape [A]))) (un-univEq (maybeEmb′ (<is≤ 0<1) [B])))
         (≅-un-univ (
           PE.subst (λ X → _ ⊢ Π F ^ rF ° lF ▹ G ° lG ° _ ≅  Π F' ^ rF' ° lF' ▹ X ° lG' ° _ ^ _ ) G≡G
           (PE.subst (λ X → _ ⊢ Π F ^ rF ° lF ▹ G ° lG ° _ ≅  Π X ^ rF' ° lF' ▹ G′ ° lG' ° _ ^ _ ) F≡F
             (PE.subst (λ X → _ ⊢ Π F ^ rF ° lF ▹ G ° lG ° _ ≅  Π F′ ^ rF' ° lF' ▹ G′ ° X ° _ ^ _ ) lG≡lG
             (PE.subst (λ X → _ ⊢ Π F ^ rF ° lF ▹ G ° lG ° _ ≅  Π F′ ^ rF' ° X ▹ G′ ° lG ° _ ^ _ ) lF≡lF
             (PE.subst (λ X → _ ⊢ Π F ^ rF ° lF ▹ G ° lG ° _ ≅  Π F′ ^ X ° lF ▹ G′ ° lG ° _ ^ _ ) rF≡rF A≡B)))))) λ [ρ] ⊢Δ → Lwk.wkEq [ρ] ⊢Δ [A] [A≡B]
un-univEqEq-Shape {¹} {Γ} {A} {B} {.%} _ _ (emb¹⁰ (∃ᵥ (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                        (∃ᵣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext')))
                                    (∃₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  let [A] = ∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext
      [B] = ∃ᵣ′ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext'
      [A≡B] = ∃₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]
      F≡F , G≡G  = ∃-PE-injectivity (whrDet* (D′ , Whnf.∃ₙ) (red D' , Whnf.∃ₙ))
  in Uₜ₌ (un-univEq [A]) (irrelevanceTerm {l = next ¹} (Ugen (wf (escape [B]))) (Ugen (wf (escape [A]))) (un-univEq (maybeEmb′ (<is≤ 0<1) [B])))
         (≅-un-univ (
           PE.subst (λ X → _ ⊢ ∃ F ▹ G ≅  ∃ F' ▹ X ^ _ ) G≡G
           (PE.subst (λ X → _ ⊢ ∃ F ▹ G ≅  ∃ X ▹ G′ ^ _ ) F≡F A≡B))) λ [ρ] ⊢Δ → Lwk.wkEq [ρ] ⊢Δ [A] [A≡B]
un-univEqEq-Shape {¹} {Γ} {A} {B} {.%} _ _ (emb¹⁰ (emb⁰¹ (Emptyᵥ [[ ⊢A , ⊢Empty , D ]] EmptyB))) [A≡B] =
  let [A] = Emptyᵣ [[ ⊢A , ⊢Empty , D ]]
      [B] = Emptyᵣ [[ redFirst* [A≡B] , ⊢Empty , [A≡B] ]]
  in Uₜ₌ (un-univEq [A]) (irrelevanceTerm {l = next ¹} (Ugen (wf (escape [B]))) (Ugen (wf (escape [A]))) (un-univEq [B]))
         (≅ₜ-Emptyrefl (wf ⊢A)) λ [ρ] ⊢Δ → Lwk.wkEq [ρ] ⊢Δ [A] [A≡B]
un-univEqEq-Shape {¹} {Γ} {A} {B} {r} _ _ (emb¹⁰ (emb⁰¹ (ne (ne K D neK K≡K) neB))) (ne₌ M D′ neM K≡M) =
  let [A] = ne′ K D neK K≡K
      [B] = ne′ M D′ neM (~-trans (~-sym K≡M) K≡M)
      [A≡B] = ne₌ M D′ neM K≡M
  in Uₜ₌ (un-univEq [A]) (irrelevanceTerm {l = next ¹} (Ugen (wf (escape [B]))) (Ugen (wf (escape [A]))) (un-univEq [B]))
         (~-to-≅ₜ K≡M) λ [ρ] ⊢Δ → Lwk.wkEq [ρ] ⊢Δ [A] [A≡B]
un-univEqEq-Shape {¹} {Γ} {A} {B} {r} _ _ (emb¹⁰ (emb⁰¹ (Πᵥ (Πᵣ rF lF lG lF< lG< F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                        (Πᵣ rF' lF' lG' lF<' lG<' F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext'))))
                                    (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  let [A] = Πᵣ′ rF lF lG lF< lG< F G D ⊢F ⊢G A≡A [F] [G] G-ext
      [B] = Πᵣ′ rF' lF' lG' lF<' lG<' F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext'
      [A≡B] = Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]
      F≡F , rF≡rF , lF≡lF , G≡G , lG≡lG , _ = Π-PE-injectivity (whrDet* (D′ , Whnf.Πₙ) (red D' , Whnf.Πₙ))
  in Uₜ₌ (un-univEq (maybeEmb′ (<is≤ 0<1) [A])) (irrelevanceTerm {l = next ¹} (Ugen (wf (escape [B]))) (Ugen (wf (escape [A]))) (un-univEq (maybeEmb′ (<is≤ 0<1) [B])))
         (≅-un-univ (
           PE.subst (λ X → _ ⊢ Π F ^ rF ° lF ▹ G ° lG  ° _ ≅  Π F' ^ rF' ° lF' ▹ X ° lG' ° _ ^ _ ) G≡G
           (PE.subst (λ X → _ ⊢ Π F ^ rF ° lF ▹ G ° lG ° _ ≅  Π X ^ rF' ° lF' ▹ G′ ° lG' ° _ ^ _ ) F≡F
             (PE.subst (λ X → _ ⊢ Π F ^ rF ° lF ▹ G ° lG ° _ ≅  Π F′ ^ rF' ° lF' ▹ G′ ° X ° _ ^ _ ) lG≡lG
             (PE.subst (λ X → _ ⊢ Π F ^ rF ° lF ▹ G ° lG ° _ ≅  Π F′ ^ rF' ° X ▹ G′ ° lG ° _ ^ _ ) lF≡lF
             (PE.subst (λ X → _ ⊢ Π F ^ rF ° lF ▹ G ° lG ° _ ≅  Π F′ ^ X ° lF ▹ G′ ° lG ° _  ^ _ ) rF≡rF A≡B)))))) λ [ρ] ⊢Δ → Lwk.wkEq [ρ] ⊢Δ [A] [A≡B]
un-univEqEq-Shape {¹} {Γ} {A} {B} {.%} _ _ (emb¹⁰ (emb⁰¹ (∃ᵥ (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                                        (∃ᵣ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext'))))
                                    (∃₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  let [A] = ∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext
      [B] = ∃ᵣ′ F' G' D' ⊢F' ⊢G' A≡A' [F'] [G'] G-ext'
      [A≡B] = ∃₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]
      F≡F , G≡G  = ∃-PE-injectivity (whrDet* (D′ , Whnf.∃ₙ) (red D' , Whnf.∃ₙ))
  in Uₜ₌ (un-univEq (maybeEmb′ (<is≤ 0<1) [A])) (irrelevanceTerm {l = next ¹} (Ugen (wf (escape [B]))) (Ugen (wf (escape [A]))) (un-univEq (maybeEmb′ (<is≤ 0<1) [B])))
         (≅-un-univ (
           PE.subst (λ X → _ ⊢ ∃ F ▹ G ≅  ∃ F' ▹ X ^ _ ) G≡G
           (PE.subst (λ X → _ ⊢ ∃ F ▹ G ≅  ∃ X ▹ G′ ^ _ ) F≡F A≡B))) λ [ρ] ⊢Δ → Lwk.wkEq [ρ] ⊢Δ [A] [A≡B]

un-univEqEq : ∀ {l Γ A B r }
          ([A] : Γ ⊩⟨ ι l ⟩ A ^ [ r , ι l ]) ([B] : Γ ⊩⟨ ι l ⟩ B ^ [ r , ι l ])
          ([A≡B] : Γ ⊩⟨ ι l ⟩ A ≡ B ^ [ r , ι l ] / [A])
          → let [U] : Γ ⊩⟨ next l ⟩ Univ r l ^ [ ! , next l ]
                [U] = Ugen (wf (escape [A]))
            in Γ ⊩⟨ next l ⟩ A ≡ B ∷ Univ r l ^ [ ! , next l ] / [U]
un-univEqEq [A] [B] [A≡B] = un-univEqEq-Shape [A] [B] (goodCases [A] [B] [A≡B]) [A≡B]
