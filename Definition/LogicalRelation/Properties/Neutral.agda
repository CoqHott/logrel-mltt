{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Neutral {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties.Reflexivity
open import Definition.LogicalRelation.Properties.Escape
open import Definition.LogicalRelation.Properties.Symmetry

open import Tools.Product
import Tools.PropositionalEquality as PE

import Data.Fin as Fin
import Data.Nat as Nat


-- Neutral reflexive types are reducible.
neu : ∀ {l Γ A r ll} (neA : Neutral A)
    → Γ ⊢ A ^ [ r , ι ll ]
    → Γ ⊢ A ~ A ∷ Univ r ll ^ [ ! , next ll ]
    → Γ ⊩⟨ l ⟩ A ^ [ r , ι ll ]
neu neA A A~A = ne′ _ (idRed:*: A) neA A~A

  -- Helper function for reducible neutral equality of a specific type of derivation.
neuEq′ : ∀ {l Γ A B r ll} ([A] : Γ ⊩⟨ l ⟩ne A ^[ r , ll ])
         (neA : Neutral A)
         (neB : Neutral B)
       → Γ ⊢ A ^ [ r , ι ll ] → Γ ⊢ B ^ [ r , ι ll ]
       → Γ ⊢ A ~ B ∷ Univ r ll ^ [ ! , next ll ]
       → Γ ⊩⟨ l ⟩ A ≡ B ^ [ r , ι ll ] / ne-intr [A]
neuEq′ (noemb (ne K [[ ⊢A , ⊢B , D ]] neK K≡K)) neA neB A B A~B =
  let A≡K = whnfRed* D (ne neA)
  in  ne₌ _ (idRed:*: B) neB (PE.subst (λ x → _ ⊢ x ~ _ ∷ _ ^ _) A≡K A~B)
neuEq′ {ι ¹} (emb {ι ⁰} (Nat.s≤s Nat.z≤n) X) = neuEq′ X 
neuEq′ {ι ¹} (emb {ι ¹} (Nat.s≤s ()) X) 
neuEq′ {ι ¹} (emb {∞} (Nat.s≤s ()) X) 
neuEq′ {∞} (emb {ι ⁰} (Nat.s≤s Nat.z≤n) X) = neuEq′ X 
neuEq′ {∞} (emb {ι ¹} (Nat.s≤s (Nat.s≤s Nat.z≤n)) X) = neuEq′ X
neuEq′ {∞} (emb {∞} (Nat.s≤s (Nat.s≤s ())) X)

-- neuEq′ x neB A:≡:B

-- Neutrally equal types are of reducible equality.
neuEq : ∀ {l Γ A B r ll} ([A] : Γ ⊩⟨ l ⟩ A ^ [ r , ι ll ])
        (neA : Neutral A)
        (neB : Neutral B)
      → Γ ⊢ A ^ [ r , ι ll ] → Γ ⊢ B ^ [ r , ι ll ]
      → Γ ⊢ A ~ B ∷ Univ r ll ^ [ ! , next ll ]
      → Γ ⊩⟨ l ⟩ A ≡ B ^ [ r , ι ll ] / [A]
neuEq [A] neA neB A B A~B =
  irrelevanceEq (ne-intr (ne-elim neA [A]))
                [A]
                (neuEq′ (ne-elim neA [A]) neA neB A B A~B)

mutual 
  neuTerm⁰ : ∀ {Γ A r n} ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ r) (neN : Neutral n)
          → Γ ⊢ n ∷ A ^ r
          → Γ ⊢ n ~ n ∷ A ^ r
          → Γ ⊩⟨ ι ⁰ ⟩ n ∷ A ^ r / [A]

  neuTerm⁰ (ℕᵣ [[ ⊢A , ⊢B , D ]]) neN n n~n =
    let A≡ℕ  = subset* D
        n~n′ = ~-conv n~n A≡ℕ
        n≡n  = ~-to-≅ₜ n~n′
    in  ℕₜ _ (idRedTerm:*: (conv n A≡ℕ)) n≡n (ne (neNfₜ neN (conv n A≡ℕ) n~n′))
  neuTerm⁰ {r = [ ! , ll ]} (ne′ K [[ ⊢A , ⊢B , D ]] neK K≡K) neN n n~n =
    let A≡K = subset* D
    in  neₜ _ (idRedTerm:*: (conv n A≡K)) (neNfₜ neN (conv n A≡K)
            (~-conv n~n A≡K))
  neuTerm⁰ {r = [ ! , ll ]} (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) neN n n~n =
    let A≡ΠFG = subset* (red D)
    in  Πₜ _ (idRedTerm:*: (conv n A≡ΠFG)) (ne neN) (~-to-≅ₜ (~-conv n~n A≡ΠFG))
           (λ {ρ} [ρ] ⊢Δ [a] [b] [a≡b] →
              let A≡ΠFG = subset* (red D)
                  ρA≡ρΠFG = wkEq [ρ] ⊢Δ (subset* (red D))
                  G[a]≡G[b] = escapeEq ([G] [ρ] ⊢Δ [b])
                                          (symEq ([G] [ρ] ⊢Δ [a]) ([G] [ρ] ⊢Δ [b])
                                                 (G-ext [ρ] ⊢Δ [a] [b] [a≡b]))
                  a = escapeTerm ([F] [ρ] ⊢Δ) [a]
                  b = escapeTerm ([F] [ρ] ⊢Δ) [b]
                  a≡b = escapeTermEq ([F] [ρ] ⊢Δ) [a≡b]
                  ρn = conv (wkTerm [ρ] ⊢Δ n) ρA≡ρΠFG
                  neN∘a = ∘ₙ (wkNeutral ρ neN)
                  neN∘b = ∘ₙ (wkNeutral ρ neN)
              in  neuEqTerm⁰ ([G] [ρ] ⊢Δ [a]) neN∘a neN∘b
                            (ρn ∘ⱼ a)
                            (conv (ρn ∘ⱼ b) (≅-eq G[a]≡G[b]))
                            (~-app (~-wk [ρ] ⊢Δ (~-conv n~n A≡ΠFG)) a≡b))
           (λ {ρ} [ρ] ⊢Δ [a] →
              let ρA≡ρΠFG = wkEq [ρ] ⊢Δ (subset* (red D))
                  a = escapeTerm ([F] [ρ] ⊢Δ) [a]
                  a≡a = escapeTermEq ([F] [ρ] ⊢Δ) (reflEqTerm ([F] [ρ] ⊢Δ) [a])
              in  neuTerm⁰ ([G] [ρ] ⊢Δ [a]) (∘ₙ (wkNeutral ρ neN))
                          (conv (wkTerm [ρ] ⊢Δ n) ρA≡ρΠFG ∘ⱼ a)
                          (~-app (~-wk [ρ] ⊢Δ (~-conv n~n A≡ΠFG)) a≡a))
  neuTerm⁰ (Emptyᵣ [[ ⊢A , ⊢B , D ]]) neN n n~n =
    let A≡ℕ  = subset* D
    in Emptyₜ (ne (conv n A≡ℕ))
  neuTerm⁰ {r = [ % , ll ]} (ne′ K [[ ⊢A , ⊢B , D ]] neK K≡K) neN n n~n =
    let A≡K = subset* D
    in  neₜ n
  neuTerm⁰ {r = [ % , ll ]} (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) neN n n~n = let A≡ΠFG = subset* (red D) in conv n A≡ΠFG
  neuTerm⁰ {r = [ % , ll ]} (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) neN n n~n = let A≡ΠFG = subset* (red D) in conv n A≡ΠFG

  neuEqTerm⁰ : ∀ {Γ A n n′ r} ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ r)
              (neN : Neutral n) (neN′ : Neutral n′)
            → Γ ⊢ n  ∷ A ^ r
            → Γ ⊢ n′ ∷ A ^ r
            → Γ ⊢ n ~ n′ ∷ A ^ r
            → Γ ⊩⟨ ι ⁰ ⟩ n ≡ n′ ∷ A ^ r / [A]

  neuEqTerm⁰ (ℕᵣ [[ ⊢A , ⊢B , D ]]) neN neN′ n n′ n~n′ =
    let A≡ℕ = subset* D
        n~n′₁ = ~-conv n~n′ A≡ℕ
        n≡n′ = ~-to-≅ₜ n~n′₁
    in  ℕₜ₌ _ _ (idRedTerm:*: (conv n A≡ℕ)) (idRedTerm:*: (conv n′ A≡ℕ))
            n≡n′ (ne (neNfₜ₌ neN neN′ n~n′₁))
  neuEqTerm⁰ (Emptyᵣ [[ ⊢A , ⊢B , D ]]) neN neN′ n n′ n~n′ =
    let A≡Empty = subset* D
    in  Emptyₜ₌  (ne (conv n A≡Empty) (conv n′ A≡Empty))
  neuEqTerm⁰ {r = [ ! , ll ]} (ne (ne K [[ ⊢A , ⊢B , D ]] neK K≡K)) neN neN′ n n′ n~n′ =
    let A≡K = subset* D
    in  neₜ₌ _ _ (idRedTerm:*: (conv n A≡K)) (idRedTerm:*: (conv n′ A≡K))
             (neNfₜ₌ neN neN′ (~-conv n~n′ A≡K))
  neuEqTerm⁰ {r = [ % , ll ]} (ne (ne K [[ ⊢A , ⊢B , D ]] neK K≡K)) neN neN′ n n′ n~n′ =
    let A≡K = subset* D
    in neₜ₌ n n′
  neuEqTerm⁰ {r = [ ! , ll ]} (Πᵣ′ rF F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext) neN neN′ n n′ n~n′ =
    let [ΠFG] = Πᵣ′ rF F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext
        A≡ΠFG = subset* D
        n~n′₁ = ~-conv n~n′ A≡ΠFG
        n≡n′ = ~-to-≅ₜ n~n′₁
        n~n = ~-trans n~n′ (~-sym n~n′)
        n′~n′ = ~-trans (~-sym n~n′) n~n′
    in  Πₜ₌ _ _ (idRedTerm:*: (conv n A≡ΠFG)) (idRedTerm:*: (conv n′ A≡ΠFG))
            (ne neN) (ne neN′) n≡n′
            (neuTerm⁰ [ΠFG] neN n n~n) (neuTerm⁰ [ΠFG] neN′ n′ n′~n′)
            (λ {ρ} [ρ] ⊢Δ [a] →
               let ρA≡ρΠFG = wkEq [ρ] ⊢Δ A≡ΠFG
                   ρn = wkTerm [ρ] ⊢Δ n
                   ρn′ = wkTerm [ρ] ⊢Δ n′
                   a = escapeTerm ([F] [ρ] ⊢Δ) [a]
                   a≡a = escapeTermEq ([F] [ρ] ⊢Δ)
                                          (reflEqTerm ([F] [ρ] ⊢Δ) [a])
                   neN∙a   = ∘ₙ (wkNeutral ρ neN)
                   neN′∙a′ = ∘ₙ (wkNeutral ρ neN′)
               in  neuEqTerm⁰ ([G] [ρ] ⊢Δ [a]) neN∙a neN′∙a′
                             (conv ρn  ρA≡ρΠFG ∘ⱼ a)
                             (conv ρn′ ρA≡ρΠFG ∘ⱼ a)
                             (~-app (~-wk [ρ] ⊢Δ n~n′₁) a≡a))
  neuEqTerm⁰ {r = [ % , ll ]} (Πᵣ′ rF F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext) neN neN′ n n′ n~n′ =
    let A≡ΠFG = subset* D
    in conv n A≡ΠFG , conv n′ A≡ΠFG
  neuEqTerm⁰ {r = [ % , ll ]} (∃ᵣ′ F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext) neN neN′ n n′ n~n′ =
    let A≡ΠFG = subset* D
    in conv n A≡ΠFG , conv n′ A≡ΠFG




mutual
  -- Neutral reflexive terms are reducible.
  neuTerm : ∀ {l Γ A r n} ([A] : Γ ⊩⟨ l ⟩ A ^ r) (neN : Neutral n)
          → Γ ⊢ n ∷ A ^ r
          → Γ ⊢ n ~ n ∷ A ^ r
          → Γ ⊩⟨ l ⟩ n ∷ A ^ r / [A]
  neuTerm {ι ¹} (Uᵣ′ A .(next ⁰) r ⁰ (Nat.s≤s Nat.z≤n) PE.refl [[ ⊢A , ⊢U , D ]]) neN n n~n = 
    let n' = (conv n (subset* D))
        n~n' = ~-conv  n~n (subset* D)
        [n] = neu neN (univ n') n~n'
    in Uₜ _ (idRedTerm:*: n') (ne neN) (~-to-≅ₜ n~n') [n]
          (λ [a] [a'] →
             let a = escapeTerm [n] [a]
                 a' = escapeTerm [n] [a']
                 a≡a = escapeTermEq [n] (reflEqTerm [n] [a])
                 a'≡a' = escapeTermEq [n] (reflEqTerm [n] [a'])
             in neu (Idₙ neN) (univ (Idⱼ n' a a')) (~-Id n~n' a≡a a'≡a'))
          (λ {_ PE.refl [B] ⊢e [a] →
             let a = escapeTerm [n] [a]
                 a≡a = escapeTermEq [n] (reflEqTerm [n] [a])
                 B≡B = ≅-un-univ (escapeEq [B] (reflEq [B]))
             in neuTerm⁰ [B] (castₙ neN) (castⱼ n' (un-univ (escape [B])) ⊢e a) (~-cast n~n' B≡B a≡a)})
  neuTerm {∞} (Uᵣ′ A .(next ⁰) r ⁰ (Nat.s≤s Nat.z≤n) PE.refl [[ ⊢A , ⊢U , D ]]) neN n n~n =
    let n' = (conv n (subset* D))
        n~n' = ~-conv  n~n (subset* D)
        [n] = neu neN (univ n') n~n'
    in Uₜ _ (idRedTerm:*: n') (ne neN) (~-to-≅ₜ n~n') [n]
          (λ [a] [a'] →
             let a = escapeTerm [n] [a]
                 a' = escapeTerm [n] [a']
                 a≡a = escapeTermEq [n] (reflEqTerm [n] [a])
                 a'≡a' = escapeTermEq [n] (reflEqTerm [n] [a'])
             in neu (Idₙ neN) (univ (Idⱼ n' a a')) (~-Id n~n' a≡a a'≡a'))
          (λ {_ PE.refl [B] ⊢e [a] →
             let a = escapeTerm [n] [a]
                 a≡a = escapeTermEq [n] (reflEqTerm [n] [a])
                 B≡B = ≅-un-univ (escapeEq [B] (reflEq [B]))
             in neuTerm⁰ [B] (castₙ neN) (castⱼ n' (un-univ (escape [B])) ⊢e a) (~-cast n~n' B≡B a≡a)})
  neuTerm {ι ¹} (Uᵣ′ A .(next ¹) r ¹ (Nat.s≤s ()) PE.refl [[ ⊢A , ⊢U , D ]]) 
  neuTerm {∞} (Uᵣ′ A .(next ¹) r ¹ (Nat.s≤s (Nat.s≤s Nat.z≤n)) PE.refl [[ ⊢A , ⊢U , D ]]) neN n n~n =
    let n' = (conv n (subset* D))
        n~n' = ~-conv  n~n (subset* D)
        [n] = neu neN (univ n') n~n'
    in Uₜ _ (idRedTerm:*: n') (ne neN) (~-to-≅ₜ n~n') [n]
          (λ [a] [a'] →
             let a = escapeTerm [n] [a]
                 a' = escapeTerm [n] [a']
                 a≡a = escapeTermEq [n] (reflEqTerm [n] [a])
                 a'≡a' = escapeTermEq [n] (reflEqTerm [n] [a'])
             in neu (Idₙ neN) (univ (Idⱼ n' a a')) (~-Id n~n' a≡a a'≡a'))
          (λ {()})
  neuTerm (ℕᵣ [[ ⊢A , ⊢B , D ]]) neN n n~n =
    let A≡ℕ  = subset* D
        n~n′ = ~-conv n~n A≡ℕ
        n≡n  = ~-to-≅ₜ n~n′
    in  ℕₜ _ (idRedTerm:*: (conv n A≡ℕ)) n≡n (ne (neNfₜ neN (conv n A≡ℕ) n~n′))
  neuTerm {r = [ ! , ll ]} (ne′ K [[ ⊢A , ⊢B , D ]] neK K≡K) neN n n~n =
    let A≡K = subset* D
    in  neₜ _ (idRedTerm:*: (conv n A≡K)) (neNfₜ neN (conv n A≡K)
            (~-conv n~n A≡K))
  neuTerm {r = [ ! , ll ]} (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) neN n n~n =
    let A≡ΠFG = subset* (red D)
    in  Πₜ _ (idRedTerm:*: (conv n A≡ΠFG)) (ne neN) (~-to-≅ₜ (~-conv n~n A≡ΠFG))
           (λ {ρ} [ρ] ⊢Δ [a] [b] [a≡b] →
              let A≡ΠFG = subset* (red D)
                  ρA≡ρΠFG = wkEq [ρ] ⊢Δ (subset* (red D))
                  G[a]≡G[b] = escapeEq ([G] [ρ] ⊢Δ [b])
                                          (symEq ([G] [ρ] ⊢Δ [a]) ([G] [ρ] ⊢Δ [b])
                                                 (G-ext [ρ] ⊢Δ [a] [b] [a≡b]))
                  a = escapeTerm ([F] [ρ] ⊢Δ) [a]
                  b = escapeTerm ([F] [ρ] ⊢Δ) [b]
                  a≡b = escapeTermEq ([F] [ρ] ⊢Δ) [a≡b]
                  ρn = conv (wkTerm [ρ] ⊢Δ n) ρA≡ρΠFG
                  neN∘a = ∘ₙ (wkNeutral ρ neN)
                  neN∘b = ∘ₙ (wkNeutral ρ neN)
              in  neuEqTerm ([G] [ρ] ⊢Δ [a]) neN∘a neN∘b
                            (ρn ∘ⱼ a)
                            (conv (ρn ∘ⱼ b) (≅-eq G[a]≡G[b]))
                            (~-app (~-wk [ρ] ⊢Δ (~-conv n~n A≡ΠFG)) a≡b))
           (λ {ρ} [ρ] ⊢Δ [a] →
              let ρA≡ρΠFG = wkEq [ρ] ⊢Δ (subset* (red D))
                  a = escapeTerm ([F] [ρ] ⊢Δ) [a]
                  a≡a = escapeTermEq ([F] [ρ] ⊢Δ) (reflEqTerm ([F] [ρ] ⊢Δ) [a])
              in  neuTerm ([G] [ρ] ⊢Δ [a]) (∘ₙ (wkNeutral ρ neN))
                          (conv (wkTerm [ρ] ⊢Δ n) ρA≡ρΠFG ∘ⱼ a)
                          (~-app (~-wk [ρ] ⊢Δ (~-conv n~n A≡ΠFG)) a≡a))
  -- neuTerm {r = %} (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) neN n n~n = {!!}
  neuTerm (Emptyᵣ [[ ⊢A , ⊢B , D ]]) neN n n~n =
    let A≡ℕ  = subset* D
    in Emptyₜ (ne (conv n A≡ℕ))
  neuTerm {r = [ % , ll ]} (ne′ K [[ ⊢A , ⊢B , D ]] neK K≡K) neN n n~n =
    let A≡K = subset* D
    in  neₜ n
  neuTerm {r = [ % , ll ]} (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) neN n n~n = let A≡ΠFG = subset* (red D) in conv n A≡ΠFG
  neuTerm {r = [ % , ll ]} (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) neN n n~n = let A≡ΠFG = subset* (red D) in conv n A≡ΠFG
  neuTerm {ι ¹} (emb {l′ = ι ⁰} l< X) neN n = neuTerm X neN n
  neuTerm {∞} (emb {l′ = ι ⁰} l< X) neN n = neuTerm X neN n
  neuTerm {∞} (emb {l′ = ι ¹} l< X) neN n = neuTerm X neN n
  neuTerm {ι ¹} (emb {l′ = ι ¹} (Nat.s≤s ()) X) 
  neuTerm {ι ¹} (emb {l′ = ∞} (Nat.s≤s ()) X)
  neuTerm {∞} (emb {l′ = ∞} (Nat.s≤s (Nat.s≤s ())) X) 

  -- Neutrally equal terms are of reducible equality.
  neuEqTerm : ∀ {l Γ A n n′ r} ([A] : Γ ⊩⟨ l ⟩ A ^ r)
              (neN : Neutral n) (neN′ : Neutral n′)
            → Γ ⊢ n  ∷ A ^ r
            → Γ ⊢ n′ ∷ A ^ r
            → Γ ⊢ n ~ n′ ∷ A ^ r
            → Γ ⊩⟨ l ⟩ n ≡ n′ ∷ A ^ r / [A]
  neuEqTerm {ι ¹} (Uᵣ′ A _ r ⁰ (Nat.s≤s Nat.z≤n) PE.refl D) neN neN′ n n′ n~n = 
    let n' = conv n (subset* (red D))
        n′' = conv n′ (subset* (red D))
        n~n' = ~-conv n~n (subset* (red D))
        [n]  = neu neN  (univ n') (~-trans n~n' (~-sym n~n'))
        [n′] = neu neN′ (univ n′') (~-trans (~-sym n~n') n~n')
    in Uₜ₌ _ _ (idRedTerm:*: n') (idRedTerm:*: n′') (ne neN) (ne neN′) (~-to-≅ₜ n~n') [n] [n′] (neuEq [n] neN neN′ (univ n') (univ n′') n~n') 
  neuEqTerm {ι ¹} (Uᵣ′ a _ r ¹ (Nat.s≤s ()) e D)
  neuEqTerm {∞} (Uᵣ′ A _ r ⁰ (Nat.s≤s Nat.z≤n) PE.refl D) neN neN′ n n′ n~n =
    let n' = conv n (subset* (red D))
        n′' = conv n′ (subset* (red D))
        n~n' = ~-conv n~n (subset* (red D))
        [n]  = neu neN  (univ n') (~-trans n~n' (~-sym n~n'))
        [n′] = neu neN′ (univ n′') (~-trans (~-sym n~n') n~n')
    in Uₜ₌ _ _ (idRedTerm:*: n') (idRedTerm:*: n′') (ne neN) (ne neN′) (~-to-≅ₜ n~n') [n] [n′] (neuEq [n] neN neN′ (univ n') (univ n′') n~n') 
  neuEqTerm {∞} (Uᵣ′ A _ r ¹ (Nat.s≤s (Nat.s≤s Nat.z≤n)) PE.refl D) neN neN′ n n′ n~n =
    let n' = conv n (subset* (red D))
        n′' = conv n′ (subset* (red D))
        n~n' = ~-conv n~n (subset* (red D))
        [n]  = neu neN  (univ n') (~-trans n~n' (~-sym n~n'))
        [n′] = neu neN′ (univ n′') (~-trans (~-sym n~n') n~n')
    in Uₜ₌ _ _ (idRedTerm:*: n') (idRedTerm:*: n′') (ne neN) (ne neN′) (~-to-≅ₜ n~n') [n] [n′] (neuEq [n] neN neN′ (univ n') (univ n′') n~n') 
  neuEqTerm (ℕᵣ [[ ⊢A , ⊢B , D ]]) neN neN′ n n′ n~n′ =
    let A≡ℕ = subset* D
        n~n′₁ = ~-conv n~n′ A≡ℕ
        n≡n′ = ~-to-≅ₜ n~n′₁
    in  ℕₜ₌ _ _ (idRedTerm:*: (conv n A≡ℕ)) (idRedTerm:*: (conv n′ A≡ℕ))
            n≡n′ (ne (neNfₜ₌ neN neN′ n~n′₁))
  neuEqTerm (Emptyᵣ [[ ⊢A , ⊢B , D ]]) neN neN′ n n′ n~n′ =
    let A≡Empty = subset* D
    in  Emptyₜ₌  (ne (conv n A≡Empty) (conv n′ A≡Empty))
  neuEqTerm {r = [ ! , ll ]} (ne (ne K [[ ⊢A , ⊢B , D ]] neK K≡K)) neN neN′ n n′ n~n′ =
    let A≡K = subset* D
    in  neₜ₌ _ _ (idRedTerm:*: (conv n A≡K)) (idRedTerm:*: (conv n′ A≡K))
             (neNfₜ₌ neN neN′ (~-conv n~n′ A≡K))
  neuEqTerm {r = [ % , ll ]} (ne (ne K [[ ⊢A , ⊢B , D ]] neK K≡K)) neN neN′ n n′ n~n′ =
    let A≡K = subset* D
    in neₜ₌ n n′
  neuEqTerm {r = [ ! , ll ]} (Πᵣ′ rF F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext) neN neN′ n n′ n~n′ =
    let [ΠFG] = Πᵣ′ rF F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext
        A≡ΠFG = subset* D
        n~n′₁ = ~-conv n~n′ A≡ΠFG
        n≡n′ = ~-to-≅ₜ n~n′₁
        n~n = ~-trans n~n′ (~-sym n~n′)
        n′~n′ = ~-trans (~-sym n~n′) n~n′
    in  Πₜ₌ _ _ (idRedTerm:*: (conv n A≡ΠFG)) (idRedTerm:*: (conv n′ A≡ΠFG))
            (ne neN) (ne neN′) n≡n′
            (neuTerm [ΠFG] neN n n~n) (neuTerm [ΠFG] neN′ n′ n′~n′)
            (λ {ρ} [ρ] ⊢Δ [a] →
               let ρA≡ρΠFG = wkEq [ρ] ⊢Δ A≡ΠFG
                   ρn = wkTerm [ρ] ⊢Δ n
                   ρn′ = wkTerm [ρ] ⊢Δ n′
                   a = escapeTerm ([F] [ρ] ⊢Δ) [a]
                   a≡a = escapeTermEq ([F] [ρ] ⊢Δ)
                                          (reflEqTerm ([F] [ρ] ⊢Δ) [a])
                   neN∙a   = ∘ₙ (wkNeutral ρ neN)
                   neN′∙a′ = ∘ₙ (wkNeutral ρ neN′)
               in  neuEqTerm ([G] [ρ] ⊢Δ [a]) neN∙a neN′∙a′
                             (conv ρn  ρA≡ρΠFG ∘ⱼ a)
                             (conv ρn′ ρA≡ρΠFG ∘ⱼ a)
                             (~-app (~-wk [ρ] ⊢Δ n~n′₁) a≡a))
  neuEqTerm {r = [ % , ll ]} (Πᵣ′ rF F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext) neN neN′ n n′ n~n′ =
    let A≡ΠFG = subset* D
    in conv n A≡ΠFG , conv n′ A≡ΠFG
  neuEqTerm {r = [ % , ll ]} (∃ᵣ′ F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext) neN neN′ n n′ n~n′ =
    let A≡ΠFG = subset* D
    in conv n A≡ΠFG , conv n′ A≡ΠFG
  neuEqTerm {ι ¹} (emb {l′ = ι ⁰} l< X) neN n neN′ n:≡:n′ = neuEqTerm X neN n neN′ n:≡:n′
  neuEqTerm {∞} (emb {l′ = ι ⁰} l< X) neN n neN′ n:≡:n′ = neuEqTerm X neN n neN′ n:≡:n′
  neuEqTerm {∞} (emb {l′ = ι ¹} l< X) neN n neN′ n:≡:n′ = neuEqTerm X neN n neN′ n:≡:n′
  neuEqTerm {ι ¹} (emb {l′ = ι ¹} (Nat.s≤s ()) X) 
  neuEqTerm {ι ¹} (emb {l′ = ∞} (Nat.s≤s ()) X) 
  neuEqTerm {∞} (emb {l′ = ∞} (Nat.s≤s (Nat.s≤s ())) X) 
 
