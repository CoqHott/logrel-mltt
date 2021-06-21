{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Neutral {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties.Reflexivity
open import Definition.LogicalRelation.Properties.Escape
open import Definition.LogicalRelation.Properties.Symmetry
import Definition.LogicalRelation.Weakening as W

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
neuEq′ {ι ¹} (emb emb< X) = neuEq′ X 
neuEq′ {∞} (emb ∞< X) = neuEq′ X

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
  neuTerm⁰ {r = [ ! , ll ]} (Πᵣ′ rF lF lG lF≤ lG≤ F G D ⊢F ⊢G A≡A [F] [G] G-ext) neN n n~n =
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
  neuTerm⁰ {r = [ % , ll ]} (Πᵣ′ rF lF lG lF≤ lG≤ F G D ⊢F ⊢G A≡A [F] [G] G-ext) neN n n~n = let A≡ΠFG = subset* (red D) in conv n A≡ΠFG
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
  neuEqTerm⁰ {r = [ ! , ll ]} (Πᵣ′ rF lF lG lF≤ lG≤ F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext) neN neN′ n n′ n~n′ =
    let [ΠFG] = Πᵣ′ rF lF lG lF≤ lG≤ F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext
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
  neuEqTerm⁰ {r = [ % , ll ]} (Πᵣ′ rF lF lG lF≤ lG≤ F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext) neN neN′ n n′ n~n′ =
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
  neuTerm {ι ¹} (Uᵣ′ A .(next ⁰) r ⁰ l< PE.refl [[ ⊢A , ⊢U , D ]]) neN n n~n = 
    let n' = (conv n (subset* D))
        n~n' = ~-conv  n~n (subset* D)
        [n] = neu {l = ι ¹} neN (univ n') n~n'
    in Uₜ _ (idRedTerm:*: n') (ne neN) (~-to-≅ₜ n~n')
            (λ {ρ} [ρ] ⊢Δ → let n'ρ = wkTerm [ρ] ⊢Δ n'
                                n~n'ρ = ~-wk [ρ] ⊢Δ n~n'
                                [nρ] = neu (wkNeutral ρ neN) (univ n'ρ) n~n'ρ
                            in [nρ])             
  neuTerm {∞} (Uᵣ′ A .(next ¹) r ¹ l< PE.refl [[ ⊢A , ⊢U , D ]]) neN n n~n =
    let n' = (conv n (subset* D))
        n~n' = ~-conv  n~n (subset* D)
        [n] = neu {l = ∞} neN (univ n') n~n'
    in Uₜ _ (idRedTerm:*: n') (ne neN) (~-to-≅ₜ n~n')
            (λ {ρ} [ρ] ⊢Δ → let n'ρ = wkTerm [ρ] ⊢Δ n'
                                n~n'ρ = ~-wk [ρ] ⊢Δ n~n'
                                [nρ] = neu (wkNeutral ρ neN) (univ n'ρ) n~n'ρ
                            in [nρ])
  neuTerm (ℕᵣ [[ ⊢A , ⊢B , D ]]) neN n n~n =
    let A≡ℕ  = subset* D
        n~n′ = ~-conv n~n A≡ℕ
        n≡n  = ~-to-≅ₜ n~n′
    in  ℕₜ _ (idRedTerm:*: (conv n A≡ℕ)) n≡n (ne (neNfₜ neN (conv n A≡ℕ) n~n′))
  neuTerm {r = [ ! , ll ]} (ne′ K [[ ⊢A , ⊢B , D ]] neK K≡K) neN n n~n =
    let A≡K = subset* D
    in  neₜ _ (idRedTerm:*: (conv n A≡K)) (neNfₜ neN (conv n A≡K)
            (~-conv n~n A≡K))
  neuTerm {r = [ ! , ll ]} (Πᵣ′ rF lF lG lF≤ lG≤ F G D ⊢F ⊢G A≡A [F] [G] G-ext) neN n n~n =
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
  neuTerm (Emptyᵣ [[ ⊢A , ⊢B , D ]]) neN n n~n =
    let A≡ℕ  = subset* D
    in Emptyₜ (ne (conv n A≡ℕ))
  neuTerm {r = [ % , ll ]} (ne′ K [[ ⊢A , ⊢B , D ]] neK K≡K) neN n n~n =
    let A≡K = subset* D
    in  neₜ n
  neuTerm {r = [ % , ll ]} (Πᵣ′ rF lF lG lF≤ lG≤ F G D ⊢F ⊢G A≡A [F] [G] G-ext) neN n n~n = let A≡ΠFG = subset* (red D) in conv n A≡ΠFG
  neuTerm {r = [ % , ll ]} (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) neN n n~n = let A≡ΠFG = subset* (red D) in conv n A≡ΠFG
  neuTerm {ι ¹} (emb l< X) neN n = neuTerm X neN n
  neuTerm {∞} (emb l< X) neN n = neuTerm X neN n

  -- Neutrally equal terms are of reducible equality.
  neuEqTerm : ∀ {l Γ A n n′ r} ([A] : Γ ⊩⟨ l ⟩ A ^ r)
              (neN : Neutral n) (neN′ : Neutral n′)
            → Γ ⊢ n  ∷ A ^ r
            → Γ ⊢ n′ ∷ A ^ r
            → Γ ⊢ n ~ n′ ∷ A ^ r
            → Γ ⊩⟨ l ⟩ n ≡ n′ ∷ A ^ r / [A]
  neuEqTerm {ι ¹} (Uᵣ′ A _ r ⁰ l< PE.refl D) neN neN′ n n′ n~n' =
    let n~n = ~-trans n~n' (~-sym n~n')
        n'~n' = ~-trans (~-sym n~n') n~n' 
        [[n]]   = neuTerm (Uᵣ (Uᵣ r ⁰ l< PE.refl D)) neN n n~n
        [[n']]  = neuTerm (Uᵣ (Uᵣ r ⁰ l< PE.refl D)) neN′ n′ n'~n'
        n' = conv n (subset* (red D))
        n′' = conv n′ (subset* (red D))
        n~n'U = ~-conv n~n' (subset* (red D))
        [n]  = neu {l = ι ¹} neN  (univ n') (~-conv n~n (subset* (red D)))
        [n′] = neu {l = ι ¹} neN′ (univ n′') (~-conv n'~n' (subset* (red D)))
    in Uₜ₌ [[n]] [[n']] (~-to-≅ₜ n~n'U)
           (λ [ρ] ⊢Δ → W.wkEq [ρ] ⊢Δ [n] ((neuEq [n] neN neN′ (univ n') (univ n′') n~n'U)))
  neuEqTerm {∞} (Uᵣ′ A _ r ¹ l< PE.refl D) neN neN′ n n′ n~n' =
    let n~n = ~-trans n~n' (~-sym n~n')
        n'~n' = ~-trans (~-sym n~n') n~n' 
        [[n]]   = neuTerm (Uᵣ (Uᵣ r ¹ l< PE.refl D)) neN n n~n
        [[n']]  = neuTerm (Uᵣ (Uᵣ r ¹ l< PE.refl D)) neN′ n′ n'~n'
        n' = conv n (subset* (red D))
        n′' = conv n′ (subset* (red D))
        n~n'U = ~-conv n~n' (subset* (red D))
        [n]  = neu {l = ∞} neN  (univ n') (~-conv n~n (subset* (red D)))
        [n′] = neu {l = ∞} neN′ (univ n′') (~-conv n'~n' (subset* (red D)))
    in Uₜ₌ [[n]] [[n']] (~-to-≅ₜ n~n'U)
           (λ [ρ] ⊢Δ → W.wkEq [ρ] ⊢Δ [n] ((neuEq [n] neN neN′ (univ n') (univ n′') n~n'U)))
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
  neuEqTerm {r = [ ! , ll ]} (Πᵣ′ rF lF lG lF≤ lG≤ F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext) neN neN′ n n′ n~n′ =
    let [ΠFG] = Πᵣ′ rF lF lG lF≤ lG≤ F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext
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
  neuEqTerm {r = [ % , ll ]} (Πᵣ′ rF lF lG lF≤ lG≤ F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext) neN neN′ n n′ n~n′ =
    let A≡ΠFG = subset* D
    in conv n A≡ΠFG , conv n′ A≡ΠFG
  neuEqTerm {r = [ % , ll ]} (∃ᵣ′ F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext) neN neN′ n n′ n~n′ =
    let A≡ΠFG = subset* D
    in conv n A≡ΠFG , conv n′ A≡ΠFG
  neuEqTerm {ι ¹} (emb l< X) neN n neN′ n:≡:n′ = neuEqTerm X neN n neN′ n:≡:n′
  neuEqTerm {∞} (emb l< X) neN n neN′ n:≡:n′ = neuEqTerm X neN n neN′ n:≡:n′
 

-- Neutral reflexive types are reducible.
neu:⇒*: : ∀ {l Γ A K r ll} (neK : Neutral K)
    → Γ ⊢ A :⇒*: K ^ [ r , ι ll ]
    → Γ ⊢ K ~ K ∷ Univ r ll ^ [ ! , next ll ]
    → Γ ⊩⟨ l ⟩ A ^ [ r , ι ll ]
neu:⇒*: neK D K~K = ne′ _ D neK K~K

  -- Helper function for reducible neutral equality of a specific type of derivation.
neuEq:⇒*:′ : ∀ {l Γ A B K L r ll} ([A] : Γ ⊩⟨ l ⟩ne A ^[ r , ll ])
         (neK : Neutral K)
         (neL : Neutral L)
       → Γ ⊢ A :⇒*: K ^ [ r , ι ll ]
       → Γ ⊢ B :⇒*: L ^ [ r , ι ll ]
       → Γ ⊢ K ~ L ∷ Univ r ll ^ [ ! , next ll ]
       → Γ ⊩⟨ l ⟩ A ≡ B ^ [ r , ι ll ] / ne-intr [A]
neuEq:⇒*:′ (noemb (ne A' [[ ⊢A , ⊢B , D ]] neA A≡A)) neK neL [[ ⊢A' , ⊢K , D' ]] [B] A~B = 
  let A≡K = whrDet* (D , ne neA) (D' , ne neK) -- (ne neA)
  in ne₌ _ [B] neL (PE.subst (λ x → _ ⊢ x ~ _ ∷ _ ^ _) (PE.sym A≡K) A~B)
neuEq:⇒*:′ {ι ¹} (emb emb< X) = neuEq:⇒*:′ X 
neuEq:⇒*:′ {∞} (emb ∞< X) = neuEq:⇒*:′ X

-- neuEq′ x neB A:≡:B

-- Neutrally equal types are of reducible equality.
neuEq:⇒*: : ∀ {l Γ A B K L r ll} ([A] : Γ ⊩⟨ l ⟩ A ^ [ r , ι ll ])
         (neK : Neutral K)
         (neL : Neutral L)
       → Γ ⊢ A :⇒*: K ^ [ r , ι ll ]
       → Γ ⊢ B :⇒*: L ^ [ r , ι ll ]
       → Γ ⊢ K ~ L ∷ Univ r ll ^ [ ! , next ll ]
      → Γ ⊩⟨ l ⟩ A ≡ B ^ [ r , ι ll ] / [A]
neuEq:⇒*: [A] neK neL [[ ⊢A , ⊢K , D ]] B A~B =
  let ne-intrA = ne-elim′ D neK [A] PE.refl
  in irrelevanceEq (ne-intr ne-intrA)
                [A]
                (neuEq:⇒*:′ ne-intrA neK neL [[ ⊢A , ⊢K , D ]] B A~B)

app:⇒*: : ∀ {Γ a t u A B rA lA lB l}
          (⊢a : Γ ⊢ a ∷ A ^ [ rA , ι lA ])
          (D : Γ ⊢ t :⇒*: u ∷ (Π A ^ rA ° lA ▹ B ° lB) ^ ι l)
        → Γ ⊢ t ∘ a :⇒*: u ∘ a ∷ B [ a ] ^ ι lB
app:⇒*: ⊢a [[ ⊢t , ⊢u , D ]] = [[ ⊢t ∘ⱼ ⊢a , ⊢u ∘ⱼ ⊢a , appRed* ⊢a D ]]  


mutual 
  neuTerm:⇒*:⁰ : ∀ {Γ A ll t n} ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ ! , ll ]) (neN : Neutral n)
          → Γ ⊢ t :⇒*: n ∷ A ^ ll
          → Γ ⊢ n ~ n ∷ A ^ [ ! , ll ]
          → Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ ! , ll ] / [A]

  neuTerm:⇒*:⁰ (ℕᵣ [[ ⊢A , ⊢B , D ]]) neN [[ ⊢t , n , D' ]] n~n =
    let A≡ℕ  = subset* D
        n~n′ = ~-conv n~n A≡ℕ
        n≡n  = ~-to-≅ₜ n~n′
    in  ℕₜ _ (conv:⇒*: [[ ⊢t , n , D' ]] A≡ℕ) n≡n (ne (neNfₜ neN (conv n A≡ℕ) n~n′))
  neuTerm:⇒*:⁰ (ne′ K [[ ⊢A , ⊢B , D ]] neK K≡K) neN [[ ⊢t , n , D' ]] n~n =
    let A≡K = subset* D
    in  neₜ _ (conv:⇒*: [[ ⊢t , n , D' ]] A≡K) (neNfₜ neN (conv n A≡K)
            (~-conv n~n A≡K))
  neuTerm:⇒*:⁰ (Πᵣ′ rF lF lG lF≤ lG≤ F G D ⊢F ⊢G A≡A [F] [G] G-ext) neN [[ ⊢t , n , D' ]] n~n =
    let A≡ΠFG = subset* (red D)
    in  Πₜ _ (conv:⇒*: [[ ⊢t , n , D' ]] A≡ΠFG) (ne neN) (~-to-≅ₜ (~-conv n~n A≡ΠFG))
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
              in  neuEqTerm⁰ ([G] [ρ] ⊢Δ [a]) neN∘a neN∘b (ρn ∘ⱼ a) (conv (ρn ∘ⱼ b) (≅-eq G[a]≡G[b])) 
                             ((~-app (~-wk [ρ] ⊢Δ (~-conv n~n A≡ΠFG)) a≡b)))
           (λ {ρ} [ρ] ⊢Δ [a] →
              let ρA≡ρΠFG = wkEq [ρ] ⊢Δ (subset* (red D))
                  a = escapeTerm ([F] [ρ] ⊢Δ) [a]
                  a≡a = escapeTermEq ([F] [ρ] ⊢Δ) (reflEqTerm ([F] [ρ] ⊢Δ) [a])
              in  neuTerm ([G] [ρ] ⊢Δ [a]) (∘ₙ (wkNeutral ρ neN))
                          (conv (wkTerm [ρ] ⊢Δ n) ρA≡ρΠFG ∘ⱼ a)
                          (~-app (~-wk [ρ] ⊢Δ (~-conv n~n A≡ΠFG)) a≡a))

  neuEqTerm:⇒*:⁰ : ∀ {Γ A n n′ t u ll} ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ ! , ll ])
              (neN : Neutral n) (neN′ : Neutral n′)
            → Γ ⊢ t :⇒*: n ∷ A ^ ll
            → Γ ⊢ u :⇒*: n′ ∷ A ^ ll
            → Γ ⊢ n ~ n′ ∷ A ^ [ ! , ll ]
            → Γ ⊩⟨ ι ⁰ ⟩ t ≡ u ∷ A ^ [ ! , ll ] / [A]

  neuEqTerm:⇒*:⁰ (ℕᵣ [[ ⊢A , ⊢B , D ]]) neN neN′ [[ ⊢t , n , D' ]] [[ ⊢u , n′ , D′ ]] n~n′ =
    let A≡ℕ = subset* D
        n~n′₁ = ~-conv n~n′ A≡ℕ
        n≡n′ = ~-to-≅ₜ n~n′₁
    in  ℕₜ₌ _ _ (conv:⇒*: [[ ⊢t , n , D' ]] A≡ℕ) (conv:⇒*: [[ ⊢u , n′ , D′ ]] A≡ℕ)
            n≡n′ (ne (neNfₜ₌ neN neN′ n~n′₁))
  neuEqTerm:⇒*:⁰ (ne (ne K [[ ⊢A , ⊢B , D ]] neK K≡K)) neN neN′ [[ ⊢t , n , D' ]] [[ ⊢u , n′ , D′ ]] n~n′ =
    let A≡K = subset* D
    in  neₜ₌ _ _ (conv:⇒*: [[ ⊢t , n , D' ]] A≡K) (conv:⇒*: [[ ⊢u , n′ , D′ ]] A≡K)
             (neNfₜ₌ neN neN′ (~-conv n~n′ A≡K))
  neuEqTerm:⇒*:⁰ (Πᵣ′ rF lF lG lF≤ lG≤ F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext) neN neN′ [[ ⊢t , n , D' ]] [[ ⊢u , n′ , D′ ]] n~n′ =
    let [ΠFG] = Πᵣ′ rF lF lG lF≤ lG≤ F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext
        A≡ΠFG = subset* D
        n~n′₁ = ~-conv n~n′ A≡ΠFG
        n≡n′ = ~-to-≅ₜ n~n′₁
        n~n = ~-trans n~n′ (~-sym n~n′)
        n′~n′ = ~-trans (~-sym n~n′) n~n′
    in  Πₜ₌ _ _ (conv:⇒*: [[ ⊢t , n , D' ]] A≡ΠFG) (conv:⇒*: [[ ⊢u , n′ , D′ ]] A≡ΠFG)
            (ne neN) (ne neN′) n≡n′
            (neuTerm:⇒*:⁰ [ΠFG] neN [[ ⊢t , n , D' ]] n~n) (neuTerm:⇒*:⁰ [ΠFG] neN′ [[ ⊢u , n′ , D′ ]] n′~n′)
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
                             (~-app (~-wk [ρ] ⊢Δ n~n′₁) a≡a) )


mutual
  -- Neutral reflexive terms are reducible.
  neuTerm:⇒*: : ∀ {l Γ A ll t n} ([A] : Γ ⊩⟨ l ⟩ A ^ [ ! , ll ]) (neN : Neutral n)
          → Γ ⊢ t :⇒*: n ∷ A ^ ll
          → Γ ⊢ n ~ n ∷ A ^ [ ! , ll ]
          → Γ ⊩⟨ l ⟩ t ∷ A ^ [ ! , ll ] / [A]
  neuTerm:⇒*: {ι ¹} (Uᵣ′ A .(next ⁰) r ⁰ l< PE.refl [[ ⊢A , ⊢U , D ]]) neN [[ ⊢t , n , D' ]] n~n = 
    let D'' = conv:⇒*: [[ ⊢t , n , D' ]] (subset* D)
        n~n' = ~-conv  n~n (subset* D)
    in Uₜ _ (conv:⇒*: [[ ⊢t , n , D' ]] (subset* D))
            (ne neN) (~-to-≅ₜ n~n')
            (λ {ρ} [ρ] ⊢Δ → let ρD' = wkRed:*:Term [ρ] ⊢Δ D''
                                n~n'ρ = ~-wk [ρ] ⊢Δ n~n'            
                            in neu:⇒*: (wkNeutral ρ neN) (univ:⇒*: ρD') n~n'ρ)
  neuTerm:⇒*: {∞} (Uᵣ′ A .(next ¹) r ¹ l< PE.refl [[ ⊢A , ⊢U , D ]]) neN  [[ ⊢t , n , D' ]] n~n =
    let D'' = conv:⇒*: [[ ⊢t , n , D' ]] (subset* D)
        n~n' = ~-conv  n~n (subset* D)
    in Uₜ _ (conv:⇒*: [[ ⊢t , n , D' ]] (subset* D))
            (ne neN) (~-to-≅ₜ n~n')
            (λ {ρ} [ρ] ⊢Δ → let ρD' = wkRed:*:Term [ρ] ⊢Δ D''
                                n~n'ρ = ~-wk [ρ] ⊢Δ n~n'            
                            in neu:⇒*: (wkNeutral ρ neN) (univ:⇒*: ρD') n~n'ρ)
  neuTerm:⇒*: (ℕᵣ [[ ⊢A , ⊢B , D ]]) neN [[ ⊢t , n , D' ]] n~n =
    let A≡ℕ  = subset* D
        n~n′ = ~-conv n~n A≡ℕ
        n≡n  = ~-to-≅ₜ n~n′
    in  ℕₜ _ (conv:⇒*: [[ ⊢t , n , D' ]] A≡ℕ) n≡n (ne (neNfₜ neN (conv n A≡ℕ) n~n′))
  neuTerm:⇒*: (ne′ K [[ ⊢A , ⊢B , D ]] neK K≡K) neN [[ ⊢t , n , D' ]] n~n =
    let A≡K = subset* D
    in  neₜ _ (conv:⇒*: [[ ⊢t , n , D' ]] A≡K) (neNfₜ neN (conv n A≡K)
            (~-conv n~n A≡K))
  neuTerm:⇒*: (Πᵣ′ rF lF lG lF≤ lG≤ F G D ⊢F ⊢G A≡A [F] [G] G-ext) neN [[ ⊢t , n , D' ]] n~n =
    let A≡ΠFG = subset* (red D)
    in  Πₜ _ (conv:⇒*: [[ ⊢t , n , D' ]] A≡ΠFG) (ne neN) (~-to-≅ₜ (~-conv n~n A≡ΠFG))
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
              in  neuEqTerm ([G] [ρ] ⊢Δ [a]) neN∘a neN∘b (ρn ∘ⱼ a) (conv (ρn ∘ⱼ b) (≅-eq G[a]≡G[b])) 
                            ((~-app (~-wk [ρ] ⊢Δ (~-conv n~n A≡ΠFG)) a≡b)))
           (λ {ρ} [ρ] ⊢Δ [a] →
              let ρA≡ρΠFG = wkEq [ρ] ⊢Δ (subset* (red D))
                  a = escapeTerm ([F] [ρ] ⊢Δ) [a]
                  a≡a = escapeTermEq ([F] [ρ] ⊢Δ) (reflEqTerm ([F] [ρ] ⊢Δ) [a])
              in  neuTerm ([G] [ρ] ⊢Δ [a]) (∘ₙ (wkNeutral ρ neN))
                          (conv (wkTerm [ρ] ⊢Δ n) ρA≡ρΠFG ∘ⱼ a)
                          (~-app (~-wk [ρ] ⊢Δ (~-conv n~n A≡ΠFG)) a≡a))
  neuTerm:⇒*: {ι ¹} (emb l< X) neN n n:≡:n′ = neuTerm:⇒*: X neN n n:≡:n′
  neuTerm:⇒*: {∞} (emb l< X) neN n n:≡:n′ = neuTerm:⇒*: X neN n n:≡:n′

  -- Neutrally equal terms are of reducible equality.
  neuEqTerm:⇒*: : ∀ {l Γ A t u n n′ ll} ([A] : Γ ⊩⟨ l ⟩ A ^ [ ! , ll ])
              (neN : Neutral n) (neN′ : Neutral n′)
            → Γ ⊢ t :⇒*: n ∷ A ^ ll
            → Γ ⊢ u :⇒*: n′ ∷ A ^ ll
            → Γ ⊢ n ~ n′ ∷ A ^ [ ! , ll ]
            → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ [ ! , ll ] / [A]
  neuEqTerm:⇒*: {ι ¹} (Uᵣ′ A _ r ⁰ l< PE.refl [[ ⊢A , ⊢U , D ]]) neN neN′  [[ ⊢t , n , D' ]] [[ ⊢u , n′ , D′ ]] n~n' =
    let n~n = ~-trans n~n' (~-sym n~n')
        n'~n' = ~-trans (~-sym n~n') n~n' 
        n~n'U = ~-conv n~n' (subset* D)
        n~nU = ~-conv n~n (subset* D)
        [t] = neuTerm:⇒*: (Uᵣ′ A _ r ⁰ l< PE.refl [[ ⊢A , ⊢U , D ]]) neN [[ ⊢t , n , D' ]] n~n
        Uₜ _ _ _ _ [Δt] = [t]
        D'' = conv:⇒*: [[ ⊢t , n , D' ]] (subset* D)
        D′' = conv:⇒*: [[ ⊢u , n′ , D′ ]] (subset* D)
    in Uₜ₌ [t]
           (neuTerm:⇒*: (Uᵣ′ A _ r ⁰ l< PE.refl [[ ⊢A , ⊢U , D ]]) neN′ [[ ⊢u , n′ , D′ ]] n'~n')
           (~-to-≅ₜ n~n'U)
           λ {ρ} [ρ] ⊢Δ → let ρD' = wkRed:*:Term [ρ] ⊢Δ D''
                              ρD′ = wkRed:*:Term [ρ] ⊢Δ D′'
                              n~nUρ = ~-wk [ρ] ⊢Δ n~nU
                              n~n'Uρ = ~-wk [ρ] ⊢Δ n~n'U
                          in neuEq:⇒*: {l = ι ¹} (neu:⇒*: (wkNeutral ρ neN) (univ:⇒*: ρD') n~nUρ) (wkNeutral ρ neN) (wkNeutral ρ neN′)
                                       (univ:⇒*: ρD') (univ:⇒*: ρD′) n~n'Uρ
  neuEqTerm:⇒*: {∞} (Uᵣ′ A _ r ¹ l< PE.refl [[ ⊢A , ⊢U , D ]]) neN neN′  [[ ⊢t , n , D' ]] [[ ⊢u , n′ , D′ ]] n~n' =
    let n~n = ~-trans n~n' (~-sym n~n')
        n'~n' = ~-trans (~-sym n~n') n~n' 
        n~n'U = ~-conv n~n' (subset* D)
        n~nU = ~-conv n~n (subset* D)
        [t] = neuTerm:⇒*: (Uᵣ′ A _ r ¹ l< PE.refl [[ ⊢A , ⊢U , D ]]) neN [[ ⊢t , n , D' ]] n~n
        Uₜ _ _ _ _ [Δt] = [t]
        D'' = conv:⇒*: [[ ⊢t , n , D' ]] (subset* D)
        D′' = conv:⇒*: [[ ⊢u , n′ , D′ ]] (subset* D)
    in Uₜ₌ [t]
           (neuTerm:⇒*: (Uᵣ′ A _ r ¹ l< PE.refl [[ ⊢A , ⊢U , D ]]) neN′ [[ ⊢u , n′ , D′ ]] n'~n')
           (~-to-≅ₜ n~n'U)
           λ {ρ} [ρ] ⊢Δ → let ρD' = wkRed:*:Term [ρ] ⊢Δ D''
                              ρD′ = wkRed:*:Term [ρ] ⊢Δ D′'
                              n~nUρ = ~-wk [ρ] ⊢Δ n~nU
                              n~n'Uρ = ~-wk [ρ] ⊢Δ n~n'U
                          in neuEq:⇒*: {l = ∞} (neu:⇒*: (wkNeutral ρ neN) (univ:⇒*: ρD') n~nUρ) (wkNeutral ρ neN) (wkNeutral ρ neN′)
                                       (univ:⇒*: ρD') (univ:⇒*: ρD′) n~n'Uρ
  neuEqTerm:⇒*: (ℕᵣ [[ ⊢A , ⊢B , D ]]) neN neN′ [[ ⊢t , n , D' ]] [[ ⊢u , n′ , D′ ]] n~n′ =
    let A≡ℕ = subset* D
        n~n′₁ = ~-conv n~n′ A≡ℕ
        n≡n′ = ~-to-≅ₜ n~n′₁
    in  ℕₜ₌ _ _ (conv:⇒*: [[ ⊢t , n , D' ]] A≡ℕ) (conv:⇒*: [[ ⊢u , n′ , D′ ]] A≡ℕ)
            n≡n′ (ne (neNfₜ₌ neN neN′ n~n′₁))
  neuEqTerm:⇒*: (ne (ne K [[ ⊢A , ⊢B , D ]] neK K≡K)) neN neN′ [[ ⊢t , n , D' ]] [[ ⊢u , n′ , D′ ]] n~n′ =
    let A≡K = subset* D
    in  neₜ₌ _ _ (conv:⇒*: [[ ⊢t , n , D' ]] A≡K) (conv:⇒*: [[ ⊢u , n′ , D′ ]] A≡K)
             (neNfₜ₌ neN neN′ (~-conv n~n′ A≡K))
  neuEqTerm:⇒*: (Πᵣ′ rF lF lG lF≤ lG≤ F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext) neN neN′ [[ ⊢t , n , D' ]] [[ ⊢u , n′ , D′ ]] n~n′ =
    let [ΠFG] = Πᵣ′ rF lF lG lF≤ lG≤ F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext
        A≡ΠFG = subset* D
        n~n′₁ = ~-conv n~n′ A≡ΠFG
        n≡n′ = ~-to-≅ₜ n~n′₁
        n~n = ~-trans n~n′ (~-sym n~n′)
        n′~n′ = ~-trans (~-sym n~n′) n~n′
    in  Πₜ₌ _ _ (conv:⇒*: [[ ⊢t , n , D' ]] A≡ΠFG) (conv:⇒*: [[ ⊢u , n′ , D′ ]] A≡ΠFG)
            (ne neN) (ne neN′) n≡n′
            (neuTerm:⇒*: [ΠFG] neN [[ ⊢t , n , D' ]] n~n) (neuTerm:⇒*: [ΠFG] neN′ [[ ⊢u , n′ , D′ ]] n′~n′)
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
                             (~-app (~-wk [ρ] ⊢Δ n~n′₁) a≡a) )
  neuEqTerm:⇒*: {ι ¹} (emb l< X) neN n neN′ n:≡:n′ = neuEqTerm:⇒*: X neN n neN′ n:≡:n′
  neuEqTerm:⇒*: {∞} (emb l< X) neN n neN′ n:≡:n′ = neuEqTerm:⇒*: X neN n neN′ n:≡:n′
