{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Successor {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.ShapeView

open import Tools.Product

import Data.Fin as Fin
import Data.Nat as Nat


-- Helper function for successors for specific reducible derivations.
sucTerm′ : ∀ {l Γ n}
           ([ℕ] : Γ ⊩⟨ l ⟩ℕ ℕ)
         → Γ ⊩⟨ l ⟩ n ∷ ℕ ^ [ ! , ι ⁰ ] / ℕ-intr [ℕ]
         → Γ ⊩⟨ l ⟩ suc n ∷ ℕ ^ [ ! , ι ⁰ ] / ℕ-intr [ℕ]
sucTerm′ (noemb D) (ℕₜ n [[ ⊢t , ⊢u , d ]] n≡n prop) =
  let natN = naturalNf (natural prop)
  in  ℕₜ _ [[ sucⱼ ⊢t , sucⱼ ⊢u , suc* d ]]
         (≅-suc-cong n≡n)
         (sucᵣ prop)
sucTerm′ (emb emb< x) [n] = sucTerm′ x [n]
sucTerm′ (emb ∞< x) [n] = sucTerm′ x [n]

-- Reducible natural numbers can be used to construct reducible successors.
sucTerm : ∀ {l Γ n} ([ℕ] : Γ ⊩⟨ l ⟩ ℕ ^ [ ! , ι ⁰ ])
        → Γ ⊩⟨ l ⟩ n ∷ ℕ ^ [ ! , ι ⁰ ] / [ℕ]
        → Γ ⊩⟨ l ⟩ suc n ∷ ℕ ^ [ ! , ι ⁰ ] / [ℕ]
sucTerm [ℕ] [n] =
  let [n]′ = irrelevanceTerm [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [n]
  in  irrelevanceTerm (ℕ-intr (ℕ-elim [ℕ]))
                      [ℕ]
                      (sucTerm′ (ℕ-elim [ℕ]) [n]′)

-- Helper function for successor equality for specific reducible derivations.
sucEqTerm′ : ∀ {l Γ n n′}
             ([ℕ] : Γ ⊩⟨ l ⟩ℕ ℕ)
           → Γ ⊩⟨ l ⟩ n ≡ n′ ∷ ℕ ^ [ ! , ι ⁰ ] / ℕ-intr [ℕ]
           → Γ ⊩⟨ l ⟩ suc n ≡ suc n′ ∷ ℕ ^ [ ! , ι ⁰ ] / ℕ-intr [ℕ]
sucEqTerm′ (noemb D) (ℕₜ₌ k k′ d d′ t≡u prop) =
  let natK , natK′ = split prop
  in  ℕₜ₌ _ _  (suc'* d) (suc'* d′) (≅-suc-cong t≡u) (sucᵣ prop) 
sucEqTerm′ (emb emb< x) [n≡n′] = sucEqTerm′ x [n≡n′]
sucEqTerm′ (emb ∞< x) [n≡n′] = sucEqTerm′ x [n≡n′]

-- Reducible natural number equality can be used to construct reducible equality
-- of the successors of the numbers.
sucEqTerm : ∀ {l Γ n n′} ([ℕ] : Γ ⊩⟨ l ⟩ ℕ ^ [ ! , ι ⁰ ] )
          → Γ ⊩⟨ l ⟩ n ≡ n′ ∷ ℕ ^ [ ! , ι ⁰ ] / [ℕ]
          → Γ ⊩⟨ l ⟩ suc n ≡ suc n′ ∷ ℕ ^ [ ! , ι ⁰ ] / [ℕ]
sucEqTerm [ℕ] [n≡n′] =
  let [n≡n′]′ = irrelevanceEqTerm [ℕ] (ℕ-intr (ℕ-elim [ℕ])) [n≡n′]
  in  irrelevanceEqTerm (ℕ-intr (ℕ-elim [ℕ])) [ℕ]
                        (sucEqTerm′ (ℕ-elim [ℕ]) [n≡n′]′)
