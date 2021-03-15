{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Escape {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties
open import Definition.LogicalRelation

open import Tools.Product
import Tools.PropositionalEquality as PE

import Data.Fin as Fin
import Data.Nat as Nat

-- Reducible types are well-formed.
escape : ∀ {l Γ A r} → Γ ⊩⟨ l ⟩ A ^ r → Γ ⊢ A ^ r
escape (Uᵣ′ _ _ _ _ _ PE.refl [[ ⊢A , ⊢B , D ]]) = ⊢A
escape (ℕᵣ [[ ⊢A , ⊢B , D ]]) = ⊢A
escape (Emptyᵣ [[ ⊢A , ⊢B , D ]]) = ⊢A
escape (ne′ K [[ ⊢A , ⊢B , D ]] neK K≡K) = ⊢A
escape (Πᵣ′ rF F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext) = ⊢A
escape (∃ᵣ′ F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext) = ⊢A
escape {ι ¹} (emb {l′ = ι ⁰} (Nat.s≤s X) A) = escape A
escape {∞} (emb {l′ = ι ⁰} (Nat.s≤s X) A) = escape A
escape {∞} (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) A) = escape A
escape {∞} (emb {l′ = ∞} (Nat.s≤s (Nat.s≤s ())) A)

-- Reducible type equality respect the equality relation.
escapeEq : ∀ {l Γ A B r} → ([A] : Γ ⊩⟨ l ⟩ A ^ r)
            → Γ ⊩⟨ l ⟩ A ≡ B ^ r / [A]
            → Γ ⊢ A ≅ B ^ r
escapeEq (Uᵣ′ _ _ _ _ _ PE.refl [[ ⊢A , ⊢B , D ]]) D′ = ≅-red D D′ Uₙ Uₙ (≅-Urefl (wf ⊢A))
escapeEq (ℕᵣ [[ ⊢A , ⊢B , D ]]) D′ = ≅-red D D′ ℕₙ ℕₙ (≅-univ (≅ₜ-ℕrefl (wf ⊢A)))
escapeEq (Emptyᵣ [[ ⊢A , ⊢B , D ]]) D′ = ≅-red D D′ Emptyₙ Emptyₙ (≅-univ (≅ₜ-Emptyrefl (wf ⊢A)))
escapeEq (ne′ K D neK K≡K) (ne₌ M D′ neM K≡M) =
  ≅-red (red D) (red D′) (ne neK) (ne neM) (~-to-≅ K≡M)
escapeEq (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
             (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ≅-red (red D) D′ Πₙ Πₙ A≡B
escapeEq (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
             (∃₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ≅-red (red D) D′ ∃ₙ ∃ₙ A≡B
escapeEq {ι ¹} (emb {l′ = ι ⁰} (Nat.s≤s X) A) A≡B = escapeEq A A≡B
escapeEq {∞} (emb {l′ = ι ⁰} (Nat.s≤s X) A) A≡B = escapeEq A A≡B
escapeEq {∞} (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) A) A≡B = escapeEq A A≡B
escapeEq {∞} (emb {l′ = ∞} (Nat.s≤s (Nat.s≤s ())) A) A≡B

-- Reducible terms are well-formed.
escapeTerm : ∀ {l Γ A t r} → ([A] : Γ ⊩⟨ l ⟩ A ^ r)
              → Γ ⊩⟨ l ⟩ t ∷ A ^ r / [A]
              → Γ ⊢ t ∷ A ^ r
escapeTerm (Uᵣ′ _ _ _ _ l< PE.refl D) (Uₜ A [[ ⊢t , ⊢u , d ]] typeA A≡A [A] [IdA] IdAExt [castA] castAExt) = conv ⊢t (sym (subset* (red D)))
escapeTerm (ℕᵣ D) (ℕₜ n [[ ⊢t , ⊢u , d ]] t≡t prop) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (Emptyᵣ D) (Emptyₜ (ne ⊢t)) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm {r = [ ! , l ]} (ne′ K D neK K≡K) (neₜ k [[ ⊢t , ⊢u , d ]] nf) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm {r = [ % , l ]} (ne′ K D neK K≡K) (neₜ d) = d
escapeTerm {r = [ ! , l ] } (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
               (f , [[ ⊢t , ⊢u , d ]] , funcF , f≡f , [f] , [f]₁) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm {r = [ % , l ]} (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) ⊢t = conv ⊢t (sym (subset* (red D)))
escapeTerm (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) ⊢t = conv ⊢t (sym (subset* (red D)))
escapeTerm {ι ¹} (emb {l′ = ι ⁰} (Nat.s≤s X) A) t = escapeTerm A t
escapeTerm {∞} (emb {l′ = ι ⁰} (Nat.s≤s X) A) t = escapeTerm A t
escapeTerm {∞} (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) A) t = escapeTerm A t
escapeTerm {∞} (emb {l′ = ∞} (Nat.s≤s (Nat.s≤s ())) A) t

-- Reducible term equality respect the equality relation.
escapeTermEq : ∀ {l Γ A t u r} → ([A] : Γ ⊩⟨ l ⟩ A ^ r)
                → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ r / [A]
                → Γ ⊢ t ≅ u ∷ A ^ r
escapeTermEq (Uᵣ′ _ _ _ _ l< PE.refl D) (Uₜ₌ (Uₜ A d typeA A≡A [t] [IdA] IdAExt [castA] castAext) (Uₜ B d′ typeB B≡B [u] [IdB] IdBExt [castB] castBext) A≡B [A≡B] IdHo castHo) = ≅ₜ-red (red D) (redₜ d) (redₜ d′) Uₙ (typeWhnf typeA) (typeWhnf typeB) A≡B
escapeTermEq (ℕᵣ D) (ℕₜ₌ k k′ d d′ k≡k′ prop) =
  let natK , natK′ = split prop
  in  ≅ₜ-red (red D) (redₜ d) (redₜ d′) ℕₙ
             (naturalWhnf natK) (naturalWhnf natK′) k≡k′
escapeTermEq (Emptyᵣ D) (Emptyₜ₌ (ne ⊢t ⊢u)) =
  ~-to-≅ₜ (~-irrelevance ((conv ⊢t (sym (subset* (red D)))))  ((conv ⊢u (sym (subset* (red D))))))
escapeTermEq {r = [ ! , l ]} (ne′ K D neK K≡K)
                 (neₜ₌ k m d d′ (neNfₜ₌ neT neU t≡u)) =
  ≅ₜ-red (red D) (redₜ d) (redₜ d′) (ne neK) (ne neT) (ne neU)
         (~-to-≅ₜ t≡u)
escapeTermEq {r = [ % , l ]} (ne′ K D neK K≡K)
                 (neₜ₌ d d′) = ~-to-≅ₜ (~-irrelevance d d′)
escapeTermEq {r = [ ! , l ]} (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                 (Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g]) =
  ≅ₜ-red (red D) (redₜ d) (redₜ d′) Πₙ (functionWhnf funcF) (functionWhnf funcG) f≡g
escapeTermEq {r = [ % , l ] } (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) (⊢t , ⊢u) = ~-to-≅ₜ (~-irrelevance ((conv ⊢t (sym (subset* (red D))))) ((conv ⊢u (sym (subset* (red D))))))
escapeTermEq (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (⊢t , ⊢u) = ~-to-≅ₜ (~-irrelevance ((conv ⊢t (sym (subset* (red D))))) ((conv ⊢u (sym (subset* (red D))))))
escapeTermEq {ι ¹} (emb {l′ = ι ⁰} (Nat.s≤s X) A) t≡u = escapeTermEq A t≡u
escapeTermEq {∞} (emb {l′ = ι ⁰} (Nat.s≤s X) A) t≡u = escapeTermEq A t≡u
escapeTermEq {∞} (emb {l′ = ι ¹} (Nat.s≤s (Nat.s≤s X)) A) t≡u = escapeTermEq A t≡u
escapeTermEq {∞} (emb {l′ = ∞} (Nat.s≤s (Nat.s≤s ())) A) t≡u
