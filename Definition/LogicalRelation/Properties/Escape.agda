{-# OPTIONS --without-K  #-}

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


-- Reducible types are well-formed.
escape : ∀ {l Γ A s} → Γ ⊩⟨ l ⟩ A ⦂ s → Γ ⊢ A ⦂ s
escape (Uᵣ′ _ l′ l< ⊢Γ) = Uⱼ ⊢Γ
escape (ℕᵣ [ ⊢A , ⊢B , D ]) = ⊢A
escape (Emptyᵣ [ ⊢A , ⊢B , D ]) = ⊢A
escape (ne′ K [ ⊢A , ⊢B , D ] neK K≡K) = ⊢A
escape (Πᵣ′ sF F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) = ⊢A
escape (cstrᵣ′ K KcodU a [ ⊢A , ⊢B , D ] ⊢a A≡A [domK] [a] [Yi]) = ⊢A
escape (emb 0<1 A) = escape A

-- Reducible type equality respect the equality relation.
escapeEq : ∀ {l Γ A B s} → ([A] : Γ ⊩⟨ l ⟩ A ⦂ s)
            → Γ ⊩⟨ l ⟩ A ≡ B ⦂ s / [A]
            → Γ ⊢ A ≅ B ⦂ s
escapeEq (Uᵣ′ _ l′ l< ⊢Γ) PE.refl = ≅-Urefl ⊢Γ
escapeEq (ℕᵣ [ ⊢A , ⊢B , D ]) D′ = ≅-red D D′ ℕₙ ℕₙ (≅-ℕrefl (wf ⊢A))
escapeEq (Emptyᵣ [ ⊢A , ⊢B , D ]) D′ = ≅-red D D′ Emptyₙ Emptyₙ (≅-Emptyrefl (wf ⊢A))
escapeEq (ne′ K D neK K≡K) (ne₌ M D′ neM K≡M) =
  ≅-red (red D) (red D′) (ne neK) (ne neM) (~-to-≅ K≡M)
escapeEq (Πᵣ′ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
             (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  ≅-red (red D) D′ Πₙ Πₙ A≡B
escapeEq (cstrᵣ′ K KcodU a D ⊢a A≡A [domK] [a] [Yi]) (cstr₌ a' D' A≡B [a≡a']) =
  ≅-red (red D) (red D') cstrₙ cstrₙ (≅-cstr-cong KcodU (wfTerm ⊢a) A≡B)
escapeEq (emb 0<1 A) A≡B = escapeEq A A≡B

-- Reducible terms are well-formed.
escapeTerm : ∀ {l Γ A t s} → ([A] : Γ ⊩⟨ l ⟩ A ⦂ s)
              → Γ ⊩⟨ l ⟩ t ∷ A ⦂ s / [A]
              → Γ ⊢ t ∷ A ⦂ s
escapeTerm (Uᵣ′ _ l′ l< ⊢Γ) (Uₜ A [ ⊢t , ⊢u , d ] typeA A≡A [A]) = ⊢t
escapeTerm (ℕᵣ D) (ℕₜ n [ ⊢t , ⊢u , d ] t≡t prop) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (Emptyᵣ D) (Emptyₜ e [ ⊢t , ⊢u , d ] t≡t prop) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (ne′ K D neK K≡K) (neₜ k [ ⊢t , ⊢u , d ] nf) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (Πᵣ′ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
               (f , [ ⊢t , ⊢u , d ] , funcF , f≡f , [f] , [f]₁) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (cstrᵣ′ K KcodU a D ⊢a A≡A [domK] [a] [Yi]) (cstrₜ k [ ⊢t , ⊢u , d ] k≡k [k]) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (emb 0<1 A) t = escapeTerm A t

-- Reducible term equality respect the equality relation.
escapeTermEq : ∀ {l Γ A t u s} → ([A] : Γ ⊩⟨ l ⟩ A ⦂ s)
                → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ⦂ s / [A]
                → Γ ⊢ t ≅ u ∷ A ⦂ s
escapeTermEq (Uᵣ′ s' l′ l< ⊢Γ) (Uₜ₌ A B d d′ typeA typeB A≡B [A] [B] [A≡B]) =
  ≅ₜ-red (id (Uⱼ ⊢Γ)) (redₜ d) (redₜ d′) Uₙ (typeWhnf typeA) (typeWhnf typeB) A≡B
escapeTermEq (ℕᵣ D) (ℕₜ₌ k k′ d d′ k≡k′ prop) =
  let natK , natK′ = split prop
  in  ≅ₜ-red (red D) (redₜ d) (redₜ d′) ℕₙ
             (naturalWhnf natK) (naturalWhnf natK′) k≡k′
escapeTermEq (Emptyᵣ D) (Emptyₜ₌ k k′ d d′ k≡k′ prop) =
  let natK , natK′ = esplit prop
  in  ≅ₜ-red (red D) (redₜ d) (redₜ d′) Emptyₙ
             (ne natK) (ne natK′) k≡k′
escapeTermEq (ne′ K D neK K≡K)
                 (neₜ₌ k m d d′ (neNfₜ₌ neT neU t≡u)) =
  ≅ₜ-red (red D) (redₜ d) (redₜ d′) (ne neK) (ne neT) (ne neU)
         (~-to-≅ₜ t≡u)
escapeTermEq (Πᵣ′ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                 (Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g]) =
  ≅ₜ-red (red D) (redₜ d) (redₜ d′) Πₙ (functionWhnf funcF) (functionWhnf funcG) f≡g
escapeTermEq (cstrᵣ′ K KcodU a D ⊢a A≡A [domK] [a] [Yi]) (cstrₜ₌ k k' d d' k≡k' [k] [k'] [k≡k']) =
  ≅ₜ-red (red D) (redₜ d) (redₜ d') cstrₙ ([Cstr]-prop-left-Whnf [k≡k']) ([Cstr]-prop-right-Whnf [k≡k']) k≡k'
escapeTermEq (emb 0<1 A) t≡u = escapeTermEq A t≡u
