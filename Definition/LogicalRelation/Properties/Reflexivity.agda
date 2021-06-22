{-# OPTIONS --without-K  #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Reflexivity {{eqrel : EqRelSet}} where

open import Definition.Untyped
open import Definition.Typed
open import Definition.LogicalRelation

open import Tools.Product
import Tools.PropositionalEquality as PE

reflNatural-prop : ∀ {Γ n}
                → Natural-prop Γ n
                → [Natural]-prop Γ n n
reflNatural-prop (sucᵣ (ℕₜ n d t≡t prop)) =
  sucᵣ (ℕₜ₌ n n d d t≡t
            (reflNatural-prop prop))
reflNatural-prop zeroᵣ = zeroᵣ
reflNatural-prop (ne (neNfₜ neK ⊢k k≡k)) = ne (neNfₜ₌ neK neK k≡k)

reflEmpty-prop : ∀ {Γ n}
                → Empty-prop Γ n
                → [Empty]-prop Γ n n
reflEmpty-prop (ne (neNfₜ neK ⊢k k≡k)) = ne (neNfₜ₌ neK neK k≡k)


module ReflCstr (K : constructors)
            {Pi : ∀ ki → [ K ]-cstr (cstr-cod ki) → Term → Set}
            {Pirel : ∀ ki → [ K ]-cstr (cstr-cod ki) → Term → Term → Set}
            (reflPi : ∀ ki kiK t → Pi ki kiK t → Pirel ki kiK t t)
            where

  open Cstr K Pi
  open [Cstr] K Pirel

  reflEqCstr : ∀ {Γ t a s} → Γ ⊩cstr t ∷K a ⦂ s → Γ ⊩cstr t ≡ t ∷K a ⦂ s
  reflCstr-prop : ∀ {Γ t a s}
                → Cstr-prop Γ a s t
                → [Cstr]-prop Γ a s t t

  reflEqCstr (cstrₜ k D k≡k [k]) = cstrₜ k k D D k≡k (reflCstr-prop [k])

  reflCstr-prop (cstrᵣ kK x) = cstrᵣ kK (reflPi _ _ _ x)
  reflCstr-prop (cstr-recᵣ kK kdomK x ⊢Kx [x]) = cstr-recᵣ kK kdomK (reflPi _ _ _ x) ⊢Kx (reflEqCstr [x])
  reflCstr-prop (ne (neNfₜ neK ⊢k k≡k)) = ne (neNfₜ₌ neK neK k≡k)


-- reflCstr-prop : ∀ {K Γ Pi t a s Pirel}
--               → (∀ ki kiK t → Pi ki kiK t → Pirel ki kiK t t)
--               → Cstr-prop K Γ Pi a s t
--               → [Cstr]-prop K Γ Pirel a s t t
-- reflCstr-prop reflPi (cstrᵣ kK x) = cstrᵣ kK (reflPi _ kK _ x)
-- reflCstr-prop reflPi (ne (neNfₜ neK ⊢k k≡k)) = ne (neNfₜ₌ neK neK k≡k)


reflBox-prop : ∀ {P Γ F sF t Prel}
             → (∀ x → P x → Prel x x)
             → Box-prop P Γ F sF t
             → [Box]-prop Prel Γ F sF t t
reflBox-prop reflP (boxᵣ x) = boxᵣ (reflP _ x)
reflBox-prop reflP (ne (neNfₜ neK ⊢k k≡k)) = ne (neNfₜ₌ neK neK k≡k)


reflEqTerm0 : ∀ {Γ A t s} ([A] : Γ ⊩⟨ ⁰ ⟩ A ⦂ s)
          → Γ ⊩⟨ ⁰ ⟩ t ∷ A ⦂ s / [A]
          → Γ ⊩⟨ ⁰ ⟩ t ≡ t ∷ A ⦂ s / [A]
reflEqTerm0 (ℕᵣ D) (ℕₜ n [ ⊢t , ⊢u , d ] t≡t prop) =
  ℕₜ₌ n n [ ⊢t , ⊢u , d ] [ ⊢t , ⊢u , d ] t≡t
      (reflNatural-prop prop)
reflEqTerm0 (Emptyᵣ D) (Emptyₜ n [ ⊢t , ⊢u , d ] t≡t prop) =
  Emptyₜ₌ n n [ ⊢t , ⊢u , d ] [ ⊢t , ⊢u , d ] t≡t
    (reflEmpty-prop prop)
reflEqTerm0 (ne′ K D neK K≡K) (neₜ k d (neNfₜ neK₁ ⊢k k≡k)) =
  neₜ₌ k k d d (neNfₜ₌ neK₁ neK₁ k≡k)
reflEqTerm0 (Πᵣ′ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Πₜ f d funcF f≡f [f] [f]₁) =
  Πₜ₌ f f d d funcF funcF f≡f
      (Πₜ f d funcF f≡f [f] [f]₁)
      (Πₜ f d funcF f≡f [f] [f]₁)
      (λ ρ ⊢Δ [a] → [f] ρ ⊢Δ [a] [a] (reflEqTerm0 ([F] ρ ⊢Δ) [a]))
reflEqTerm0 {Γ = Γ} {s = s} (cstrᵣ′ K KcodU a D ⊢a A≡A [domK] [a] [Yi]) d =
  cstrₜ₌ d d (ReflCstr.reflEqCstr K refl-aux d)
  where
    refl-aux : (ki : constructors) (kiK : [ K ]-cstr (cstr-cod ki))
               (t : Term) →
               LogRel.cstr-arg-dispatch ⁰ (λ ()) Γ s K [domK] [Yi] ki kiK t →
               LogRel.cstr≡-arg-dispatch ⁰ (λ ()) Γ s K [domK] [Yi] ki kiK t t
    refl-aux ki kiK t d with [Yi] ki kiK
    ... | LogRel.cstᵣ [A] = reflEqTerm0 [A] d
    ... | LogRel.monᵣ _ _ = d
reflEqTerm0 (Boxᵣ′ F sF D ⊢F A≡A [F]) (boxₜ b d b≡b [b]) =
  let bb = boxₜ b d b≡b [b] in
  boxₜ₌ b b d d b≡b bb bb (reflBox-prop (λ x d → reflEqTerm0 [F] d) [b])

reflEq0 : ∀ {Γ A s} ([A] : Γ ⊩⟨ ⁰ ⟩ A ⦂ s) → Γ ⊩⟨ ⁰ ⟩ A ≡ A ⦂ s / [A]
reflEq0 (Uᵣ′ _ l′ l< ⊢Γ) = PE.refl
reflEq0 (ℕᵣ D) = red D
reflEq0 (Emptyᵣ D) = red D
reflEq0 (ne′ K [ ⊢A , ⊢B , D ] neK K≡K) =
  ne₌ _ [ ⊢A , ⊢B , D ] neK K≡K
reflEq0 (Πᵣ′ sF F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) =
  Π₌ _ _ D A≡A
    (λ ρ ⊢Δ → reflEq0 ([F] ρ ⊢Δ))
    (λ ρ ⊢Δ [a] → reflEq0 ([G] ρ ⊢Δ [a]))
reflEq0 (cstrᵣ′ K KcodU a D ⊢a A≡A [domK] [a] [Yi]) = cstr₌ _ D A≡A (reflEqTerm0 [domK] [a])
reflEq0 (Boxᵣ′ F sF D ⊢F A≡A [F]) =
  Box₌ F D A≡A (reflEq0 [F])

mutual
  -- Reflexivity of reducible types.
  reflEq : ∀ {l Γ A s} ([A] : Γ ⊩⟨ l ⟩ A ⦂ s) → Γ ⊩⟨ l ⟩ A ≡ A ⦂ s / [A]
  reflEq (Uᵣ′ _ l′ l< ⊢Γ) = PE.refl
  reflEq (ℕᵣ D) = red D
  reflEq (Emptyᵣ D) = red D
  reflEq (ne′ K [ ⊢A , ⊢B , D ] neK K≡K) =
    ne₌ _ [ ⊢A , ⊢B , D ] neK K≡K
  reflEq (Πᵣ′ sF F G [ ⊢A , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) =
    Π₌ _ _ D A≡A
      (λ ρ ⊢Δ → reflEq ([F] ρ ⊢Δ))
      (λ ρ ⊢Δ [a] → reflEq ([G] ρ ⊢Δ [a]))
  reflEq {l} (cstrᵣ′ K KcodU a D ⊢a A≡A [domK] [a] [Yi]) = cstr₌ _ D A≡A (reflEqTerm {l} [domK] [a])
  reflEq (Boxᵣ′ F sF D ⊢F A≡A [F]) = Box₌ F D A≡A (reflEq [F])
  reflEq (emb 0<1 [A]) = reflEq [A]

  -- Reflexivity of reducible terms.
  reflEqTerm : ∀ {l Γ A t s} ([A] : Γ ⊩⟨ l ⟩ A ⦂ s)
            → Γ ⊩⟨ l ⟩ t ∷ A ⦂ s / [A]
            → Γ ⊩⟨ l ⟩ t ≡ t ∷ A ⦂ s / [A]
  reflEqTerm (Uᵣ′ _ ⁰ 0<1 ⊢Γ) (Uₜ A d typeA A≡A [A]) =
    Uₜ₌ A A d d typeA typeA A≡A [A] [A] (reflEq0 [A]) --(reflEq [A])
  reflEqTerm (ℕᵣ D) (ℕₜ n [ ⊢t , ⊢u , d ] t≡t prop) =
    ℕₜ₌ n n [ ⊢t , ⊢u , d ] [ ⊢t , ⊢u , d ] t≡t
        (reflNatural-prop prop)
  reflEqTerm (Emptyᵣ D) (Emptyₜ n [ ⊢t , ⊢u , d ] t≡t prop) =
    Emptyₜ₌ n n [ ⊢t , ⊢u , d ] [ ⊢t , ⊢u , d ] t≡t
      (reflEmpty-prop prop)
  reflEqTerm (ne′ K D neK K≡K) (neₜ k d (neNfₜ neK₁ ⊢k k≡k)) =
    neₜ₌ k k d d (neNfₜ₌ neK₁ neK₁ k≡k)
  reflEqTerm (Πᵣ′ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Πₜ f d funcF f≡f [f] [f]₁) =
    Πₜ₌ f f d d funcF funcF f≡f
        (Πₜ f d funcF f≡f [f] [f]₁)
        (Πₜ f d funcF f≡f [f] [f]₁)
        (λ ρ ⊢Δ [a] → [f] ρ ⊢Δ [a] [a] (reflEqTerm ([F] ρ ⊢Δ) [a]))
  reflEqTerm {l} {Γ} {s = s} (cstrᵣ′ K KcodU a D ⊢a A≡A [domK] [a] [Yi]) d =
    cstrₜ₌ d d (ReflCstr.reflEqCstr K refl-aux d)
    where
      refl-aux : (ki : constructors) (kiK : [ K ]-cstr (cstr-cod ki))
                (t : Term) →
                LogRel.cstr-arg-dispatch l (logRelRec l) Γ s K [domK] [Yi] ki kiK t →
                LogRel.cstr≡-arg-dispatch l (logRelRec l) Γ s K [domK] [Yi] ki kiK t t
      refl-aux ki kiK t d with [Yi] ki kiK
      ... | LogRel.cstᵣ [A] = reflEqTerm [A] d
      ... | LogRel.monᵣ _ _ = d
  reflEqTerm (Boxᵣ′ F sF D ⊢F A≡A [F]) (boxₜ b d b≡b [b]) =
    let bb = boxₜ b d b≡b [b] in
    boxₜ₌ b b d d b≡b bb bb (reflBox-prop (λ x d → reflEqTerm [F] d) [b])
  reflEqTerm (emb 0<1 [A]) t = reflEqTerm [A] t
