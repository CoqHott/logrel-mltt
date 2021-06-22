{-# OPTIONS --allow-unsolved-metas #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Cast {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
import Definition.Typed.Weakening as Twk
open import Definition.Typed.EqualityRelation
open import Definition.Typed.RedSteps
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Application
open import Definition.LogicalRelation.Substitution
import Definition.LogicalRelation.Weakening as Lwk
open import Definition.LogicalRelation.Substitution.Properties
import Definition.LogicalRelation.Substitution.Irrelevance as S
open import Definition.LogicalRelation.Substitution.Reflexivity
open import Definition.LogicalRelation.Substitution.Weakening
-- open import Definition.LogicalRelation.Substitution.Introductions.Nat
open import Definition.LogicalRelation.Substitution.Introductions.Empty
open import Definition.LogicalRelation.ShapeView
-- open import Definition.LogicalRelation.Substitution.Introductions.Pi
-- open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Definition.LogicalRelation.Substitution.Introductions.Universe
open import Definition.LogicalRelation.Substitution.MaybeEmbed
open import Definition.LogicalRelation.Substitution.Introductions.Castlemmas

open import Tools.Product
open import Tools.Empty
import Tools.Unit as TU
import Tools.PropositionalEquality as PE
import Data.Nat as Nat


~-irrelevanceTerm : ∀ {t t' u u' A A' r Γ} (eqA : A PE.≡ A') (eqt : t PE.≡ t') (equ : u PE.≡ u')
                  → Γ ⊢ t ~ u ∷ A ^ r
                  → Γ ⊢ t' ~ u' ∷ A' ^ r
~-irrelevanceTerm PE.refl PE.refl PE.refl X = X

[cast]irr : ∀ {A B Γ}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ % , ι ⁰ ])
         ([B] : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ % , ι ⁰ ]) →
         ∀ {t e} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ % , ι ⁰ ] / [A]) → (⊢e : Γ ⊢ e ∷ Id (Univ % ⁰) A B ^ [ % , ι ¹ ]) →
         Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ∷ B ^ [ % , ι ⁰ ] / [B]
[cast]irr {A} {B} ⊢Γ [A] [B] {t} {e} [t] ⊢e = 
  let ⊢A = escape {l = ι ⁰} {A = A} [A] 
      ⊢B = escape {l = ι ⁰} {A = B} [B] 
      ⊢t = escapeTerm {l = ι ⁰} {A = A} [A] [t]
  in logRelIrr [B] (castⱼ (un-univ ⊢A) (un-univ ⊢B) ⊢e ⊢t)

[castext]irr : ∀ {A A′ B B′ Γ}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ % , ι ⁰ ])
         ([A′] : Γ ⊩⟨ ι ⁰ ⟩ A′ ^ [ % , ι ⁰ ])
         ([A≡A′] : Γ ⊩⟨ ι ⁰ ⟩ A ≡ A′ ^ [ % , ι ⁰ ] / [A])
         ([B] : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ % , ι ⁰ ])
         ([B′] : Γ ⊩⟨ ι ⁰ ⟩ B′ ^ [ % , ι ⁰ ])
         ([B≡B′] : Γ ⊩⟨ ι ⁰ ⟩ B ≡ B′ ^ [ % , ι ⁰ ] / [B])
       → (∀ {t t′ e e′} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ % , ι ⁰ ] / [A])
                        → ([t′] : Γ ⊩⟨ ι ⁰ ⟩ t′ ∷ A′ ^ [ % , ι ⁰ ] / [A′])
                        → ([t≡t′] : Γ ⊩⟨ ι ⁰ ⟩ t ≡ t′ ∷ A ^ [ % , ι ⁰ ] / [A])
                        → (⊢e : Γ ⊢ e ∷ Id (Univ % ⁰) A B ^ [ % , ι ¹ ])
                        → (⊢e′ : Γ ⊢ e′ ∷ Id (Univ % ⁰) A′ B′ ^ [ % , ι ¹ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ≡ cast ⁰ A′ B′ e′ t′ ∷ B ^ [ % , ι ⁰ ] / [B])
[castext]irr {A} {A′} {B} {B′} ⊢Γ [A] [A′] [A≡A′] [B] [B′] [B≡B′] [t] [t′] [t≡t′] ⊢e ⊢e′ =
  let ⊢A = escape {l = ι ⁰} {A = A} [A] 
      ⊢B = escape {l = ι ⁰} {A = B} [B] 
      ⊢A′ = escape {l = ι ⁰} {A = A′} [A′] 
      ⊢B′ = escape {l = ι ⁰} {A = B′} [B′] 
      ⊢t = escapeTerm {l = ι ⁰} {A = A} [A] [t]
      ⊢t′ = escapeTerm {l = ι ⁰} {A = A′} [A′] [t′]
  in logRelIrrEq [B] (castⱼ (un-univ ⊢A) (un-univ ⊢B) ⊢e ⊢t) (conv (castⱼ (un-univ ⊢A′) (un-univ ⊢B′) ⊢e′ ⊢t′) (sym (≅-eq (escapeEq [B] [B≡B′]))))


[cast]Ne : ∀ {A B Γ}
         (⊢Γ : ⊢ Γ)
         ([A] :  Γ ⊩ne A ^[ ! , ⁰ ])
         ([B] : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ ! , ι ⁰ ]) →
         ∀ {t e} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ ! , ι ⁰ ] / ne [A]) → (⊢e : Γ ⊢ e ∷ Id (Univ ! ⁰) A B ^ [ % , ι ¹ ]) →
         Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ∷ B ^ [ ! , ι ⁰ ] / [B]
[cast]Ne {A} {B} ⊢Γ (ne K D neK K≡K) [B] {t} {e} [t] ⊢e =
  let [[ ⊢A , ⊢K , DK ]] = D
      ⊢A≡K = subset* DK
      ⊢B = escape {l = ι ⁰} [B]
      B≅B = ≅-un-univ (escapeEq {l = ι ⁰} [B] (reflEq {l = ι ⁰} [B]))
      cast~cast = ~-cast K≡K B≅B (≅-conv (escapeTermEq {l = ι ⁰} {A = A} (ne′ K D neK K≡K) (reflEqTerm {l = ι ⁰} (ne′ K D neK K≡K) [t])) ⊢A≡K)
  in neuTerm:⇒*: {t = cast ⁰ A B e t} [B] (castₙ neK) (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ne′ K D neK K≡K) [t]) (un-univ:⇒*: D)) cast~cast 

[castext]Ne : ∀ {A A′ B B′ Γ}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩ne A ^[ ! , ⁰ ])
         ([A′] : Γ ⊩ne A′ ^[ ! , ⁰ ])
         ([A≡A′] : Γ ⊩⟨ ι ⁰ ⟩ A ≡ A′ ^ [ ! , ι ⁰ ] / ne [A])
         ([B] : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ ! , ι ⁰ ])
         ([B′] : Γ ⊩⟨ ι ⁰ ⟩ B′ ^ [ ! , ι ⁰ ])
         ([B≡B′] : Γ ⊩⟨ ι ⁰ ⟩ B ≡ B′ ^ [ ! , ι ⁰ ] / [B])
       → (∀ {t t′ e e′} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ ! , ι ⁰ ] / ne [A])
                        → ([t′] : Γ ⊩⟨ ι ⁰ ⟩ t′ ∷ A′ ^ [ ! , ι ⁰ ] / ne [A′])
                        → ([t≡t′] : Γ ⊩⟨ ι ⁰ ⟩ t ≡ t′ ∷ A ^ [ ! , ι ⁰ ] / ne [A])
                        → (⊢e : Γ ⊢ e ∷ Id (U ⁰) A B ^ [ % , ι ¹ ])
                        → (⊢e′ : Γ ⊢ e′ ∷ Id (U ⁰) A′ B′ ^ [ % , ι ¹ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ≡ cast ⁰ A′ B′ e′ t′ ∷ B ^ [ ! , ι ⁰ ] / [B])
[castext]Ne {A} {A′} {B} {B′} ⊢Γ (ne K D neK K≡K) (ne K′ D′ neK′ K′≡K′) (ne₌ M D′′ neM K≡M) [B] [B′] [B≡B′] [t] [t′] [t≡t′] ⊢e ⊢e′ = 
  let [A] = ne K D neK K≡K
      [A′] = ne K′ D′ neK′ K′≡K′
      ⊢A = escape {l = ι ⁰} {A = A} (ne [A]) 
      ⊢B = escape {l = ι ⁰} {A = B} [B] 
      ⊢A′ = escape {l = ι ⁰} {A = A′} (ne [A′]) 
      ⊢B′ = escape {l = ι ⁰} {A = B′} [B′] 
      ⊢t = escapeTerm {l = ι ⁰} {A = A} (ne [A]) [t]
      ⊢t′ = escapeTerm {l = ι ⁰} {A = A′} (ne [A′]) [t′]
      t≅t′ = escapeTermEq {l = ι ⁰} {A = A} (ne [A]) [t≡t′]
  in neuEqTerm:⇒*: [B] (castₙ neK) (castₙ neM)
                   (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ne [A]) [t]) (un-univ:⇒*: D))
                   (conv:⇒*: (CastRed*Term ⊢B′ ⊢e′ (escapeTerm {l = ι ⁰} (ne [A′]) [t′]) (un-univ:⇒*: D′′)) (sym (≅-eq (escapeEq [B] [B≡B′]))))
                   (~-cast K≡M (≅-un-univ (escapeEq [B] [B≡B′])) (≅-conv t≅t′ (subset* (red D))))



[cast]ℕ : ∀ {A B Γ}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩ℕ A)
         ([B] : Γ ⊩ℕ B) →
         ∀ {t e} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ ! , ι ⁰ ] / ℕᵣ [A]) → (⊢e : Γ ⊢ e ∷ Id (Univ ! ⁰) A B ^ [ % , ι ¹ ]) →
         Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ∷ B ^ [ ! , ι ⁰ ] / ℕᵣ [B]
[cast]ℕ {A} {B} ⊢Γ [[ ⊢A , ⊢ℕ , D ]] [[ ⊢B , ⊢ℕ' , D' ]] {t} {e} (ℕₜ .(suc _) d n≡n (sucᵣ {a} x)) ⊢e =
  let ⊢t = escapeTerm {l = ι ⁰} (ℕᵣ [[ ⊢A , ⊢ℕ , D ]]) (ℕₜ (suc a) d n≡n (sucᵣ x))
      [N] = idRed:*: (univ (ℕⱼ ⊢Γ))
      ⊢eℕℕ = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* D)) (un-univ≡ (subset* D'))))
      ⊢eℕB = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* D)) (refl (un-univ ⊢B))))
      rec = [cast]ℕ ⊢Γ (idRed:*: ⊢ℕ) (idRed:*: ⊢ℕ) x ⊢eℕℕ
      cast≅cast = escapeTermEq {l = ι ⁰} (ℕᵣ (idRed:*: ⊢ℕ)) (reflEqTerm {l = ι ⁰} (ℕᵣ (idRed:*: ⊢ℕ)) rec)
  in ℕₜ (suc (cast ⁰ ℕ ℕ e a)) ((conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ℕᵣ [[ ⊢A , ⊢ℕ , D ]]) (ℕₜ (suc a) d n≡n (sucᵣ x))) (un-univ:⇒*: [[ ⊢A , ⊢ℕ , D ]]))
                                                   (transTerm:⇒:* (CastRed*Termℕ ⊢eℕB (conv ⊢t (subset* D)) [[ ⊢B , ⊢ℕ' , D' ]])
                                                                  (conv:⇒*: (transTerm:⇒:* (CastRed*Termℕℕ ⊢eℕℕ d)
                                                                  (CastRed*Termℕsuc ⊢eℕℕ (escapeTerm {l = ι ⁰} (ℕᵣ (idRed:*: ⊢ℕ)) x))) (sym (subset* D'))))) (subset* D') ))
        (≅-suc-cong cast≅cast) (Natural-prop.sucᵣ rec)
[cast]ℕ {A} {B} ⊢Γ [[ ⊢A , ⊢ℕ , D ]] [[ ⊢B , ⊢ℕ' , D' ]] {t} {e} (ℕₜ .zero d n≡n zeroᵣ) ⊢e =
  let ⊢t = escapeTerm {l = ι ⁰} (ℕᵣ [[ ⊢A , ⊢ℕ , D ]]) (ℕₜ zero d n≡n zeroᵣ)
      ⊢eℕℕ = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* D)) (un-univ≡ (subset* D'))))
  in ℕₜ zero ((conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ℕᵣ [[ ⊢A , ⊢ℕ , D ]]) (ℕₜ zero d n≡n zeroᵣ)) (un-univ:⇒*: [[ ⊢A , ⊢ℕ , D ]]))
                                                   (transTerm:⇒:* (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* D))
                                                                  (refl (un-univ ⊢B))))) (conv ⊢t (subset* D)) [[ ⊢B , ⊢ℕ' , D' ]])
                                                                  (conv:⇒*: (transTerm:⇒:* (CastRed*Termℕℕ ⊢eℕℕ d)
                                                                    (CastRed*Termℕzero ⊢eℕℕ)) (sym (subset* D'))))) (subset* D') ))
        (≅ₜ-zerorefl ⊢Γ) Natural-prop.zeroᵣ
[cast]ℕ {A} {B} ⊢Γ [[ ⊢A , ⊢ℕ , D ]] [[ ⊢B , ⊢ℕ' , D' ]] {t} {e} (ℕₜ n d n≡n (ne x)) ⊢e =
  let ⊢t = escapeTerm {l = ι ⁰} (ℕᵣ [[ ⊢A , ⊢ℕ , D ]]) (ℕₜ n d n≡n (ne x))
      ⊢eℕℕ = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* D)) (un-univ≡ (subset* D'))))
      neNfₜ nen ⊢n n~n = x
  in ℕₜ (cast ⁰ ℕ ℕ e n) ((conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ℕᵣ [[ ⊢A , ⊢ℕ , D ]]) (ℕₜ n d n≡n (ne x))) (un-univ:⇒*: [[ ⊢A , ⊢ℕ , D ]]))
                                                   (transTerm:⇒:* (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* D))
                                                                  (refl (un-univ ⊢B))))) (conv ⊢t (subset* D)) [[ ⊢B , ⊢ℕ' , D' ]])
                                                                  (conv:⇒*: (CastRed*Termℕℕ ⊢eℕℕ d) (sym (subset* D'))))) (subset* D') ))
        (~-to-≅ₜ (~-castℕℕ (wfTerm ⊢n) n~n)) (ne (neNfₜ (castℕℕₙ nen) (castⱼ (ℕⱼ (wfTerm ⊢n)) (ℕⱼ (wfTerm ⊢n)) ⊢eℕℕ ⊢n) (~-castℕℕ (wfTerm ⊢n) n~n)))



[cast] : ∀ {A B Γ r}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ r , ι ⁰ ])
         ([B] : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ r , ι ⁰ ])
       → (∀ {t e} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ r , ι ⁰ ] / [A]) → (⊢e : Γ ⊢ e ∷ Id (Univ r ⁰) A B ^ [ % , ι ¹ ]) → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ∷ B ^ [ r , ι ⁰ ] / [B])
       × (∀ {t e} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ B ^ [ r , ι ⁰ ] / [B]) → (⊢e : Γ ⊢ e ∷ Id (Univ r ⁰) B A ^ [ % , ι ¹ ]) → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ B A e t ∷ A ^ [ r , ι ⁰ ] / [A])
[castext] : ∀ {A A′ B B′ Γ r}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ r , ι ⁰ ])
         ([A′] : Γ ⊩⟨ ι ⁰ ⟩ A′ ^ [ r , ι ⁰ ])
         ([A≡A′] : Γ ⊩⟨ ι ⁰ ⟩ A ≡ A′ ^ [ r , ι ⁰ ] / [A])
         ([B] : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ r , ι ⁰ ])
         ([B′] : Γ ⊩⟨ ι ⁰ ⟩ B′ ^ [ r , ι ⁰ ])
         ([B≡B′] : Γ ⊩⟨ ι ⁰ ⟩ B ≡ B′ ^ [ r , ι ⁰ ] / [B])
       → (∀ {t t′ e e′} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ r , ι ⁰ ] / [A])
                        → ([t′] : Γ ⊩⟨ ι ⁰ ⟩ t′ ∷ A′ ^ [ r , ι ⁰ ] / [A′])
                        → ([t≡t′] : Γ ⊩⟨ ι ⁰ ⟩ t ≡ t′ ∷ A ^ [ r , ι ⁰ ] / [A])
                        → (⊢e : Γ ⊢ e ∷ Id (Univ r ⁰) A B ^ [ % , ι ¹ ])
                        → (⊢e′ : Γ ⊢ e′ ∷ Id (Univ r ⁰) A′ B′ ^ [ % , ι ¹ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ≡ cast ⁰ A′ B′ e′ t′ ∷ B ^ [ r , ι ⁰ ] / [B])
       × (∀ {t t′ e e′} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ B ^ [ r , ι ⁰ ] / [B])
                        → ([t′] : Γ ⊩⟨ ι ⁰ ⟩ t′ ∷ B′ ^ [ r , ι ⁰ ] / [B′])
                        → ([t≡t′] : Γ ⊩⟨ ι ⁰ ⟩ t ≡ t′ ∷ B ^ [ r , ι ⁰ ] / [B])
                        → (⊢e : Γ ⊢ e ∷ Id (Univ r ⁰) B A ^ [ % , ι ¹ ])
                        → (⊢e′ : Γ ⊢ e′ ∷ Id (Univ r ⁰) B′ A′ ^ [ % , ι ¹ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ B A e t ≡ cast ⁰ B′ A′ e′ t′ ∷ A ^ [ r , ι ⁰ ] / [A])
[castextShape] : ∀ {A A′ B B′ Γ r}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ r , ι ⁰ ])
         ([A′] : Γ ⊩⟨ ι ⁰ ⟩ A′ ^ [ r , ι ⁰ ])
         (ShapeA : ShapeView Γ (ι ⁰) (ι ⁰) A A′ [ r , ι ⁰ ] [ r , ι ⁰ ] [A] [A′])
         ([A≡A′] : Γ ⊩⟨ ι ⁰ ⟩ A ≡ A′ ^ [ r , ι ⁰ ] / [A])
         ([B] : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ r , ι ⁰ ])
         ([B′] : Γ ⊩⟨ ι ⁰ ⟩ B′ ^ [ r , ι ⁰ ])
         (ShapeB : ShapeView Γ (ι ⁰) (ι ⁰) B B′ [ r , ι ⁰ ] [ r , ι ⁰ ] [B] [B′])
         ([B≡B′] : Γ ⊩⟨ ι ⁰ ⟩ B ≡ B′ ^ [ r , ι ⁰ ] / [B])
       → (∀ {t t′ e e′} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ r , ι ⁰ ] / [A])
                        → ([t′] : Γ ⊩⟨ ι ⁰ ⟩ t′ ∷ A′ ^ [ r , ι ⁰ ] / [A′])
                        → ([t≡t′] : Γ ⊩⟨ ι ⁰ ⟩ t ≡ t′ ∷ A ^ [ r , ι ⁰ ] / [A])
                        → (⊢e : Γ ⊢ e ∷ Id (Univ r ⁰) A B ^ [ % , ι ¹ ])
                        → (⊢e′ : Γ ⊢ e′ ∷ Id (Univ r ⁰) A′ B′ ^ [ % , ι ¹ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ≡ cast ⁰ A′ B′ e′ t′ ∷ B ^ [ r , ι ⁰ ] / [B])
       × (∀ {t t′ e e′} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ B ^ [ r , ι ⁰ ] / [B])
                        → ([t′] : Γ ⊩⟨ ι ⁰ ⟩ t′ ∷ B′ ^ [ r , ι ⁰ ] / [B′])
                        → ([t≡t′] : Γ ⊩⟨ ι ⁰ ⟩ t ≡ t′ ∷ B ^ [ r , ι ⁰ ] / [B])
                        → (⊢e : Γ ⊢ e ∷ Id (Univ r ⁰) B A ^ [ % , ι ¹ ])
                        → (⊢e′ : Γ ⊢ e′ ∷ Id (Univ r ⁰) B′ A′ ^ [ % , ι ¹ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ B A e t ≡ cast ⁰ B′ A′ e′ t′ ∷ A ^ [ r , ι ⁰ ] / [A])


[castextShape] {A} {C} {B} {D} {Γ} ⊢Γ .(ℕᵣ ℕA₁) .(ℕᵣ ℕB₁) (ℕᵥ ℕA₁ ℕB₁) [A≡C] .(ℕᵣ ℕA) .(ℕᵣ ℕB) (ℕᵥ ℕA ℕB) [B≡D] =
  {!!} , {!!}
[castextShape] {A} {C} {B} {D} {Γ} ⊢Γ .(ne neA) .(ne neB) (ne neA neB) [A≡C] .(ℕᵣ ℕA) .(ℕᵣ ℕB) (ℕᵥ ℕA ℕB) [B≡D] =
  ([castext]Ne ⊢Γ neA neB [A≡C] (ℕᵣ ℕA) (ℕᵣ ℕB) [B≡D]) ,
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let ne K [[ ⊢A , ⊢K , D ]] neK K≡K = neA
        ne₌ K′ [[ ⊢A′ , ⊢K′ , D′ ]] neK' K≡K' = [A≡C]
        ⊢B≡ℕ = subset* (red ℕA)
        ⊢t = conv (escapeTerm {l = ι ⁰} (ℕᵣ ℕA) [t]) ⊢B≡ℕ
        ⊢D≡ℕ = subset* (red ℕB)
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (ℕᵣ ℕB) [t′]) ⊢D≡ℕ
        t≅t′ = escapeTermEq {l = ι ⁰} (ℕᵣ ℕA) [t≡t′]
    in neₜ₌ (cast ⁰ ℕ K e t) (cast ⁰ ℕ K′ e′ t′)
            (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A ⊢e (escapeTerm {l = ι ⁰} (ℕᵣ ℕA) [t]) (un-univ:⇒*: ℕA))
                                                   (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A) )) (un-univ≡ ⊢B≡ℕ)
                                                                  (refl (un-univ ⊢A))))) ⊢t [[ ⊢A , ⊢K , D ]])) (subset* D))
            (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A′ ⊢e′ (escapeTerm {l = ι ⁰} (ℕᵣ ℕB) [t′]) (un-univ:⇒*: ℕB))
                                                   (CastRed*Termℕ (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A′) )) (un-univ≡ ⊢D≡ℕ)
                                                                  (refl (un-univ ⊢A′))))) ⊢t′ [[ ⊢A′ , ⊢K′ , D′ ]]))
                                                                  (trans (subset* D′) (sym (≅-eq (≅-univ (~-to-≅ₜ K≡K'))))))
            (neNfₜ₌ (castℕₙ neK) (castℕₙ neK') (~-castℕ ⊢Γ K≡K' (≅-conv t≅t′ ⊢B≡ℕ))))
[castextShape] {A} {C} {B} {D} {Γ} {r = !} ⊢Γ _ _ (Πᵥ (Πᵣ rF .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext)
                                                  (Πᵣ rF′ .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢C , ⊢Π′ , DΠB ]] ⊢F′ ⊢G′ C≡C [F]′ [G]′ G-ext′))
                                              (Π₌ F′₁ G′₁ D₌ A≡B [F≡F′] [G≡G′]) .(ℕᵣ ℕA) .(ℕᵣ ℕB) (ℕᵥ ℕA ℕB) [B≡D] =
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let ΠA = Πᵣ rF ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext
        ΠB = Πᵣ rF′ ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢C , ⊢Π′ , DΠB ]] ⊢F′ ⊢G′ C≡C [F]′ [G]′ G-ext′
        ⊢A≡Π = subset* DΠA
        ⊢t = conv (escapeTerm {l = ι ⁰} (Πᵣ ΠA) [t]) ⊢A≡Π
        ⊢C≡Π = subset* DΠB
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (Πᵣ ΠB) [t′]) ⊢C≡Π 
        t≅t′ = escapeTermEq {l = ι ⁰} (Πᵣ ΠA) [t≡t′]
        ΠFG′≡ΠFG′₁ = whrDet* (DΠB , Πₙ) (D₌ , Πₙ)
        F′≡F′₁ , rF≡rF′ , _ , G′≡G′₁ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₁
        ⊢B = escape {l = ι ⁰} (ℕᵣ ℕA)
        ⊢D = escape {l = ι ⁰} (ℕᵣ ℕB)
        ⊢B≡D = escapeEq {l = ι ⁰} (ℕᵣ ℕA) [B≡D]
        cast~cast = ~-irrelevanceTerm  PE.refl PE.refl (PE.cong₃ (λ X Y Z → cast ⁰ (Π X ^ Y ° ⁰ ▹ Z ° ⁰) _ _ _ ) (PE.sym F′≡F′₁) (PE.sym rF≡rF′) (PE.sym G′≡G′₁) )
                                       (~-castΠℕ (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ A≡B) (≅-conv t≅t′ ⊢A≡Π))
    in neuEqTerm:⇒*: { n = cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰) ℕ e t} {n′ = cast ⁰ (Π F′ ^ rF′ ° ⁰ ▹ G′ ° ⁰) ℕ e′ t′} (ℕᵣ ℕA)
                     castΠℕₙ castΠℕₙ
                     (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (Πᵣ ΠA) [t]) (un-univ:⇒*: [[ ⊢A , ⊢Π , DΠA ]]))
                                      (CastRed*TermΠ (un-univ ⊢F) (un-univ ⊢G) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A) )) (un-univ≡ ⊢A≡Π)
                                                                  (refl (un-univ ⊢B))))) ⊢t ℕA))
                     (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢D ⊢e′ (escapeTerm {l = ι ⁰} (Πᵣ ΠB) [t′]) (un-univ:⇒*: [[ ⊢C , ⊢Π′ , DΠB ]]))
                                     (CastRed*TermΠ (un-univ ⊢F′) (un-univ ⊢G′) (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢C) )) (un-univ≡ ⊢C≡Π)
                                                                  (refl (un-univ ⊢D))))) ⊢t′ ℕB)) (sym (≅-eq ⊢B≡D)))
                     (~-conv cast~cast (sym (subset* (red ℕA))))),
  λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let ΠA = Πᵣ rF ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext
        ⊢A≡Π = subset* DΠA
        ⊢B≡ℕ = subset* (red ℕA)
        ⊢D≡ℕ = subset* (red ℕB)
        ⊢t = conv (escapeTerm {l = ι ⁰} (ℕᵣ ℕA) [t]) ⊢B≡ℕ
        ⊢C≡Π = subset* DΠB
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (ℕᵣ ℕB) [t′]) ⊢D≡ℕ 
        t≅t′ = escapeTermEq {l = ι ⁰} (ℕᵣ ℕA) [t≡t′]
        ΠFG′≡ΠFG′₁ = whrDet* (DΠB , Πₙ) (D₌ , Πₙ)
        F′≡F′₁ , rF≡rF′ , _ , G′≡G′₁ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₁
        ⊢B = escape {l = ι ⁰} (ℕᵣ ℕA)
        ⊢D = escape {l = ι ⁰} (ℕᵣ ℕB)
        ⊢A≡C = escapeEq {l = ι ⁰} (Πᵣ ΠA) (Π₌ F′₁ G′₁ D₌ A≡B [F≡F′] [G≡G′])
        cast~cast = ~-irrelevanceTerm  PE.refl PE.refl (PE.cong₃ (λ X Y Z → cast ⁰ _ (Π X ^ Y ° ⁰ ▹ Z ° ⁰) _ _ ) (PE.sym F′≡F′₁) (PE.sym rF≡rF′) (PE.sym G′≡G′₁) )
                                       (~-castℕΠ (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ A≡B) (≅-conv t≅t′ ⊢B≡ℕ))
    in neuEqTerm:⇒*: { n = cast ⁰ ℕ (Π F ^ rF ° ⁰ ▹ G ° ⁰) e t} {n′ = cast ⁰ ℕ  (Π F′ ^ rF′ ° ⁰ ▹ G′ ° ⁰) e′ t′} (Πᵣ ΠA)
                     castℕΠₙ castℕΠₙ
                     (transTerm:⇒:* (CastRed*Term ⊢A ⊢e (escapeTerm {l = ι ⁰} (ℕᵣ ℕA) [t]) (un-univ:⇒*: ℕA))
                                      (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A) )) (un-univ≡ ⊢B≡ℕ)
                                                                  (refl (un-univ ⊢A)))))
                                                     ⊢t [[ ⊢A , ⊢Π , DΠA ]]))
                     (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢C ⊢e′ (escapeTerm {l = ι ⁰} (ℕᵣ ℕB) [t′]) (un-univ:⇒*: ℕB))
                                     (CastRed*Termℕ (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢C) )) (un-univ≡ ⊢D≡ℕ)
                                                                  (refl (un-univ ⊢C))))) ⊢t′ [[ ⊢C , ⊢Π′ , DΠB ]])) (sym (≅-eq ⊢A≡C)))
                     (~-conv cast~cast (sym (subset* DΠA)))
[castextShape] {A} {C} {B} {D} {Γ} ⊢Γ .(ℕᵣ ℕA) .(ℕᵣ ℕB) (ℕᵥ ℕA ℕB) [A≡C] .(ne neA) .(ne neB) (ne neA neB) [B≡D] =
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let ne K [[ ⊢A , ⊢K , D ]] neK K≡K = neA
        ne₌ K′ [[ ⊢A′ , ⊢K′ , D′ ]] neK' K≡K' = [B≡D]
        ⊢B≡ℕ = subset* (red ℕA)
        ⊢t = conv (escapeTerm {l = ι ⁰} (ℕᵣ ℕA) [t]) ⊢B≡ℕ
        ⊢D≡ℕ = subset* (red ℕB)
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (ℕᵣ ℕB) [t′]) ⊢D≡ℕ
        t≅t′ = escapeTermEq {l = ι ⁰} (ℕᵣ ℕA) [t≡t′]
    in neₜ₌ (cast ⁰ ℕ K e t) (cast ⁰ ℕ K′ e′ t′)
            (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A ⊢e (escapeTerm {l = ι ⁰} (ℕᵣ ℕA) [t]) (un-univ:⇒*: ℕA))
                                                   (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A) )) (un-univ≡ ⊢B≡ℕ)
                                                                  (refl (un-univ ⊢A))))) ⊢t [[ ⊢A , ⊢K , D ]])) (subset* D))
            (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A′ ⊢e′ (escapeTerm {l = ι ⁰} (ℕᵣ ℕB) [t′]) (un-univ:⇒*: ℕB))
                                                   (CastRed*Termℕ (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢A′) )) (un-univ≡ ⊢D≡ℕ)
                                                                  (refl (un-univ ⊢A′))))) ⊢t′ [[ ⊢A′ , ⊢K′ , D′ ]]))
                                                                  (trans (subset* D′) (sym (≅-eq (≅-univ (~-to-≅ₜ K≡K'))))))
            (neNfₜ₌ (castℕₙ neK) (castℕₙ neK') (~-castℕ ⊢Γ K≡K' (≅-conv t≅t′ ⊢B≡ℕ)))) ,
  ([castext]Ne ⊢Γ neA neB [B≡D] (ℕᵣ ℕA) (ℕᵣ ℕB) [A≡C])
[castextShape] {A} {C} {B} {D} {Γ} {r = !} ⊢Γ .(ne neA₁) .(ne neB₁) (ne neA₁ neB₁) [A≡C] .(ne neA) .(ne neB) (ne neA neB) [B≡D] =
  ([castext]Ne ⊢Γ neA₁ neB₁ [A≡C] (ne neA) (ne neB) [B≡D]) , ([castext]Ne ⊢Γ neA neB [B≡D] (ne neA₁) (ne neB₁) [A≡C])
[castextShape] {A} {C} {B} {D} {Γ} {r = !} ⊢Γ _ _ (Πᵥ (Πᵣ rF .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext)
                                                  (Πᵣ rF′ .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢C , ⊢Π′ , DΠB ]] ⊢F′ ⊢G′ C≡C [F]′ [G]′ G-ext′))
                                              (Π₌ F′₁ G′₁ D₌ A≡B [F≡F′] [G≡G′]) .(ne neA) .(ne neB) (ne neA neB) [B≡D] = 
  (λ {t} {t′} {e} {e′} [t] [t′] [t≡t′] ⊢e ⊢e′ →
    let ne K [[ ⊢B , ⊢K , D ]] neK K≡K = neA
        ne₌ K′ [[ ⊢D , ⊢K′ , D′ ]] neK' K≡K' = [B≡D]
        ΠA = Πᵣ rF ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext
        ΠB = Πᵣ rF′ ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢C , ⊢Π′ , DΠB ]] ⊢F′ ⊢G′ C≡C [F]′ [G]′ G-ext′
        ⊢A≡Π = subset* DΠA
        ⊢t = conv (escapeTerm {l = ι ⁰} (Πᵣ ΠA) [t]) ⊢A≡Π
        ⊢C≡Π = subset* DΠB
        ⊢t′ = conv (escapeTerm {l = ι ⁰} (Πᵣ ΠB) [t′]) ⊢C≡Π 
        t≅t′ = escapeTermEq {l = ι ⁰} (Πᵣ ΠA) [t≡t′]
        ΠFG′≡ΠFG′₁ = whrDet* (DΠB , Πₙ) (D₌ , Πₙ)
        F′≡F′₁ , rF≡rF′ , _ , G′≡G′₁ , _  = Π-PE-injectivity ΠFG′≡ΠFG′₁
    in neₜ₌ (cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰) K e t) (cast ⁰ (Π F′ ^ rF′ ° ⁰ ▹ G′ ° ⁰) K′ e′ t′)
            (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (Πᵣ ΠA) [t]) (un-univ:⇒*: [[ ⊢A , ⊢Π , DΠA ]]))
                                      (CastRed*TermΠ (un-univ ⊢F) (un-univ ⊢G) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A) )) (un-univ≡ ⊢A≡Π)
                                                                  (refl (un-univ ⊢B))))) ⊢t [[ ⊢B , ⊢K , D ]]))
                      (subset* D))
            (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢D ⊢e′ (escapeTerm {l = ι ⁰} (Πᵣ ΠB) [t′]) (un-univ:⇒*: [[ ⊢C , ⊢Π′ , DΠB ]]))
                                     (CastRed*TermΠ (un-univ ⊢F′) (un-univ ⊢G′) (conv ⊢e′ (univ (Id-cong (refl (univ 0<1 (wf ⊢C) )) (un-univ≡ ⊢C≡Π)
                                                                  (refl (un-univ ⊢D))))) ⊢t′ [[ ⊢D , ⊢K′ , D′ ]]))
                      (trans (subset* D′) (sym (≅-eq (≅-univ (~-to-≅ₜ K≡K'))))))
            (neNfₜ₌ (castΠₙ neK) (castΠₙ neK')
                    (~-irrelevanceTerm  PE.refl PE.refl (PE.cong₃ (λ X Y Z → cast ⁰ (Π X ^ Y ° ⁰ ▹ Z ° ⁰) _ _ _ ) (PE.sym F′≡F′₁) (PE.sym rF≡rF′) (PE.sym G′≡G′₁) )
                                        (~-castΠ (≅-un-univ A≡B) K≡K' (≅-conv t≅t′ ⊢A≡Π))))) ,
  ([castext]Ne ⊢Γ neA neB [B≡D] (Πᵣ′ rF ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢Π , DΠA ]] ⊢F ⊢G A≡A [F] [G] G-ext)
                                (Πᵣ′ rF′ ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢C , ⊢Π′ , DΠB ]] ⊢F′ ⊢G′ C≡C [F]′ [G]′ G-ext′) (Π₌ F′₁ G′₁ D₌ A≡B [F≡F′] [G≡G′]))
[castextShape] {A} {C} {B} {D} {Γ} ⊢Γ .(ℕᵣ ℕA) .(ℕᵣ ℕB) (ℕᵥ ℕA ℕB) [A≡C] .(Πᵣ ΠA) .(Πᵣ ΠB) (Πᵥ ΠA ΠB) [B≡D] = {!!}
[castextShape] {A} {C} {B} {D} {Γ} {r = !} ⊢Γ .(ne neA) .(ne neB) (ne neA neB) [A≡C] .(Πᵣ ΠA) .(Πᵣ ΠB) (Πᵥ ΠA ΠB) [B≡D] =
  ([castext]Ne ⊢Γ neA neB [A≡C] (Πᵣ ΠA) (Πᵣ ΠB) [B≡D]) , {!!}
[castextShape] {A} {C} {B} {D} {Γ} {r = %} ⊢Γ [A] [C] _ [A≡C] [B] [D] _ [B≡D] =
  [castext]irr {A} {C} {B} {D} {Γ} ⊢Γ [A] [C] [A≡C] [B] [D] [B≡D] , [castext]irr {B} {D} {A} {C} {Γ} ⊢Γ [B] [D] [B≡D] [A] [C] [A≡C]
[castextShape] {A} {C} {B} {D} {Γ} {r = !} ⊢Γ .(Πᵣ ΠA₁) .(Πᵣ ΠB₁) (Πᵥ ΠA₁ ΠB₁) [A≡C] .(Πᵣ ΠA) .(Πᵣ ΠB) (Πᵥ ΠA ΠB) [B≡D] = {!!}



[cast] ⊢Γ  = {!!}
{-
[cast] ⊢Γ (ℕᵣ x) (ℕᵣ x₁) = (λ [t] ⊢e → [cast]ℕ ⊢Γ x x₁ [t] ⊢e) , (λ [t] ⊢e → [cast]ℕ ⊢Γ x₁ x [t] ⊢e)
[cast] {A} {B} ⊢Γ (ℕᵣ x) (ne′ K [[ ⊢B , ⊢K , D ]] neK K≡K) =
  (λ {t} {e} [t] ⊢e → let ⊢A≡ℕ = let [[ _ , _ , Dx ]] = x in un-univ≡ (subset* Dx)
                          ⊢A≡ℕ' = let [[ _ , _ , Dx ]] = x in subset* Dx
                          ⊢t = conv (escapeTerm {l = ι ⁰} (ℕᵣ x) [t]) ⊢A≡ℕ'                      
                      in neₜ (cast ⁰ ℕ K e t)
                          (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ℕᵣ x) [t]) (un-univ:⇒*: x))
                                                   (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) ⊢A≡ℕ
                                                                  (refl (un-univ ⊢B))))) ⊢t [[ ⊢B , ⊢K , D ]])) (subset* D) )
                          (neNfₜ (castℕₙ neK) (castⱼ (ℕⱼ (wf ⊢B)) (un-univ ⊢K) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) ))
                                                     ⊢A≡ℕ (un-univ≡ (subset* D)))))
                                                     ⊢t)
                                              (~-castℕ (wf ⊢B) K≡K (≅-conv (escapeTermEq {l = ι ⁰} {A = A} (ℕᵣ x) (reflEqTerm {l = ι ⁰} (ℕᵣ x) [t])) ⊢A≡ℕ' )))) ,
  λ {t} {e} [t] ⊢e → [cast]Ne ⊢Γ (ne K [[ ⊢B , ⊢K , D ]] neK K≡K) (ℕᵣ x) [t] ⊢e
[cast] {A} {B} {r = .!} ⊢Γ (ℕᵣ x) (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext) =
  (λ {t} {e} [t] ⊢e →
    let ⊢A≡ℕ = let [[ _ , _ , Dx ]] = x in un-univ≡ (subset* (red x))
        ⊢A≡ℕ' = let [[ _ , _ , Dx ]] = x in subset* (red x)
        ⊢t = conv (escapeTerm {l = ι ⁰} (ℕᵣ x) [t]) ⊢A≡ℕ'
        t≅t = ≅-conv (escapeTermEq {l = ι ⁰} {A = A} (ℕᵣ x) (reflEqTerm {l = ι ⁰} (ℕᵣ x) [t])) ⊢A≡ℕ'
        cast~cast = ~-castℕΠ (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ B≡B) t≅t 
    in neuTerm:⇒*: {t = cast ⁰ A B e t} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext)
                   castℕΠₙ (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ℕᵣ x) [t]) (un-univ:⇒*: x))
                                                   (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) ⊢A≡ℕ
                                                                  (refl (un-univ ⊢B))))) ⊢t [[ ⊢B , ⊢Π , D ]])) (~-conv cast~cast (sym (subset* D)))) ,
  λ {t} {e} [t] ⊢e →
    let ⊢B≡Π = un-univ≡ (subset* D)
        ⊢B≡Π' = subset* D
        [[ ⊢A , ⊢N , Dx ]] = x
        ⊢A≡ℕ = subset* Dx
        ⊢t' = escapeTerm {l = ι ⁰} {A = B} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext) [t]
        ⊢t = conv {B = (Π F ^ rF ° ⁰ ▹ G ° ⁰)} ⊢t' ⊢B≡Π'
        t≅t = ≅-conv (escapeTermEq {l = ι ⁰} {A = B} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext)
              (reflEqTerm {l = ι ⁰} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext) [t])) ⊢B≡Π'
        cast~cast = ~-castΠℕ (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ B≡B) t≅t 
    in neuTerm:⇒*: {l = ∞} (ℕᵣ x) castΠℕₙ (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A ⊢e ⊢t' (un-univ:⇒*:  [[ ⊢B , ⊢Π , D ]]))
                                                   (CastRed*TermΠ (un-univ ⊢F ) (un-univ ⊢G) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) ⊢B≡Π
                                                                  (refl (un-univ ⊢A))))) ⊢t [[ ⊢A , ⊢N , Dx ]])) (refl ⊢A )) (~-conv cast~cast (sym ⊢A≡ℕ)) 
[cast] {A} {B}  ⊢Γ (ne′ K [[ ⊢B , ⊢K , D ]] neK K≡K) (ℕᵣ x) =
   (λ {t} {e} [t] ⊢e → [cast]Ne ⊢Γ (ne K [[ ⊢B , ⊢K , D ]] neK K≡K) (ℕᵣ x) [t] ⊢e) ,
   (λ {t} {e} [t] ⊢e → let ⊢A≡ℕ = let [[ _ , _ , Dx ]] = x in un-univ≡ (subset* Dx)
                           ⊢A≡ℕ' = let [[ _ , _ , Dx ]] = x in subset* Dx
                           ⊢t = conv (escapeTerm {l = ι ⁰} (ℕᵣ x) [t]) ⊢A≡ℕ'                      
                       in neₜ (cast ⁰ ℕ K e t)
                              (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ℕᵣ x) [t]) (un-univ:⇒*: x))
                                                   (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) ⊢A≡ℕ
                                                                  (refl (un-univ ⊢B))))) ⊢t [[ ⊢B , ⊢K , D ]])) (subset* D) )
                              (neNfₜ (castℕₙ neK) (castⱼ (ℕⱼ (wf ⊢B)) (un-univ ⊢K) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) ))
                                                     ⊢A≡ℕ (un-univ≡ (subset* D)))))
                                                     ⊢t)
                                              (~-castℕ (wf ⊢B) K≡K (≅-conv (escapeTermEq {l = ι ⁰} {A = B} (ℕᵣ x) (reflEqTerm {l = ι ⁰} (ℕᵣ x) [t])) ⊢A≡ℕ' ))))
[cast] {r = !} ⊢Γ (ne x) (ne x₁) = (λ {t} {e} [t] ⊢e → [cast]Ne ⊢Γ x (ne x₁) [t] ⊢e) , λ {t} {e} [t] ⊢e → [cast]Ne ⊢Γ x₁ (ne x) [t] ⊢e
[cast] {A} {B} {r = !} ⊢Γ (ne′ K [[ ⊢A , ⊢K , D ]] neK K≡K) (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , DΠ ]] ⊢F ⊢G B≡B [F] [G] G-ext)  =
  (λ {t} {e} [t] ⊢e → [cast]Ne ⊢Γ (ne K [[ ⊢A , ⊢K , D ]] neK K≡K) (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , DΠ ]] ⊢F ⊢G B≡B [F] [G] G-ext) [t] ⊢e) ,
  (λ {t} {e} [t] ⊢e →  let ⊢B≡Π = un-univ≡ (subset* DΠ)
                           ⊢B≡Π' = subset* DΠ
                           [Π] = Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , DΠ ]] ⊢F ⊢G B≡B [F] [G] G-ext
                           ⊢t' = escapeTerm {l = ι ⁰} [Π] [t]
                           ⊢t = conv ⊢t' ⊢B≡Π'
                       in neₜ (cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰) K e t)
                              (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A ⊢e ⊢t' (un-univ:⇒*: [[ ⊢B , ⊢Π , DΠ ]]))
                                                   (CastRed*TermΠ (un-univ ⊢F) (un-univ ⊢G) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) ⊢B≡Π
                                                                  (refl (un-univ ⊢A))))) ⊢t [[ ⊢A , ⊢K , D ]])) (subset* D) )
                              (neNfₜ (castΠₙ neK) (castⱼ (Πⱼ ≡is≤ PE.refl ▹ ≡is≤ PE.refl ▹ un-univ ⊢F ▹ un-univ ⊢G) (un-univ ⊢K) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) ))
                                                     ⊢B≡Π (un-univ≡ (subset* D)))))
                                                     ⊢t)
                                              (~-castΠ (≅-un-univ B≡B) K≡K (≅-conv (escapeTermEq {l = ι ⁰} {A = B} [Π] (reflEqTerm {l = ι ⁰} [Π] [t])) ⊢B≡Π' ))))
[cast] {A} {B} ⊢Γ (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext) (ℕᵣ x) =
  (λ {t} {e} [t] ⊢e →
    let ⊢B≡Π = un-univ≡ (subset* D)
        ⊢B≡Π' = subset* D
        [[ ⊢A , ⊢N , Dx ]] = x
        ⊢A≡ℕ = subset* Dx
        ⊢t' = escapeTerm {l = ι ⁰} {A = A} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext) [t]
        ⊢t = conv {B = (Π F ^ rF ° ⁰ ▹ G ° ⁰)} ⊢t' ⊢B≡Π'
        t≅t = ≅-conv (escapeTermEq {l = ι ⁰} {A = A} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext)
              (reflEqTerm {l = ι ⁰} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext) [t])) ⊢B≡Π'
        cast~cast = ~-castΠℕ (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ B≡B) t≅t 
    in neuTerm:⇒*: {l = ∞} {t = cast ⁰ A B e t} (ℕᵣ x) castΠℕₙ (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A ⊢e ⊢t' (un-univ:⇒*:  [[ ⊢B , ⊢Π , D ]]))
                                                   (CastRed*TermΠ (un-univ ⊢F ) (un-univ ⊢G) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) ⊢B≡Π
                                                                  (refl (un-univ ⊢A))))) ⊢t [[ ⊢A , ⊢N , Dx ]])) (refl ⊢A )) (~-conv cast~cast (sym ⊢A≡ℕ))) ,
   (λ {t} {e} [t] ⊢e →
    let ⊢A≡ℕ = let [[ _ , _ , Dx ]] = x in un-univ≡ (subset* (red x))
        ⊢A≡ℕ' = let [[ _ , _ , Dx ]] = x in subset* (red x)
        ⊢t = conv (escapeTerm {l = ι ⁰} (ℕᵣ x) [t]) ⊢A≡ℕ'
        t≅t = ≅-conv (escapeTermEq {l = ι ⁰} {A = B} (ℕᵣ x) (reflEqTerm {l = ι ⁰} (ℕᵣ x) [t])) ⊢A≡ℕ'
        cast~cast = ~-castℕΠ (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ B≡B) t≅t 
    in neuTerm:⇒*: {t = cast ⁰ B A e t} (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , D ]] ⊢F ⊢G B≡B [F] [G] G-ext)
                   castℕΠₙ (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ℕᵣ x) [t]) (un-univ:⇒*: x))
                                                   (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) ⊢A≡ℕ
                                                                  (refl (un-univ ⊢B))))) ⊢t [[ ⊢B , ⊢Π , D ]])) (~-conv cast~cast (sym (subset* D))))
[cast] {A} {B} {r = !} ⊢Γ (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , DΠ ]] ⊢F ⊢G B≡B [F] [G] G-ext) (ne′ K [[ ⊢A , ⊢K , D ]] neK K≡K) =
  (λ {t} {e} [t] ⊢e →  let ⊢B≡Π = un-univ≡ (subset* DΠ)
                           ⊢B≡Π' = subset* DΠ
                           [Π] = Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , DΠ ]] ⊢F ⊢G B≡B [F] [G] G-ext
                           ⊢t' = escapeTerm {l = ι ⁰} [Π] [t]
                           ⊢t = conv ⊢t' ⊢B≡Π'
                       in neₜ (cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰) K e t)
                              (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢A ⊢e ⊢t' (un-univ:⇒*: [[ ⊢B , ⊢Π , DΠ ]]))
                                                   (CastRed*TermΠ (un-univ ⊢F) (un-univ ⊢G) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) ⊢B≡Π
                                                                  (refl (un-univ ⊢A))))) ⊢t [[ ⊢A , ⊢K , D ]])) (subset* D) )
                              (neNfₜ (castΠₙ neK) (castⱼ (Πⱼ ≡is≤ PE.refl ▹ ≡is≤ PE.refl ▹ un-univ ⊢F ▹ un-univ ⊢G) (un-univ ⊢K) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) ))
                                                     ⊢B≡Π (un-univ≡ (subset* D)))))
                                                     ⊢t)
                                              (~-castΠ (≅-un-univ B≡B) K≡K (≅-conv (escapeTermEq {l = ι ⁰} {A = A} [Π] (reflEqTerm {l = ι ⁰} [Π] [t])) ⊢B≡Π' )))) ,
  (λ {t} {e} [t] ⊢e → [cast]Ne ⊢Γ (ne K [[ ⊢A , ⊢K , D ]] neK K≡K) (Πᵣ′ rF lF lG (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢B , ⊢Π , DΠ ]] ⊢F ⊢G B≡B [F] [G] G-ext) [t] ⊢e)
[cast] {r = %} ⊢Γ [A] [B] = [cast]irr ⊢Γ [A] [B] , [cast]irr ⊢Γ [B] [A] 
[cast] {A} {B} {Γ} {r = !} ⊢Γ (Πᵣ′ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D ⊢F ⊢G A≡A [F] [G] G-ext)
  (Πᵣ′ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext) =
  (λ {t} {e} [t] ⊢e →
    let [A] = Πᵣ′ % ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D ⊢F ⊢G A≡A [F] [G] G-ext
        ⊢A = escape [A]
        [B] = Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext
        ⊢B = escape [B]
        ⊢t = escapeTerm [A] [t]
        ⊢A≡Π = subset* (red D)
        ⊢B≡Π = subset* (red D₁)
        ⊢t≡t = ≅-conv (escapeTermEq {l = ι ⁰} [A] (reflEqTerm {l = ι ⁰} [A] [t])) ⊢A≡Π
        cast~cast = ~-conv (~-castΠΠ%! (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ A≡A) (un-univ ⊢F₁) (un-univ ⊢G₁) (≅-un-univ A₁≡A₁) ⊢t≡t) (sym ⊢B≡Π)       
    in neuTerm:⇒*: {t = cast ⁰ A B e t} [B]
                                  castΠΠ%!ₙ (transTerm:⇒:* (CastRed*Term ⊢B ⊢e ⊢t (un-univ:⇒*: D))
                                                   (CastRed*TermΠ (un-univ ⊢F ) (un-univ ⊢G) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ ⊢A≡Π)
                                                                  (refl (un-univ ⊢B))))) (conv ⊢t ⊢A≡Π) D₁)) cast~cast) ,
  (λ {t} {e} [t] ⊢e →
    let [A] = Πᵣ′ % ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D ⊢F ⊢G A≡A [F] [G] G-ext
        ⊢A = escape [A]
        [B] = Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext
        ⊢B = escape [B]
        ⊢t = escapeTerm [B] [t]
        ⊢A≡Π = subset* (red D)
        ⊢B≡Π = subset* (red D₁)
        ⊢t≡t = ≅-conv (escapeTermEq {l = ι ⁰} [B] (reflEqTerm {l = ι ⁰} [B] [t])) ⊢B≡Π
        cast~cast = ~-conv (~-castΠΠ!% (un-univ ⊢F₁) (un-univ ⊢G₁) (≅-un-univ A₁≡A₁) (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ A≡A) ⊢t≡t) (sym ⊢A≡Π)       
    in neuTerm:⇒*: {t = cast ⁰ B A e t} [A]
                                  castΠΠ!%ₙ (transTerm:⇒:* (CastRed*Term ⊢A ⊢e ⊢t (un-univ:⇒*: D₁))
                                                   (CastRed*TermΠ (un-univ ⊢F₁ ) (un-univ ⊢G₁) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A) )) (un-univ≡ ⊢B≡Π)
                                                                  (refl (un-univ ⊢A))))) (conv ⊢t ⊢B≡Π) D)) cast~cast)
[cast] {A} {B} {Γ} {r = !} ⊢Γ (Πᵣ′ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D ⊢F ⊢G A≡A [F] [G] G-ext)
  (Πᵣ′ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext) = 
  (λ {t} {e} [t] ⊢e →
    let [A] = Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D ⊢F ⊢G A≡A [F] [G] G-ext
        ⊢A = escape [A]
        [B] = Πᵣ′ % ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext
        ⊢B = escape [B]
        ⊢t = escapeTerm [A] [t]
        ⊢A≡Π = subset* (red D)
        ⊢B≡Π = subset* (red D₁)
        ⊢t≡t = ≅-conv (escapeTermEq {l = ι ⁰} [A] (reflEqTerm {l = ι ⁰} [A] [t])) ⊢A≡Π
        cast~cast = ~-conv (~-castΠΠ!% (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ A≡A) (un-univ ⊢F₁) (un-univ ⊢G₁) (≅-un-univ A₁≡A₁) ⊢t≡t) (sym ⊢B≡Π)       
    in neuTerm:⇒*: {t = cast ⁰ A B e t} [B]
                                  castΠΠ!%ₙ (transTerm:⇒:* (CastRed*Term ⊢B ⊢e ⊢t (un-univ:⇒*: D))
                                                   (CastRed*TermΠ (un-univ ⊢F ) (un-univ ⊢G) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ ⊢A≡Π)
                                                                  (refl (un-univ ⊢B))))) (conv ⊢t ⊢A≡Π) D₁)) cast~cast) ,
  (λ {t} {e} [t] ⊢e →
    let [A] = Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D ⊢F ⊢G A≡A [F] [G] G-ext
        ⊢A = escape [A]
        [B] = Πᵣ′ % ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext
        ⊢B = escape [B]
        ⊢t = escapeTerm [B] [t]
        ⊢A≡Π = subset* (red D)
        ⊢B≡Π = subset* (red D₁)
        ⊢t≡t = ≅-conv (escapeTermEq {l = ι ⁰} [B] (reflEqTerm {l = ι ⁰} [B] [t])) ⊢B≡Π
        cast~cast = ~-conv (~-castΠΠ%! (un-univ ⊢F₁) (un-univ ⊢G₁) (≅-un-univ A₁≡A₁) (un-univ ⊢F) (un-univ ⊢G) (≅-un-univ A≡A) ⊢t≡t) (sym ⊢A≡Π)       
    in neuTerm:⇒*: {t = cast ⁰ B A e t} [A]
                                  castΠΠ%!ₙ (transTerm:⇒:* (CastRed*Term ⊢A ⊢e ⊢t (un-univ:⇒*: D₁))
                                                   (CastRed*TermΠ (un-univ ⊢F₁ ) (un-univ ⊢G₁) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A) )) (un-univ≡ ⊢B≡Π)
                                                                  (refl (un-univ ⊢A))))) (conv ⊢t ⊢B≡Π) D)) cast~cast)
[cast] {A} {B} {Γ} {r = !} ⊢Γ (Πᵣ′ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢ΠFG , D ]] ⊢F ⊢G A≡A [F] [G] G-ext)
  (Πᵣ′ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢B , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext) =
  [cast]₁ , [cast]₂
  where
    module b₁ = cast-ΠΠ-lemmas ⊢Γ ⊢F [F] ⊢F₁ [F₁]
                               (λ [ρ] ⊢Δ → proj₂ ([cast] ⊢Δ ([F] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ)))
                               (λ [ρ] ⊢Δ → proj₂ ([castext] ⊢Δ ([F] [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) (reflEq ([F] [ρ] ⊢Δ)) ([F₁] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ) (reflEq ([F₁] [ρ] ⊢Δ))))
    module b₂ = cast-ΠΠ-lemmas ⊢Γ ⊢F₁ [F₁] ⊢F [F]
                               (λ [ρ] ⊢Δ → proj₁ ([cast] ⊢Δ ([F] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ)))
                               (λ [ρ] ⊢Δ → proj₁ ([castext] ⊢Δ ([F] [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) (reflEq ([F] [ρ] ⊢Δ)) ([F₁] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ) (reflEq ([F₁] [ρ] ⊢Δ))))

    [A] = (Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢ΠFG , D ]] ⊢F ⊢G A≡A [F] [G] G-ext)
    [B] = (Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢B , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)

    [cast]₁ : ∀ {t e} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ ! , ι ⁰ ] / [A])
      → (⊢e : Γ ⊢ e ∷ Id (U ⁰) A B ^ [ % , ι ¹ ])
      → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ∷ B ^ [ ! , ι ⁰ ] / [B]
    [cast]₁ {t} {e} (f , [[ ⊢t , ⊢f , Df ]] , funf , f≡f , [fext] , [f]) ⊢e = [castΠΠ]
      where
        open cast-ΠΠ-lemmas-2 ⊢Γ ⊢A ⊢ΠFG D ⊢F ⊢G A≡A [F] [G] G-ext ⊢B ⊢ΠF₁G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext ⊢e
                              (λ [ρ] ⊢Δ [x] [y] → proj₁ ([cast] ⊢Δ ([G] [ρ] ⊢Δ [x]) ([G₁] [ρ] ⊢Δ [y])))
                              (λ [ρ] ⊢Δ [x] [x′] [x≡x′] [y] [y′] [y≡y′] →
                                proj₁ ([castext] ⊢Δ ([G] [ρ] ⊢Δ [x]) ([G] [ρ] ⊢Δ [x′]) (G-ext [ρ] ⊢Δ [x] [x′] [x≡x′])
                                                    ([G₁] [ρ] ⊢Δ [y]) ([G₁] [ρ] ⊢Δ [y′]) (G₁-ext [ρ] ⊢Δ [y] [y′] [y≡y′])))
                              ⊢t Df [fext] [f] b₁.[b] b₁.[bext]

    [cast]₂ : ∀ {t e} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ B ^ [ ! , ι ⁰ ] / [B])
      → (⊢e : Γ ⊢ e ∷ Id (U ⁰) B A ^ [ % , ι ¹ ])
      → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ B A e t ∷ A ^ [ ! , ι ⁰ ] / [A]
    [cast]₂ {t} {e} (f , [[ ⊢t , ⊢f , Df ]] , funf , f≡f , [fext] , [f]) ⊢e = [castΠΠ]
      where
        open cast-ΠΠ-lemmas-2 ⊢Γ ⊢B ⊢ΠF₁G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext ⊢A ⊢ΠFG D ⊢F ⊢G A≡A [F] [G] G-ext ⊢e
                              (λ [ρ] ⊢Δ [y] [x] → proj₂ ([cast] ⊢Δ ([G] [ρ] ⊢Δ [x]) ([G₁] [ρ] ⊢Δ [y])))
                              (λ [ρ] ⊢Δ [y] [y′] [y≡y′] [x] [x′] [x≡x′] →
                                proj₂ ([castext] ⊢Δ ([G] [ρ] ⊢Δ [x]) ([G] [ρ] ⊢Δ [x′]) (G-ext [ρ] ⊢Δ [x] [x′] [x≡x′])
                                                    ([G₁] [ρ] ⊢Δ [y]) ([G₁] [ρ] ⊢Δ [y′]) (G₁-ext [ρ] ⊢Δ [y] [y′] [y≡y′])))
                              ⊢t Df [fext] [f] b₂.[b] b₂.[bext]
[cast] {A} {B} {Γ} {r = !} ⊢Γ (Πᵣ′ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢ΠFG , D ]] ⊢F ⊢G A≡A [F] [G] G-ext)
  (Πᵣ′ % .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢B , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext) =
  [cast]₁ , [cast]₂
  where
    module b₁ = cast-ΠΠ-lemmas ⊢Γ ⊢F [F] ⊢F₁ [F₁]
                               (λ [ρ] ⊢Δ → proj₂ ([cast] ⊢Δ ([F] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ)))
                               (λ [ρ] ⊢Δ → proj₂ ([castext] ⊢Δ ([F] [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) (reflEq ([F] [ρ] ⊢Δ)) ([F₁] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ) (reflEq ([F₁] [ρ] ⊢Δ))))
    module b₂ = cast-ΠΠ-lemmas ⊢Γ ⊢F₁ [F₁] ⊢F [F]
                               (λ [ρ] ⊢Δ → proj₁ ([cast] ⊢Δ ([F] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ)))
                               (λ [ρ] ⊢Δ → proj₁ ([castext] ⊢Δ ([F] [ρ] ⊢Δ) ([F] [ρ] ⊢Δ) (reflEq ([F] [ρ] ⊢Δ)) ([F₁] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ) (reflEq ([F₁] [ρ] ⊢Δ))))

    [A] = (Πᵣ′ % ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G [[ ⊢A , ⊢ΠFG , D ]] ⊢F ⊢G A≡A [F] [G] G-ext)
    [B] = (Πᵣ′ % ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢B , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)

    [cast]₁ : ∀ {t e} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ ! , ι ⁰ ] / [A])
      → (⊢e : Γ ⊢ e ∷ Id (U ⁰) A B ^ [ % , ι ¹ ])
      → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ∷ B ^ [ ! , ι ⁰ ] / [B]
    [cast]₁ {t} {e} (f , [[ ⊢t , ⊢f , Df ]] , funf , f≡f , [fext] , [f]) ⊢e = [castΠΠ]
      where
        open cast-ΠΠ-lemmas-2 ⊢Γ ⊢A ⊢ΠFG D ⊢F ⊢G A≡A [F] [G] G-ext ⊢B ⊢ΠF₁G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext ⊢e
                              (λ [ρ] ⊢Δ [x] [y] → proj₁ ([cast] ⊢Δ ([G] [ρ] ⊢Δ [x]) ([G₁] [ρ] ⊢Δ [y])))
                              (λ [ρ] ⊢Δ [x] [x′] [x≡x′] [y] [y′] [y≡y′] →
                                proj₁ ([castext] ⊢Δ ([G] [ρ] ⊢Δ [x]) ([G] [ρ] ⊢Δ [x′]) (G-ext [ρ] ⊢Δ [x] [x′] [x≡x′])
                                                    ([G₁] [ρ] ⊢Δ [y]) ([G₁] [ρ] ⊢Δ [y′]) (G₁-ext [ρ] ⊢Δ [y] [y′] [y≡y′])))
                              ⊢t Df [fext] [f] b₁.[b] b₁.[bext]

    [cast]₂ : ∀ {t e} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ B ^ [ ! , ι ⁰ ] / [B])
      → (⊢e : Γ ⊢ e ∷ Id (U ⁰) B A ^ [ % , ι ¹ ])
      → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ B A e t ∷ A ^ [ ! , ι ⁰ ] / [A]
    [cast]₂ {t} {e} (f , [[ ⊢t , ⊢f , Df ]] , funf , f≡f , [fext] , [f]) ⊢e = [castΠΠ]
      where
        open cast-ΠΠ-lemmas-2 ⊢Γ ⊢B ⊢ΠF₁G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext ⊢A ⊢ΠFG D ⊢F ⊢G A≡A [F] [G] G-ext ⊢e
                              (λ [ρ] ⊢Δ [y] [x] → proj₂ ([cast] ⊢Δ ([G] [ρ] ⊢Δ [x]) ([G₁] [ρ] ⊢Δ [y])))
                              (λ [ρ] ⊢Δ [y] [y′] [y≡y′] [x] [x′] [x≡x′] →
                                proj₂ ([castext] ⊢Δ ([G] [ρ] ⊢Δ [x]) ([G] [ρ] ⊢Δ [x′]) (G-ext [ρ] ⊢Δ [x] [x′] [x≡x′])
                                                    ([G₁] [ρ] ⊢Δ [y]) ([G₁] [ρ] ⊢Δ [y′]) (G₁-ext [ρ] ⊢Δ [y] [y′] [y≡y′])))
                              ⊢t Df [fext] [f] b₂.[b] b₂.[bext]
-}
{-
[castext] {A₁} {A₂} {A₃} {A₄} {Γ} {r = !} ⊢Γ
  (Πᵣ′ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)
  (Πᵣ′ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₂ G₂ [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]] ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext)
  (Π₌ F₂′ G₂′ D₂′ A₁≡A₂′ [F₁≡F₂′] [G₁≡G₂′])
  (Πᵣ′ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₃ G₃ [[ ⊢A₃ , ⊢ΠF₃G₃ , D₃ ]] ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext)
  (Πᵣ′ ! .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₄ G₄ [[ ⊢A₄ , ⊢ΠF₄G₄ , D₄ ]] ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext)
  (Π₌ F₄′ G₄′ D₄′ A₃≡A₄′ [F₃≡F₄′] [G₃≡G₄′]) =
     ([castext]₁ , [castext]₂)
   where
      module b₁ = cast-ΠΠ-lemmas ⊢Γ ⊢F₁ [F₁] ⊢F₃ [F₃]
                                 (λ [ρ] ⊢Δ → proj₂ ([cast] ⊢Δ ([F₁] [ρ] ⊢Δ) ([F₃] [ρ] ⊢Δ)))
                                 (λ [ρ] ⊢Δ → proj₂ ([castext] ⊢Δ ([F₁] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ) (reflEq ([F₁] [ρ] ⊢Δ)) ([F₃] [ρ] ⊢Δ) ([F₃] [ρ] ⊢Δ) (reflEq ([F₃] [ρ] ⊢Δ))))
      module b₂ = cast-ΠΠ-lemmas ⊢Γ ⊢F₂ [F₂] ⊢F₄ [F₄]
                                 (λ [ρ] ⊢Δ → proj₂ ([cast] ⊢Δ ([F₂] [ρ] ⊢Δ) ([F₄] [ρ] ⊢Δ)))
                                 (λ [ρ] ⊢Δ → proj₂ ([castext] ⊢Δ ([F₂] [ρ] ⊢Δ) ([F₂] [ρ] ⊢Δ) (reflEq ([F₂] [ρ] ⊢Δ)) ([F₄] [ρ] ⊢Δ) ([F₄] [ρ] ⊢Δ) (reflEq ([F₄] [ρ] ⊢Δ))))
      module b₃ = cast-ΠΠ-lemmas ⊢Γ ⊢F₃ [F₃] ⊢F₁ [F₁]
                                 (λ [ρ] ⊢Δ → proj₁ ([cast] ⊢Δ ([F₁] [ρ] ⊢Δ) ([F₃] [ρ] ⊢Δ)))
                                 (λ [ρ] ⊢Δ → proj₁ ([castext] ⊢Δ ([F₁] [ρ] ⊢Δ) ([F₁] [ρ] ⊢Δ) (reflEq ([F₁] [ρ] ⊢Δ)) ([F₃] [ρ] ⊢Δ) ([F₃] [ρ] ⊢Δ) (reflEq ([F₃] [ρ] ⊢Δ))))
      module b₄ = cast-ΠΠ-lemmas ⊢Γ ⊢F₄ [F₄] ⊢F₂ [F₂]
                                 (λ [ρ] ⊢Δ → proj₁ ([cast] ⊢Δ ([F₂] [ρ] ⊢Δ) ([F₄] [ρ] ⊢Δ)))
                                 (λ [ρ] ⊢Δ → proj₁ ([castext] ⊢Δ ([F₂] [ρ] ⊢Δ) ([F₂] [ρ] ⊢Δ) (reflEq ([F₂] [ρ] ⊢Δ)) ([F₄] [ρ] ⊢Δ) ([F₄] [ρ] ⊢Δ) (reflEq ([F₄] [ρ] ⊢Δ))))

      [A₁] = (Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ [[ ⊢A₁ , ⊢ΠF₁G₁ , D₁ ]] ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext)
      [A₂] = (Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₂ G₂ [[ ⊢A₂ , ⊢ΠF₂G₂ , D₂ ]] ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext)
      [A₁≡A₂] = (Π₌ F₂′ G₂′ D₂′ A₁≡A₂′ [F₁≡F₂′] [G₁≡G₂′])
      [A₃] = (Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₃ G₃ [[ ⊢A₃ , ⊢ΠF₃G₃ , D₃ ]] ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext)
      [A₄] = (Πᵣ′ ! ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₄ G₄ [[ ⊢A₄ , ⊢ΠF₄G₄ , D₄ ]] ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext)
      [A₃≡A₄] = (Π₌ F₄′ G₄′ D₄′ A₃≡A₄′ [F₃≡F₄′] [G₃≡G₄′])

      Π≡Π = whrDet* (D₂ , Whnf.Πₙ) (D₂′ , Whnf.Πₙ)
      F₂≡F₂′ = let x , _ , _ , _ , _ = Π-PE-injectivity Π≡Π in x
      G₂≡G₂′ = let _ , _ , _ , x , _ = Π-PE-injectivity Π≡Π in x
      Π≡Π′ = whrDet* (D₄ , Whnf.Πₙ) (D₄′ , Whnf.Πₙ)
      F₄≡F₄′ = let x , _ , _ , _ , _ = Π-PE-injectivity Π≡Π′ in x
      G₄≡G₄′ = let _ , _ , _ , x , _ = Π-PE-injectivity Π≡Π′ in x

      A₁≡A₂ = PE.subst₂ (λ X Y → Γ ⊢ Π F₁ ^ ! ° ⁰ ▹ G₁ ° ⁰ ≅ Π X ^ ! ° ⁰ ▹ Y ° ⁰ ^ [ ! , ι ⁰ ]) (PE.sym F₂≡F₂′) (PE.sym G₂≡G₂′) A₁≡A₂′
      A₃≡A₄ = PE.subst₂ (λ X Y → Γ ⊢ Π F₃ ^ ! ° ⁰ ▹ G₃ ° ⁰ ≅ Π X ^ ! ° ⁰ ▹ Y ° ⁰ ^ [ ! , ι ⁰ ]) (PE.sym F₄≡F₄′) (PE.sym G₄≡G₄′) A₃≡A₄′
      [F₁≡F₂] = PE.subst (λ X → ∀ {ρ Δ} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Δ ⊩⟨ ι ⁰ ⟩ wk ρ F₁ ≡ wk ρ X ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
                         (PE.sym F₂≡F₂′) [F₁≡F₂′]
      [F₃≡F₄] = PE.subst (λ X → ∀ {ρ Δ} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → Δ ⊩⟨ ι ⁰ ⟩ wk ρ F₃ ≡ wk ρ X ^ [ ! , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
                         (PE.sym F₄≡F₄′) [F₃≡F₄′]
      [G₁≡G₂] = PE.subst (λ X → ∀ {ρ Δ a} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
                                → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F₁ ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
                                → Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₁ [ a ] ≡ wk (lift ρ) X [ a ] ^ [ ! , ι ⁰ ] / [G₁] [ρ] ⊢Δ [a])
                         (PE.sym G₂≡G₂′) [G₁≡G₂′]
      [G₃≡G₄] = PE.subst (λ X → ∀ {ρ Δ a} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
                                → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F₃ ^ [ ! , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
                                → Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G₃ [ a ] ≡ wk (lift ρ) X [ a ] ^ [ ! , ι ⁰ ] / [G₃] [ρ] ⊢Δ [a])
                         (PE.sym G₄≡G₄′) [G₃≡G₄′]

      [b₁≡b₂] : ∀ {ρ Δ e₁₃ e₂₄ x₃ x₄} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          → (Δ ⊢ e₁₃ ∷ Id (U ⁰) (wk ρ F₁) (wk ρ F₃) ^ [ % , ι ¹ ])
          → (Δ ⊢ e₂₄ ∷ Id (U ⁰) (wk ρ F₂) (wk ρ F₄) ^ [ % , ι ¹ ])
          → (Δ ⊩⟨ ι ⁰ ⟩ x₃ ∷ wk ρ F₃ ^ [ ! , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
          → (Δ ⊩⟨ ι ⁰ ⟩ x₄ ∷ wk ρ F₄ ^ [ ! , ι ⁰ ] / [F₄] [ρ] ⊢Δ)
          → (Δ ⊩⟨ ι ⁰ ⟩ x₃ ≡ x₄ ∷ wk ρ F₃ ^ [ ! , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
          → Δ ⊩⟨ ι ⁰ ⟩ b₁.b ρ e₁₃ x₃ ≡ b₂.b ρ e₂₄ x₄ ∷ wk ρ F₁ ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ
      [b₁≡b₂] [ρ] ⊢Δ ⊢e₁₃ ⊢e₂₄ [x₃] [x₄] [x₃≡x₄] =
        let
          ⊢e₃₁ = Idsymⱼ (univ 0<1 ⊢Δ) (un-univ (escape ([F₁] [ρ] ⊢Δ)))
            (un-univ (escape ([F₃] [ρ] ⊢Δ))) ⊢e₁₃
          ⊢e₄₂ = Idsymⱼ (univ 0<1 ⊢Δ) (un-univ (escape ([F₂] [ρ] ⊢Δ)))
            (un-univ (escape ([F₄] [ρ] ⊢Δ))) ⊢e₂₄
        in proj₂ ([castext] ⊢Δ ([F₁] [ρ] ⊢Δ) ([F₂] [ρ] ⊢Δ) ([F₁≡F₂] [ρ] ⊢Δ) ([F₃] [ρ] ⊢Δ) ([F₄] [ρ] ⊢Δ) ([F₃≡F₄] [ρ] ⊢Δ)) [x₃] [x₄] [x₃≡x₄] ⊢e₃₁ ⊢e₄₂

      [b₃≡b₄] : ∀ {ρ Δ e₃₁ e₄₂ x₁ x₂} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          → (Δ ⊢ e₃₁ ∷ Id (U ⁰) (wk ρ F₃) (wk ρ F₁) ^ [ % , ι ¹ ])
          → (Δ ⊢ e₄₂ ∷ Id (U ⁰) (wk ρ F₄) (wk ρ F₂) ^ [ % , ι ¹ ])
          → (Δ ⊩⟨ ι ⁰ ⟩ x₁ ∷ wk ρ F₁ ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
          → (Δ ⊩⟨ ι ⁰ ⟩ x₂ ∷ wk ρ F₂ ^ [ ! , ι ⁰ ] / [F₂] [ρ] ⊢Δ)
          → (Δ ⊩⟨ ι ⁰ ⟩ x₁ ≡ x₂ ∷ wk ρ F₁ ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
          → Δ ⊩⟨ ι ⁰ ⟩ b₃.b ρ e₃₁ x₁ ≡ b₄.b ρ e₄₂ x₂ ∷ wk ρ F₃ ^ [ ! , ι ⁰ ] / [F₃] [ρ] ⊢Δ
      [b₃≡b₄] [ρ] ⊢Δ ⊢e₃₁ ⊢e₄₂ [x₁] [x₂] [x₁≡x₂] =
        let
          ⊢e₁₃ = Idsymⱼ (univ 0<1 ⊢Δ) (un-univ (escape ([F₃] [ρ] ⊢Δ)))
            (un-univ (escape ([F₁] [ρ] ⊢Δ))) ⊢e₃₁
          ⊢e₂₄ = Idsymⱼ (univ 0<1 ⊢Δ) (un-univ (escape ([F₄] [ρ] ⊢Δ)))
            (un-univ (escape ([F₂] [ρ] ⊢Δ))) ⊢e₄₂
        in proj₁ ([castext] ⊢Δ ([F₁] [ρ] ⊢Δ) ([F₂] [ρ] ⊢Δ) ([F₁≡F₂] [ρ] ⊢Δ) ([F₃] [ρ] ⊢Δ) ([F₄] [ρ] ⊢Δ) ([F₃≡F₄] [ρ] ⊢Δ)) [x₁] [x₂] [x₁≡x₂] ⊢e₁₃ ⊢e₂₄

      [castext]₁ : (∀ {t₁ t₂ e₁₃ e₂₄} → ([t₁] : Γ ⊩⟨ ι ⁰ ⟩ t₁ ∷ A₁ ^ [ ! , ι ⁰ ] / [A₁])
                        → ([t₁] : Γ ⊩⟨ ι ⁰ ⟩ t₂ ∷ A₂ ^ [ ! , ι ⁰ ] / [A₂])
                        → ([t₁≡t₂] : Γ ⊩⟨ ι ⁰ ⟩ t₁ ≡ t₂ ∷ A₁ ^ [ ! , ι ⁰ ] / [A₁])
                        → (⊢e₁₃ : Γ ⊢ e₁₃ ∷ Id (U ⁰) A₁ A₃ ^ [ % , ι ¹ ])
                        → (⊢e₂₄ : Γ ⊢ e₂₄ ∷ Id (U ⁰) A₂ A₄ ^ [ % , ι ¹ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A₁ A₃ e₁₃ t₁ ≡ cast ⁰ A₂ A₄ e₂₄ t₂ ∷ A₃ ^ [ ! , ι ⁰ ] / [A₃])
      [castext]₁ {t₁} {t₂} {e₁₃} {e₂₄}
        (f₁ , [[ ⊢t₁ , ⊢f₁ , Df₁ ]] , funf₁ , f₁≡f₁ , [f₁ext] , [f₁])
        (f₂ , [[ ⊢t₂ , ⊢f₂ , Df₂ ]] , funf₂ , f₂≡f₂ , [f₂ext] , [f₂])
        (f₁′ , f₂′ , [[ _ , ⊢f₁′ , Df₁′ ]] , [[ _ , ⊢f₂′ , Df₂′ ]] , funf₁′ , funf₂′ , _ , _ , _ , [f₁′≡f₂′])
        ⊢e₁₃ ⊢e₂₄ =
          ( (lam F₃ ▹ g₁.g (step id) (var 0))
          , (lam F₄ ▹ g₂.g (step id) (var 0))
          , g₁.Dg
          , conv:* g₂.Dg (sym (≅-eq A₃≡A₄))
          , lamₙ
          , lamₙ
          , g₁≡g₂
          , g₁.[castΠΠ]
          , convTerm₂ [A₃] [A₄] [A₃≡A₄] g₂.[castΠΠ]
          , [g₁a≡g₂a] )
          where
            f₁≡f₁′ = whrDet*Term (Df₁ , functionWhnf funf₁) (Df₁′ , functionWhnf funf₁′)
            f₂≡f₂′ = whrDet*Term (Df₂ , functionWhnf funf₂) (Df₂′ , functionWhnf funf₂′)
            [f₁≡f₂] = PE.subst₂ (λ X Y → ∀ {ρ Δ a} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F₁ ^ [ ! , ι ⁰ ] / [F₁] [ρ] ⊢Δ)
              → Δ ⊩⟨ ι ⁰ ⟩ wk ρ X ∘ a ≡ wk ρ Y ∘ a ∷ wk (lift ρ) G₁ [ a ] ^ [ ! , ι ⁰ ] / [G₁] [ρ] ⊢Δ [a]) (PE.sym f₁≡f₁′) (PE.sym f₂≡f₂′) [f₁′≡f₂′]

            open cast-ΠΠ-lemmas-3 ⊢Γ ⊢A₁ ⊢ΠF₁G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext
              ⊢A₂ ⊢ΠF₂G₂ D₂ ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext
              ⊢A₃ ⊢ΠF₃G₃ D₃ ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext
              ⊢A₄ ⊢ΠF₄G₄ D₄ ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext
              A₁≡A₂ A₃≡A₄ [F₁≡F₂] [F₃≡F₄] [G₁≡G₂] [G₃≡G₄]
              ⊢e₁₃ ⊢e₂₄
              ⊢t₁ Df₁ [f₁ext] [f₁]
              ⊢t₂ Df₂ [f₂ext] [f₂]
              [f₁≡f₂]
              (λ [ρ] ⊢Δ [x] [y] → proj₁ ([cast] ⊢Δ ([G₁] [ρ] ⊢Δ [x]) ([G₃] [ρ] ⊢Δ [y])))
              (λ [ρ] ⊢Δ [x] [y] → proj₁ ([cast] ⊢Δ ([G₂] [ρ] ⊢Δ [x]) ([G₄] [ρ] ⊢Δ [y])))
              (λ [ρ] ⊢Δ [x] [x′] [x≡x′] [y] [y′] [y≡y′] →
                proj₁ ([castext] ⊢Δ ([G₁] [ρ] ⊢Δ [x]) ([G₁] [ρ] ⊢Δ [x′]) (G₁-ext [ρ] ⊢Δ [x] [x′] [x≡x′])
                                    ([G₃] [ρ] ⊢Δ [y]) ([G₃] [ρ] ⊢Δ [y′]) (G₃-ext [ρ] ⊢Δ [y] [y′] [y≡y′])))
              (λ [ρ] ⊢Δ [x] [x′] [x≡x′] [y] [y′] [y≡y′] →
                proj₁ ([castext] ⊢Δ ([G₂] [ρ] ⊢Δ [x]) ([G₂] [ρ] ⊢Δ [x′]) (G₂-ext [ρ] ⊢Δ [x] [x′] [x≡x′])
                                    ([G₄] [ρ] ⊢Δ [y]) ([G₄] [ρ] ⊢Δ [y′]) (G₄-ext [ρ] ⊢Δ [y] [y′] [y≡y′])))
              (λ [ρ] ⊢Δ [x₁] [x₂] [G₁x₁≡G₂x₂] [x₃] [x₄] [G₃x₃≡G₄x₄] →
                proj₁ ([castext] ⊢Δ ([G₁] [ρ] ⊢Δ [x₁]) ([G₂] [ρ] ⊢Δ [x₂]) [G₁x₁≡G₂x₂]
                                    ([G₃] [ρ] ⊢Δ [x₃]) ([G₄] [ρ] ⊢Δ [x₄]) [G₃x₃≡G₄x₄]))
              b₁.[b] b₁.[bext] b₂.[b] b₂.[bext] [b₁≡b₂]

      [castext]₂ : (∀ {t₃ t₄ e₃₁ e₄₂} → ([t₃] : Γ ⊩⟨ ι ⁰ ⟩ t₃ ∷ A₃ ^ [ ! , ι ⁰ ] / [A₃])
                        → ([t₄] : Γ ⊩⟨ ι ⁰ ⟩ t₄ ∷ A₄ ^ [ ! , ι ⁰ ] / [A₄])
                        → ([t₃≡t₄] : Γ ⊩⟨ ι ⁰ ⟩ t₃ ≡ t₄ ∷ A₃ ^ [ ! , ι ⁰ ] / [A₃])
                        → (⊢e₃₁ : Γ ⊢ e₃₁ ∷ Id (U ⁰) A₃ A₁ ^ [ % , ι ¹ ])
                        → (⊢e₄₂ : Γ ⊢ e₄₂ ∷ Id (U ⁰) A₄ A₂ ^ [ % , ι ¹ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A₃ A₁ e₃₁ t₃ ≡ cast ⁰ A₄ A₂ e₄₂ t₄ ∷ A₁ ^ [ ! , ι ⁰ ] / [A₁])
      [castext]₂ {t₃} {t₄} {e₃₁} {e₄₂}
        (f₃ , [[ ⊢t₃ , ⊢f₃ , Df₃ ]] , funf₃ , f₃≡f₃ , [f₃ext] , [f₃])
        (f₄ , [[ ⊢t₄ , ⊢f₄ , Df₄ ]] , funf₄ , f₄≡f₄ , [f₄ext] , [f₄])
        (f₃′ , f₄′ , [[ _ , ⊢f₃′ , Df₃′ ]] , [[ _ , ⊢f₄′ , Df₄′ ]] , funf₃′ , funf₄′ , _ , _ , _ , [f₃′≡f₄′])
        ⊢e₃₁ ⊢e₄₂ =
          ( (lam F₁ ▹ g₁.g (step id) (var 0))
          , (lam F₂ ▹ g₂.g (step id) (var 0))
          , g₁.Dg
          , conv:* g₂.Dg (sym (≅-eq A₁≡A₂))
          , lamₙ
          , lamₙ
          , g₁≡g₂
          , g₁.[castΠΠ]
          , convTerm₂ [A₁] [A₂] [A₁≡A₂] g₂.[castΠΠ]
          , [g₁a≡g₂a] )
          where
            f₃≡f₃′ = whrDet*Term (Df₃ , functionWhnf funf₃) (Df₃′ , functionWhnf funf₃′)
            f₄≡f₄′ = whrDet*Term (Df₄ , functionWhnf funf₄) (Df₄′ , functionWhnf funf₄′)
            [f₃≡f₄] = PE.subst₂ (λ X Y → ∀ {ρ Δ a} → ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F₃ ^ [ ! , ι ⁰ ] / [F₃] [ρ] ⊢Δ)
              → Δ ⊩⟨ ι ⁰ ⟩ wk ρ X ∘ a ≡ wk ρ Y ∘ a ∷ wk (lift ρ) G₃ [ a ] ^ [ ! , ι ⁰ ] / [G₃] [ρ] ⊢Δ [a]) (PE.sym f₃≡f₃′) (PE.sym f₄≡f₄′) [f₃′≡f₄′]

            open cast-ΠΠ-lemmas-3 ⊢Γ ⊢A₃ ⊢ΠF₃G₃ D₃ ⊢F₃ ⊢G₃ A₃≡A₃ [F₃] [G₃] G₃-ext
              ⊢A₄ ⊢ΠF₄G₄ D₄ ⊢F₄ ⊢G₄ A₄≡A₄ [F₄] [G₄] G₄-ext
              ⊢A₁ ⊢ΠF₁G₁ D₁ ⊢F₁ ⊢G₁ A₁≡A₁ [F₁] [G₁] G₁-ext
              ⊢A₂ ⊢ΠF₂G₂ D₂ ⊢F₂ ⊢G₂ A₂≡A₂ [F₂] [G₂] G₂-ext
              A₃≡A₄ A₁≡A₂ [F₃≡F₄] [F₁≡F₂] [G₃≡G₄] [G₁≡G₂]
              ⊢e₃₁ ⊢e₄₂
              ⊢t₃ Df₃ [f₃ext] [f₃]
              ⊢t₄ Df₄ [f₄ext] [f₄]
              [f₃≡f₄]
              (λ [ρ] ⊢Δ [y] [x] → proj₂ ([cast] ⊢Δ ([G₁] [ρ] ⊢Δ [x]) ([G₃] [ρ] ⊢Δ [y])))
              (λ [ρ] ⊢Δ [y] [x] → proj₂ ([cast] ⊢Δ ([G₂] [ρ] ⊢Δ [x]) ([G₄] [ρ] ⊢Δ [y])))
              (λ [ρ] ⊢Δ [y] [y′] [y≡y′] [x] [x′] [x≡x′] →
                proj₂ ([castext] ⊢Δ ([G₁] [ρ] ⊢Δ [x]) ([G₁] [ρ] ⊢Δ [x′]) (G₁-ext [ρ] ⊢Δ [x] [x′] [x≡x′])
                                    ([G₃] [ρ] ⊢Δ [y]) ([G₃] [ρ] ⊢Δ [y′]) (G₃-ext [ρ] ⊢Δ [y] [y′] [y≡y′])))
              (λ [ρ] ⊢Δ [y] [y′] [y≡y′] [x] [x′] [x≡x′] →
                proj₂ ([castext] ⊢Δ ([G₂] [ρ] ⊢Δ [x]) ([G₂] [ρ] ⊢Δ [x′]) (G₂-ext [ρ] ⊢Δ [x] [x′] [x≡x′])
                                    ([G₄] [ρ] ⊢Δ [y]) ([G₄] [ρ] ⊢Δ [y′]) (G₄-ext [ρ] ⊢Δ [y] [y′] [y≡y′])))
              (λ [ρ] ⊢Δ [x₃] [x₄] [G₃x₃≡G₄x₄] [x₁] [x₂] [G₁x₁≡G₂x₂] →
                proj₂ ([castext] ⊢Δ ([G₁] [ρ] ⊢Δ [x₁]) ([G₂] [ρ] ⊢Δ [x₂]) [G₁x₁≡G₂x₂]
                                    ([G₃] [ρ] ⊢Δ [x₃]) ([G₄] [ρ] ⊢Δ [x₄]) [G₃x₃≡G₄x₄]))
              b₃.[b] b₃.[bext] b₄.[b] b₄.[bext] [b₃≡b₄]
-}
[castext] {A} {C} {B} {D} {Γ} ⊢Γ [A] [C] [A≡C] [B] [D] [B≡D] = [castextShape] ⊢Γ [A] [C] (goodCases [A] [C] [A≡C]) [A≡C] [B] [D] (goodCases [B] [D] [B≡D]) [B≡D]


{-

cast∞ : ∀ {A B r t e Γ}
         (⊢Γ : ⊢ Γ)
         ([U] : Γ ⊩⟨ ∞ ⟩ Univ r ⁰ ^ [ ! , ι ¹ ])
         ([AU] : Γ ⊩⟨ ∞ ⟩ A ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [U])
         ([BU] : Γ ⊩⟨ ∞ ⟩ B ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [U])
         ([A] : Γ ⊩⟨ ∞ ⟩ A ^ [ r , ι ⁰ ])
         ([B] : Γ ⊩⟨ ∞ ⟩ B ^ [ r , ι ⁰ ])
         ([t] : Γ ⊩⟨ ∞ ⟩ t ∷ A ^ [ r , ι ⁰ ] / [A])
         ([Id] : Γ ⊩⟨ ∞ ⟩ Id (Univ r ⁰) A B ^ [ % , ι ¹ ]) →
         ([e] : Γ ⊩⟨ ∞ ⟩ e ∷ Id (Univ r ⁰) A B ^ [ % , ι ¹ ] / [Id] ) →
         Γ ⊩⟨ ∞ ⟩ cast ⁰ A B e t ∷ B ^ [ r , ι ⁰ ] / [B]
cast∞ {A} {B} {r} {t} {e} {Γ} ⊢Γ [U] [AU] [BU] [A] [B] [t] [Id] [e] =
  let
    [A]′ : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ r , ι ⁰ ]
    [A]′ = univEq [U] [AU]
    [B]′ : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ r , ι ⁰ ]
    [B]′ = univEq [U] [BU]
    [t]′ : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ r , ι ⁰ ] / [A]′
    [t]′ = irrelevanceTerm [A] (emb ∞< (emb emb< [A]′)) [t]
    ⊢e : Γ ⊢ e ∷ Id (Univ r ⁰) A B ^ [ % , ι ¹ ]
    ⊢e = escapeTerm [Id] [e]
    x : Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ∷ B ^ [ r , ι ⁰ ] / [B]′
    x = proj₁ ([cast] ⊢Γ [A]′ [B]′) [t]′ ⊢e
  in irrelevanceTerm (emb ∞< (emb emb< [B]′)) [B] x


castᵗᵛ : ∀ {A B r t e Γ}
         ([Γ] : ⊩ᵛ Γ)
         ([U] : Γ ⊩ᵛ⟨ ∞ ⟩ Univ r ⁰ ^ [ ! , ι ¹ ] / [Γ])
         ([AU] : Γ ⊩ᵛ⟨ ∞ ⟩ A ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [Γ] / [U])
         ([BU] : Γ ⊩ᵛ⟨ ∞ ⟩ B ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [Γ] / [U])
         ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ r , ι ⁰ ] / [Γ])
         ([B] : Γ ⊩ᵛ⟨ ∞ ⟩ B ^ [ r , ι ⁰ ] / [Γ])
         ([t] : Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ [ r , ι ⁰ ] / [Γ] / [A])
         ([Id] : Γ ⊩ᵛ⟨ ∞ ⟩ Id (Univ r ⁰) A B ^ [ % , ι ¹ ] / [Γ]) →
         ([e] : Γ ⊩ᵛ⟨ ∞ ⟩ e ∷ Id (Univ r ⁰) A B ^ [ % , ι ¹ ] / [Γ] / [Id] ) →
         Γ ⊩ᵛ⟨ ∞ ⟩ cast ⁰ A B e t ∷ B ^ [ r , ι ⁰ ] / [Γ] / [B]
castᵗᵛ {A} {B} {t} {e} {Γ} [Γ] [U] [AU] [BU] [A] [B] [t] [Id] [e] ⊢Δ [σ] =
  cast∞ ⊢Δ (proj₁ ([U] ⊢Δ [σ])) (proj₁ ([AU] ⊢Δ [σ])) (proj₁ ([BU] ⊢Δ [σ]))
    (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([B] ⊢Δ [σ]))
    (proj₁ ([t] ⊢Δ [σ])) (proj₁ ([Id] ⊢Δ [σ])) (proj₁ ([e] ⊢Δ [σ]))
  , {!!}

cast-congᵗᵛ : ∀ {A A' B B' t t' e e' Γ}
         ([Γ] : ⊩ᵛ Γ) →
         ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ ! , ι ⁰ ] / [Γ])
         ([A'] : Γ ⊩ᵛ⟨ ∞ ⟩ A' ^ [ ! , ι ⁰ ] / [Γ])
         ([A≡A']ₜ : Γ ⊩ᵛ⟨ ∞ ⟩ A ≡ A' ^ [ ! , ι ⁰ ] / [Γ] / [A])
         ([B] : Γ ⊩ᵛ⟨ ∞ ⟩ B ^ [ ! , ι ⁰ ] / [Γ])
         ([B'] : Γ ⊩ᵛ⟨ ∞ ⟩ B' ^ [ ! , ι ⁰ ] / [Γ])
         ([B≡B']ₜ : Γ ⊩ᵛ⟨ ∞ ⟩ B ≡ B' ^ [ ! , ι ⁰ ] / [Γ] / [B] )
         ([t] : Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ [ ! , ι ⁰ ] / [Γ] / [A])
         ([t≡t']ₜ : Γ ⊩ᵛ⟨ ∞ ⟩ t ≡ t' ∷ A ^ [ ! , ι ⁰ ] / [Γ] / [A] )
         ([Id] : Γ ⊩ᵛ⟨ ∞ ⟩ Id (U ⁰) A B ^ [ % , ι ¹ ] / [Γ])
         ([e] : Γ ⊩ᵛ⟨ ∞ ⟩ e ∷ Id (U ⁰) A B ^ [ % , ι ¹ ] / [Γ] / [Id] )
         ([Id'] : Γ ⊩ᵛ⟨ ∞ ⟩ Id (U ⁰) A' B' ^ [ % , ι ¹ ] / [Γ])
         ([e'] : Γ ⊩ᵛ⟨ ∞ ⟩ e' ∷ Id (U ⁰) A' B' ^ [ % , ι ¹ ] / [Γ] / [Id'] ) →
         Γ ⊩ᵛ⟨ ∞ ⟩ cast ⁰ A B e t ≡ cast ⁰ A' B' e' t' ∷ B ^ [ ! , ι ⁰ ] / [Γ] / [B]
cast-congᵗᵛ = {!!}

-}
