{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.CastRefl {{eqrel : EqRelSet}} where
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
--open import Definition.LogicalRelation.Substitution.Introductions.Cast

open import Tools.Product
open import Tools.Empty using (⊥; ⊥-elim)
import Tools.Unit as TU
import Tools.PropositionalEquality as PE
import Data.Nat as Nat


[castrefl]ℕ : ∀ {A B t e Γ}
             (⊢Γ : ⊢ Γ)
             ([A] : Γ ⊩ℕ A)
             ([B] : Γ ⊩ℕ B) 
             ([A≡B] : Γ ⊩⟨ ι ⁰ ⟩ A ≡ B ^ [ ! , ι ⁰ ] / ℕᵣ [A])
             (⊢t : Γ ⊢ t ∷ A ^ [ ! , ι ⁰ ])
             ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ ! , ι ⁰ ] / ℕᵣ [A])
             (⊢e : Γ ⊢ e ∷ Id (U ⁰) A B ^ [ % , ι ⁰ ])
             → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ≡ t ∷ B ^ [ ! , ι ⁰ ] / ℕᵣ [B]
[castrefl]ℕ {e = e} ⊢Γ [[ ⊢A , ⊢ℕA , DA ]] [[ ⊢B , ⊢ℕB , DB ]] [A≡B] ⊢t (ℕₜ .(suc a) d n≡n (sucᵣ {a} (ℕₜ n [[ ⊢a , ⊢u , d₁ ]] n≡n₁ prop))) ⊢e =
  let ⊢eℕℕ = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* DA)) (un-univ≡ (subset* DB))))
      rec = [castrefl]ℕ ⊢Γ (idRed:*: ⊢ℕA) (idRed:*: ⊢ℕA) (reflEq {l = ι ⁰} (ℕᵣ (idRed:*: ⊢ℕA))) 
                       ⊢a (ℕₜ n [[ ⊢a , ⊢u , d₁ ]] n≡n₁ prop) ⊢eℕℕ
      cast≅ = escapeTermEq {l = ι ⁰} (ℕᵣ (idRed:*: ⊢ℕA)) rec
  in ℕₜ₌ (suc (cast ⁰ ℕ ℕ e a)) (suc a) (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B ⊢e ⊢t (un-univ:⇒*: [[ ⊢A , ⊢ℕA , DA ]]))
                                                   (transTerm:⇒:* (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* DA))
                                                                  (refl (un-univ ⊢B))))) (conv ⊢t (subset* DA)) [[ ⊢B , ⊢ℕB , DB ]])
                                                                  (conv:⇒*: (transTerm:⇒:* (CastRed*Termℕℕ ⊢eℕℕ d)
                                                                  (CastRed*Termℕsuc ⊢eℕℕ (escapeTerm {l = ι ⁰} (ℕᵣ (idRed:*: (univ (ℕⱼ ⊢Γ)))) (ℕₜ n [[ ⊢a , ⊢u , d₁ ]] n≡n₁ prop))))
                                                                  (sym (subset* DB))))) (subset* DB))
                                                  d (≅-suc-cong cast≅) (sucᵣ rec)
[castrefl]ℕ ⊢Γ [[ ⊢A , ⊢ℕA , DA ]] [[ ⊢B , ⊢ℕB , DB ]] [A≡B] ⊢t (ℕₜ .zero d n≡n zeroᵣ) ⊢e =
  let ⊢eℕℕ = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* DA)) (un-univ≡ (subset* DB))))
  in ℕₜ₌ zero zero (conv:⇒*: (transTerm:⇒:* (CastRed*Term ⊢B ⊢e ⊢t (un-univ:⇒*: [[ ⊢A , ⊢ℕA , DA ]]))
                                                   (transTerm:⇒:* (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* DA))
                                                                  (refl (un-univ ⊢B))))) (conv ⊢t (subset* DA)) [[ ⊢B , ⊢ℕB , DB ]])
                                                                  (conv:⇒*: (transTerm:⇒:* (CastRed*Termℕℕ ⊢eℕℕ d)
                                                                    (CastRed*Termℕzero ⊢eℕℕ)) (sym (subset* DB))))) (subset* DB))
         d (≅ₜ-zerorefl ⊢Γ) zeroᵣ
[castrefl]ℕ ⊢Γ [[ ⊢A , ⊢ℕA , DA ]] [[ ⊢B , ⊢ℕB , DB ]] [A≡B] ⊢t (ℕₜ n d n≡n (ne (neNfₜ neK ⊢k k≡k))) ⊢e =
  let ⊢eℕℕ = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) )) (un-univ≡ (subset* DA)) (un-univ≡ (subset* DB))))
      ⊢B≡B′ = escapeEq {l = ι ⁰} (ℕᵣ [[ ⊢B , ⊢ℕB , DB ]]) [A≡B]
  in neuEqTerm:⇒*: {l = ι ⁰} (ℕᵣ [[ ⊢B , ⊢ℕB , DB ]]) (castℕℕₙ neK) neK
                   (transTerm:⇒:* (CastRed*Term ⊢B ⊢e ⊢t (un-univ:⇒*: [[ ⊢A , ⊢ℕA , DA ]]))
                                                   (transTerm:⇒:* (CastRed*Termℕ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) ))(un-univ≡ (subset* DA))
                                                                  (refl (un-univ ⊢B))))) (conv ⊢t (subset* DA)) [[ ⊢B , ⊢ℕB , DB ]])
                                                                  (conv:⇒*: (CastRed*Termℕℕ ⊢eℕℕ d) (sym (subset* DB)))))
                   (conv:⇒*: d (sym (subset* DB))) (~-conv (~-castℕ-refl ⊢eℕℕ ⊢k neK) (sym (subset* DB))) 


[castrefl]Ne : ∀ {A B Γ}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩ne A ^[ ! , ⁰ ])
         ([B] : Γ ⊩ne B ^[ ! , ⁰ ])
         ([A≡B] : Γ ⊩⟨ ι ⁰ ⟩ A ≡ B ^ [ ! , ι ⁰ ] / ne [A])
       → (∀ {t e} → ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ ! , ι ⁰ ] / ne [A])
                        → (⊢e : Γ ⊢ e ∷ Id (U ⁰) A B ^ [ % , ι ⁰ ])
                        → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ≡ t ∷ B ^ [ ! , ι ⁰ ] / ne [B])
[castrefl]Ne {A} {B} ⊢Γ (ne K D neK K≡K) [B] (ne₌ M D′ neM K≡M) (neₜ k d (neNfₜ neK₁ ⊢k k≡k)) ⊢e = 
  let [A] = ne K D neK K≡K
      [[ ⊢A , ⊢K , DK ]] = D
      [A≡B] = ne₌ M D′ neM K≡M
      ⊢A≡K = subset* DK
      [[ ⊢B , _ , DM ]] = D′
      ⊢B≡M = subset* DM
      [[ ⊢tk , _ , dk ]] = d
      [t] = neₜ k d (neNfₜ neK₁ ⊢k k≡k)
      ⊢t = escapeTerm {l = ι ⁰} {A = A} (ne [A]) [t]
      ⊢e' = conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢A))) (un-univ≡ ⊢A≡K) (un-univ≡ ⊢B≡M))) 
  in neuEqTerm:⇒*: {l = ι ⁰} (ne [B]) (castₙ neK neM) neK₁
                   (transTerm:⇒:* (CastRed*Term ⊢B ⊢e (escapeTerm {l = ι ⁰} (ne [A]) [t]) (un-univ:⇒*: D)) (CastRedR*Term ⊢K neK (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢B) ))(un-univ≡ (subset* DK)) (refl (un-univ ⊢B))))) ⊢tk (un-univ:⇒*: D′))) 
                   (conv:⇒*: d (trans (sym ⊢A≡K) (≅-eq (escapeEq {l = ι ⁰} (ne [A]) [A≡B])))) 
                   (~-conv (~-cast-refl K≡M ⊢e' (≅ₜ-red (id ⊢K) dk (id ⊢k) (ne neK) (ne neK₁) (ne neK₁) (~-to-≅ₜ k≡k))) (sym ⊢B≡M) ) 


[castreflShape] : ∀ {A B t e Γ r}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ r , ι ⁰ ])
         ([B] : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ r , ι ⁰ ])
         ([A≡B] : Γ ⊩⟨ ι ⁰ ⟩ A ≡ B ^ [ r , ι ⁰ ] / [A])
         (Shape : ShapeView Γ (ι ⁰) (ι ⁰) A B [ r , ι ⁰ ] [ r , ι ⁰ ] [A] [B])
         ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ r , ι ⁰ ] / [A])
         (⊢e : Γ ⊢ e ∷ Id (Univ r ⁰) A B ^ [ % , ι ⁰ ])
         → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ≡ t ∷ B ^ [ r , ι ⁰ ] / [B]
[castreflShape] ⊢Γ .(ℕᵣ ℕA) .(ℕᵣ ℕB) [A≡B] (ℕᵥ ℕA ℕB) [t] ⊢e = [castrefl]ℕ ⊢Γ ℕA ℕB [A≡B] (escapeTerm {l = ι ⁰} (ℕᵣ ℕA) [t]) [t] ⊢e 
[castreflShape] {r = !} ⊢Γ .(ne neA) .(ne neB) [A≡B] (ne neA neB) [t] ⊢e = [castrefl]Ne ⊢Γ neA neB [A≡B] [t] ⊢e
[castreflShape] {A} {B} {t} {e} {Γ} {r}  ⊢Γ .(Πᵣ′ rF ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                   .(Πᵣ′ rF₁ ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁) [A≡B]
                   (Πᵥ (Πᵣ rF ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                       (Πᵣ rF₁ ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)) [t] ⊢e = 
  let eval = lam F₁ ▹
                         (let a = cast ⁰ (wk1 F₁) (wk1 F) (Idsym (Univ rF ⁰) (wk1 F) (wk1 F₁) (fst (wk1 e))) (var 0) in
                         cast ⁰ (G [ a ]↑) G₁ ((snd (wk1 e)) ∘ (var 0) ^ ⁰) ((wk1 t) ∘ a ^ ⁰)) ^ ⁰
      [[ ⊢B , ⊢Π₁ , DΠ₁ ]] = D₁                         
      [ΠFG] = Πᵣ′ rF₁ ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ ([[ ⊢Π₁ , ⊢Π₁ , id ⊢Π₁ ]]) ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁
      [A] , t≡eval = redSubst*Term (cast-Π {!!} {!!} {!!} {!!} {!!} {!!} ⇨ id {!!}) [ΠFG] {!!}
  in transEqTerm {u = eval} (Πᵣ′ rF₁ ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
                 {!!} {!!}
[castreflShape] {r = %} ⊢Γ [A] [B] [A≡B] _ [t] ⊢e =
  let ⊢A = escape {l = ι ⁰} [A] 
      ⊢B = escape {l = ι ⁰} [B] 
      ⊢t = escapeTerm {l = ι ⁰} [A] [t]
  in logRelIrrEq {l = ι ⁰} [B] (castⱼ (un-univ ⊢A) (un-univ ⊢B) ⊢e ⊢t) (conv ⊢t (≅-eq (escapeEq {l = ι ⁰} [A] [A≡B])))

[castrefl] : ∀ {A B t e Γ r}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ r , ι ⁰ ])
         ([B] : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ r , ι ⁰ ])
         ([A≡B] : Γ ⊩⟨ ι ⁰ ⟩ A ≡ B ^ [ r , ι ⁰ ] / [A])
         ([t] : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ r , ι ⁰ ] / [A])
         (⊢e : Γ ⊢ e ∷ Id (Univ r ⁰) A B ^ [ % , ι ⁰ ])
         → Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ≡ t ∷ B ^ [ r , ι ⁰ ] / [B]
[castrefl] ⊢Γ [A] [B] [A≡B] [t] ⊢e = [castreflShape] ⊢Γ [A] [B] [A≡B] (goodCases [A] [B] [A≡B]) [t] ⊢e 

castrefl∞ : ∀ {A B r t e Γ}
         (⊢Γ : ⊢ Γ)
         ([U] : Γ ⊩⟨ ∞ ⟩ Univ r ⁰ ^ [ ! , ι ¹ ])
         ([AU] : Γ ⊩⟨ ∞ ⟩ A ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [U])
         ([BU] : Γ ⊩⟨ ∞ ⟩ B ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [U])
         ([UA≡UB] : Γ ⊩⟨ ∞ ⟩ A ≡ B ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [U])
         ([A] : Γ ⊩⟨ ∞ ⟩ A ^ [ r , ι ⁰ ])
         ([B] : Γ ⊩⟨ ∞ ⟩ B ^ [ r , ι ⁰ ])
         ([t] : Γ ⊩⟨ ∞ ⟩ t ∷ A ^ [ r , ι ⁰ ] / [A])
         ([Id] : Γ ⊩⟨ ∞ ⟩ Id (Univ r ⁰) A B ^ [ % , ι ⁰ ]) →
         ([e] : Γ ⊩⟨ ∞ ⟩ e ∷ Id (Univ r ⁰) A B ^ [ % , ι ⁰ ] / [Id] ) →
         Γ ⊩⟨ ∞ ⟩ cast ⁰ A B e t ≡ t ∷ B ^ [ r , ι ⁰ ] / [B]
castrefl∞ {A} {B} {r} {t} {e} {Γ} ⊢Γ [U] [AU] [BU] [UA≡UB] [A] [B] [t] [Id] [e] =
  let
    [A]′ : Γ ⊩⟨ ι ⁰ ⟩ A ^ [ r , ι ⁰ ]
    [A]′ = univEq [U] [AU]
    [t]′ : Γ ⊩⟨ ι ⁰ ⟩ t ∷ A ^ [ r , ι ⁰ ] / [A]′
    [t]′ = irrelevanceTerm [A] (emb ∞< (emb emb< [A]′)) [t]
    [B]′ : Γ ⊩⟨ ι ⁰ ⟩ B ^ [ r , ι ⁰ ] 
    [B]′ = univEq [U] [BU]
    [A≡B]′ : Γ ⊩⟨ ι ⁰ ⟩ A ≡ B ^ [ r , ι ⁰ ] / [A]′
    [A≡B]′ = univEqEq [U] [A]′ [UA≡UB]
    ⊢e : Γ ⊢ e ∷ Id (Univ r ⁰) A B ^ [ % , ι ⁰ ]
    ⊢e = escapeTerm [Id] [e]
    x : Γ ⊩⟨ ι ⁰ ⟩ cast ⁰ A B e t ≡ t ∷ B ^ [ r , ι ⁰ ] / [B]′
    x = [castrefl] ⊢Γ [A]′ [B]′ [A≡B]′ [t]′ ⊢e 
  in irrelevanceEqTerm (emb ∞< (emb emb< [B]′)) [B] x

abstract

  cast-reflᵗᵛ : ∀ {A B e t r Γ}
              ([Γ] : ⊩ᵛ Γ) →
              ([U] : Γ ⊩ᵛ⟨ ∞ ⟩ Univ r ⁰ ^ [ ! , ι ¹ ] / [Γ])
              ([AU] : Γ ⊩ᵛ⟨ ∞ ⟩ A ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [Γ] / [U])
              ([BU] : Γ ⊩ᵛ⟨ ∞ ⟩ B ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [Γ] / [U])
              ([UA≡UB] : Γ ⊩ᵛ⟨ ∞ ⟩ A ≡ B ∷ Univ r ⁰ ^ [ ! , ι ¹ ] / [Γ] / [U])
              ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ r , ι ⁰ ] / [Γ])
              ([B] : Γ ⊩ᵛ⟨ ∞ ⟩ B ^ [ r , ι ⁰ ] / [Γ])
              ([t] : Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ [ r , ι ⁰ ] / [Γ] / [A])
              ([Id] : Γ ⊩ᵛ⟨ ∞ ⟩ Id (Univ r ⁰) A B ^ [ % , ι ⁰ ] / [Γ])
              ([e] : Γ ⊩ᵛ⟨ ∞ ⟩ e ∷ Id (Univ r ⁰) A B ^ [ % , ι ⁰ ] / [Γ] / [Id] ) →
              Γ ⊩ᵛ⟨ ∞ ⟩ cast ⁰ A B e t ≡ t ∷ B ^ [ r , ι ⁰ ] / [Γ] / [B]
  cast-reflᵗᵛ [Γ] [U] [AU] [BU] [UA≡UB] [A] [B]
              [t] [Id] [e] ⊢Δ [σ] =
    castrefl∞ ⊢Δ (proj₁ ([U] ⊢Δ [σ])) 
      (proj₁ ([AU] ⊢Δ [σ])) (proj₁ ([BU] ⊢Δ [σ])) ([UA≡UB] ⊢Δ [σ])
      (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([B] ⊢Δ [σ])) 
      (proj₁ ([t] ⊢Δ [σ])) (proj₁ ([Id] ⊢Δ [σ])) (proj₁ ([e] ⊢Δ [σ]))

