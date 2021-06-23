{-# OPTIONS --allow-unsolved-metas #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Id {{eqrel : EqRelSet}} where
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
open import Definition.LogicalRelation.Substitution.Introductions.Pi
open import Definition.LogicalRelation.Substitution.Introductions.Idlemmas
open import Definition.LogicalRelation.Substitution.Introductions.IdUniv
open import Definition.LogicalRelation.Substitution.MaybeEmbed
-- open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Definition.LogicalRelation.Substitution.Introductions.Universe

open import Tools.Product
open import Tools.Empty
import Tools.Unit as TU
import Tools.PropositionalEquality as PE
import Data.Nat as Nat

[ℕ] : ∀ {Γ} → ⊢ Γ → Γ ⊩⟨ ι ⁰ ⟩ ℕ ^ [ ! , ι ⁰ ]
[ℕ] ⊢Γ = ℕᵣ (idRed:*: (univ (ℕⱼ ⊢Γ)))

maybeEmb″ : ∀ {l A r Γ}
         → Γ ⊩⟨ ι ⁰ ⟩ A ^ r
         → Γ ⊩⟨ l ⟩ A ^ r
maybeEmb″ {ι ⁰} [A] = [A]
maybeEmb″ {ι ¹} [A] = emb emb< [A]
maybeEmb″ {∞} [A] = emb ∞< (emb emb< [A])

IdTypeNat : ∀ {Γ l t u}
  (⊢Γ : ⊢ Γ)
  ([t] : Γ ⊩ℕ t ∷ℕ)
  ([u] : Γ ⊩ℕ u ∷ℕ)
  → Γ ⊩⟨ l ⟩ Id ℕ t u ^ [ % , ι ⁰ ]
IdTypeNat {Γ} {l} {t} {u} ⊢Γ (ℕₜ .(suc m′) [[ ⊢tℕ , ⊢mℕ , dt ]] m≡m (sucᵣ {m′} [m′])) (ℕₜ .(suc n′) [[ ⊢uℕ , ⊢nℕ , du ]] n≡n (sucᵣ {n′} [n′])) =
  let [Idmn] = IdTypeNat ⊢Γ [m′] [n′]
      ⊢m′ℕ = escapeTerm ([ℕ] ⊢Γ) [m′]
      ⊢n′ℕ = escapeTerm ([ℕ] ⊢Γ) [n′]
      nfId = univ⇒* ((IdℕRed*Term′ ⊢tℕ ⊢mℕ dt ⊢uℕ ⇨∷* IdℕSRed*Term′ ⊢m′ℕ ⊢uℕ ⊢nℕ du)
        ⇨∷* (Id-ℕ-SS ⊢m′ℕ ⊢n′ℕ ⇨ id (Idⱼ (ℕⱼ ⊢Γ) ⊢m′ℕ ⊢n′ℕ)))
  in proj₁ (redSubst* nfId [Idmn])
IdTypeNat {Γ} {l} {t} {u} ⊢Γ (ℕₜ .(suc m′) [[ ⊢tℕ , ⊢mℕ , dt ]] m≡m (sucᵣ {m′} [m′])) (ℕₜ .zero [[ ⊢uℕ , ⊢nℕ , du ]] n≡n zeroᵣ) =
  let ⊢m′ℕ = escapeTerm ([ℕ] ⊢Γ) [m′]
      nfId = (IdℕRed*Term′ ⊢tℕ ⊢mℕ dt ⊢uℕ)
        ⇨∷* (IdℕSRed*Term′ ⊢m′ℕ ⊢uℕ ⊢nℕ du ⇨∷* (Id-ℕ-S0 ⊢m′ℕ ⇨ id (Emptyⱼ ⊢Γ)))
  in Emptyᵣ [[ univ (Idⱼ (ℕⱼ ⊢Γ) ⊢tℕ ⊢uℕ) , univ (Emptyⱼ ⊢Γ) , univ⇒* nfId ]]
IdTypeNat {Γ} {l} {t} {u} ⊢Γ (ℕₜ .(suc m′) [[ ⊢tℕ , ⊢mℕ , dt ]] m≡m (sucᵣ {m′} [m′])) (ℕₜ n [[ ⊢uℕ , ⊢nℕ , du ]] n≡n (ne (neNfₜ nen _ n∼n))) =
  let ⊢m′ℕ = escapeTerm ([ℕ] ⊢Γ) [m′]
      nfId = (IdℕRed*Term′ ⊢tℕ ⊢mℕ dt ⊢uℕ) ⇨∷* IdℕSRed*Term′ ⊢m′ℕ ⊢uℕ ⊢nℕ du
      m′≡m′ = escapeTermEq ([ℕ] ⊢Γ) (reflEqTerm ([ℕ] ⊢Γ) [m′])
  in ne′ (Id ℕ (suc m′) n) [[ univ (Idⱼ (ℕⱼ ⊢Γ) ⊢tℕ ⊢uℕ) , univ (Idⱼ (ℕⱼ ⊢Γ) ⊢mℕ ⊢nℕ) , univ⇒* nfId ]] (IdℕSₙ nen) (~-IdℕS ⊢Γ m′≡m′ n∼n)
IdTypeNat {Γ} {l} {t} {u} ⊢Γ (ℕₜ .zero [[ ⊢tℕ , ⊢mℕ , dt ]] m≡m zeroᵣ) (ℕₜ .(suc n′) [[ ⊢uℕ , ⊢nℕ , du ]] n≡n (sucᵣ {n′} [n′])) =
  let ⊢n′ = escapeTerm ([ℕ] ⊢Γ) [n′]
      nfId = (IdℕRed*Term′ ⊢tℕ ⊢mℕ dt ⊢uℕ)
        ⇨∷* (Idℕ0Red*Term′ ⊢uℕ ⊢nℕ du ⇨∷* (Id-ℕ-0S ⊢n′ ⇨ id (Emptyⱼ ⊢Γ)))
  in Emptyᵣ [[ univ (Idⱼ (ℕⱼ ⊢Γ) ⊢tℕ ⊢uℕ) , univ (Emptyⱼ ⊢Γ) , univ⇒* nfId ]]
IdTypeNat {Γ} {l} {t} {u} ⊢Γ (ℕₜ .zero [[ ⊢tℕ , ⊢mℕ , dt ]] m≡m zeroᵣ) (ℕₜ .zero [[ ⊢uℕ , ⊢nℕ , du ]] n≡n zeroᵣ) =
  let nfId = (IdℕRed*Term′ ⊢tℕ ⊢mℕ dt ⊢uℕ)
        ⇨∷* (Idℕ0Red*Term′ ⊢uℕ ⊢nℕ du ⇨∷* (Id-ℕ-00 ⊢Γ ⇨ id (Unitⱼ ⊢Γ)))
  in proj₁ (redSubst* (univ⇒* nfId) (maybeEmb″ (UnitType ⊢Γ)))
IdTypeNat {Γ} {l} {t} {u} ⊢Γ (ℕₜ .zero [[ ⊢tℕ , ⊢mℕ , dt ]] m≡m zeroᵣ) (ℕₜ n [[ ⊢uℕ , ⊢nℕ , du ]] n≡n (ne (neNfₜ nen _ n∼n))) =
  let nfId = (IdℕRed*Term′ ⊢tℕ ⊢mℕ dt ⊢uℕ) ⇨∷* Idℕ0Red*Term′ ⊢uℕ ⊢nℕ du
  in ne′ (Id ℕ zero n) [[ univ (Idⱼ (ℕⱼ ⊢Γ) ⊢tℕ ⊢uℕ) , univ (Idⱼ (ℕⱼ ⊢Γ) (zeroⱼ ⊢Γ) ⊢nℕ) , univ⇒* nfId ]] (Idℕ0ₙ nen) (~-Idℕ0 ⊢Γ n∼n)
IdTypeNat {Γ} {l} {t} {u} ⊢Γ (ℕₜ m [[ ⊢tℕ , ⊢mℕ , dt ]] m≡m (ne (neNfₜ nem _ m∼m))) [u] =
  let
    ⊢u = escapeTerm ([ℕ] ⊢Γ) [u]
    u≡u = escapeTermEq {l = ι ⁰} ([ℕ] ⊢Γ) (reflEqTerm ([ℕ] ⊢Γ) [u])
  in ne′ (Id ℕ m u) [[ univ (Idⱼ (ℕⱼ ⊢Γ) ⊢tℕ ⊢u) , univ (Idⱼ (ℕⱼ ⊢Γ) ⊢mℕ ⊢u) ,
    univ⇒* (IdℕRed*Term′ ⊢tℕ ⊢mℕ dt ⊢u) ]] (Idℕₙ nem) (~-Idℕ ⊢Γ m∼m u≡u)

IdType : ∀ {A t u Γ l lA}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ l ⟩ A ^ [ ! , ι lA ])
         ([t] : Γ ⊩⟨ l ⟩ t ∷ A ^ [ ! , ι lA ] / [A])
         ([u] : Γ ⊩⟨ l ⟩ u ∷ A ^ [ ! , ι lA ] / [A])
       → Γ ⊩⟨ l ⟩ Id A t u ^ [ % , ι lA ]
IdTypeExt : ∀ {A B t u v w Γ l lA}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ l ⟩ A ^ [ ! , ι lA ])
         ([B] : Γ ⊩⟨ l ⟩ B ^ [ ! , ι lA ])
         ([A≡B] : Γ ⊩⟨ l ⟩ A ≡ B ^ [ ! , ι lA ] / [A])
         ([t] : Γ ⊩⟨ l ⟩ t ∷ A ^ [ ! , ι lA ] / [A])
         ([v] : Γ ⊩⟨ l ⟩ v ∷ B ^ [ ! , ι lA ] / [B])
         ([t≡v] : Γ ⊩⟨ l ⟩ t ≡ v ∷ A ^ [ ! , ι lA ] / [A])
         ([u] : Γ ⊩⟨ l ⟩ u ∷ A ^ [ ! , ι lA ] / [A])
         ([w] : Γ ⊩⟨ l ⟩ w ∷ B ^ [ ! , ι lA ] / [B])
         ([u≡w] : Γ ⊩⟨ l ⟩ u ≡ w ∷ A ^ [ ! , ι lA ] / [A])
       → Γ ⊩⟨ l ⟩ Id A t u ≡ Id B v w ^ [ % , ι lA ] / IdType ⊢Γ [A] [t] [u]
IdType ⊢Γ (Uᵣ (Uᵣ r ¹ l< () d)) [t] [u]
IdType {A} {t} {u} {Γ} {ι .¹} {.¹} ⊢Γ (Uᵣ (Uᵣ ! ⁰ emb< PE.refl [[ ⊢A , ⊢B , D ]])) (Uₜ K d typeK K≡K [t]) (Uₜ M d₁ typeM M≡M [u]) =
  let
    [t0] : Γ ⊩⟨ ι ⁰ ⟩ t ^ [ ! , ι ⁰ ]
    [t0] = PE.subst (λ X → Γ ⊩⟨ ι ⁰ ⟩ X ^ [ ! , ι ⁰ ]) (wk-id t) ([t] Twk.id ⊢Γ)
    [u0] = PE.subst (λ X → Γ ⊩⟨ ι ⁰ ⟩ X ^ [ ! , ι ⁰ ]) (wk-id u) ([u] Twk.id ⊢Γ)
    ⊢tA = conv (un-univ (escape [t0])) (sym (subset* D))
    ⊢uA = conv (un-univ (escape [u0])) (sym (subset* D))
  in proj₁ (redSubst* (IdRed* ⊢tA ⊢uA D) (IdTypeU ⊢Γ [t0] [u0]))

IdType {A} {t} {u} {Γ} {ι .¹} {.¹} ⊢Γ (Uᵣ (Uᵣ % ⁰ emb< PE.refl [[ ⊢A , ⊢B , D ]])) (Uₜ K d typeK K≡K [t]) (Uₜ M d₁ typeM M≡M [u]) =
  let
    [t0] : Γ ⊩⟨ ι ⁰ ⟩ t ^ [ % , ι ⁰ ]
    [t0] = PE.subst (λ X → Γ ⊩⟨ ι ⁰ ⟩ X ^ [ % , ι ⁰ ]) (wk-id t) ([t] Twk.id ⊢Γ)
    [u0] = PE.subst (λ X → Γ ⊩⟨ ι ⁰ ⟩ X ^ [ % , ι ⁰ ]) (wk-id u) ([u] Twk.id ⊢Γ)
    ⊢tA = conv (un-univ (escape [t0])) (sym (subset* D))
    ⊢uA = conv (un-univ (escape [u0])) (sym (subset* D))
  in proj₁ (redSubst* (IdRed* ⊢tA ⊢uA D) (IdTypeSProp ⊢Γ [t0] [u0]))

IdType ⊢Γ (ℕᵣ [[ ⊢A , ⊢B , D ]]) (ℕₜ n d n≡n prop) (ℕₜ n₁ d₁ n≡n₁ prop₁) =
  let
    [[ ⊢tℕ , _ , _ ]] = d
    [[ ⊢uℕ , _ , _ ]] = d₁
  in proj₁ (redSubst* (IdRed* (conv ⊢tℕ (sym (subset* D))) (conv ⊢uℕ (sym (subset* D))) D)
    (IdTypeNat ⊢Γ (ℕₜ n d n≡n prop) (ℕₜ n₁ d₁ n≡n₁ prop₁)))

IdType {A} {t} {u} {Γ} {l} {lA} ⊢Γ (ne′ K [[ ⊢A , ⊢B , D ]] neK K≡K) [t] [u] =
  let
    [A] = ne′ K [[ ⊢A , ⊢B , D ]] neK K≡K
    ⊢tA = escapeTerm {l = l} [A] [t]
    ⊢uA = escapeTerm {l = l} [A] [u]
    [K] = neu {l = l} neK ⊢B K≡K
    [A]′ , [A≡K] = redSubst* D [K]
    [t:K] = convTerm₁ [A]′ [K] [A≡K] (irrelevanceTerm [A] [A]′ [t])
    [u:K] = convTerm₁ [A]′ [K] [A≡K] (irrelevanceTerm [A] [A]′ [u])
    t≡t = escapeTermEq [K] (reflEqTerm [K] [t:K])
    u≡u = escapeTermEq [K] (reflEqTerm [K] [u:K])
    [Id] : Γ ⊩⟨ l ⟩ Id A t u ^ [ % , ι lA ]
    [Id] = ne′ (Id K t u) (redSProp (IdRed*Term ⊢tA ⊢uA [[ ⊢A , ⊢B , D ]])) (Idₙ neK) (~-Id K≡K t≡t u≡u)
  in [Id]

IdType {A} {t} {u} {Γ} {l} {lA} ⊢Γ (Πᵣ′ rF lF lG lF≤ lG≤ F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext)
  (f , [[ ⊢t , ⊢f , Df ]] , funf , f≡f , [fext] , [f]) (g , [[ ⊢u , ⊢g , Dg ]] , fung , g≡g , [gext] , [g]) =
  let
    ⊢tA = conv ⊢t (sym (subset* D))
    ⊢uA = conv ⊢u (sym (subset* D))

    [F0] : Γ ⊩⟨ l ⟩ F ^ [ rF , ι lF ]
    [F0] = PE.subst (λ X → Γ ⊩⟨ l ⟩ X ^ [ rF , ι lF ]) (wk-id F) ([F] Twk.id ⊢Γ)

    ⊢idG : Γ ∙ F ^ [ rF , ι lF ] ⊢ Id G (wk1 t ∘ var 0) (wk1 u ∘ var 0) ^ [ % , ι lG ]
    ⊢idG = let
        ⊢t∘0 = PE.subst (λ X → _ ⊢ wk1 t ∘ var 0 ∷ X ^ [ ! , ι lG ]) (wkSingleSubstId G)
          (Twk.wkTerm (Twk.step Twk.id) (⊢Γ ∙ ⊢F) ⊢t ∘ⱼ var (⊢Γ ∙ ⊢F) here)
        ⊢u∘0 = PE.subst (λ X → _ ⊢ wk1 u ∘ var 0 ∷ X ^ [ ! , ι lG ]) (wkSingleSubstId G)
          (Twk.wkTerm (Twk.step Twk.id) (⊢Γ ∙ ⊢F) ⊢u ∘ⱼ var (⊢Γ ∙ ⊢F) here)
      in univ (Idⱼ (un-univ ⊢G) ⊢t∘0 ⊢u∘0)

    ⊢funext : Γ ⊢ Π F ^ rF ° lF ▹ (Id G ((wk1 t) ∘ (var 0)) ((wk1 u) ∘ (var 0))) ° lG ^ [ % , ι lA ]
    ⊢funext = univ (Πⱼ lF≤ ▹ lG≤ ▹ un-univ ⊢F ▹ un-univ ⊢idG)

    Did : Γ ⊢ Id A t u ⇒* Π F ^ rF ° lF ▹ (Id G ((wk1 t) ∘ (var 0)) ((wk1 u) ∘ (var 0))) ° lG ^ [ % , ι lA ]
    Did =  IdRed* ⊢tA ⊢uA D ⇨* (univ (Id-Π lF≤ lG≤ (un-univ ⊢F) (un-univ ⊢G) ⊢t ⊢u) ⇨ id ⊢funext)

    [idG] : ∀ {ρ Δ a}
          → ([ρ] : Twk._∷_⊆_ ρ Δ Γ) → (⊢Δ : ⊢ Δ)
          → (Δ ⊩⟨ l ⟩ a ∷ wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ)
          → Δ ⊩⟨ l ⟩ wk (lift ρ) (Id G (wk1 t ∘ var 0) (wk1 u ∘ var 0)) [ a ] ^ [ % , ι lG ]
    [idG] {ρ} {Δ} {a} [ρ] ⊢Δ [a] =
      let
        [t∘a] : Δ ⊩⟨ l ⟩ wk ρ t ∘ a ∷ wk (lift ρ) G [ a ] ^ [ ! , ι lG ] / [G] [ρ] ⊢Δ [a]
        [t∘a] = proj₁ (redSubst*Term
          (appRed* (escapeTerm ([F] [ρ] ⊢Δ) [a]) (Twk.wkRed*Term [ρ] ⊢Δ Df))
          ([G] [ρ] ⊢Δ [a]) ([f] [ρ] ⊢Δ [a]))
        [u∘a] : Δ ⊩⟨ l ⟩ wk ρ u ∘ a ∷ wk (lift ρ) G [ a ] ^ [ ! , ι lG ] / [G] [ρ] ⊢Δ [a]
        [u∘a] = proj₁ (redSubst*Term
          (appRed* (escapeTerm ([F] [ρ] ⊢Δ) [a]) (Twk.wkRed*Term [ρ] ⊢Δ Dg))
          ([G] [ρ] ⊢Δ [a]) ([g] [ρ] ⊢Δ [a]))
        [Id] : Δ ⊩⟨ l ⟩ (Id (wk (lift ρ) G [ a ]) (wk ρ t ∘ a) (wk ρ u ∘ a)) ^ [ % , ι lG ]
        [Id] = IdType ⊢Δ ([G] [ρ] ⊢Δ [a]) [t∘a] [u∘a]
      in PE.subst₂ (λ X Y → Δ ⊩⟨ l ⟩ (Id _ (X ∘ a) (Y ∘ a)) ^ [ % , ι lG ]) (PE.sym (irrelevant-subst′ ρ t a)) (PE.sym (irrelevant-subst′ ρ u a)) [Id]

    [idG0] : Γ ∙ F ^ [ rF , ι lF ] ⊩⟨ l ⟩ (Id G (wk1 t ∘ var 0) (wk1 u ∘ var 0)) ^ [ % , ι lG ]
    [idG0] = PE.subst₃ (λ X Y Z → _ ⊩⟨ l ⟩ (Id X (Y ∘ var 0) (Z ∘ var 0)) ^ _)
      (wkSingleSubstId G) (wkSingleSubstId (wk1 t)) (wkSingleSubstId (wk1 u))
      ([idG] {step id} {Γ ∙ F ^ [ rF , ι lF ]} {var 0} (Twk.step Twk.id)
       (⊢Γ ∙ ⊢F) (neuTerm ([F] (Twk.step Twk.id) (⊢Γ ∙ ⊢F)) (var 0)
         (var (⊢Γ ∙ ⊢F) here) (~-var (var (⊢Γ ∙ ⊢F) here))))

    [idGext] : ∀ {ρ Δ a b}
          → ([ρ] : Twk._∷_⊆_ ρ Δ Γ)
          → (⊢Δ : ⊢ Δ)
          → ([a] : Δ ⊩⟨ l ⟩ a ∷ wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ)
          → ([b] : Δ ⊩⟨ l ⟩ b ∷ wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ)
          → ([a≡b] : Δ ⊩⟨ l ⟩ a ≡ b ∷ wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ)
          → Δ ⊩⟨ l ⟩ wk (lift ρ) (Id G (wk1 t ∘ var 0) (wk1 u ∘ var 0)) [ a ] ≡ wk (lift ρ) (Id G (wk1 t ∘ var 0) (wk1 u ∘ var 0)) [ b ] ^ [ % , ι lG ] / [idG] [ρ] ⊢Δ [a]
    [idGext] {ρ} {Δ} {a} {b} [ρ] ⊢Δ [a] [b] [a≡b] =
      let
        [Ga] = [G] [ρ] ⊢Δ [a]
        [Gb] = [G] [ρ] ⊢Δ [b]
        [t∘a] , [ta≡fa] = redSubst*Term
          (appRed* (escapeTerm ([F] [ρ] ⊢Δ) [a]) (Twk.wkRed*Term [ρ] ⊢Δ Df))
          [Ga] ([f] [ρ] ⊢Δ [a])
        [u∘a] , [ua≡ga] = redSubst*Term
          (appRed* (escapeTerm ([F] [ρ] ⊢Δ) [a]) (Twk.wkRed*Term [ρ] ⊢Δ Dg))
          [Ga] ([g] [ρ] ⊢Δ [a])
        [Ga≡Gb] : Δ ⊩⟨ l ⟩ wk (lift ρ) G [ a ] ≡ wk (lift ρ) G [ b ] ^ [ ! , ι lG ] / [Ga]
        [Ga≡Gb] = G-ext [ρ] ⊢Δ [a] [b] [a≡b]
        [t∘b:Gb] , [tb≡fb:Gb] = redSubst*Term
          (appRed* (escapeTerm ([F] [ρ] ⊢Δ) [b]) (Twk.wkRed*Term [ρ] ⊢Δ Df))
          [Gb] ([f] [ρ] ⊢Δ [b])
        [t∘b] : Δ ⊩⟨ l ⟩ wk ρ t ∘ b ∷ wk (lift ρ) G [ a ] ^ [ ! , ι lG ] / [Ga]
        [t∘b] = convTerm₂ [Ga] [Gb] [Ga≡Gb] [t∘b:Gb]
        [u∘b:Gb] , [ub≡gb:Gb] = redSubst*Term
          (appRed* (escapeTerm ([F] [ρ] ⊢Δ) [b]) (Twk.wkRed*Term [ρ] ⊢Δ Dg))
          [Gb] ([g] [ρ] ⊢Δ [b])
        [u∘b] : Δ ⊩⟨ l ⟩ wk ρ u ∘ b ∷ wk (lift ρ) G [ a ] ^ [ ! , ι lG ] / [Ga]
        [u∘b] = convTerm₂ [Ga] [Gb] [Ga≡Gb] [u∘b:Gb]
        [ta≡tb] : Δ ⊩⟨ l ⟩ wk ρ t ∘ a ≡ wk ρ t ∘ b ∷ wk (lift ρ) G [ a ] ^ [ ! , ι lG ] / [Ga]
        [ta≡tb] = transEqTerm [Ga] (transEqTerm [Ga] [ta≡fa] ([fext] [ρ] ⊢Δ [a] [b] [a≡b])) (symEqTerm [Ga] (convEqTerm₂ [Ga] [Gb] [Ga≡Gb] [tb≡fb:Gb]))
        [ua≡ub] : Δ ⊩⟨ l ⟩ wk ρ u ∘ a ≡ wk ρ u ∘ b ∷ wk (lift ρ) G [ a ] ^ [ ! , ι lG ] / [Ga]
        [ua≡ub] = transEqTerm [Ga] (transEqTerm [Ga] [ua≡ga] ([gext] [ρ] ⊢Δ [a] [b] [a≡b])) (symEqTerm [Ga] (convEqTerm₂ [Ga] [Gb] [Ga≡Gb] [ub≡gb:Gb]))
        [IdExt] : Δ ⊩⟨ l ⟩ (Id (wk (lift ρ) G [ a ]) (wk ρ t ∘ a) (wk ρ u ∘ a)) ≡ (Id (wk (lift ρ) G [ b ]) (wk ρ t ∘ b) (wk ρ u ∘ b)) ^ [ % , ι lG ] / IdType ⊢Δ [Ga] [t∘a] [u∘a]
        [IdExt] = IdTypeExt ⊢Δ [Ga] [Gb] [Ga≡Gb] [t∘a] [t∘b:Gb] [ta≡tb] [u∘a] [u∘b:Gb] [ua≡ub]
      in irrelevanceEq″
        (PE.cong₂ (λ X Y → Id _ (X ∘ a) (Y ∘ a)) (PE.sym (irrelevant-subst′ ρ t a)) (PE.sym (irrelevant-subst′ ρ u a)))
        (PE.cong₂ (λ X Y → Id _ (X ∘ b) (Y ∘ b)) (PE.sym (irrelevant-subst′ ρ t b)) (PE.sym (irrelevant-subst′ ρ u b)))
        PE.refl PE.refl
        (IdType ⊢Δ [Ga] [t∘a] [u∘a]) ([idG] [ρ] ⊢Δ [a]) [IdExt]
  in Πᵣ (Πᵣ rF lF lG lF≤ lG≤ F (Id G ((wk1 t) ∘ (var 0)) ((wk1 u) ∘ (var 0)))
      [[ univ (Idⱼ (un-univ ⊢A) ⊢tA ⊢uA) , ⊢funext , Did ]]
      ⊢F ⊢idG
      (≅-univ (≅ₜ-Π-cong ⊢F (≅-un-univ (escapeEqRefl [F0]))
        (≅-un-univ (escapeEqRefl [idG0]))))
      [F] [idG] [idGext])

IdType ⊢Γ (emb {l′ = ι ⁰} emb< [A]) [t] [u] = emb emb< (IdType ⊢Γ [A] [t] [u])
IdType ⊢Γ (emb {l′ = ι ¹} ∞< [A]) [t] [u] = emb ∞< (IdType ⊢Γ [A] [t] [u])

IdTypeExt ⊢Γ [A] [B] [t] [v] [t≡v] [u] [w] [u≡w] = {!!}

-- IdTypeExt {A} {A′} {t} {t′} {u} {u′} {Γ} ⊢Γ (ℕᵣ [[ ⊢A , ⊢B , D ]]) [A′] [A≡A′] [t] [t′] [t≡t′] [u] [u′] [u≡u′] = {!!}

-- IdTypeExt {A} {A′} {t} {t′} {u} {u′} {Γ} ⊢Γ (ne′ K [[ ⊢A , ⊢B , D ]] neK K≡K) [A′] (ne₌ M [[ ⊢A′ , ⊢B′ ,  D′ ]] neM K≡M) [t] [t′] [t≡t′] [u] [u′] [u≡u′] =
--   let
--     [A] = (ne′ K [[ ⊢A , ⊢B , D ]] neK K≡K)
--     ⊢t′A′ = escapeTerm {l = ι ⁰} [A′] [t′]
--     ⊢u′A′ = escapeTerm {l = ι ⁰} [A′] [u′]
--     A≡K = subset* D
--     t≡t′ = ≅-conv (escapeTermEq {l = ι ⁰} [A] [t≡t′]) A≡K
--     u≡u′ = ≅-conv (escapeTermEq {l = ι ⁰} [A] [u≡u′]) A≡K
--   in
--   ne₌ (Id M t′ u′) (redSProp (IdRed*Term ⊢t′A′ ⊢u′A′ [[ ⊢A′ , ⊢B′ , D′ ]]))
--     (Idₙ neM) (~-Id K≡M t≡t′ u≡u′)

-- IdTypeExt {A} {A′} {t} {t′} {u} {u′} {Γ} ⊢Γ
--   (Πᵣ′ rF .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F G D ⊢F ⊢G A≡A [F] [G] G-ext)
--   (Πᵣ′ rF′ .⁰ .⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢A′ , ⊢B′ , D′ ]] ⊢F′ ⊢G′ A′≡A′ [F′] [G′] G′-ext)
--   (Π₌ F′₀ G′₀ D′₀ A≡B [F≡F′₀] [G≡G′₀])
--   [t] [t′] (f₀ , f′₀ , [[ ⊢t , ⊢f₀ , Df₀ ]] , [[ ⊢t′ , ⊢f′₀ , Df′₀ ]] , funf₀ , funf′₀ , f₀≡f′₀ , [t]′ , [t′]′ , [f₀≡f′₀])
--   [u] [u′] (g₀ , g′₀ , [[ ⊢u , ⊢g₀ , Dg₀ ]] , [[ ⊢u′ , ⊢g′₀ , Dg′₀ ]] , fung₀ , fung′₀ , g₀≡g′₀ , [u]′ , [u′]′ , [g₀≡g′₀]) = {!!}
--   -- let
--   --   Π≡Π = whrDet* (D′ , Whnf.Πₙ) (D′₀ , Whnf.Πₙ)
--   --   F′≡F′₀ , rF′≡rF , lF′≡lF , G′≡G′₀ , lG′≡lG = Π-PE-injectivity Π≡Π
--   --   [F≡F′] = PE.subst (λ X → ∀ {ρ} {Δ} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ) → Δ ⊩⟨ ι ⁰ ⟩ wk ρ F ≡ wk ρ X ^ [ rF , _ ] / [F] [ρ] ⊢Δ) (PE.sym F′≡F′₀) [F≡F′₀]
--   --   [G≡G′] = PE.subst (λ X → ∀ {ρ} {Δ} {a} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ) → ([a] : _) → Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G [ a ] ≡ wk (lift ρ) X [ a ] ^ [ _ , _ ] / [G] [ρ] ⊢Δ [a]) (PE.sym G′≡G′₀) [G≡G′₀]

--   --   f , [[ ⊢t , _ , Df ]] , funf , _ , _ , [f] = [t]
--   --   f₀≡f = whrDet*Term (Df₀ , functionWhnf funf₀) (Df , functionWhnf funf)
--   --   f′ , [[ ⊢t′ , _ , Df′ ]] , funf′ , _ , _ , [f′] = [t′]
--   --   f′₀≡f′ = whrDet*Term (Df′₀ , functionWhnf funf′₀) (Df′ , functionWhnf funf′)
--   --   g , [[ ⊢u , _ , Dg ]] , fung , _ , _ , [g] = [u]
--   --   g₀≡g = whrDet*Term (Dg₀ , functionWhnf fung₀) (Dg , functionWhnf fung)
--   --   g′ , [[ ⊢u′ , _ , Dg′ ]] , fung′ , _ , _ , [g′] = [u′]
--   --   g′₀≡g′ = whrDet*Term (Dg′₀ , functionWhnf fung′₀) (Dg′ , functionWhnf fung′)

--   --   [text] = λ {ρ} {Δ} {a} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
--   --         ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F ^ [ rF , ι ⁰ ] / [F] [ρ] ⊢Δ) → redSubst*Term
--   --         (appRed* (escapeTerm ([F] [ρ] ⊢Δ) [a]) (Twk.wkRed*Term [ρ] ⊢Δ Df))
--   --         ([G] [ρ] ⊢Δ [a]) ([f] [ρ] ⊢Δ [a])
--   --   [t′ext] = λ {ρ} {Δ} {a} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
--   --         ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F′ ^ [ rF′ , ι ⁰ ] / [F′] [ρ] ⊢Δ) → redSubst*Term
--   --         (appRed* (escapeTerm ([F′] [ρ] ⊢Δ) [a]) (Twk.wkRed*Term [ρ] ⊢Δ Df′))
--   --         ([G′] [ρ] ⊢Δ [a]) ([f′] [ρ] ⊢Δ [a])
--   --   [uext] = λ {ρ} {Δ} {a} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
--   --         ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F ^ [ rF , ι ⁰ ] / [F] [ρ] ⊢Δ) → redSubst*Term
--   --         (appRed* (escapeTerm ([F] [ρ] ⊢Δ) [a]) (Twk.wkRed*Term [ρ] ⊢Δ Dg))
--   --         ([G] [ρ] ⊢Δ [a]) ([g] [ρ] ⊢Δ [a])
--   --   [u′ext] = λ {ρ} {Δ} {a} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
--   --         ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F′ ^ [ rF′ , ι ⁰ ] / [F′] [ρ] ⊢Δ) → redSubst*Term
--   --         (appRed* (escapeTerm ([F′] [ρ] ⊢Δ) [a]) (Twk.wkRed*Term [ρ] ⊢Δ Dg′))
--   --         ([G′] [ρ] ⊢Δ [a]) ([g′] [ρ] ⊢Δ [a])

--   --   [idG] = λ {ρ} {Δ} {a} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F ^ [ rF , ι ⁰ ] / [F] [ρ] ⊢Δ) →
--   --     PE.subst₂ (λ X Y → Δ ⊩⟨ ι ⁰ ⟩ Id (subst (sgSubst a) (wk (lift ρ) G)) (X ∘ a) (Y ∘ a) ^ [ % , ι ⁰ ])
--   --       (PE.sym (irrelevant-subst′ ρ t a)) (PE.sym (irrelevant-subst′ ρ u a))
--   --       (IdType ⊢Δ ([G] [ρ] ⊢Δ [a]) (proj₁ ([text] [ρ] ⊢Δ [a])) (proj₁ ([uext] [ρ] ⊢Δ [a])))
--   --   [idG≡idG′] : ∀ {ρ Δ a}
--   --         → ([ρ] : Twk._∷_⊆_ ρ Δ Γ)
--   --         → (⊢Δ : ⊢ Δ)
--   --         → ([a] : Δ ⊩⟨ ι ⁰ ⟩ a ∷ wk ρ F ^ [ rF , ι ⁰ ] / [F] [ρ] ⊢Δ)
--   --         → Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) (Id G (wk1 t ∘ var 0) (wk1 u ∘ var 0)) [ a ] ≡ wk (lift ρ) (Id G′ (wk1 t′ ∘ var 0) (wk1 u′ ∘ var 0)) [ a ] ^ [ % , ι ⁰ ] / [idG] [ρ] ⊢Δ [a]
--   --   [idG≡idG′] {ρ} {Δ} {a} [ρ] ⊢Δ [a] =
--   --     let
--   --       [aF′] = convTerm₁′ (PE.sym rF′≡rF) PE.refl ([F] [ρ] ⊢Δ) ([F′] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ) [a]
--   --       [Ga] = [G] [ρ] ⊢Δ [a]
--   --       [G′a] = [G′] [ρ] ⊢Δ [aF′]
--   --       [Ga≡G′a] : Δ ⊩⟨ ι ⁰ ⟩ wk (lift ρ) G [ a ] ≡ wk (lift ρ) G′ [ a ] ^ [ ! , ι ⁰ ] / [Ga]
--   --       [Ga≡G′a] = [G≡G′] [ρ] ⊢Δ [a]
--   --       [t∘a] , [ta≡fa] = [text] [ρ] ⊢Δ [a]
--   --       [t′∘a] , [t′a≡f′a] = [t′ext] [ρ] ⊢Δ [aF′]
--   --       [fa≡f′a] = PE.subst₂ (λ X Y → Δ ⊩⟨ ι ⁰ ⟩ wk ρ X ∘ a ≡ wk ρ Y ∘ a ∷ wk (lift ρ) G [ a ] ^ [ ! , ι ⁰ ] / [Ga]) f₀≡f f′₀≡f′ ([f₀≡f′₀] [ρ] ⊢Δ [a])
--   --       [ta≡t′a] : Δ ⊩⟨ ι ⁰ ⟩ wk ρ t ∘ a ≡ wk ρ t′ ∘ a ∷ wk (lift ρ) G [ a ] ^ [ ! , ι ⁰ ] / [Ga]
--   --       [ta≡t′a] = transEqTerm [Ga] (transEqTerm [Ga] [ta≡fa] [fa≡f′a]) (symEqTerm [Ga] (convEqTerm₂ [Ga] [G′a] [Ga≡G′a] [t′a≡f′a]))
--   --       [u∘a] , [ua≡ga] = [uext] [ρ] ⊢Δ [a]
--   --       [u′∘a] , [u′a≡g′a] = [u′ext] [ρ] ⊢Δ [aF′]
--   --       [ga≡g′a] = PE.subst₂ (λ X Y → Δ ⊩⟨ ι ⁰ ⟩ wk ρ X ∘ a ≡ wk ρ Y ∘ a ∷ wk (lift ρ) G [ a ] ^ [ ! , ι ⁰ ] / [Ga]) g₀≡g g′₀≡g′ ([g₀≡g′₀] [ρ] ⊢Δ [a])
--   --       [ua≡u′a] : Δ ⊩⟨ ι ⁰ ⟩ wk ρ u ∘ a ≡ wk ρ u′ ∘ a ∷ wk (lift ρ) G [ a ] ^ [ ! , ι ⁰ ] / [Ga]
--   --       [ua≡u′a] = transEqTerm [Ga] (transEqTerm [Ga] [ua≡ga] [ga≡g′a]) (symEqTerm [Ga] (convEqTerm₂ [Ga] [G′a] [Ga≡G′a] [u′a≡g′a]))
--   --       [idG≡idG′]′ : Δ ⊩⟨ ι ⁰ ⟩ Id (wk (lift ρ) G [ a ]) (wk ρ t ∘ a) (wk ρ u ∘ a) ≡ Id (wk (lift ρ) G′ [ a ]) (wk ρ t′ ∘ a) (wk ρ u′ ∘ a) ^ [ % , ι ⁰ ] / IdType ⊢Δ [Ga] [t∘a] [u∘a]
--   --       [idG≡idG′]′ = IdTypeExt ⊢Δ [Ga] [G′a] [Ga≡G′a] [t∘a] [t′∘a] [ta≡t′a] [u∘a] [u′∘a] [ua≡u′a]
--   --     in irrelevanceEq″ (PE.cong₂ (λ X Y → Id (wk (lift ρ) G [ a ]) (X ∘ a) (Y ∘ a)) (PE.sym (irrelevant-subst′ ρ t a)) (PE.sym (irrelevant-subst′ ρ u a)))
--   --       (PE.cong₂ (λ X Y → Id (wk (lift ρ) G′ [ a ]) (X ∘ a) (Y ∘ a)) (PE.sym (irrelevant-subst′ ρ t′ a)) (PE.sym (irrelevant-subst′ ρ u′ a)))
--   --       PE.refl PE.refl
--   --       (IdType ⊢Δ [Ga] [t∘a] [u∘a]) ([idG] [ρ] ⊢Δ [a]) [idG≡idG′]′

--   --   [var0] = neuTerm ([F] (Twk.step Twk.id) (⊢Γ ∙ ⊢F)) (var 0) (var (⊢Γ ∙ ⊢F) here) (~-var (var (⊢Γ ∙ ⊢F) here))
--   --   ⊢idG≡idG′₀ : Γ ∙ F ^ [ rF , ι ⁰ ] ⊢ (Id G (wk1 t ∘ var 0) (wk1 u ∘ var 0)) ≅ (Id G′ (wk1 t′ ∘ var 0) (wk1 u′ ∘ var 0)) ^ [ % , ι ⁰ ]
--   --   ⊢idG≡idG′₀ = PE.subst₃ (λ X Y Z → _ ⊢ (Id X (Y ∘ var 0) (Z ∘ var 0)) ≅ _ ^ _)
--   --     (wkSingleSubstId G) (wkSingleSubstId (wk1 t)) (wkSingleSubstId (wk1 u))
--   --     (PE.subst₃ (λ X Y Z → _ ⊢ _ ≅ (Id X (Y ∘ var 0) (Z ∘ var 0)) ^ _)
--   --       (wkSingleSubstId G′) (wkSingleSubstId (wk1 t′)) (wkSingleSubstId (wk1 u′))
--   --       (escapeEq ([idG] (Twk.step Twk.id) (⊢Γ ∙ ⊢F) [var0]) ([idG≡idG′] {step id} {Γ ∙ F ^ [ rF , ι ⁰ ]} {var 0} (Twk.step Twk.id) (⊢Γ ∙ ⊢F) [var0])))

--   --   ⊢F≡F′ = PE.subst₂ (λ X Y → _ ⊢ X ≅ Y ^ _) (wk-id F) (PE.trans (wk-id F′₀) (PE.sym F′≡F′₀))
--   --     (escapeEq ([F] Twk.id ⊢Γ) ([F≡F′₀] Twk.id ⊢Γ))

--   --   [A′] = (Πᵣ′ rF′ ⁰ ⁰ (≡is≤ PE.refl) (≡is≤ PE.refl) F′ G′ [[ ⊢A′ , ⊢B′ , D′ ]] ⊢F′ ⊢G′ A′≡A′ [F′] [G′] G′-ext)
--   --   ⊢t′A′ = escapeTerm {l = ι ⁰} [A′] [t′]
--   --   ⊢u′A′ = escapeTerm {l = ι ⁰} [A′] [u′]
--   --   ⊢t′∘a = PE.subst (λ X → _ ⊢ wk1 t′ ∘ var 0 ∷ X ^ [ ! , ι ⁰ ]) (wkSingleSubstId G′)
--   --     (Twk.wkTerm (Twk.step Twk.id) (⊢Γ ∙ ⊢F′) ⊢t′ ∘ⱼ var (⊢Γ ∙ ⊢F′) here)
--   --   ⊢u′∘a = PE.subst (λ X → _ ⊢ wk1 u′ ∘ var 0 ∷ X ^ [ ! , ι ⁰ ]) (wkSingleSubstId G′)
--   --     (Twk.wkTerm (Twk.step Twk.id) (⊢Γ ∙ ⊢F′) ⊢u′ ∘ⱼ var (⊢Γ ∙ ⊢F′) here)
--   --   ⊢funext′ : Γ ⊢ Π F′ ^ rF′ ° ⁰ ▹ Id G′ (wk1 t′ ∘ var 0) (wk1 u′ ∘ var 0) ° ⁰ ^ [ % , ι ⁰ ]
--   --   ⊢funext′ = univ (Πⱼ ≡is≤ PE.refl ▹ ≡is≤ PE.refl ▹ un-univ ⊢F′ ▹ Idⱼ (un-univ ⊢G′) ⊢t′∘a ⊢u′∘a)
--   --   Did : Γ ⊢ Id A′ t′ u′ ⇒* Π F′ ^ rF′ ° ⁰ ▹ (Id G′ ((wk1 t′) ∘ (var 0)) ((wk1 u′) ∘ (var 0))) ° ⁰ ^ [ % , ι ⁰ ]
--   --   Did = IdRed* ⊢t′A′ ⊢u′A′ D′ ⇨* ((univ (Id-Π (≡is≤ PE.refl) (≡is≤ PE.refl) (un-univ ⊢F′) (un-univ ⊢G′) ⊢t′ ⊢u′)) ⇨ id ⊢funext′)
--   -- in
--   -- Π₌ F′ (Id G′ ((wk1 t′) ∘ (var 0)) ((wk1 u′) ∘ (var 0)))
--   --   (PE.subst (λ X → Γ ⊢ Id A′ t′ u′ ⇒* Π F′ ^ X ° ⁰ ▹ _ ° ⁰ ^ [ % , ι ⁰ ]) rF′≡rF Did)
--   --   (≅-univ (≅ₜ-Π-cong ⊢F (≅-un-univ ⊢F≡F′) (≅-un-univ ⊢idG≡idG′₀))) [F≡F′] [idG≡idG′]

-- IdTypeExt ⊢Γ (Πᵣ′ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
--   (ℕᵣ [[ ⊢A′ , ⊢B′ , D′ ]])
--   (Π₌ F′′ G′′ D′′ A≡B [F≡F′] [G≡G′]) [t] [t′] [t≡t′] [u] [u′] [u≡u′] =
--   ⊥-elim (ℕ≢Π (whrDet* (D′ , ℕₙ) (D′′ , Πₙ)))

-- IdTypeExt ⊢Γ (Πᵣ′ rF lF lG _ _ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
--   (ne′ M [[ ⊢A′ , ⊢B′ , D′ ]] neM M≡M)
--   (Π₌ F′′ G′′ D′′ A≡B [F≡F′] [G≡G′]) [t] [t′] [t≡t′] [u] [u′] [u≡u′] =
--   ⊥-elim (Π≢ne neM (whrDet* (D′′ , Πₙ) (D′ , ne neM)))

-- IdTerm : ∀ {A t u Γ l}
--          (⊢Γ : ⊢ Γ)
--          ([A] : Γ ⊩⟨ l ⟩ A ^ !)
--          ([t] : Γ ⊩⟨ l ⟩ t ∷ A ^ ! / [A])
--          ([u] : Γ ⊩⟨ l ⟩ u ∷ A ^ ! / [A])
--        → Γ ⊩⟨ ¹ ⟩ Id A t u ∷ SProp ^ ! / Uᵣ′ _ ⁰ 0<1 ⊢Γ
-- IdTerm {A} {t} {u} {Γ} {l} ⊢Γ [A] [t] [u] with escapeTerm {l = l} [A] [t] | escapeTerm {l = l} [A] [u]
-- IdTerm ⊢Γ (Uᵣ (Uᵣ l′ l< ⊢Γ₁)) [t] [u] | ⊢tA | ⊢uA = {!!}
-- IdTerm {A} {t} {u} {Γ} {l} ⊢Γ (ℕᵣ [ ⊢A , ⊢B , D ]) [t] [u] | ⊢tA | ⊢uA =
--   proj₁ (redSubst*Term (IdRed*Term′ ⊢tA ⊢uA D) (Uᵣ′ _ ⁰ 0<1 ⊢Γ) (aux [t] [u]))
--   where
--     [A] = (ℕᵣ ([ ⊢A , ⊢B , D ]))
--     [ℕ] : Γ ⊩⟨ l ⟩ ℕ ^ !
--     [ℕ] = ℕᵣ (idRed:*: (ℕⱼ ⊢Γ))
--     A≡ℕ = redSubst* D [ℕ]

-- IdTerm {A} {t} {u} {Γ} {l} ⊢Γ (ne′ K D neK K≡K) [t] [u] | ⊢tA | ⊢uA =
--   let [A] = ne′ K D neK K≡K
--       [K] = neu {l = l} neK (_⊢_:⇒*:_^_.⊢B D) K≡K
--       A≡K = redSubst* (_⊢_:⇒*:_^_.D D) [K]
--       [t]′ = convTerm₁ (proj₁ A≡K) [K] (proj₂ A≡K)
--         (irrelevanceTerm  {l = l} [A] (proj₁ A≡K) [t])
--       [u]′ = convTerm₁ (proj₁ A≡K) [K] (proj₂ A≡K)
--         (irrelevanceTerm {l = l} [A] (proj₁ A≡K) [u])
--       t≡t = escapeTermEq [K] (reflEqTerm [K] [t]′)
--       u≡u = escapeTermEq [K] (reflEqTerm [K] [u]′)
--   in Uₜ (Id K t u)
--     (IdRed*Term ⊢tA ⊢uA D)
--     (ne (Idₙ neK))
--     (~-to-≅ₜ (~-Id K≡K t≡t u≡u))
--     (ne′ (Id K t u) (redSProp (IdRed*Term ⊢tA ⊢uA D)) (Idₙ neK) (~-Id K≡K t≡t u≡u))
-- IdTerm ⊢Γ (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) [t] [u] | ⊢tA | ⊢uA = {!!}
-- IdTerm {A} {t} {u} {Γ} {⁰} ⊢Γ (emb {l′ = l′} () [A]) [t] [u] | ⊢tA | ⊢uA
-- IdTerm {A} {t} {u} {Γ} {¹} ⊢Γ (emb {l′ = .⁰} 0<1 [A]) [t] [u] | ⊢tA | ⊢uA =
--   IdTerm ⊢Γ [A] [t] [u]


Idᵛ : ∀ {A t u Γ l}
       ([Γ] : ⊩ᵛ Γ)
       ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ ! , ι l ] / [Γ])
       ([t] : Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ [ ! , ι l ] / [Γ] / [A])
       ([u] : Γ ⊩ᵛ⟨ ∞ ⟩ u ∷ A ^ [ ! , ι l ] / [Γ] / [A])
     → Γ ⊩ᵛ⟨ ∞ ⟩ Id A t u ^ [ % , ι l ] / [Γ]
Idᵛ [Γ] [A] [t] [u] ⊢Δ [σ] = {!!}
  -- (IdTerm ⊢Δ (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ])) (proj₁ ([u] ⊢Δ [σ])))
  -- , {!!}

Idᵗᵛ : ∀ {A t u Γ l}
       ([Γ] : ⊩ᵛ Γ)
       ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ ! , ι l ] / [Γ])
       ([t] : Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ [ ! , ι l ] / [Γ] / [A])
       ([u] : Γ ⊩ᵛ⟨ ∞ ⟩ u ∷ A ^ [ ! , ι l ] / [Γ] / [A])
     → Γ ⊩ᵛ⟨ ∞ ⟩ Id A t u ∷ SProp l ^ [ ! , next l ] / [Γ] / maybeEmbᵛ {A = SProp _} [Γ] (Uᵛ (proj₂ (levelBounded l)) [Γ])
Idᵗᵛ [Γ] [A] [t] [u] ⊢Δ [σ] = {!!}
  -- (IdTerm ⊢Δ (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ])) (proj₁ ([u] ⊢Δ [σ])))
  -- , {!!}
