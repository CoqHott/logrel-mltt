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
open import Definition.LogicalRelation.ShapeView
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

[ℕ] : ∀ {Γ l} → ⊢ Γ → Γ ⊩⟨ l ⟩ ℕ ^ [ ! , ι ⁰ ]
[ℕ] ⊢Γ = ℕᵣ (idRed:*: (univ (ℕⱼ ⊢Γ)))

[Id]ℕ : ∀ {Γ l t u}
  (⊢Γ : ⊢ Γ)
  ([t] : Γ ⊩ℕ t ∷ℕ)
  ([u] : Γ ⊩ℕ u ∷ℕ)
  → Γ ⊩⟨ l ⟩ Id ℕ t u ^ [ % , ι ⁰ ]
[Id]ℕ {Γ} {l} {t} {u} ⊢Γ (ℕₜ .(suc m′) [[ ⊢tℕ , ⊢mℕ , dt ]] m≡m (sucᵣ {m′} [m′])) (ℕₜ .(suc n′) [[ ⊢uℕ , ⊢nℕ , du ]] n≡n (sucᵣ {n′} [n′])) =
  let [Idmn] = [Id]ℕ ⊢Γ [m′] [n′]
      ⊢m′ℕ = escapeTerm {l = ι ⁰} ([ℕ] ⊢Γ) [m′]
      ⊢n′ℕ = escapeTerm {l = ι ⁰} ([ℕ] ⊢Γ) [n′]
      nfId = univ⇒* ((IdℕRed*Term′ ⊢tℕ ⊢mℕ dt ⊢uℕ ⇨∷* IdℕSRed*Term′ ⊢m′ℕ ⊢uℕ ⊢nℕ du)
        ⇨∷* (Id-ℕ-SS ⊢m′ℕ ⊢n′ℕ ⇨ id (Idⱼ (ℕⱼ ⊢Γ) ⊢m′ℕ ⊢n′ℕ)))
  in proj₁ (redSubst* nfId [Idmn])
[Id]ℕ {Γ} {l} {t} {u} ⊢Γ (ℕₜ .(suc m′) [[ ⊢tℕ , ⊢mℕ , dt ]] m≡m (sucᵣ {m′} [m′])) (ℕₜ .zero [[ ⊢uℕ , ⊢nℕ , du ]] n≡n zeroᵣ) =
  let ⊢m′ℕ = escapeTerm {l = ι ⁰} ([ℕ] ⊢Γ) [m′]
      nfId = (IdℕRed*Term′ ⊢tℕ ⊢mℕ dt ⊢uℕ)
        ⇨∷* (IdℕSRed*Term′ ⊢m′ℕ ⊢uℕ ⊢nℕ du ⇨∷* (Id-ℕ-S0 ⊢m′ℕ ⇨ id (Emptyⱼ ⊢Γ)))
  in Emptyᵣ [[ univ (Idⱼ (ℕⱼ ⊢Γ) ⊢tℕ ⊢uℕ) , univ (Emptyⱼ ⊢Γ) , univ⇒* nfId ]]
[Id]ℕ {Γ} {l} {t} {u} ⊢Γ (ℕₜ .(suc m′) [[ ⊢tℕ , ⊢mℕ , dt ]] m≡m (sucᵣ {m′} [m′])) (ℕₜ n [[ ⊢uℕ , ⊢nℕ , du ]] n≡n (ne (neNfₜ nen _ n∼n))) =
  let ⊢m′ℕ = escapeTerm {l = ι ⁰} ([ℕ] ⊢Γ) [m′]
      nfId = (IdℕRed*Term′ ⊢tℕ ⊢mℕ dt ⊢uℕ) ⇨∷* IdℕSRed*Term′ ⊢m′ℕ ⊢uℕ ⊢nℕ du
      m′≡m′ = escapeTermEq ([ℕ] {l = ι ⁰} ⊢Γ) (reflEqTerm ([ℕ] {l = ι ⁰} ⊢Γ) [m′])
  in ne′ (Id ℕ (suc m′) n) [[ univ (Idⱼ (ℕⱼ ⊢Γ) ⊢tℕ ⊢uℕ) , univ (Idⱼ (ℕⱼ ⊢Γ) ⊢mℕ ⊢nℕ) , univ⇒* nfId ]] (IdℕSₙ nen) (~-IdℕS ⊢Γ m′≡m′ n∼n)
[Id]ℕ {Γ} {l} {t} {u} ⊢Γ (ℕₜ .zero [[ ⊢tℕ , ⊢mℕ , dt ]] m≡m zeroᵣ) (ℕₜ .(suc n′) [[ ⊢uℕ , ⊢nℕ , du ]] n≡n (sucᵣ {n′} [n′])) =
  let ⊢n′ = escapeTerm ([ℕ] {l = ι ⁰} ⊢Γ) [n′]
      nfId = (IdℕRed*Term′ ⊢tℕ ⊢mℕ dt ⊢uℕ)
        ⇨∷* (Idℕ0Red*Term′ ⊢uℕ ⊢nℕ du ⇨∷* (Id-ℕ-0S ⊢n′ ⇨ id (Emptyⱼ ⊢Γ)))
  in Emptyᵣ [[ univ (Idⱼ (ℕⱼ ⊢Γ) ⊢tℕ ⊢uℕ) , univ (Emptyⱼ ⊢Γ) , univ⇒* nfId ]]
[Id]ℕ {Γ} {l} {t} {u} ⊢Γ (ℕₜ .zero [[ ⊢tℕ , ⊢mℕ , dt ]] m≡m zeroᵣ) (ℕₜ .zero [[ ⊢uℕ , ⊢nℕ , du ]] n≡n zeroᵣ) =
  let nfId = (IdℕRed*Term′ ⊢tℕ ⊢mℕ dt ⊢uℕ)
        ⇨∷* (Idℕ0Red*Term′ ⊢uℕ ⊢nℕ du ⇨∷* (Id-ℕ-00 ⊢Γ ⇨ id (Unitⱼ ⊢Γ)))
  in proj₁ (redSubst* (univ⇒* nfId) (maybeEmb″ (UnitType ⊢Γ)))
[Id]ℕ {Γ} {l} {t} {u} ⊢Γ (ℕₜ .zero [[ ⊢tℕ , ⊢mℕ , dt ]] m≡m zeroᵣ) (ℕₜ n [[ ⊢uℕ , ⊢nℕ , du ]] n≡n (ne (neNfₜ nen _ n∼n))) =
  let nfId = (IdℕRed*Term′ ⊢tℕ ⊢mℕ dt ⊢uℕ) ⇨∷* Idℕ0Red*Term′ ⊢uℕ ⊢nℕ du
  in ne′ (Id ℕ zero n) [[ univ (Idⱼ (ℕⱼ ⊢Γ) ⊢tℕ ⊢uℕ) , univ (Idⱼ (ℕⱼ ⊢Γ) (zeroⱼ ⊢Γ) ⊢nℕ) , univ⇒* nfId ]] (Idℕ0ₙ nen) (~-Idℕ0 ⊢Γ n∼n)
[Id]ℕ {Γ} {l} {t} {u} ⊢Γ (ℕₜ m [[ ⊢tℕ , ⊢mℕ , dt ]] m≡m (ne (neNfₜ nem _ m∼m))) [u] =
  let
    ⊢u = escapeTerm ([ℕ] {l = ι ⁰} ⊢Γ) [u]
    u≡u = escapeTermEq {l = ι ⁰} ([ℕ] ⊢Γ) (reflEqTerm ([ℕ] {l = ι ⁰} ⊢Γ) [u])
  in ne′ (Id ℕ m u) [[ univ (Idⱼ (ℕⱼ ⊢Γ) ⊢tℕ ⊢u) , univ (Idⱼ (ℕⱼ ⊢Γ) ⊢mℕ ⊢u) ,
    univ⇒* (IdℕRed*Term′ ⊢tℕ ⊢mℕ dt ⊢u) ]] (Idℕₙ nem) (~-Idℕ ⊢Γ m∼m u≡u)

escapeEqℕ₁  : ∀ {Γ m n} → Γ ⊩ℕ m ≡ n ∷ℕ → Γ ⊢ m ∷ ℕ ^ [ ! , ι ⁰ ]
escapeEqℕ₁ (ℕₜ₌ k k′ [[ ⊢t , ⊢u , d ]] d′ k≡k′ prop) = ⊢t

escapeEqℕ₂  : ∀ {Γ m n} → Γ ⊩ℕ m ≡ n ∷ℕ → Γ ⊢ n ∷ ℕ ^ [ ! , ι ⁰ ]
escapeEqℕ₂ (ℕₜ₌ k k′ d [[ ⊢t , ⊢u , d' ]] k≡k′ prop) = ⊢t

irrelevanceEqTermℕ : ∀ {Γ A t t′ u u′ r ll l} 
                        (eqt : t PE.≡ t′) (equ : u PE.≡ u′)
                        (p : Γ ⊩⟨ l ⟩ A ^ [ r , ll ]) 
                      → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ [ r , ll ] / p → Γ ⊩⟨ l ⟩ t′ ≡ u′ ∷ A ^ [ r , ll ] / p
irrelevanceEqTermℕ PE.refl PE.refl p t≡u = t≡u

[IdExt]ℕ : ∀ {Γ l t u v w}
  (⊢Γ : ⊢ Γ)
  ([t] : Γ ⊩ℕ t ∷ℕ)
  ([u] : Γ ⊩ℕ u ∷ℕ)
  ([v] : Γ ⊩ℕ v ∷ℕ)
  ([w] : Γ ⊩ℕ w ∷ℕ)
  ([t≡v] : Γ ⊩ℕ t ≡ v ∷ℕ)
  ([u≡w] : Γ ⊩ℕ u ≡ w ∷ℕ)
  →  Γ ⊩⟨ l ⟩ Id ℕ t u ≡ Id ℕ v w ^ [ % , ι ⁰ ] / [Id]ℕ ⊢Γ [t] [u]


[IdExt]ℕ {Γ} {l} {t} {u} {v} {w} ⊢Γ
            (ℕₜ .(suc _) [[ ⊢tℕ , ⊢mℕ , dt ]] n≡n₁ (sucᵣ {n} [t']))
            (ℕₜ .(suc _) [[ ⊢uℕ , ⊢nℕ , du ]] n≡n (sucᵣ {n₂} [u']))
            (ℕₜ .(suc _) [[ ⊢vℕ , ⊢oℕ , dv ]] n≡n₂ (sucᵣ {n₁} [v']))
            (ℕₜ .(suc _) [[ ⊢wℕ , ⊢pℕ , dw ]] n≡n₃ (sucᵣ {n₃} [w']))
            (ℕₜ₌ .(suc _) .(suc _) d₄ d′ k≡k′ (sucᵣ [t≡v']))
            (ℕₜ₌ .(suc _) .(suc _) d₅ d′₁ k≡k′₁ (sucᵣ [u≡w'])) =
  let t≡t' = suc-PE-injectivity (whrDet*Term (dt , sucₙ) (redₜ d₄ , sucₙ))
      u≡u' = suc-PE-injectivity (whrDet*Term (du , sucₙ) (redₜ d₅ , sucₙ))
      v≡v' = suc-PE-injectivity (whrDet*Term (dv , sucₙ) (redₜ d′ , sucₙ))
      w≡w' = suc-PE-injectivity (whrDet*Term (dw , sucₙ) (redₜ d′₁ , sucₙ))
      [t] = ℕₜ (suc _) [[ ⊢tℕ , ⊢mℕ , dt ]] n≡n₁ (sucᵣ [t'])
      [u] = ℕₜ (suc _) [[ ⊢uℕ , ⊢nℕ , du ]] n≡n (sucᵣ [u'])
      [v] = ℕₜ (suc _) [[ ⊢vℕ , ⊢oℕ , dv ]] n≡n₂ (sucᵣ [v'])
      [w] = ℕₜ (suc _) [[ ⊢wℕ , ⊢pℕ , dw ]] n≡n₃ (sucᵣ [w'])
      [Idmn] = [IdExt]ℕ {l = l} ⊢Γ [t'] [u'] [v'] [w'] (irrelevanceEqTermℕ {l = l} (PE.sym t≡t') (PE.sym v≡v') ([ℕ] ⊢Γ) [t≡v'])
                                               (irrelevanceEqTermℕ {l = l} (PE.sym u≡u') (PE.sym w≡w') ([ℕ] ⊢Γ) [u≡w']) 
      ⊢t′ℕ = escapeTerm {l = ι ⁰} ([ℕ] ⊢Γ) [t']
      ⊢u′ℕ = escapeTerm {l = ι ⁰} ([ℕ] ⊢Γ) [u']
      nfId = univ⇒* ((IdℕRed*Term′ ⊢tℕ ⊢mℕ dt ⊢uℕ ⇨∷* IdℕSRed*Term′ ⊢t′ℕ ⊢uℕ ⊢nℕ du)
        ⇨∷* (Id-ℕ-SS ⊢t′ℕ ⊢u′ℕ ⇨ id (Idⱼ (ℕⱼ ⊢Γ) ⊢t′ℕ ⊢u′ℕ)))
      ⊢v′ℕ = escapeTerm {l = ι ⁰} ([ℕ] ⊢Γ) [v']
      ⊢w′ℕ = escapeTerm {l = ι ⁰} ([ℕ] ⊢Γ) [w']
      nfId' = univ⇒* ((IdℕRed*Term′ ⊢vℕ ⊢oℕ dv ⊢wℕ ⇨∷* IdℕSRed*Term′ ⊢v′ℕ ⊢wℕ ⊢pℕ dw)
        ⇨∷* (Id-ℕ-SS ⊢v′ℕ ⊢w′ℕ ⇨ id (Idⱼ (ℕⱼ ⊢Γ) ⊢v′ℕ ⊢w′ℕ)))
      [IdA] , [IdA≡ℕ] = redSubst* {l = l} nfId ([Id]ℕ ⊢Γ [t'] [u'])
      [IdB] , [IdB≡ℕ] = redSubst* {l = l} nfId' ([Id]ℕ ⊢Γ [v'] [w'])
      [IdA≡ℕ]′ = irrelevanceEq {A = Id ℕ t u} {B = Id ℕ n n₂} {l = l} [IdA] ([Id]ℕ ⊢Γ [t] [u]) [IdA≡ℕ] 
      [IdB≡ℕ]′ = irrelevanceEq {A = Id ℕ v w} {B = Id ℕ n₁ n₃} {l = l} {l′ = l} [IdB] ([Id]ℕ ⊢Γ [v] [w]) [IdB≡ℕ] 
  in transEq {A = Id ℕ t u} {B = Id ℕ n n₂} {C = Id ℕ v w} {l = l} {l′ = l} {l″ = l} ([Id]ℕ ⊢Γ [t] [u]) ([Id]ℕ ⊢Γ [t'] [u']) ([Id]ℕ ⊢Γ [v] [w])
                  [IdA≡ℕ]′ 
                  (transEq {A = Id ℕ n n₂} {B = Id ℕ n₁ n₃} {C = Id ℕ v w} {l = l} {l′ = l} {l″ = l} ([Id]ℕ ⊢Γ [t'] [u']) ([Id]ℕ ⊢Γ [v'] [w']) ([Id]ℕ ⊢Γ [v] [w])
                                   [Idmn] (symEq {A = Id ℕ v w} {B = Id ℕ n₁ n₃} ([Id]ℕ ⊢Γ [v] [w]) ([Id]ℕ ⊢Γ [v'] [w']) [IdB≡ℕ]′)) 

[IdExt]ℕ {Γ} {l} {t} {u} {v} {w} ⊢Γ 
  (ℕₜ .(suc _) [[ ⊢tℕ , ⊢mℕ , dt ]] n≡n₁ (sucᵣ {n} [t'])) 
  (ℕₜ .zero [[ ⊢uℕ , ⊢nℕ , du ]] n≡n zeroᵣ) 
  (ℕₜ .(suc _) [[ ⊢vℕ , ⊢oℕ , dv ]] n≡n₂ (sucᵣ {m} [v'])) 
  (ℕₜ .zero [[ ⊢wℕ , ⊢pℕ , dw ]] n≡n₃ zeroᵣ) 
  (ℕₜ₌ .(suc _) .(suc _) d₄ d′ k≡k′ (sucᵣ x))
  (ℕₜ₌ .zero .zero d₅ d′₁ k≡k′₁ zeroᵣ) = 
  let [t] = ℕₜ (suc _) [[ ⊢tℕ , ⊢mℕ , dt ]] n≡n₁ (sucᵣ [t'])
      [u] = ℕₜ zero [[ ⊢uℕ , ⊢nℕ , du ]] n≡n zeroᵣ
      [v] = ℕₜ (suc _) [[ ⊢vℕ , ⊢oℕ , dv ]] n≡n₂ (sucᵣ [v'])
      [w] = ℕₜ zero [[ ⊢wℕ , ⊢pℕ , dw ]] n≡n₃ zeroᵣ
      ⊢t′ℕ = escapeTerm {l = ι ⁰} ([ℕ] ⊢Γ) [t']
      nfId = univ⇒* ((IdℕRed*Term′ ⊢tℕ ⊢mℕ dt ⊢uℕ)
        ⇨∷* (IdℕSRed*Term′ ⊢t′ℕ ⊢uℕ ⊢nℕ du ⇨∷* (Id-ℕ-S0 ⊢t′ℕ ⇨ id (Emptyⱼ ⊢Γ))))
      ⊢v′ℕ = escapeTerm {l = ι ⁰} ([ℕ] ⊢Γ) [v']
      nfId' = univ⇒* ((IdℕRed*Term′ ⊢vℕ ⊢oℕ dv ⊢wℕ)
        ⇨∷* (IdℕSRed*Term′ ⊢v′ℕ ⊢wℕ ⊢pℕ dw ⇨∷* (Id-ℕ-S0 ⊢v′ℕ ⇨ id (Emptyⱼ ⊢Γ))))
      [Empty] = Emptyᵣ (idRed:*: (univ (Emptyⱼ ⊢Γ)))
      [IdA] , [IdA≡ℕ] = redSubst* {l = l} nfId [Empty]
      [IdB] , [IdB≡ℕ] = redSubst* {l = l} nfId' [Empty]
      [IdA≡ℕ]′ = irrelevanceEq {A = Id ℕ t u} {B = Empty} {l = l} {l′ = l} [IdA] ([Id]ℕ ⊢Γ [t] [u]) [IdA≡ℕ] 
      [IdB≡ℕ]′ = irrelevanceEq {A = Id ℕ v w} {B = Empty} {l = l} {l′ = l} [IdB] ([Id]ℕ ⊢Γ [v] [w]) [IdB≡ℕ] 
  in transEq {A = Id ℕ t u} {B = Empty} {C = Id ℕ v w} {l = l} {l′ = l} {l″ = l} ([Id]ℕ ⊢Γ [t] [u]) [Empty] ([Id]ℕ ⊢Γ [v] [w])
                  [IdA≡ℕ]′  (symEq {A = Id ℕ v w} {B = Empty} {l = l} {l′ = l} ([Id]ℕ ⊢Γ [v] [w]) [Empty] [IdB≡ℕ]′) 


[IdExt]ℕ {Γ} {l} {u} {t} {w} {v} ⊢Γ 
  (ℕₜ .zero [[ ⊢uℕ , ⊢nℕ , du ]] n≡n zeroᵣ) 
  (ℕₜ .(suc _) [[ ⊢tℕ , ⊢mℕ , dt ]] n≡n₁ (sucᵣ {n} [t'])) 
  (ℕₜ .zero [[ ⊢wℕ , ⊢pℕ , dw ]] n≡n₃ zeroᵣ) 
  (ℕₜ .(suc _) [[ ⊢vℕ , ⊢oℕ , dv ]] n≡n₂ (sucᵣ {m} [v'])) 
  (ℕₜ₌ .zero .zero d₅ d′₁ k≡k′₁ zeroᵣ) 
  (ℕₜ₌ .(suc _) .(suc _) d₄ d′ k≡k′ (sucᵣ x)) =
  let [t] = ℕₜ (suc _) [[ ⊢tℕ , ⊢mℕ , dt ]] n≡n₁ (sucᵣ [t'])
      [u] = ℕₜ zero [[ ⊢uℕ , ⊢nℕ , du ]] n≡n zeroᵣ
      [v] = ℕₜ (suc _) [[ ⊢vℕ , ⊢oℕ , dv ]] n≡n₂ (sucᵣ [v'])
      [w] = ℕₜ zero [[ ⊢wℕ , ⊢pℕ , dw ]] n≡n₃ zeroᵣ
      ⊢t′ℕ = escapeTerm {l = ι ⁰} ([ℕ] ⊢Γ) [t']
      nfId = univ⇒* ((IdℕRed*Term′ ⊢tℕ ⊢mℕ dt ⊢uℕ)
        ⇨∷* (IdℕSRed*Term′ ⊢t′ℕ ⊢uℕ ⊢nℕ du ⇨∷* (Id-ℕ-S0 ⊢t′ℕ ⇨ id (Emptyⱼ ⊢Γ))))
      ⊢v′ℕ = escapeTerm {l = ι ⁰} ([ℕ] ⊢Γ) [v']
      nfId' = univ⇒* ((IdℕRed*Term′ ⊢vℕ ⊢oℕ dv ⊢wℕ)
        ⇨∷* (IdℕSRed*Term′ ⊢v′ℕ ⊢wℕ ⊢pℕ dw ⇨∷* (Id-ℕ-S0 ⊢v′ℕ ⇨ id (Emptyⱼ ⊢Γ))))
      [Empty] = Emptyᵣ (idRed:*: (univ (Emptyⱼ ⊢Γ)))
      [IdA] , [IdA≡ℕ] = redSubst* {l = l} nfId [Empty]
      [IdB] , [IdB≡ℕ] = redSubst* {l = l} nfId' [Empty]
      [IdA≡ℕ]′ = irrelevanceEq {A = Id ℕ t u} {B = Empty} {l = l} {l′ = l} [IdA] ([Id]ℕ ⊢Γ [t] [u]) [IdA≡ℕ] 
      [IdB≡ℕ]′ = irrelevanceEq {A = Id ℕ v w} {B = Empty} {l = l} {l′ = l} [IdB] ([Id]ℕ ⊢Γ [v] [w]) [IdB≡ℕ] 
   in transEq {A = Id ℕ u t} {B = Empty} {C = Id ℕ w v} {l = l} {l′ = l} {l″ = l} ([Id]ℕ ⊢Γ [u] [t]) [Empty] ([Id]ℕ ⊢Γ [w] [v])
                  [IdB≡ℕ]′  (symEq {A = Id ℕ w v} {B = Empty} {l = l} {l′ = l} ([Id]ℕ ⊢Γ [w] [v]) [Empty] [IdA≡ℕ]′) 

[IdExt]ℕ {Γ} {l} {t} {u} {v} {w} ⊢Γ (ℕₜ .zero [[ ⊢tℕ , ⊢mℕ , dt ]] n≡n₁ zeroᵣ) (ℕₜ .zero [[ ⊢uℕ , ⊢nℕ , du ]] n≡n zeroᵣ)
            (ℕₜ .zero [[ ⊢vℕ , ⊢oℕ , dv ]] n≡n₂ zeroᵣ) (ℕₜ .zero [[ ⊢wℕ , ⊢pℕ , dw ]] n≡n₃ zeroᵣ)
            (ℕₜ₌ .zero .zero d₄ d′ k≡k′ zeroᵣ) (ℕₜ₌ .zero .zero d₅ d′₁ k≡k′₁ zeroᵣ) =
  let [t] = ℕₜ zero [[ ⊢tℕ , ⊢mℕ , dt ]] n≡n₁ zeroᵣ
      [u] = ℕₜ zero [[ ⊢uℕ , ⊢nℕ , du ]] n≡n zeroᵣ
      [v] = ℕₜ zero [[ ⊢vℕ , ⊢oℕ , dv ]] n≡n₂ zeroᵣ
      [w] = ℕₜ zero [[ ⊢wℕ , ⊢pℕ , dw ]] n≡n₃ zeroᵣ
      nfId = univ⇒* ((IdℕRed*Term′ ⊢tℕ ⊢mℕ dt ⊢uℕ)
        ⇨∷* (Idℕ0Red*Term′ ⊢uℕ ⊢nℕ du ⇨∷* (Id-ℕ-00 ⊢Γ ⇨ id (Unitⱼ ⊢Γ))))
      nfId' = univ⇒* ((IdℕRed*Term′ ⊢vℕ ⊢oℕ dv ⊢wℕ)
        ⇨∷* (Idℕ0Red*Term′ ⊢wℕ ⊢pℕ dw ⇨∷* (Id-ℕ-00 ⊢Γ ⇨ id (Unitⱼ ⊢Γ))))
      [Unit] = UnitType ⊢Γ
      [IdA] , [IdA≡ℕ] = redSubst* nfId [Unit]
      [IdB] , [IdB≡ℕ] = redSubst* nfId' [Unit]
      [IdA≡ℕ]′ = irrelevanceEq {A = Id ℕ t u} {B = Unit} {l = ι ⁰} {l′ = l} [IdA] ([Id]ℕ ⊢Γ [t] [u]) [IdA≡ℕ] 
      [IdB≡ℕ]′ = irrelevanceEq {A = Id ℕ v w} {B = Unit} {l = ι ⁰} {l′ = l} [IdB] ([Id]ℕ ⊢Γ [v] [w]) [IdB≡ℕ] 
  in transEq {A = Id ℕ t u} {B = Unit} {C = Id ℕ v w} {l = l} {l′ = ι ⁰} {l″ = l} ([Id]ℕ ⊢Γ [t] [u]) [Unit] ([Id]ℕ ⊢Γ [v] [w])
                  [IdA≡ℕ]′  (symEq {A = Id ℕ v w} {B = Unit} {l = l} {l′ = ι ⁰} ([Id]ℕ ⊢Γ [v] [w]) [Unit] [IdB≡ℕ]′) 


[IdExt]ℕ {Γ} {l} {t} {u} {v} {w} ⊢Γ (ℕₜ .(suc _) [[ ⊢tℕ , ⊢mℕ , dt ]] n≡n₁ (sucᵣ {t'} [t'])) (ℕₜ n [[ ⊢uℕ , ⊢nℕ , du ]] n≡n (ne (neNfₜ neKu ⊢ku k≡ku)))
         (ℕₜ .(suc _) [[ ⊢vℕ , ⊢oℕ , dv ]] n≡n₂ (sucᵣ {v'} [v'])) (ℕₜ n₃ [[ ⊢wℕ , ⊢pℕ , dw ]] n≡n₃ (ne (neNfₜ neKw ⊢kw k≡kw)))
         (ℕₜ₌ .(suc _) .(suc _) d₄ d′ k≡k′ (sucᵣ [t≡v'])) (ℕₜ₌ k₁ k′₁ d₅ d′₁ k≡k′₁ (ne (neNfₜ₌ neK neM K~M))) = 
  let t≡t' = suc-PE-injectivity (whrDet*Term (dt , sucₙ) (redₜ d₄ , sucₙ))
      v≡v' = suc-PE-injectivity (whrDet*Term (dv , sucₙ) (redₜ d′ , sucₙ))
      u≡u' = whrDet*Term (du , ne neKu) (redₜ d₅ , ne neK)
      w≡w' = whrDet*Term (dw , ne neKw) (redₜ d′₁ , ne neM)
      [t] = ℕₜ (suc _) [[ ⊢tℕ , ⊢mℕ , dt ]] n≡n₁ (sucᵣ [t'])
      [u] = ℕₜ n [[ ⊢uℕ , ⊢nℕ , du ]] n≡n (ne (neNfₜ neKu ⊢ku k≡ku))
      [v] = ℕₜ (suc _) [[ ⊢vℕ , ⊢oℕ , dv ]] n≡n₂ (sucᵣ [v'])
      [w] = ℕₜ n₃ [[ ⊢wℕ , ⊢pℕ , dw ]] n≡n₃ (ne (neNfₜ neKw ⊢kw k≡kw))
      [suct'] = ℕₜ (suc t') (idRedTerm:*: ⊢mℕ) n≡n₁ (sucᵣ [t'])
      [n] = ℕₜ n (idRedTerm:*: ⊢nℕ) n≡n (ne (neNfₜ neKu ⊢ku k≡ku))
      [sucv'] = ℕₜ (suc v') (idRedTerm:*: ⊢oℕ) n≡n₂ (sucᵣ [v'])
      [n₃] = ℕₜ n₃ (idRedTerm:*: ⊢pℕ) n≡n₃ (ne (neNfₜ neKw ⊢kw k≡kw))
      ⊢t′ℕ = escapeTerm {l = ι ⁰} ([ℕ] ⊢Γ) [t']
      ⊢v′ℕ = escapeTerm {l = ι ⁰} ([ℕ] ⊢Γ) [v']
      nfId = univ⇒* ((IdℕRed*Term′ ⊢tℕ ⊢mℕ dt ⊢uℕ) ⇨∷* IdℕSRed*Term′ ⊢t′ℕ ⊢uℕ ⊢nℕ du)
      nfId' = univ⇒* ((IdℕRed*Term′ ⊢vℕ ⊢oℕ dv ⊢wℕ) ⇨∷* IdℕSRed*Term′ ⊢v′ℕ ⊢wℕ ⊢pℕ dw)
      [IdA] , [IdA≡ℕ] = redSubst* nfId ([Id]ℕ ⊢Γ [suct'] [n])
      [IdB] , [IdB≡ℕ] = redSubst* nfId' ([Id]ℕ ⊢Γ [sucv'] [n₃])
      [IdA≡ℕ]′ = irrelevanceEq {A = Id ℕ t u} {B = Id ℕ (suc t') n} {l = ι ⁰} {l′ = l} [IdA] ([Id]ℕ ⊢Γ [t] [u]) [IdA≡ℕ] 
      [IdB≡ℕ]′ = irrelevanceEq {A = Id ℕ v w} {B = Id ℕ (suc v') n₃} {l = ι ⁰} {l′ = l} [IdB] ([Id]ℕ ⊢Γ [v] [w]) [IdB≡ℕ]
      [Idneutral] : Γ ⊩⟨ l ⟩ Id ℕ (suc t') n ≡ Id ℕ (suc v') n₃ ^ [ % , ι ⁰ ] / ([Id]ℕ ⊢Γ [suct'] [n])
      [Idneutral] = ne₌ (Id ℕ (suc v') n₃) (idRed:*: (univ (Idⱼ (ℕⱼ ⊢Γ) ⊢oℕ ⊢pℕ))) (IdℕSₙ neKw)
                (~-IdℕS ⊢Γ (let X = escapeTermEq {l = l} ([ℕ] ⊢Γ) [t≡v'] in
                                PE.subst (λ X → Γ ⊢ X ≅ _ ∷ ℕ ^ [ ! , ι ⁰ ]) (PE.sym t≡t') (PE.subst (λ X → Γ ⊢ _ ≅ X ∷ ℕ ^ [ ! , ι ⁰ ]) (PE.sym v≡v') X) )
                           (PE.subst (λ X → Γ ⊢ X ~ _ ∷ ℕ ^ [ ! , ι ⁰ ]) (PE.sym u≡u') (PE.subst (λ X → Γ ⊢ k₁ ~ X ∷ ℕ ^ [ ! , ι ⁰ ]) (PE.sym w≡w') K~M)))
  in transEq {A = Id ℕ t u} {B = Id ℕ (suc t') n} {C = Id ℕ v w} {l = l} {l′ = l} {l″ = l} ([Id]ℕ ⊢Γ [t] [u]) ([Id]ℕ ⊢Γ [suct'] [n]) ([Id]ℕ ⊢Γ [v] [w])
                  [IdA≡ℕ]′ 
                  (transEq {A = Id ℕ (suc t') n} {B = Id ℕ (suc v') n₃} {C = Id ℕ v w} {l = l} {l′ = l} {l″ = l} ([Id]ℕ ⊢Γ [suct'] [n]) ([Id]ℕ ⊢Γ [sucv'] [n₃]) ([Id]ℕ ⊢Γ [v] [w])
                                   [Idneutral] (symEq {A = Id ℕ v w} {B = Id ℕ (suc v') n₃} {l = l} {l′ = l} ([Id]ℕ ⊢Γ [v] [w]) ([Id]ℕ ⊢Γ [sucv'] [n₃]) [IdB≡ℕ]′)) 

[IdExt]ℕ {Γ} {l} {t} {u} {v} {w} ⊢Γ (ℕₜ n₁ [[ ⊢tℕ , ⊢mℕ , dt ]] n≡n₁ (ne (neNfₜ neKt ⊢kt k≡kt))) [u] (ℕₜ n₂ [[ ⊢vℕ , ⊢oℕ , dv ]] n≡n₂ (ne (neNfₜ neKv ⊢kv k≡kv))) [w]
            (ℕₜ₌ k k′ d₄ d′ k≡k′ (ne (neNfₜ₌ neK neM K~M))) [u=w] =
  let [t] = ℕₜ n₁ [[ ⊢tℕ , ⊢mℕ , dt ]] n≡n₁ (ne (neNfₜ neKt ⊢kt k≡kt))
      [v] = ℕₜ n₂ [[ ⊢vℕ , ⊢oℕ , dv ]] n≡n₂ (ne (neNfₜ neKv ⊢kv k≡kv))
      ⊢u = escapeTerm ([ℕ] {l = ι ⁰} ⊢Γ) [u]
      ⊢w = escapeTerm ([ℕ] {l = ι ⁰} ⊢Γ) [w]
      u≡w = escapeTermEq {l = ι ⁰} ([ℕ] ⊢Γ) [u=w]
      t≡t' = whrDet*Term (dt , ne neKt) (redₜ d₄ , ne neK)
      v≡v' = whrDet*Term (dv , ne neKv) (redₜ d′ , ne neM)
      nfId = univ⇒* (IdℕRed*Term′ ⊢tℕ ⊢mℕ dt ⊢u) 
      nfId' = univ⇒* (IdℕRed*Term′ ⊢vℕ ⊢oℕ dv ⊢w)
      [n₁] = ℕₜ n₁ (idRedTerm:*: ⊢mℕ) n≡n₁ (ne (neNfₜ neKt ⊢kt k≡kt))
      [n₂] = ℕₜ n₂ (idRedTerm:*: ⊢oℕ) n≡n₂ (ne (neNfₜ neKv ⊢kv k≡kv))
      [IdA] , [IdA≡ℕ] = redSubst* nfId ([Id]ℕ ⊢Γ [n₁] [u])
      [IdB] , [IdB≡ℕ] = redSubst* nfId' ([Id]ℕ ⊢Γ [n₂] [w])
      [IdA≡ℕ]′ = irrelevanceEq {A = Id ℕ t u} {B = Id ℕ n₁ u} {l = ι ⁰} {l′ = l} [IdA] ([Id]ℕ ⊢Γ [t] [u]) [IdA≡ℕ] 
      [IdB≡ℕ]′ = irrelevanceEq {A = Id ℕ v w} {B = Id ℕ n₂ w} {l = ι ⁰} {l′ = l} [IdB] ([Id]ℕ ⊢Γ [v] [w]) [IdB≡ℕ]
      [Idneutral] : Γ ⊩⟨ l ⟩ Id ℕ n₁ u ≡ Id ℕ n₂ w ^ [ % , ι ⁰ ] / ([Id]ℕ ⊢Γ [n₁] [u])
      [Idneutral] = ne₌ (Id ℕ n₂ w) (idRed:*: (univ (Idⱼ (ℕⱼ ⊢Γ) ⊢oℕ ⊢w))) (Idℕₙ neKv)
                        (~-Idℕ ⊢Γ (PE.subst (λ X → Γ ⊢ X ~ _ ∷ ℕ ^ [ ! , ι ⁰ ]) (PE.sym t≡t') (PE.subst (λ X → Γ ⊢ _ ~ X ∷ ℕ ^ [ ! , ι ⁰ ]) (PE.sym v≡v') K~M)) u≡w)
  in transEq {A = Id ℕ t u} {B = Id ℕ n₁ u} {C = Id ℕ v w} {l = l} {l′ = l} {l″ = l} ([Id]ℕ ⊢Γ [t] [u]) ([Id]ℕ ⊢Γ [n₁] [u]) ([Id]ℕ ⊢Γ [v] [w])
                  [IdA≡ℕ]′ 
                  (transEq {A = Id ℕ n₁ u} {B = Id ℕ n₂ w} {C = Id ℕ v w} {l = l} {l′ = l} {l″ = l} ([Id]ℕ ⊢Γ [n₁] [u]) ([Id]ℕ ⊢Γ [n₂] [w]) ([Id]ℕ ⊢Γ [v] [w])
                                   [Idneutral] (symEq {A = Id ℕ v w} {B = Id ℕ n₂ w} {l = l} {l′ = l} ([Id]ℕ ⊢Γ [v] [w]) ([Id]ℕ ⊢Γ [n₂] [w]) [IdB≡ℕ]′)) 

[IdExt]ℕ {Γ} {l} {t} {u} {v} {w} ⊢Γ (ℕₜ .zero [[ ⊢tℕ , ⊢mℕ , dt ]] n≡n₁ zeroᵣ) (ℕₜ n [[ ⊢uℕ , ⊢nℕ , du ]] n≡n (ne (neNfₜ neKu ⊢ku k≡ku)))
         (ℕₜ .zero [[ ⊢vℕ , ⊢oℕ , dv ]] n≡n₂ zeroᵣ) (ℕₜ n₃ [[ ⊢wℕ , ⊢pℕ , dw ]] n≡n₃ (ne (neNfₜ neKw ⊢kw k≡kw)))
         (ℕₜ₌ .zero .zero d₄ d′ k≡k′ zeroᵣ) (ℕₜ₌ k₁ k′₁ d₅ d′₁ k≡k′₁ (ne (neNfₜ₌ neK neM K~M))) = 
  let u≡u' = whrDet*Term (du , ne neKu) (redₜ d₅ , ne neK)
      w≡w' = whrDet*Term (dw , ne neKw) (redₜ d′₁ , ne neM)
      [t] = ℕₜ zero [[ ⊢tℕ , ⊢mℕ , dt ]] n≡n₁ zeroᵣ
      [u] = ℕₜ n [[ ⊢uℕ , ⊢nℕ , du ]] n≡n (ne (neNfₜ neKu ⊢ku k≡ku))
      [v] = ℕₜ zero [[ ⊢vℕ , ⊢oℕ , dv ]] n≡n₂ zeroᵣ
      [w] = ℕₜ n₃ [[ ⊢wℕ , ⊢pℕ , dw ]] n≡n₃ (ne (neNfₜ neKw ⊢kw k≡kw))
      [n] = ℕₜ n (idRedTerm:*: ⊢nℕ) n≡n (ne (neNfₜ neKu ⊢ku k≡ku))
      [n₃] = ℕₜ n₃ (idRedTerm:*: ⊢pℕ) n≡n₃ (ne (neNfₜ neKw ⊢kw k≡kw))
      [zero] = ℕₜ zero (idRedTerm:*: (zeroⱼ ⊢Γ)) (≅ₜ-zerorefl ⊢Γ) zeroᵣ
      nfId = univ⇒* ((IdℕRed*Term′ ⊢tℕ ⊢mℕ dt ⊢uℕ) ⇨∷* Idℕ0Red*Term′ ⊢uℕ ⊢nℕ du)
      nfId' = univ⇒* ((IdℕRed*Term′ ⊢vℕ ⊢oℕ dv ⊢wℕ) ⇨∷* Idℕ0Red*Term′ ⊢wℕ ⊢pℕ dw)
      [IdA] , [IdA≡ℕ] = redSubst* nfId ([Id]ℕ ⊢Γ [zero] [n])
      [IdB] , [IdB≡ℕ] = redSubst* nfId' ([Id]ℕ ⊢Γ [zero] [n₃])
      [IdA≡ℕ]′ = irrelevanceEq {A = Id ℕ t u} {B = Id ℕ zero n} {l = ι ⁰} {l′ = l} [IdA] ([Id]ℕ ⊢Γ [t] [u]) [IdA≡ℕ] 
      [IdB≡ℕ]′ = irrelevanceEq {A = Id ℕ v w} {B = Id ℕ zero n₃} {l = ι ⁰} {l′ = l} [IdB] ([Id]ℕ ⊢Γ [v] [w]) [IdB≡ℕ]
      [Idneutral] : Γ ⊩⟨ l ⟩ Id ℕ zero n ≡ Id ℕ zero n₃ ^ [ % , ι ⁰ ] / ([Id]ℕ ⊢Γ [zero] [n])
      [Idneutral] = ne₌ (Id ℕ zero n₃) (idRed:*: (univ (Idⱼ (ℕⱼ ⊢Γ) ⊢oℕ ⊢pℕ))) (Idℕ0ₙ neKw)
                (~-Idℕ0 ⊢Γ (PE.subst (λ X → Γ ⊢ X ~ _ ∷ ℕ ^ [ ! , ι ⁰ ]) (PE.sym u≡u') (PE.subst (λ X → Γ ⊢ k₁ ~ X ∷ ℕ ^ [ ! , ι ⁰ ]) (PE.sym w≡w') K~M)))
  in transEq {A = Id ℕ t u} {B = Id ℕ zero n} {C = Id ℕ v w} {l = l} {l′ = l} {l″ = l} ([Id]ℕ ⊢Γ [t] [u]) ([Id]ℕ ⊢Γ [zero] [n]) ([Id]ℕ ⊢Γ [v] [w])
                  [IdA≡ℕ]′ 
                  (transEq {A = Id ℕ zero n} {B = Id ℕ zero n₃} {C = Id ℕ v w} {l = l} {l′ = l} {l″ = l} ([Id]ℕ ⊢Γ [zero] [n]) ([Id]ℕ ⊢Γ [zero] [n₃]) ([Id]ℕ ⊢Γ [v] [w])
                                   [Idneutral] (symEq {A = Id ℕ v w} {B = Id ℕ zero n₃} {l = l} {l′ = l} ([Id]ℕ ⊢Γ [v] [w]) ([Id]ℕ ⊢Γ [zero] [n₃]) [IdB≡ℕ]′)) 

-- refuting cases


[IdExt]ℕ ⊢Γ (ℕₜ .zero d₁ n≡n₁ zeroᵣ) _ _ _ (ℕₜ₌ .(suc _) .(suc _) d₄ d′ k≡k′ (sucᵣ x)) _ = ⊥-elim (zero≢suc (whrDet*Term (redₜ d₁ , zeroₙ) (redₜ d₄ , sucₙ)))
[IdExt]ℕ ⊢Γ (ℕₜ n₁ d₁ n≡n₁ (ne (neNfₜ neK ⊢k k≡k))) _ _ _ (ℕₜ₌ .(suc _) .(suc _) d₄ d′ k≡k′ (sucᵣ x)) _ = ⊥-elim (suc≢ne neK (whrDet*Term (redₜ d₄ , sucₙ) (redₜ d₁ , ne neK)))
[IdExt]ℕ ⊢Γ _ _ (ℕₜ .zero d₂ n≡n₂ zeroᵣ) _ (ℕₜ₌ .(suc _) .(suc _) d₄ d′ k≡k′ (sucᵣ x)) _ = ⊥-elim (zero≢suc (whrDet*Term (redₜ d₂ , zeroₙ) (redₜ d′ , sucₙ)))
[IdExt]ℕ ⊢Γ _ _ (ℕₜ n₂ d₂ n≡n₂ (ne (neNfₜ neK ⊢k k≡k))) _ (ℕₜ₌ .(suc _) .(suc _) d₄ d′ k≡k′ (sucᵣ x)) _ = ⊥-elim (suc≢ne neK (whrDet*Term (redₜ d′ , sucₙ) (redₜ d₂ , ne neK)))

[IdExt]ℕ ⊢Γ _ (ℕₜ .zero d₁ n≡n₁ zeroᵣ) _ _ _ (ℕₜ₌ .(suc _) .(suc _) d₄ d′ k≡k′ (sucᵣ x)) = ⊥-elim (zero≢suc (whrDet*Term (redₜ d₁ , zeroₙ) (redₜ d₄ , sucₙ)))
[IdExt]ℕ ⊢Γ _ (ℕₜ n₁ d₁ n≡n₁ (ne (neNfₜ neK ⊢k k≡k))) _ _ _ (ℕₜ₌ .(suc _) .(suc _) d₄ d′ k≡k′ (sucᵣ x)) = ⊥-elim (suc≢ne neK (whrDet*Term (redₜ d₄ , sucₙ) (redₜ d₁ , ne neK)))
[IdExt]ℕ ⊢Γ _ _ _ (ℕₜ .zero d₂ n≡n₂ zeroᵣ) _ (ℕₜ₌ .(suc _) .(suc _) d₄ d′ k≡k′ (sucᵣ x)) = ⊥-elim (zero≢suc (whrDet*Term (redₜ d₂ , zeroₙ) (redₜ d′ , sucₙ)))
[IdExt]ℕ ⊢Γ _ _ _ (ℕₜ n₂ d₂ n≡n₂ (ne (neNfₜ neK ⊢k k≡k))) _ (ℕₜ₌ .(suc _) .(suc _) d₄ d′ k≡k′ (sucᵣ x)) = ⊥-elim (suc≢ne neK (whrDet*Term (redₜ d′ , sucₙ) (redₜ d₂ , ne neK)))

[IdExt]ℕ ⊢Γ (ℕₜ .(suc _) d n≡n (sucᵣ x₃)) _ _ _ (ℕₜ₌ .zero .zero d₅ d′₁ k≡k′₁ zeroᵣ) _ = ⊥-elim (zero≢suc (whrDet*Term (redₜ d₅ , zeroₙ) (redₜ d , sucₙ)))
[IdExt]ℕ ⊢Γ (ℕₜ n d n≡n (ne (neNfₜ neK ⊢k k≡k))) _ _ _ (ℕₜ₌ .zero .zero d₅ d′₁ k≡k′₁ zeroᵣ) _ = ⊥-elim (zero≢ne neK (whrDet*Term (redₜ d₅ , zeroₙ) (redₜ d , ne neK)))
[IdExt]ℕ ⊢Γ _ _ (ℕₜ .(suc _) d₃ n≡n₃ (sucᵣ x₃)) _ (ℕₜ₌ .zero .zero d₅ d′₁ k≡k′₁ zeroᵣ) _ = ⊥-elim (zero≢suc (whrDet*Term (redₜ d′₁ , zeroₙ) (redₜ d₃ , sucₙ)))
[IdExt]ℕ ⊢Γ _ _ (ℕₜ n₃ d₃ n≡n₃ (ne (neNfₜ neK ⊢k k≡k))) _ (ℕₜ₌ .zero .zero d₅ d′₁ k≡k′₁ zeroᵣ) _ = ⊥-elim (zero≢ne neK (whrDet*Term (redₜ d′₁ , zeroₙ) (redₜ d₃ , ne neK)))

[IdExt]ℕ ⊢Γ _ (ℕₜ .(suc _) d n≡n (sucᵣ x₃)) _ _ _ (ℕₜ₌ .zero .zero d₅ d′₁ k≡k′₁ zeroᵣ) = ⊥-elim (zero≢suc (whrDet*Term (redₜ d₅ , zeroₙ) (redₜ d , sucₙ)))
[IdExt]ℕ ⊢Γ _ (ℕₜ n d n≡n (ne (neNfₜ neK ⊢k k≡k))) _ _ _ (ℕₜ₌ .zero .zero d₅ d′₁ k≡k′₁ zeroᵣ) = ⊥-elim (zero≢ne neK (whrDet*Term (redₜ d₅ , zeroₙ) (redₜ d , ne neK)))
[IdExt]ℕ ⊢Γ _ _ _ (ℕₜ .(suc _) d₃ n≡n₃ (sucᵣ x₃)) _ (ℕₜ₌ .zero .zero d₅ d′₁ k≡k′₁ zeroᵣ) = ⊥-elim (zero≢suc (whrDet*Term (redₜ d′₁ , zeroₙ) (redₜ d₃ , sucₙ)))
[IdExt]ℕ ⊢Γ _ _ _ (ℕₜ n₃ d₃ n≡n₃ (ne (neNfₜ neK ⊢k k≡k))) _ (ℕₜ₌ .zero .zero d₅ d′₁ k≡k′₁ zeroᵣ) = ⊥-elim (zero≢ne neK (whrDet*Term (redₜ d′₁ , zeroₙ) (redₜ d₃ , ne neK)))

[IdExt]ℕ ⊢Γ (ℕₜ .(suc _) d₁ n≡n₁ (sucᵣ x₁)) _ _ _ (ℕₜ₌ k k′ d₄ d′ k≡k′ (ne (neNfₜ₌ neK neM k≡m))) _ =  ⊥-elim (suc≢ne neK (whrDet*Term (redₜ d₁ , sucₙ) (redₜ d₄ , ne neK)))
[IdExt]ℕ ⊢Γ (ℕₜ .zero d₁ n≡n₁ zeroᵣ) _ _ _ (ℕₜ₌ k k′ d₄ d′ k≡k′ (ne (neNfₜ₌ neK neM k≡m))) _ = ⊥-elim (zero≢ne neK (whrDet*Term (redₜ d₁ , zeroₙ) (redₜ d₄ , ne neK)))
[IdExt]ℕ ⊢Γ _ _ (ℕₜ .(suc _) d₁ n≡n₁ (sucᵣ x₁)) _ (ℕₜ₌ k k′ d₄ d′ k≡k′ (ne (neNfₜ₌ neK neM k≡m))) _ =  ⊥-elim (suc≢ne neM (whrDet*Term (redₜ d₁ , sucₙ) (redₜ d′ , ne neM)))
[IdExt]ℕ ⊢Γ _ _ (ℕₜ .zero d₁ n≡n₁ zeroᵣ) _ (ℕₜ₌ k k′ d₄ d′ k≡k′ (ne (neNfₜ₌ neK neM k≡m))) _ = ⊥-elim (zero≢ne neM (whrDet*Term (redₜ d₁ , zeroₙ) (redₜ d′ , ne neM)))

[IdExt]ℕ ⊢Γ _ (ℕₜ .(suc _) d₁ n≡n₁ (sucᵣ x₁)) _ _ _ (ℕₜ₌ k k′ d₄ d′ k≡k′ (ne (neNfₜ₌ neK neM k≡m))) =  ⊥-elim (suc≢ne neK (whrDet*Term (redₜ d₁ , sucₙ) (redₜ d₄ , ne neK)))
[IdExt]ℕ ⊢Γ _ (ℕₜ .zero d₁ n≡n₁ zeroᵣ) _ _ _ (ℕₜ₌ k k′ d₄ d′ k≡k′ (ne (neNfₜ₌ neK neM k≡m))) = ⊥-elim (zero≢ne neK (whrDet*Term (redₜ d₁ , zeroₙ) (redₜ d₄ , ne neK)))
[IdExt]ℕ ⊢Γ _ _ _ (ℕₜ .(suc _) d₁ n≡n₁ (sucᵣ x₁)) _ (ℕₜ₌ k k′ d₄ d′ k≡k′ (ne (neNfₜ₌ neK neM k≡m))) =  ⊥-elim (suc≢ne neM (whrDet*Term (redₜ d₁ , sucₙ) (redₜ d′ , ne neM)))
[IdExt]ℕ ⊢Γ _ _ _ (ℕₜ .zero d₁ n≡n₁ zeroᵣ) _ (ℕₜ₌ k k′ d₄ d′ k≡k′ (ne (neNfₜ₌ neK neM k≡m))) = ⊥-elim (zero≢ne neM (whrDet*Term (redₜ d₁ , zeroₙ) (redₜ d′ , ne neM)))


[Id] : ∀ {A t u Γ l lA}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ l ⟩ A ^ [ ! , ι lA ])
         ([t] : Γ ⊩⟨ l ⟩ t ∷ A ^ [ ! , ι lA ] / [A])
         ([u] : Γ ⊩⟨ l ⟩ u ∷ A ^ [ ! , ι lA ] / [A])
       → Γ ⊩⟨ l ⟩ Id A t u ^ [ % , ι lA ]
[IdExt] : ∀ {A B t v u w Γ l l' lA}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ l ⟩ A ^ [ ! , ι lA ])
         ([B] : Γ ⊩⟨ l' ⟩ B ^ [ ! , ι lA ])
         ([A≡B] : Γ ⊩⟨ l ⟩ A ≡ B ^ [ ! , ι lA ] / [A])
         ([t] : Γ ⊩⟨ l ⟩ t ∷ A ^ [ ! , ι lA ] / [A])
         ([v] : Γ ⊩⟨ l' ⟩ v ∷ B ^ [ ! , ι lA ] / [B])
         ([t≡v] : Γ ⊩⟨ l ⟩ t ≡ v ∷ A ^ [ ! , ι lA ] / [A])
         ([u] : Γ ⊩⟨ l ⟩ u ∷ A ^ [ ! , ι lA ] / [A])
         ([w] : Γ ⊩⟨ l' ⟩ w ∷ B ^ [ ! , ι lA ] / [B])
         ([u≡w] : Γ ⊩⟨ l ⟩ u ≡ w ∷ A ^ [ ! , ι lA ] / [A])
       → Γ ⊩⟨ l ⟩ Id A t u ≡ Id B v w ^ [ % , ι lA ] / [Id] ⊢Γ [A] [t] [u]
[IdExtShape] : ∀ {A B t v u w Γ l l' lA}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ l ⟩ A ^ [ ! , ι lA ])
         ([B] : Γ ⊩⟨ l' ⟩ B ^ [ ! , ι lA ])
         (ShapeA : ShapeView Γ l l' A B [ ! , ι lA ] [ ! , ι lA ] [A] [B])
         ([A≡B] : Γ ⊩⟨ l ⟩ A ≡ B ^ [ ! , ι lA ] / [A])
         ([t] : Γ ⊩⟨ l ⟩ t ∷ A ^ [ ! , ι lA ] / [A])
         ([v] : Γ ⊩⟨ l' ⟩ v ∷ B ^ [ ! , ι lA ] / [B])
         ([t≡v] : Γ ⊩⟨ l ⟩ t ≡ v ∷ A ^ [ ! , ι lA ] / [A])
         ([u] : Γ ⊩⟨ l ⟩ u ∷ A ^ [ ! , ι lA ] / [A])
         ([w] : Γ ⊩⟨ l' ⟩ w ∷ B ^ [ ! , ι lA ] / [B])
         ([u≡w] : Γ ⊩⟨ l ⟩ u ≡ w ∷ A ^ [ ! , ι lA ] / [A])
       → Γ ⊩⟨ l ⟩ Id A t u ≡ Id B v w ^ [ % , ι lA ] / [Id] ⊢Γ [A] [t] [u]

[Id] ⊢Γ (ℕᵣ [[ ⊢A , ⊢B , D ]]) (ℕₜ n d n≡n prop) (ℕₜ n₁ d₁ n≡n₁ prop₁) =
  let
    [[ ⊢tℕ , _ , _ ]] = d
    [[ ⊢uℕ , _ , _ ]] = d₁
  in proj₁ (redSubst* (IdRed* (conv ⊢tℕ (sym (subset* D))) (conv ⊢uℕ (sym (subset* D))) D)
    ([Id]ℕ ⊢Γ (ℕₜ n d n≡n prop) (ℕₜ n₁ d₁ n≡n₁ prop₁)))

[Id] ⊢Γ (Uᵣ (Uᵣ r ¹ l< () d)) [t] [u]
[Id] {A} {t} {u} {Γ} {ι .¹} {.¹} ⊢Γ (Uᵣ (Uᵣ ! ⁰ emb< PE.refl [[ ⊢A , ⊢B , D ]])) (Uₜ K d typeK K≡K [t]) (Uₜ M d₁ typeM M≡M [u]) =
  let
    [t0] : Γ ⊩⟨ ι ⁰ ⟩ t ^ [ ! , ι ⁰ ]
    [t0] = PE.subst (λ X → Γ ⊩⟨ ι ⁰ ⟩ X ^ [ ! , ι ⁰ ]) (wk-id t) ([t] Twk.id ⊢Γ)
    [u0] = PE.subst (λ X → Γ ⊩⟨ ι ⁰ ⟩ X ^ [ ! , ι ⁰ ]) (wk-id u) ([u] Twk.id ⊢Γ)
    ⊢tA = conv (un-univ (escape [t0])) (sym (subset* D))
    ⊢uA = conv (un-univ (escape [u0])) (sym (subset* D))
  in proj₁ (redSubst* (IdRed* ⊢tA ⊢uA D) ([Id]U ⊢Γ [t0] [u0]))

[Id] {A} {t} {u} {Γ} {ι .¹} {.¹} ⊢Γ (Uᵣ (Uᵣ % ⁰ emb< PE.refl [[ ⊢A , ⊢B , D ]])) (Uₜ K d typeK K≡K [t]) (Uₜ M d₁ typeM M≡M [u]) =
  let
    [t0] : Γ ⊩⟨ ι ⁰ ⟩ t ^ [ % , ι ⁰ ]
    [t0] = PE.subst (λ X → Γ ⊩⟨ ι ⁰ ⟩ X ^ [ % , ι ⁰ ]) (wk-id t) ([t] Twk.id ⊢Γ)
    [u0] = PE.subst (λ X → Γ ⊩⟨ ι ⁰ ⟩ X ^ [ % , ι ⁰ ]) (wk-id u) ([u] Twk.id ⊢Γ)
    ⊢tA = conv (un-univ (escape [t0])) (sym (subset* D))
    ⊢uA = conv (un-univ (escape [u0])) (sym (subset* D))
  in proj₁ (redSubst* (IdRed* ⊢tA ⊢uA D) ([Id]SProp ⊢Γ [t0] [u0]))

[Id] {A} {t} {u} {Γ} {l} {lA} ⊢Γ (ne′ K [[ ⊢A , ⊢B , D ]] neK K≡K) [t] [u] =
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

[Id] {A} {t} {u} {Γ} {l} {lA} ⊢Γ (Πᵣ′ rF lF lG lF≤ lG≤ F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext)
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
        [Id] = [Id] ⊢Δ ([G] [ρ] ⊢Δ [a]) [t∘a] [u∘a]
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
        [IdExt] : Δ ⊩⟨ l ⟩ (Id (wk (lift ρ) G [ a ]) (wk ρ t ∘ a) (wk ρ u ∘ a)) ≡ (Id (wk (lift ρ) G [ b ]) (wk ρ t ∘ b) (wk ρ u ∘ b)) ^ [ % , ι lG ] / [Id] ⊢Δ [Ga] [t∘a] [u∘a]
        [IdExt] = [IdExt] ⊢Δ [Ga] [Gb] [Ga≡Gb] [t∘a] [t∘b:Gb] [ta≡tb] [u∘a] [u∘b:Gb] [ua≡ub]
      in irrelevanceEq″
        (PE.cong₂ (λ X Y → Id _ (X ∘ a) (Y ∘ a)) (PE.sym (irrelevant-subst′ ρ t a)) (PE.sym (irrelevant-subst′ ρ u a)))
        (PE.cong₂ (λ X Y → Id _ (X ∘ b) (Y ∘ b)) (PE.sym (irrelevant-subst′ ρ t b)) (PE.sym (irrelevant-subst′ ρ u b)))
        PE.refl PE.refl
        ([Id] ⊢Δ [Ga] [t∘a] [u∘a]) ([idG] [ρ] ⊢Δ [a]) [IdExt]
  in Πᵣ (Πᵣ rF lF lG lF≤ lG≤ F (Id G ((wk1 t) ∘ (var 0)) ((wk1 u) ∘ (var 0)))
      [[ univ (Idⱼ (un-univ ⊢A) ⊢tA ⊢uA) , ⊢funext , Did ]]
      ⊢F ⊢idG
      (≅-univ (≅ₜ-Π-cong ⊢F (≅-un-univ (escapeEqRefl [F0]))
        (≅-un-univ (escapeEqRefl [idG0]))))
      [F] [idG] [idGext])

[Id] ⊢Γ (emb {l′ = ι ⁰} emb< [A]) [t] [u] = emb emb< ([Id] ⊢Γ [A] [t] [u])
[Id] ⊢Γ (emb {l′ = ι ¹} ∞< [A]) [t] [u] = emb ∞< ([Id] ⊢Γ [A] [t] [u])

[IdExtShape] {A} {B} {t} {v} {u} {w} {Γ} {.(ι ¹)} {.(ι ¹)} {lA} ⊢Γ _ _ (Uᵥ (Uᵣ ! .⁰ emb< PE.refl d) (Uᵣ r₁ .⁰ emb< PE.refl d₁)) [A≡B] [t] [v] [t≡v] [u] [w] [u≡w] =
  let U≡U = whrDet* (red d₁ , Uₙ) ([A≡B] , Uₙ)
      r≡r , _ = Univ-PE-injectivity U≡U
      [UA] = Uᵣ ! ⁰ emb< PE.refl d
      [UB] = Uᵣ r₁ ⁰ emb< PE.refl d₁
      [U] = Ugen ⊢Γ
      [U]' = Ugen ⊢Γ
      [UA]' , [UAeq] = redSubst* (red d) [U]
      [UB]' , [UBeq] = redSubst* (PE.subst (λ X → Γ ⊢ _ ⇒* Univ X _ ^ _) r≡r (red d₁)) [U]'
      [t]′ = convTerm₁ {t = t} [UA]' [U] [UAeq] (irrelevanceTerm (Uᵣ [UA]) [UA]' [t])
      [t^] = univEq [U] [t]′
      [v]′ = convTerm₁ {t = v} [UB]' [U] [UBeq] (irrelevanceTerm (Uᵣ [UB]) [UB]' [v])
      [v^] = univEq [U] [v]′
      [t≡v]′ = convEqTerm₁ {t = t} {u = v} [UA]' [U] [UAeq] (irrelevanceEqTerm (Uᵣ [UA]) [UA]' [t≡v])
      [t≡v^] = univEqEq [U] [t^] [t≡v]′
      [u]′ = convTerm₁ {t = u} [UA]' [U] [UAeq] (irrelevanceTerm (Uᵣ [UA]) [UA]' [u])
      [u^] = univEq [U] [u]′
      [w]′ = convTerm₁ {t = w} [UB]' [U] [UBeq] (irrelevanceTerm (Uᵣ [UB]) [UB]'  [w])
      [w^] = univEq [U] [w]′
      [u≡w]′ = convEqTerm₁ {t = u} {u = w} [UA]' [U] [UAeq] (irrelevanceEqTerm (Uᵣ [UA]) [UA]' [u≡w])
      [u≡w^] = univEqEq [U] [u^] [u≡w]′
      X = irrelevanceEq {A = Id (U ⁰) t u} {B = Id (U ⁰) v w} ([Id]U ⊢Γ [t^] [u^]) ([Id] ⊢Γ [U] [t]′ [u]′) ([IdExt]U ⊢Γ [t^] [v^] [t≡v^] [u^] [w^] [u≡w^])
      [IdA] , [IdA≡U] = redSubst* (IdRed* (escapeTerm (Uᵣ [UA]) [t]) (escapeTerm (Uᵣ [UA]) [u]) (red d)) ([Id] ⊢Γ [U] [t]′ [u]′)
      [IdB] , [IdB≡U] = redSubst* (IdRed* (escapeTerm (Uᵣ [UB]) [v]) (escapeTerm (Uᵣ [UB]) [w]) (PE.subst (λ X → Γ ⊢ _ ⇒* Univ X _ ^ _) r≡r (red d₁))) ([Id] ⊢Γ [U] [v]′ [w]′)
      [IdA≡U]′ = irrelevanceEq {A = Id A t u} {B = Id (U ⁰) t u} [IdA] ([Id] ⊢Γ (Uᵣ [UA]) [t] [u]) [IdA≡U]
      [IdB≡U]′ = irrelevanceEq {A = Id B v w} {B = Id (U ⁰) v w} [IdB] ([Id] ⊢Γ (Uᵣ [UB]) [v] [w]) [IdB≡U]
  in transEq {A = Id A t u} {B = Id (U _) t u} {C = Id B v w}  ([Id] ⊢Γ (Uᵣ [UA]) [t] [u]) ([Id] ⊢Γ [U] [t]′ [u]′) ([Id] ⊢Γ (Uᵣ [UB]) [v] [w])
                  [IdA≡U]′ 
                  (transEq {A = Id (U _) t u} {B = Id (U _) v w} {C = Id B v w} ([Id] ⊢Γ [U] [t]′ [u]′) ([Id] ⊢Γ [U] [v]′ [w]′) ([Id] ⊢Γ (Uᵣ [UB]) [v] [w])
                                   X (symEq {A = Id B v w} {B = Id (U _) v w} ([Id] ⊢Γ (Uᵣ [UB]) [v] [w]) ([Id] ⊢Γ [U] [v]′ [w]′) [IdB≡U]′)) 

[IdExtShape] {A} {B} {t} {v} {u} {w} {Γ} {.(ι ¹)} {.(ι ¹)} {lA} ⊢Γ _ _ (Uᵥ (Uᵣ % .⁰ emb< PE.refl d) (Uᵣ r₁ .⁰ emb< PE.refl d₁)) [A≡B] [t] [v] [t≡v] [u] [w] [u≡w] =
  let U≡U = whrDet* (red d₁ , Uₙ) ([A≡B] , Uₙ)
      r≡r , _ = Univ-PE-injectivity U≡U
      [UA] = Uᵣ % ⁰ emb< PE.refl d
      [UB] = Uᵣ r₁ ⁰ emb< PE.refl d₁
      [U] = Ugen ⊢Γ
      [U]' = Ugen ⊢Γ
      [UA]' , [UAeq] = redSubst* (red d) [U]
      [UB]' , [UBeq] = redSubst* (PE.subst (λ X → Γ ⊢ _ ⇒* Univ X _ ^ _) r≡r (red d₁)) [U]'
      [t]′ = convTerm₁ {t = t} [UA]' [U] [UAeq] (irrelevanceTerm (Uᵣ [UA]) [UA]' [t])
      [t^] = univEq [U] [t]′
      [v]′ = convTerm₁ {t = v} [UB]' [U] [UBeq] (irrelevanceTerm (Uᵣ [UB]) [UB]' [v])
      [v^] = univEq [U] [v]′
      [t≡v]′ = convEqTerm₁ {t = t} {u = v} [UA]' [U] [UAeq] (irrelevanceEqTerm (Uᵣ [UA]) [UA]' [t≡v])
      [t≡v^] = univEqEq [U] [t^] [t≡v]′
      [u]′ = convTerm₁ {t = u} [UA]' [U] [UAeq] (irrelevanceTerm (Uᵣ [UA]) [UA]' [u])
      [u^] = univEq [U] [u]′
      [w]′ = convTerm₁ {t = w} [UB]' [U] [UBeq] (irrelevanceTerm (Uᵣ [UB]) [UB]'  [w])
      [w^] = univEq [U] [w]′
      [u≡w]′ = convEqTerm₁ {t = u} {u = w} [UA]' [U] [UAeq] (irrelevanceEqTerm (Uᵣ [UA]) [UA]' [u≡w])
      [u≡w^] = univEqEq [U] [u^] [u≡w]′
      X = irrelevanceEq {A = Id (SProp ⁰) t u} {B = Id (SProp ⁰) v w} ([Id]SProp ⊢Γ [t^] [u^]) ([Id] ⊢Γ [U] [t]′ [u]′) ([IdExt]SProp ⊢Γ [t^] [v^] [t≡v^] [u^] [w^] [u≡w^])
      [IdA] , [IdA≡U] = redSubst* (IdRed* (escapeTerm (Uᵣ [UA]) [t]) (escapeTerm (Uᵣ [UA]) [u]) (red d)) ([Id] ⊢Γ [U] [t]′ [u]′)
      [IdB] , [IdB≡U] = redSubst* (IdRed* (escapeTerm (Uᵣ [UB]) [v]) (escapeTerm (Uᵣ [UB]) [w]) (PE.subst (λ X → Γ ⊢ _ ⇒* Univ X _ ^ _) r≡r (red d₁))) ([Id] ⊢Γ [U] [v]′ [w]′)
      [IdA≡U]′ = irrelevanceEq {A = Id A t u} {B = Id (SProp ⁰) t u} [IdA] ([Id] ⊢Γ (Uᵣ [UA]) [t] [u]) [IdA≡U]
      [IdB≡U]′ = irrelevanceEq {A = Id B v w} {B = Id (SProp ⁰) v w} [IdB] ([Id] ⊢Γ (Uᵣ [UB]) [v] [w]) [IdB≡U]
  in transEq {A = Id A t u} {B = Id (SProp _) t u} {C = Id B v w}  ([Id] ⊢Γ (Uᵣ [UA]) [t] [u]) ([Id] ⊢Γ [U] [t]′ [u]′) ([Id] ⊢Γ (Uᵣ [UB]) [v] [w])
                  [IdA≡U]′ 
                  (transEq {A = Id (SProp _) t u} {B = Id (SProp _) v w} {C = Id B v w} ([Id] ⊢Γ [U] [t]′ [u]′) ([Id] ⊢Γ [U] [v]′ [w]′) ([Id] ⊢Γ (Uᵣ [UB]) [v] [w])
                                   X (symEq {A = Id B v w} {B = Id (SProp _) v w} ([Id] ⊢Γ (Uᵣ [UB]) [v] [w]) ([Id] ⊢Γ [U] [v]′ [w]′) [IdB≡U]′)) 
[IdExtShape] {A} {B} {t} {v} {u} {w} {Γ} {l} {l'} {lA}  ⊢Γ .(ne _) .(ne _) (ne (ne K [[ ⊢A , ⊢B , D ]] neK K≡K) neB) (ne₌ M [[ ⊢A′ , ⊢B′ ,  D′ ]] neM K≡M) [t] [t′] [t≡t′] [u] [u′] [u≡u′] =
  let
    [A] = (ne′ K [[ ⊢A , ⊢B , D ]] neK K≡K)
    ⊢t′A′ = escapeTerm {l = l'} (ne neB) [t′]
    ⊢u′A′ = escapeTerm {l = l'} (ne neB) [u′]
    A≡K = subset* D
    t≡t′ : Γ ⊢ t ≅ v ∷ K ^ [ ! , ι lA ]
    t≡t′ = ≅-conv (escapeTermEq {l = l} [A] [t≡t′]) A≡K
    u≡u′ = ≅-conv (escapeTermEq {l = l} [A] [u≡u′]) A≡K
  in ne₌ (Id M v w) (univ:⇒*: (IdRed*Term ⊢t′A′ ⊢u′A′ [[ ⊢A′ , ⊢B′ , D′ ]]))
         (Idₙ neM) (~-Id K≡M t≡t′ u≡u′)

[IdExtShape] {A} {B} {t} {v} {u} {w} {Γ} {l} {l'} ⊢Γ _ _ (ℕᵥ [[ ⊢A , ⊢B , D ]] [[ ⊢A₁ , ⊢B₁ , D₁ ]]) [A≡B] [t] [v] [t≡v] [u] [w] [u≡w] =
  let [A] = [[ ⊢A , ⊢B , D ]]
      [B] = [[ ⊢A₁ , ⊢B₁ , D₁ ]]
      [ℕ]' = [ℕ] {l = l} ⊢Γ
      [A]' , [Aeq] = redSubst* D [ℕ]'
      [B]' , [Beq] = redSubst* D₁ [ℕ]'
      [t]′ = convTerm₁ {t = t} [A]' [ℕ]' [Aeq] (irrelevanceTerm {l = l} (ℕᵣ [A]) [A]' [t])
      [u]′ = convTerm₁ {t = u} [B]' [ℕ]' [Beq] (irrelevanceTerm {l = l} (ℕᵣ [B]) [B]' [u])
      [v]′ = convTerm₁ {t = v} [A]' [ℕ]' [Aeq] (irrelevanceTerm {l = l} (ℕᵣ [A]) [A]' [v])
      [w]′ = convTerm₁ {t = w} [B]' [ℕ]' [Beq] (irrelevanceTerm {l = l} (ℕᵣ [B]) [B]' [w])
      [t≡v]′ = convEqTerm₁ {t = t} {u = v} [A]' [ℕ]' [Aeq] (irrelevanceEqTerm {l = l} (ℕᵣ [A]) [A]' [t≡v])
      [u≡w]′ = convEqTerm₁ {t = u} {u = w} [B]' [ℕ]' [Beq] (irrelevanceEqTerm {l = l} (ℕᵣ [B]) [B]' [u≡w])
      X = irrelevanceEq {A = Id ℕ t u} {B = Id ℕ v w} {l = l} ([Id]ℕ ⊢Γ [t] [u]) ([Id]ℕ ⊢Γ [t]′ [u]′) ([IdExt]ℕ ⊢Γ [t]′ [u]′ [v]′ [w]′ [t≡v]′ [u≡w]′)
      [IdA] , [IdA≡U] = redSubst* {l = l} (IdRed* (escapeTerm {l = l} (ℕᵣ [A]) [t]) (escapeTerm {l = l} (ℕᵣ [A]) [u]) D) ([Id]ℕ ⊢Γ [t]′ [u]′)
      [IdB] , [IdB≡U] = redSubst* (IdRed* (escapeTerm {l = l} (ℕᵣ [B]) [v]) (escapeTerm {l = l} (ℕᵣ [B]) [w]) D₁) ([Id]ℕ ⊢Γ [v]′ [w]′)
      [IdA≡U]′ = irrelevanceEq {A = Id A t u} {B = Id ℕ t u} [IdA] ([Id] ⊢Γ (ℕᵣ [A]) [t] [u]) [IdA≡U]
      [IdB≡U]′ = irrelevanceEq {A = Id B v w} {B = Id ℕ v w} {l = l} {l′ = l}  [IdB] ([Id] ⊢Γ (ℕᵣ [B]) [v] [w]) [IdB≡U]
  in  transEq {A = Id A t u} {B = Id ℕ t u} {C = Id B v w} {l = l} {l′ = l} {l″ = l} ([Id] ⊢Γ (ℕᵣ [A]) [t] [u]) ([Id]ℕ ⊢Γ [t]′ [u]′) ([Id] ⊢Γ (ℕᵣ [B]) [v] [w])
              [IdA≡U]′ 
              (transEq {A = Id ℕ t u} {B = Id ℕ v w} {C = Id B v w} {l = l} {l′ = l} {l″ = l} ([Id]ℕ ⊢Γ [t]′ [u]′) ([Id]ℕ ⊢Γ [v]′ [w]′) ([Id] ⊢Γ (ℕᵣ [B]) [v] [w])
                       X (symEq {A = Id B v w} {B = Id ℕ v w} ([Id] ⊢Γ (ℕᵣ [B]) [v] [w]) ([Id]ℕ ⊢Γ [v]′ [w]′) [IdB≡U]′)) 


[IdExtShape] {A} {A′} {t} {t′} {u} {u′} {Γ} {l} {l'} {lA} ⊢Γ _ _
  (Πᵥ (Πᵣ rF lF lG lF≤ lG≤ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
      (Πᵣ rF′ lF′ lG′ lF≤′ lG≤′ F′ G′ [[ ⊢A′ , ⊢B′ , D′ ]] ⊢F′ ⊢G′ A′≡A′ [F′] [G′] G′-ext))
   (Π₌ F′₀ G′₀ D′₀ A≡B [F≡F′₀] [G≡G′₀])
   [t] [t′] (f₀ , f′₀ , [[ ⊢t , ⊢f₀ , Df₀ ]] , [[ ⊢t′ , ⊢f′₀ , Df′₀ ]] , funf₀ , funf′₀ , f₀≡f′₀ , [t]′ , [t′]′ , [f₀≡f′₀])
   [u] [u′] (g₀ , g′₀ , [[ ⊢u , ⊢g₀ , Dg₀ ]] , [[ ⊢u′ , ⊢g′₀ , Dg′₀ ]] , fung₀ , fung′₀ , g₀≡g′₀ , [u]′ , [u′]′ , [g₀≡g′₀]) =
  let
    F′≡F′₀ , rF′≡rF , lF′≡lF , G′≡G′₀ , lG′≡lG = Π-PE-injectivity (whrDet* (D′ , Whnf.Πₙ) (D′₀ , Whnf.Πₙ))
    [F≡F′] = PE.subst (λ X → ∀ {ρ} {Δ} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ) → Δ ⊩⟨ l ⟩ wk ρ F ≡ wk ρ X ^ [ rF , _ ] / [F] [ρ] ⊢Δ) (PE.sym F′≡F′₀) [F≡F′₀]
    [G≡G′] = PE.subst (λ X → ∀ {ρ} {Δ} {a} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) → (⊢Δ : ⊢ Δ) → ([a] : _) → Δ ⊩⟨ l ⟩ wk (lift ρ) G [ a ] ≡ wk (lift ρ) X [ a ] ^ [ _ , _ ] / [G] [ρ] ⊢Δ [a]) (PE.sym G′≡G′₀) [G≡G′₀]

    f , [[ ⊢t , _ , Df ]] , funf , _ , _ , [f] = [t]
    f₀≡f = whrDet*Term (Df₀ , functionWhnf funf₀) (Df , functionWhnf funf)
    f′ , [[ ⊢t′ , _ , Df′ ]] , funf′ , _ , _ , [f′] = [t′]
    f′₀≡f′ = whrDet*Term (Df′₀ , functionWhnf funf′₀) (Df′ , functionWhnf funf′)
    g , [[ ⊢u , _ , Dg ]] , fung , _ , _ , [g] = [u]
    g₀≡g = whrDet*Term (Dg₀ , functionWhnf fung₀) (Dg , functionWhnf fung)
    g′ , [[ ⊢u′ , _ , Dg′ ]] , fung′ , _ , _ , [g′] = [u′]
    g′₀≡g′ = whrDet*Term (Dg′₀ , functionWhnf fung′₀) (Dg′ , functionWhnf fung′)

    [text] = λ {ρ} {Δ} {a} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([a] : Δ ⊩⟨ l ⟩ a ∷ wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ) → redSubst*Term
          (appRed* (escapeTerm ([F] [ρ] ⊢Δ) [a]) (Twk.wkRed*Term [ρ] ⊢Δ Df))
          ([G] [ρ] ⊢Δ [a]) ([f] [ρ] ⊢Δ [a])
    [t′ext] = λ {ρ} {Δ} {a} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([a] : Δ ⊩⟨ l' ⟩ a ∷ wk ρ F′ ^ [ rF′ , ι lF′ ] / [F′] [ρ] ⊢Δ) → redSubst*Term
          (appRed* (escapeTerm ([F′] [ρ] ⊢Δ) [a]) (Twk.wkRed*Term [ρ] ⊢Δ Df′))
          ([G′] [ρ] ⊢Δ [a]) ([f′] [ρ] ⊢Δ [a])
    [uext] = λ {ρ} {Δ} {a} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([a] : Δ ⊩⟨ l ⟩ a ∷ wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ) → redSubst*Term
          (appRed* (escapeTerm ([F] [ρ] ⊢Δ) [a]) (Twk.wkRed*Term [ρ] ⊢Δ Dg))
          ([G] [ρ] ⊢Δ [a]) ([g] [ρ] ⊢Δ [a])
    [u′ext] = λ {ρ} {Δ} {a} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([a] : Δ ⊩⟨ l' ⟩ a ∷ wk ρ F′ ^ [ rF′ , ι lF′ ] / [F′] [ρ] ⊢Δ) → redSubst*Term
          (appRed* (escapeTerm ([F′] [ρ] ⊢Δ) [a]) (Twk.wkRed*Term [ρ] ⊢Δ Dg′))
          ([G′] [ρ] ⊢Δ [a]) ([g′] [ρ] ⊢Δ [a])

    [idG] = λ {ρ} {Δ} {a} ([ρ] : ρ Twk.∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) ([a] : Δ ⊩⟨ l ⟩ a ∷ wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ) →
      PE.subst₂ (λ X Y → Δ ⊩⟨ l ⟩ Id (subst (sgSubst a) (wk (lift ρ) G)) (X ∘ a) (Y ∘ a) ^ [ % , ι lG ])
        (PE.sym (irrelevant-subst′ ρ t a)) (PE.sym (irrelevant-subst′ ρ u a))
        ([Id] ⊢Δ ([G] [ρ] ⊢Δ [a]) (proj₁ ([text] [ρ] ⊢Δ [a])) (proj₁ ([uext] [ρ] ⊢Δ [a])))
    [idG≡idG′] : ∀ {ρ Δ a}
          → ([ρ] : Twk._∷_⊆_ ρ Δ Γ)
          → (⊢Δ : ⊢ Δ)
          → ([a] : Δ ⊩⟨ l ⟩ a ∷ wk ρ F ^ [ rF , ι lF ] / [F] [ρ] ⊢Δ)
          → Δ ⊩⟨ l ⟩ wk (lift ρ) (Id G (wk1 t ∘ var 0) (wk1 u ∘ var 0)) [ a ] ≡ wk (lift ρ) (Id G′ (wk1 t′ ∘ var 0) (wk1 u′ ∘ var 0)) [ a ] ^ [ % , ι lG ] / [idG] [ρ] ⊢Δ [a]
    [idG≡idG′] {ρ} {Δ} {a} [ρ] ⊢Δ [a] = 
      let
        [aF′] = convTerm₁′ (PE.sym rF′≡rF) (PE.cong ι (PE.sym lF′≡lF)) ([F] [ρ] ⊢Δ) ([F′] [ρ] ⊢Δ) ([F≡F′] [ρ] ⊢Δ) [a]
        [Ga] = [G] [ρ] ⊢Δ [a]
        [G′a] = [G′] [ρ] ⊢Δ [aF′]
        [Ga≡G′a] : Δ ⊩⟨ l ⟩ wk (lift ρ) G [ a ] ≡ wk (lift ρ) G′ [ a ] ^ [ ! , ι lG ] / [Ga]
        [Ga≡G′a] = [G≡G′] [ρ] ⊢Δ [a]
        [t∘a] , [ta≡fa] = [text] [ρ] ⊢Δ [a]
        [t′∘a] , [t′a≡f′a] = [t′ext] [ρ] ⊢Δ [aF′]
        [fa≡f′a] = PE.subst₂ (λ X Y → Δ ⊩⟨ l ⟩ wk ρ X ∘ a ≡ wk ρ Y ∘ a ∷ wk (lift ρ) G [ a ] ^ [ ! , ι lG ] / [Ga]) f₀≡f f′₀≡f′ ([f₀≡f′₀] [ρ] ⊢Δ [a])
        [ta≡t′a] : Δ ⊩⟨ l ⟩ wk ρ t ∘ a ≡ wk ρ t′ ∘ a ∷ wk (lift ρ) G [ a ] ^ [ ! , ι lG ] / [Ga]
        [ta≡t′a] = transEqTerm [Ga] (transEqTerm [Ga] [ta≡fa] [fa≡f′a]) (symEqTerm [Ga] (convEqTerm₂′ PE.refl (PE.cong ι (PE.sym lG′≡lG)) [Ga] [G′a] [Ga≡G′a] [t′a≡f′a]))
        [u∘a] , [ua≡ga] = [uext] [ρ] ⊢Δ [a]
        [u′∘a] , [u′a≡g′a] = [u′ext] [ρ] ⊢Δ [aF′]
        [ga≡g′a] = PE.subst₂ (λ X Y → Δ ⊩⟨ l ⟩ wk ρ X ∘ a ≡ wk ρ Y ∘ a ∷ wk (lift ρ) G [ a ] ^ [ ! , ι lG ] / [Ga]) g₀≡g g′₀≡g′ ([g₀≡g′₀] [ρ] ⊢Δ [a])
        [ua≡u′a] : Δ ⊩⟨ l ⟩ wk ρ u ∘ a ≡ wk ρ u′ ∘ a ∷ wk (lift ρ) G [ a ] ^ [ ! , ι lG ] / [Ga]
        [ua≡u′a] = transEqTerm [Ga] (transEqTerm [Ga] [ua≡ga] [ga≡g′a]) (symEqTerm [Ga] (convEqTerm₂′ PE.refl (PE.cong ι (PE.sym lG′≡lG)) [Ga] [G′a] [Ga≡G′a] [u′a≡g′a]))
        [G′a]′ = irrelevance′′ PE.refl PE.refl (PE.cong ι lG′≡lG) [G′a]
        [t′∘a]′ = irrelevanceTerm′ PE.refl PE.refl (PE.cong ι lG′≡lG) [G′a] [G′a]′ [t′∘a]
        [u′∘a]′ = irrelevanceTerm′ PE.refl PE.refl (PE.cong ι lG′≡lG) [G′a] [G′a]′ [u′∘a]
        [idG≡idG′]′ : Δ ⊩⟨ l ⟩ Id (wk (lift ρ) G [ a ]) (wk ρ t ∘ a) (wk ρ u ∘ a) ≡ Id (wk (lift ρ) G′ [ a ]) (wk ρ t′ ∘ a) (wk ρ u′ ∘ a) ^ [ % , ι lG ] / [Id] ⊢Δ [Ga] [t∘a] [u∘a]
        [idG≡idG′]′ = [IdExt] ⊢Δ [Ga] [G′a]′ [Ga≡G′a] [t∘a] [t′∘a]′ [ta≡t′a] [u∘a] [u′∘a]′ [ua≡u′a]
      in irrelevanceEq″ (PE.cong₂ (λ X Y → Id (wk (lift ρ) G [ a ]) (X ∘ a) (Y ∘ a)) (PE.sym (irrelevant-subst′ ρ t a)) (PE.sym (irrelevant-subst′ ρ u a)))
        (PE.cong₂ (λ X Y → Id (wk (lift ρ) G′ [ a ]) (X ∘ a) (Y ∘ a)) (PE.sym (irrelevant-subst′ ρ t′ a)) (PE.sym (irrelevant-subst′ ρ u′ a)))
        PE.refl PE.refl
        ([Id] ⊢Δ [Ga] [t∘a] [u∘a]) ([idG] [ρ] ⊢Δ [a]) [idG≡idG′]′

    [var0] = neuTerm ([F] (Twk.step Twk.id) (⊢Γ ∙ ⊢F)) (var 0) (var (⊢Γ ∙ ⊢F) here) (~-var (var (⊢Γ ∙ ⊢F) here))

    ⊢idG≡idG′₀ : Γ ∙ F ^ [ rF , ι lF ] ⊢ (Id G (wk1 t ∘ var 0) (wk1 u ∘ var 0)) ≅ (Id G′ (wk1 t′ ∘ var 0) (wk1 u′ ∘ var 0)) ^ [ % , ι lG ]
    ⊢idG≡idG′₀ = PE.subst₃ (λ X Y Z → _ ⊢ (Id X (Y ∘ var 0) (Z ∘ var 0)) ≅ _ ^ _)
      (wkSingleSubstId G) (wkSingleSubstId (wk1 t)) (wkSingleSubstId (wk1 u))
      (PE.subst₃ (λ X Y Z → _ ⊢ _ ≅ (Id X (Y ∘ var 0) (Z ∘ var 0)) ^ _)
        (wkSingleSubstId G′) (wkSingleSubstId (wk1 t′)) (wkSingleSubstId (wk1 u′))
        (escapeEq ([idG] (Twk.step Twk.id) (⊢Γ ∙ ⊢F) [var0]) ([idG≡idG′] {step id} {Γ ∙ F ^ [ rF , ι lF ]} {var 0} (Twk.step Twk.id) (⊢Γ ∙ ⊢F) [var0])))

    ⊢F≡F′ = PE.subst₂ (λ X Y → _ ⊢ X ≅ Y ^ _) (wk-id F) (PE.trans (wk-id F′₀) (PE.sym F′≡F′₀))
      (escapeEq ([F] Twk.id ⊢Γ) ([F≡F′₀] Twk.id ⊢Γ))

    [A′] = (Πᵣ′ rF′ lF′ lG′ lF≤′ lG≤′ F′ G′ [[ ⊢A′ , ⊢B′ , D′ ]] ⊢F′ ⊢G′ A′≡A′ [F′] [G′] G′-ext)
    ⊢t′A′ = escapeTerm {l = l'} [A′] [t′]
    ⊢u′A′ = escapeTerm {l = l'} [A′] [u′]

    ⊢t′∘a = PE.subst (λ X → _ ⊢ wk1 t′ ∘ var 0 ∷ X ^ [ ! , ι lG′ ]) (wkSingleSubstId G′)
      (Twk.wkTerm (Twk.step Twk.id) (⊢Γ ∙ ⊢F′) ⊢t′ ∘ⱼ var (⊢Γ ∙ ⊢F′) here)
    ⊢u′∘a = PE.subst (λ X → _ ⊢ wk1 u′ ∘ var 0 ∷ X ^ [ ! , ι lG′ ]) (wkSingleSubstId G′)
      (Twk.wkTerm (Twk.step Twk.id) (⊢Γ ∙ ⊢F′) ⊢u′ ∘ⱼ var (⊢Γ ∙ ⊢F′) here)
    ⊢funext′ : Γ ⊢ Π F′ ^ rF′ ° lF′ ▹ Id G′ (wk1 t′ ∘ var 0) (wk1 u′ ∘ var 0) ° lG′ ^ [ % , ι lA ]
    ⊢funext′ = univ (Πⱼ lF≤′ ▹ lG≤′ ▹ un-univ ⊢F′ ▹ Idⱼ (un-univ ⊢G′) ⊢t′∘a ⊢u′∘a)

    Did : Γ ⊢ Id A′ t′ u′ ⇒* Π F′ ^ rF′ ° lF′ ▹ (Id G′ ((wk1 t′) ∘ (var 0)) ((wk1 u′) ∘ (var 0))) ° lG′ ^ [ % , ι lA ]
    Did = IdRed* ⊢t′A′ ⊢u′A′ D′ ⇨* ((univ (Id-Π lF≤′ lG≤′ (un-univ ⊢F′) (un-univ ⊢G′) ⊢t′ ⊢u′)) ⇨ id ⊢funext′)

  in Π₌ F′ (Id G′ ((wk1 t′) ∘ (var 0)) ((wk1 u′) ∘ (var 0)))
         (PE.subst (λ X → Γ ⊢ Id A′ t′ u′ ⇒* Π F′ ^ rF ° lF ▹ _ ° X ^ [ % , ι lA ]) lG′≡lG
           (PE.subst (λ X → Γ ⊢ Id A′ t′ u′ ⇒* Π F′ ^ rF ° X ▹ _ ° lG′ ^ [ % , ι lA ]) lF′≡lF
             (PE.subst (λ X → Γ ⊢ Id A′ t′ u′ ⇒* Π F′ ^ X ° lF′ ▹ _ ° lG′ ^ [ % , ι lA ]) rF′≡rF Did))) 
        (≅-univ (≅ₜ-Π-cong ⊢F (≅-un-univ ⊢F≡F′) (≅-un-univ ⊢idG≡idG′₀))) [F≡F′] [idG≡idG′]

[IdExtShape] {A} {B} {t} {t′} {u} {u′} {Γ} ⊢Γ .(emb emb< _) [B] (emb⁰¹ {p = [A]} ShapeA) [A≡B] [t] [v] [t≡v] [u] [w] [u≡w] =
  [IdExtShape] ⊢Γ [A] [B] ShapeA [A≡B] [t] [v] [t≡v] [u] [w] [u≡w] 
[IdExtShape] {A} {B} {t} {t′} {u} {u′} {Γ} ⊢Γ [A] .(emb emb< _) (emb¹⁰ {q = [B]} ShapeA) [A≡B] [t] [v] [t≡v] [u] [w] [u≡w] =
  [IdExtShape] ⊢Γ [A] [B] ShapeA [A≡B] [t] [v] [t≡v] [u] [w] [u≡w] 
[IdExtShape] {A} {B} {t} {t′} {u} {u′} {Γ} ⊢Γ .(emb ∞< _) [B] (emb¹∞ {p = [A]} ShapeA) [A≡B] [t] [v] [t≡v] [u] [w] [u≡w] =
  [IdExtShape] ⊢Γ [A] [B] ShapeA [A≡B] [t] [v] [t≡v] [u] [w] [u≡w] 
[IdExtShape] {A} {B} {t} {t′} {u} {u′} {Γ} ⊢Γ [A] .(emb ∞< _) (emb∞¹ {q = [B]} ShapeA) [A≡B] [t] [v] [t≡v] [u] [w] [u≡w] =
  [IdExtShape] ⊢Γ [A] [B] ShapeA [A≡B] [t] [v] [t≡v] [u] [w] [u≡w] 


[IdExt] {A} {A′} {t} {t′} {u} {u′} {Γ} ⊢Γ [A] [A′] [A≡A′] [t] [t′] [t≡t′] [u] [u′] [u≡u′] =
  [IdExtShape] {A} {A′} {t} {t′} {u} {u′} {Γ} ⊢Γ [A] [A′] (goodCases [A] [A′] [A≡A′]) [A≡A′] [t] [t′] [t≡t′] [u] [u′] [u≡u′]

{-

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
-}
