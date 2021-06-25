{-# OPTIONS --allow-unsolved-metas #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.IdNat {{eqrel : EqRelSet}} where
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
