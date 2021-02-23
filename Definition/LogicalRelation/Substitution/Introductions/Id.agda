{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Id {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Application
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
import Definition.LogicalRelation.Substitution.Irrelevance as S
open import Definition.LogicalRelation.Substitution.Reflexivity
open import Definition.LogicalRelation.Substitution.Weakening
open import Definition.LogicalRelation.Substitution.Introductions.Nat
open import Definition.LogicalRelation.Substitution.Introductions.Empty
open import Definition.LogicalRelation.Substitution.Introductions.Pi
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Definition.LogicalRelation.Substitution.Introductions.Universe

open import Tools.Product
open import Tools.Empty
import Tools.Unit as TU
import Tools.PropositionalEquality as PE

Unitⱼ : ∀ {Γ} (⊢Γ : ⊢ Γ)
      → Γ ⊢ Unit ∷ SProp ^ !
Unitⱼ ⊢Γ = Πⱼ Emptyⱼ ⊢Γ ▹ Emptyⱼ (⊢Γ ∙ Emptyⱼ ⊢Γ)

typeUnit : Type Unit
typeUnit = Πₙ

Unit≡Unit : ∀ {Γ} (⊢Γ : ⊢ Γ)
          → Γ ⊢ Unit ≅ Unit ∷ SProp ^ !
Unit≡Unit ⊢Γ = ≅ₜ-Π-cong (Emptyⱼ ⊢Γ) (≅ₜ-Emptyrefl ⊢Γ) (≅ₜ-Emptyrefl (⊢Γ ∙ Emptyⱼ ⊢Γ))

Unitᵛ : ∀ {Γ l} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ l ⟩ Unit ^ % / [Γ]
Unitᵛ {Γ} {l} [Γ] =
  let [Empty] = Emptyᵛ {l = ¹} [Γ]
      [Empty]₁ : Γ ∙ Empty ^ % ⊩ᵛ⟨ l ⟩ Empty ^ % / [Γ] ∙ [Empty]
      [Empty]₁ = Emptyᵛ {l = l} (_∙_ {Γ} {Empty} [Γ] [Empty])
  in Πᵛ {Empty} {Empty} [Γ] (Emptyᵛ [Γ]) (λ {Δ} {σ} → [Empty]₁ {Δ} {σ})

UnitType : ∀ {Γ l} (⊢Γ : ⊢ Γ) → Γ ⊩⟨ l ⟩ Unit ^ %
UnitType {Γ} {l} ⊢Γ = proj₁ (Unitᵛ ε {Γ} {idSubst} ⊢Γ TU.tt)

Unitᵗᵛ : ∀ {Γ} ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ ¹ ⟩ Unit ∷ SProp ^ ! / [Γ] / (Uᵛ [Γ])
Unitᵗᵛ {Γ} [Γ] =
  let [Empty] = Emptyᵛ {l = ¹} [Γ]
      [SProp]₁ : Γ ∙ Empty ^ % ⊩ᵛ⟨ ¹ ⟩ SProp ^ ! / [Γ] ∙ [Empty]
      [SProp]₁ = Uᵛ (_∙_ {Γ} {Empty} [Γ] [Empty])
      [Empty]₁ = Emptyᵗᵛ [Γ]
      [Empty]₂ = Emptyᵗᵛ (_∙_ {Γ} {Empty} [Γ] [Empty])
  in Πᵗᵛ {Empty} {Empty} [Γ] [Empty] (λ {Δ} {σ} → [SProp]₁ {Δ} {σ})
           [Empty]₁ (λ {Δ} {σ} → [Empty]₂ {Δ} {σ})


IdTerm : ∀ {A t u Γ l}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ l ⟩ A ^ !)
         ([t] : Γ ⊩⟨ l ⟩ t ∷ A ^ ! / [A])
         ([u] : Γ ⊩⟨ l ⟩ u ∷ A ^ ! / [A])
       → Γ ⊩⟨ ¹ ⟩ Id A t u ∷ SProp ^ ! / Uᵣ′ _ ⁰ 0<1 ⊢Γ
IdTerm {A} {t} {u} {Γ} {l} ⊢Γ [A] [t] [u] with escapeTerm {l = l} [A] [t] | escapeTerm {l = l} [A] [u]
IdTerm ⊢Γ (Uᵣ (Uᵣ l′ l< ⊢Γ₁)) [t] [u] | ⊢tA | ⊢uA = {!!}
IdTerm {A} {t} {u} {Γ} {l} ⊢Γ (ℕᵣ [ ⊢A , ⊢B , D ]) [t] [u] | ⊢tA | ⊢uA =
  proj₁ (redSubst*Term (IdRed*Term′ ⊢tA ⊢uA D) (Uᵣ′ _ ⁰ 0<1 ⊢Γ) (aux [t] [u]))
  where
    [A] = (ℕᵣ ([ ⊢A , ⊢B , D ]))
    [ℕ] : Γ ⊩⟨ l ⟩ ℕ ^ !
    [ℕ] = ℕᵣ (idRed:*: (ℕⱼ ⊢Γ))
    A≡ℕ = redSubst* D [ℕ]

    aux : ∀ {t u} ([t]′ : Γ ⊩⟨ l ⟩ t ∷ ℕ ^ ! / [ℕ]) ([u]′ : Γ ⊩⟨ l ⟩ u ∷ ℕ ^ ! / [ℕ]) →
        Γ ⊩⟨ ¹ ⟩ Id ℕ t u ∷ SProp ^ ! / Uᵣ′ _ ⁰ 0<1 ⊢Γ
    aux (ℕₜ .(suc m) [ ⊢tℕ , ⊢smℕ , dt ] sm≡sm (sucᵣ {m} [m]))
        (ℕₜ .(suc n) [ ⊢uℕ , ⊢snℕ , du ] sn≡sn (sucᵣ {n} [n])) =
      let [Idmn] = aux [m] [n]
          ⊢mℕ = escapeTerm [ℕ] [m]
          ⊢nℕ = escapeTerm [ℕ] [n]
          nfId = (IdℕRed*Term′ ⊢tℕ ⊢smℕ dt ⊢uℕ ⇨∷* IdℕSRed*Term′ ⊢mℕ ⊢uℕ ⊢snℕ du)
            ⇨∷* (Id-ℕ-SS ⊢mℕ ⊢nℕ ⇨ id (Idⱼ (ℕⱼ ⊢Γ) ⊢mℕ ⊢nℕ))
      in proj₁ (redSubst*Term nfId (Uᵣ′ _ ⁰ 0<1 ⊢Γ) [Idmn])
    aux (ℕₜ .(suc m) [ ⊢tℕ , ⊢smℕ , dt ] sm≡sm (sucᵣ {m} [m]))
        (ℕₜ .zero [ ⊢uℕ , ⊢0ℕ , du ] 0≡0 zeroᵣ) =
      let ⊢mℕ = escapeTerm [ℕ] [m]
          nfId = (IdℕRed*Term′ ⊢tℕ ⊢smℕ dt ⊢uℕ)
            ⇨∷* (IdℕSRed*Term′ ⊢mℕ ⊢uℕ ⊢0ℕ du ⇨∷* (Id-ℕ-S0 ⊢mℕ ⇨ id (Emptyⱼ ⊢Γ)))
          nfId′ = [ Idⱼ (ℕⱼ ⊢Γ) ⊢tℕ ⊢uℕ , Emptyⱼ ⊢Γ , nfId ]
          [Empty] = Emptyᵣ (idRed:*: (Emptyⱼ ⊢Γ))
          [Empty]′ = proj₁ (redSubst* (redSProp′ nfId) [Empty])
      in Uₜ Empty nfId′ Emptyₙ (≅ₜ-Emptyrefl ⊢Γ) [Empty]′
    aux (ℕₜ .(suc m) [ ⊢tℕ , ⊢smℕ , dt ] sm≡sm (sucᵣ {m} [m]))
        (ℕₜ k [ ⊢uℕ , ⊢kℕ , du ] k≡k′ (ne (neNfₜ neK ⊢k k≡k))) =
      let ⊢mℕ = escapeTerm [ℕ] [m]
          nfId = (IdℕRed*Term′ ⊢tℕ ⊢smℕ dt ⊢uℕ) ⇨∷* IdℕSRed*Term′ ⊢mℕ ⊢uℕ ⊢kℕ du
          nfId′ = [ Idⱼ (ℕⱼ ⊢Γ) ⊢tℕ ⊢uℕ , Idⱼ (ℕⱼ ⊢Γ) ⊢smℕ ⊢kℕ , nfId ]
          m≡m = escapeTermEq [ℕ] (reflEqTerm [ℕ] [m])
      in Uₜ (Id ℕ (suc m) k) nfId′ (ne (IdℕSₙ neK)) (~-to-≅ₜ (~-IdℕS ⊢Γ m≡m k≡k))
        (ne′ (Id ℕ (suc m) k) (redSProp nfId′) (IdℕSₙ neK) (~-IdℕS ⊢Γ m≡m k≡k))
    aux (ℕₜ .zero [ ⊢tℕ , ⊢0ℕ , dt ] 0≡0 zeroᵣ)
        (ℕₜ .(suc _) [ ⊢uℕ , ⊢sucℕ , du ] suc≡suc (sucᵣ (ℕₜ n [ ⊢u′ , ⊢nℕ , du′ ] n≡n prop))) =
      let nfId = (IdℕRed*Term′ ⊢tℕ ⊢0ℕ dt ⊢uℕ)
            ⇨∷* (Idℕ0Red*Term′ ⊢uℕ ⊢sucℕ du ⇨∷* (Id-ℕ-0S ⊢u′ ⇨ id (Emptyⱼ ⊢Γ)))
          nfId′ = [ Idⱼ (ℕⱼ ⊢Γ) ⊢tℕ ⊢uℕ , Emptyⱼ ⊢Γ , nfId ]
          [Empty] = Emptyᵣ (idRed:*: (Emptyⱼ ⊢Γ))
          [Empty]′ = proj₁ (redSubst* (redSProp′ nfId) [Empty])
      in Uₜ Empty nfId′ Emptyₙ (≅ₜ-Emptyrefl ⊢Γ) [Empty]′
    aux (ℕₜ .zero [ ⊢tℕ , ⊢0ℕ , dt ] 0≡0 zeroᵣ)
        (ℕₜ .zero [ ⊢uℕ , ⊢0ℕ′ , du ] 0≡0′ zeroᵣ) =
      let nfId = (IdℕRed*Term′ ⊢tℕ ⊢0ℕ dt ⊢uℕ)
            ⇨∷* (Idℕ0Red*Term′ ⊢uℕ ⊢0ℕ du ⇨∷* (Id-ℕ-00 ⊢Γ ⇨ id (Unitⱼ ⊢Γ)))
          nfId′ = [ Idⱼ (ℕⱼ ⊢Γ) ⊢tℕ ⊢uℕ , Unitⱼ ⊢Γ , nfId ]
          [Unit] = proj₁ (redSubst* (redSProp′ nfId) (UnitType ⊢Γ))
      in Uₜ Unit nfId′ typeUnit (Unit≡Unit ⊢Γ) [Unit]
    aux (ℕₜ .zero [ ⊢tℕ , ⊢0ℕ , dt ] 0≡0 zeroᵣ)
        (ℕₜ k [ ⊢uℕ , ⊢kℕ , du ] k≡k′ (ne (neNfₜ neK ⊢k k≡k))) =
      let nfId = (IdℕRed*Term′ ⊢tℕ ⊢0ℕ dt ⊢uℕ) ⇨∷* Idℕ0Red*Term′ ⊢uℕ ⊢kℕ du
          nfId′ = [ Idⱼ (ℕⱼ ⊢Γ) ⊢tℕ ⊢uℕ , Idⱼ (ℕⱼ ⊢Γ) (zeroⱼ ⊢Γ) ⊢kℕ , nfId ]
      in Uₜ (Id ℕ zero k) nfId′ (ne (Idℕ0ₙ neK)) (~-to-≅ₜ (~-Idℕ0 ⊢Γ k≡k))
        (ne′ (Id ℕ zero k) (redSProp nfId′) (Idℕ0ₙ neK) (~-Idℕ0 ⊢Γ k≡k))
    aux {t} {u} (ℕₜ k [ ⊢t , ⊢k , d ] n≡n (ne (neNfₜ neK ⊢k′ k≡k))) [u] =
      let nfId = [ Idⱼ (ℕⱼ ⊢Γ) ⊢t (escapeTerm [ℕ] [u]) , Idⱼ (ℕⱼ ⊢Γ) ⊢k (escapeTerm [ℕ] [u])
                 , IdℕRed*Term′ ⊢t ⊢k d (escapeTerm [ℕ] [u]) ]
          [u]′ = convTerm₁ (proj₁ A≡ℕ) [ℕ] (proj₂ A≡ℕ)
            (irrelevanceTerm {l = l} [A] (proj₁ A≡ℕ) [u])
          u≡u = escapeTermEq [ℕ] (reflEqTerm [ℕ] [u]′)
      in Uₜ (Id ℕ k u) nfId (ne (Idℕₙ neK)) (~-to-≅ₜ (~-Idℕ ⊢Γ k≡k u≡u))
        (ne′ (Id ℕ k u) (redSProp nfId) (Idℕₙ neK) (~-Idℕ ⊢Γ k≡k u≡u))

IdTerm {A} {t} {u} {Γ} {l} ⊢Γ (ne′ K D neK K≡K) [t] [u] | ⊢tA | ⊢uA =
  let [A] = ne′ K D neK K≡K
      [K] = neu {l = l} neK (_⊢_:⇒*:_^_.⊢B D) K≡K
      A≡K = redSubst* (_⊢_:⇒*:_^_.D D) [K]
      [t]′ = convTerm₁ (proj₁ A≡K) [K] (proj₂ A≡K)
        (irrelevanceTerm  {l = l} [A] (proj₁ A≡K) [t])
      [u]′ = convTerm₁ (proj₁ A≡K) [K] (proj₂ A≡K)
        (irrelevanceTerm {l = l} [A] (proj₁ A≡K) [u])
      t≡t = escapeTermEq [K] (reflEqTerm [K] [t]′)
      u≡u = escapeTermEq [K] (reflEqTerm [K] [u]′)
  in Uₜ (Id K t u)
    (IdRed*Term ⊢tA ⊢uA D)
    (ne (Idₙ neK))
    (~-to-≅ₜ (~-Id K≡K t≡t u≡u))
    (ne′ (Id K t u) (redSProp (IdRed*Term ⊢tA ⊢uA D)) (Idₙ neK) (~-Id K≡K t≡t u≡u))
IdTerm ⊢Γ (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) [t] [u] | ⊢tA | ⊢uA = {!!}
IdTerm {A} {t} {u} {Γ} {⁰} ⊢Γ (emb {l′ = l′} () [A]) [t] [u] | ⊢tA | ⊢uA
IdTerm {A} {t} {u} {Γ} {¹} ⊢Γ (emb {l′ = .⁰} 0<1 [A]) [t] [u] | ⊢tA | ⊢uA =
  IdTerm ⊢Γ [A] [t] [u]

Idᵗᵛ : ∀ {A t u Γ l}
       ([Γ] : ⊩ᵛ Γ)
       ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ ! / [Γ])
       ([t] : Γ ⊩ᵛ⟨ l ⟩ t ∷ A ^ ! / [Γ] / [A])
       ([u] : Γ ⊩ᵛ⟨ l ⟩ u ∷ A ^ ! / [Γ] / [A])
     → Γ ⊩ᵛ⟨ ¹ ⟩ Id A t u ∷ SProp ^ ! / [Γ] / Uᵛ [Γ]
Idᵗᵛ [Γ] [A] [t] [u] ⊢Δ [σ] =
  (IdTerm ⊢Δ (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ])) (proj₁ ([u] ⊢Δ [σ])))
  , {!!}
