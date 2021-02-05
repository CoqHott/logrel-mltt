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

IdRed*Term′ : ∀ {Γ A B t u}
         (⊢t : Γ ⊢ t ∷ A ^ !)
         (⊢u : Γ ⊢ u ∷ A ^ !)
         (D : Γ ⊢ A ⇒* B ^ !)
       → Γ ⊢ Id A t u ⇒* Id B t u ∷ SProp
IdRed*Term′ ⊢t ⊢u (id ⊢A) = id (Idⱼ ⊢A ⊢t ⊢u)
IdRed*Term′ ⊢t ⊢u (d ⇨ D) = Id-subst d ⊢t ⊢u
  ⇨ IdRed*Term′ (conv ⊢t (subset d)) (conv ⊢u (subset d)) D

IdRed*Term : ∀ {Γ A B t u}
          (⊢t : Γ ⊢ t ∷ A ^ !)
          (⊢u : Γ ⊢ u ∷ A ^ !)
          (D : Γ ⊢ A :⇒*: B ^ !)
        → Γ ⊢ Id A t u :⇒*: Id B t u ∷ SProp
IdRed*Term {Γ} {A} {B} ⊢t ⊢u [ ⊢A , ⊢B , D ] =
  [ Idⱼ ⊢A ⊢t ⊢u
  , Idⱼ ⊢B (conv ⊢t (subset* D)) (conv ⊢u (subset* D))
  , IdRed*Term′ ⊢t ⊢u D ]

IdℕRed*Term′ : ∀ {Γ t t′ u}
               (⊢t : Γ ⊢ t ∷ ℕ ^ !)
               (⊢t′ : Γ ⊢ t′ ∷ ℕ ^ !)
               (d : Γ ⊢ t ⇒* t′ ∷ ℕ)
               (⊢u : Γ ⊢ u ∷ ℕ ^ !)
             → Γ ⊢ Id ℕ t u ⇒* Id ℕ t′ u ∷ SProp
IdℕRed*Term′ ⊢t ⊢t′ (id x) ⊢u = id (Idⱼ (ℕⱼ (wfTerm ⊢u)) ⊢t ⊢u)
IdℕRed*Term′ ⊢t ⊢t′ (x ⇨ d) ⊢u = _⇨_ (Id-ℕ-subst x ⊢u) (IdℕRed*Term′ (redFirst*Term d) ⊢t′ d ⊢u)

IdℕRed*Term : ∀ {Γ t t′ u}
              (d : Γ ⊢ t :⇒*: t′ ∷ ℕ)
              (⊢u : Γ ⊢ u ∷ ℕ ^ !)
            → Γ ⊢ Id ℕ t u :⇒*: Id ℕ t′ u ∷ SProp
IdℕRed*Term [ ⊢t , ⊢t′ , d ] ⊢u = [ Idⱼ (ℕⱼ (wfTerm ⊢u)) ⊢t ⊢u , Idⱼ (ℕⱼ (wfTerm ⊢u)) ⊢t′ ⊢u , IdℕRed*Term′ ⊢t ⊢t′ d ⊢u ]

Idℕ0Red*Term′ : ∀ {Γ t t′}
                (⊢t : Γ ⊢ t ∷ ℕ ^ !)
                (⊢t′ : Γ ⊢ t′ ∷ ℕ ^ !)
                (d : Γ ⊢ t ⇒* t′ ∷ ℕ)
              → Γ ⊢ Id ℕ zero t ⇒* Id ℕ zero t′ ∷ SProp
Idℕ0Red*Term′ ⊢t ⊢t′ (id x) = id (Idⱼ (ℕⱼ (wfTerm ⊢t)) (zeroⱼ (wfTerm ⊢t)) ⊢t)
Idℕ0Red*Term′ ⊢t ⊢t′ (x ⇨ d) = Id-ℕ-0-subst x ⇨ Idℕ0Red*Term′ (redFirst*Term d) ⊢t′ d

redSProp′ : ∀ {Γ A B}
           (D : Γ ⊢ A ⇒* B ∷ SProp)
         → Γ ⊢ A ⇒* B ^ %
redSProp′ (id x) = id (univ x)
redSProp′ (x ⇨ D) = univ x ⇨ redSProp′ D

redSProp : ∀ {Γ A B}
           (D : Γ ⊢ A :⇒*: B ∷ SProp)
         → Γ ⊢ A :⇒*: B ^ %
redSProp [ ⊢t , ⊢u , d ] = [ (univ ⊢t) , (univ ⊢u) , redSProp′ d ]

IdTerm : ∀ {A t u Γ l}
         (⊢Γ : ⊢ Γ)
         ([A] : Γ ⊩⟨ l ⟩ A ^ !)
         ([t] : Γ ⊩⟨ l ⟩ t ∷ A ^ ! / [A])
         ([u] : Γ ⊩⟨ l ⟩ u ∷ A ^ ! / [A])
       → Γ ⊩⟨ ¹ ⟩ Id A t u ∷ SProp ^ ! / Uᵣ′ _ ⁰ 0<1 ⊢Γ
IdTerm {A} {t} {u} {Γ} {l} ⊢Γ [A] [t] [u] with escapeTerm {l = l} [A] [t] | escapeTerm {l = l} [A] [u]
IdTerm ⊢Γ (Uᵣ (Uᵣ l′ l< ⊢Γ₁)) [t] [u] | ⊢tA | ⊢uA = {!!}
IdTerm {A} {t} {u} {Γ} {l} ⊢Γ (ℕᵣ [ ⊢A , ⊢B , D ]) [t] [u] | ⊢tA | ⊢uA =
  aux [t] [u]
  where
    [A] = (ℕᵣ ([ ⊢A , ⊢B , D ]))
    [ℕ] : Γ ⊩⟨ l ⟩ ℕ ^ !
    [ℕ] = ℕᵣ (idRed:*: (ℕⱼ ⊢Γ))
    A≡ℕ = redSubst* D [ℕ]

    aux : ∀ ([t]′ : Γ ⊩⟨ l ⟩ t ∷ A ^ ! / [A]) ([u]′ : Γ ⊩⟨ l ⟩ u ∷ A ^ ! / [A]) →
        Γ ⊩⟨ ¹ ⟩ Id A t u ∷ SProp ^ ! / Uᵣ′ _ ⁰ 0<1 ⊢Γ
    aux (ℕₜ .(suc _) d n≡n (sucᵣ x)) [u]′ = {!!}
    aux (ℕₜ .zero [ ⊢tℕ , ⊢0ℕ , dt ] 0≡0 zeroᵣ)
        (ℕₜ .(suc _) [ ⊢uℕ , ⊢sucℕ , du ] suc≡suc (sucᵣ (ℕₜ n [ ⊢u′ , ⊢nℕ , du′ ] n≡n prop))) =
      let nfId = (IdRed*Term′ ⊢tA ⊢uA D ⇨∷* IdℕRed*Term′ ⊢tℕ ⊢0ℕ dt ⊢uℕ)
            ⇨∷* (Idℕ0Red*Term′ ⊢uℕ ⊢sucℕ du ⇨∷* (Id-ℕ-0S ⊢u′ ⇨ id (Emptyⱼ ⊢Γ)))
          nfId′ = [ Idⱼ ⊢A ⊢tA ⊢uA , Emptyⱼ ⊢Γ , nfId ]
          [Empty] = Emptyᵣ (idRed:*: (Emptyⱼ ⊢Γ))
          [Empty]′ = proj₁ (redSubst* (redSProp′ nfId) [Empty])
      in Uₜ Empty nfId′ Emptyₙ (≅ₜ-Emptyrefl ⊢Γ) [Empty]′
    aux (ℕₜ .zero [ ⊢tℕ , ⊢0ℕ , dt ] 0≡0 zeroᵣ)
        (ℕₜ .zero [ ⊢uℕ , ⊢0ℕ′ , du ] 0≡0′ zeroᵣ) =
      let nfId = (IdRed*Term′ ⊢tA ⊢uA D ⇨∷* IdℕRed*Term′ ⊢tℕ ⊢0ℕ dt ⊢uℕ)
            ⇨∷* (Idℕ0Red*Term′ ⊢uℕ ⊢0ℕ du ⇨∷* (Id-ℕ-00 ⊢Γ ⇨ id (Unitⱼ ⊢Γ)))
          nfId′ = [ Idⱼ ⊢A ⊢tA ⊢uA , Unitⱼ ⊢Γ , nfId ]
          [Unit] = proj₁ (redSubst* (redSProp′ nfId) (UnitType ⊢Γ))
      in Uₜ Unit nfId′ typeUnit (Unit≡Unit ⊢Γ) [Unit]
    aux (ℕₜ .zero [ ⊢tℕ , ⊢0ℕ , dt ] 0≡0 zeroᵣ)
        (ℕₜ k [ ⊢uℕ , ⊢kℕ , du ] k≡k′ (ne (neNfₜ neK ⊢k k≡k))) =
      let nfId = (IdRed*Term′ ⊢tA ⊢uA D ⇨∷* IdℕRed*Term′ ⊢tℕ ⊢0ℕ dt ⊢uℕ)
            ⇨∷* Idℕ0Red*Term′ ⊢uℕ ⊢kℕ du
          nfId′ = [ Idⱼ ⊢A ⊢tA ⊢uA , Idⱼ (ℕⱼ ⊢Γ) (zeroⱼ ⊢Γ) ⊢kℕ , nfId ]
      in Uₜ (Id ℕ zero k) nfId′ (ne (Idℕ0ₙ neK)) (~-to-≅ₜ (~-Idℕ0 ⊢Γ k≡k))
        (ne′ (Id ℕ zero k) (redSProp nfId′) (Idℕ0ₙ neK) (~-Idℕ0 ⊢Γ k≡k))
    aux (ℕₜ k [ ⊢t , ⊢k , d ] n≡n (ne (neNfₜ neK ⊢k′ k≡k))) [u] =
      let nfId = [ Idⱼ ⊢A ⊢tA ⊢uA , Idⱼ (ℕⱼ ⊢Γ) ⊢k (conv ⊢uA (subset* D))
                 , IdRed*Term′ ⊢tA ⊢uA D ⇨∷* IdℕRed*Term′ ⊢t ⊢k d (conv ⊢uA (subset* D)) ]
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
