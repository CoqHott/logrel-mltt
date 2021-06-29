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
open import Definition.LogicalRelation.Properties.Escape
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
open import Definition.LogicalRelation.Substitution.Introductions.IdNat
open import Definition.LogicalRelation.Substitution.MaybeEmbed
-- open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Definition.LogicalRelation.Substitution.Introductions.Universe

open import Tools.Product
open import Tools.Empty
import Tools.Unit as TU
import Tools.PropositionalEquality as PE
import Data.Nat as Nat


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


[Id] ⊢Γ (ℕᵣ [[ ⊢A , ⊢B , D ]]) [t] [u] = [Id]ℕGen ⊢Γ [[ ⊢A , ⊢B , D ]] [t] [u]

[Id] ⊢Γ (Uᵣ (Uᵣ r ¹ l< () d)) [t] [u]

[Id] {A} {t} {u} {Γ} {ι .¹} {.¹} ⊢Γ (Uᵣ (Uᵣ rU ⁰ emb< PE.refl [[ ⊢A , ⊢B , D ]])) [t] [u] = [Id]UGen {A} {t} {u} {Γ} ⊢Γ (Uᵣ rU ⁰ emb< PE.refl [[ ⊢A , ⊢B , D ]]) [t] [u]
  
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
  in ne′ (Id K t u) (redSProp (IdRed*Term ⊢tA ⊢uA [[ ⊢A , ⊢B , D ]])) (Idₙ neK) (~-Id K≡K t≡t u≡u)

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
        [IdExtG] : Δ ⊩⟨ l ⟩ (Id (wk (lift ρ) G [ a ]) (wk ρ t ∘ a) (wk ρ u ∘ a)) ≡ (Id (wk (lift ρ) G [ b ]) (wk ρ t ∘ b) (wk ρ u ∘ b)) ^ [ % , ι lG ] / [Id] ⊢Δ [Ga] [t∘a] [u∘a]
        [IdExtG] = [IdExt] ⊢Δ [Ga] [Gb] [Ga≡Gb] [t∘a] [t∘b:Gb] [ta≡tb] [u∘a] [u∘b:Gb] [ua≡ub]
      in irrelevanceEq″
        (PE.cong₂ (λ X Y → Id _ (X ∘ a) (Y ∘ a)) (PE.sym (irrelevant-subst′ ρ t a)) (PE.sym (irrelevant-subst′ ρ u a)))
        (PE.cong₂ (λ X Y → Id _ (X ∘ b) (Y ∘ b)) (PE.sym (irrelevant-subst′ ρ t b)) (PE.sym (irrelevant-subst′ ρ u b)))
        PE.refl PE.refl
        ([Id] ⊢Δ [Ga] [t∘a] [u∘a]) ([idG] [ρ] ⊢Δ [a]) [IdExtG]
  in Πᵣ (Πᵣ rF lF lG lF≤ lG≤ F (Id G ((wk1 t) ∘ (var 0)) ((wk1 u) ∘ (var 0)))
      [[ univ (Idⱼ (un-univ ⊢A) ⊢tA ⊢uA) , ⊢funext , Did ]]
      ⊢F ⊢idG
      (≅-univ (≅ₜ-Π-cong ⊢F (≅-un-univ (escapeEqRefl [F0]))
        (≅-un-univ (escapeEqRefl [idG0]))))
      [F] [idG] [idGext])

[Id] ⊢Γ (emb {l′ = ι ⁰} emb< [A]) [t] [u] = emb emb< ([Id] ⊢Γ [A] [t] [u])
[Id] ⊢Γ (emb {l′ = ι ¹} ∞< [A]) [t] [u] = emb ∞< ([Id] ⊢Γ [A] [t] [u])

[IdExtShape] {A} {B} {t} {v} {u} {w} {Γ} {.(ι ¹)} {.(ι ¹)} {lA} ⊢Γ (Uᵣ (Uᵣ rU ⁰ emb< PE.refl d)) (Uᵣ (Uᵣ r₁ ⁰ emb< PE.refl d₁)) (Uᵥ ._ ._) [A≡B] [t] [v] [t≡v] [u] [w] [u≡w] =
  [IdExt]UGen {A} {B} {t} {v} {u} {w} {Γ} ⊢Γ (Uᵣ rU ⁰ emb< PE.refl d) (Uᵣ r₁ ⁰ emb< PE.refl d₁) [A≡B] [t] [v] [t≡v] [u] [w] [u≡w]

[IdExtShape] {A} {B} {t} {v} {u} {w} {Γ} {l} {l'} {lA}  ⊢Γ (ne′ K [[ ⊢A , ⊢B , D ]] neK K≡K) (ne neB) (ne ._ .neB) (ne₌ M [[ ⊢A′ , ⊢B′ ,  D′ ]] neM K≡M) [t] [t′] [t≡t′] [u] [u′] [u≡u′] =
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

[IdExtShape] {A} {B} {t} {v} {u} {w} {Γ} {l} {l'} ⊢Γ (ℕᵣ [[ ⊢A , ⊢B , D ]]) (ℕᵣ [[ ⊢A₁ , ⊢B₁ , D₁ ]]) (ℕᵥ ._ ._) [A≡B] [t] [v] [t≡v] [u] [w] [u≡w] =
  [IdExt]ℕGen {A} {B} {t} {v} {u} {w} {Γ} {l} {l'} ⊢Γ [[ ⊢A , ⊢B , D ]] [[ ⊢A₁ , ⊢B₁ , D₁ ]] [A≡B] [t] [v] [t≡v] [u] [w] [u≡w]

[IdExtShape] {A} {A′} {t} {t′} {u} {u′} {Γ} {l} {l'} {lA} ⊢Γ (Πᵣ′ rF lF lG lF≤ lG≤ F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Πᵣ′ rF′ lF′ lG′ lF≤′ lG≤′ F′ G′ [[ ⊢A′ , ⊢B′ , D′ ]] ⊢F′ ⊢G′ A′≡A′ [F′] [G′] G′-ext)
  (Πᵥ .(Πᵣ rF lF lG lF≤ lG≤ F G D ⊢F ⊢G A≡A [F] [G] G-ext) .(Πᵣ rF′ lF′ lG′ lF≤′ lG≤′ F′ G′ [[ ⊢A′ , ⊢B′ , D′ ]] ⊢F′ ⊢G′ A′≡A′ [F′] [G′] G′-ext))
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

[IdExtShape] {A} {B} {t} {t′} {u} {u′} {Γ} ⊢Γ (emb emb< [A]) [B] (emb⁰¹ {p = .[A]} ShapeA) [A≡B] [t] [v] [t≡v] [u] [w] [u≡w] =
  [IdExtShape] ⊢Γ [A] [B] ShapeA [A≡B] [t] [v] [t≡v] [u] [w] [u≡w] 
[IdExtShape] {A} {B} {t} {t′} {u} {u′} {Γ} ⊢Γ [A] (emb emb< [B]) (emb¹⁰ {q = .[B]} ShapeA) [A≡B] [t] [v] [t≡v] [u] [w] [u≡w] =
  [IdExtShape] ⊢Γ [A] [B] ShapeA [A≡B] [t] [v] [t≡v] [u] [w] [u≡w] 
[IdExtShape] {A} {B} {t} {t′} {u} {u′} {Γ} ⊢Γ (emb ∞< [A]) [B] (emb¹∞ {p = .[A]} ShapeA) [A≡B] [t] [v] [t≡v] [u] [w] [u≡w] =
  [IdExtShape] ⊢Γ [A] [B] ShapeA [A≡B] [t] [v] [t≡v] [u] [w] [u≡w] 
[IdExtShape] {A} {B} {t} {t′} {u} {u′} {Γ} ⊢Γ [A] (emb ∞< [B]) (emb∞¹ {q = .[B]} ShapeA) [A≡B] [t] [v] [t≡v] [u] [w] [u≡w] =
  [IdExtShape] ⊢Γ [A] [B] ShapeA [A≡B] [t] [v] [t≡v] [u] [w] [u≡w] 

[IdExt] {A} {A′} {t} {t′} {u} {u′} {Γ} ⊢Γ [A] [A′] [A≡A′] [t] [t′] [t≡t′] [u] [u′] [u≡u′] =
  [IdExtShape] {A} {A′} {t} {t′} {u} {u′} {Γ} ⊢Γ [A] [A′] (goodCases [A] [A′] [A≡A′]) [A≡A′] [t] [t′] [t≡t′] [u] [u′] [u≡u′]



Idᵛ-min : ∀ {A t u Γ l}
       ([Γ] : ⊩ᵛ Γ)
       ([A] : Γ ⊩ᵛ⟨ ι l ⟩ A ^ [ ! , ι l ] / [Γ])
       ([t] : Γ ⊩ᵛ⟨ ι l ⟩ t ∷ A ^ [ ! , ι l ] / [Γ] / [A])
       ([u] : Γ ⊩ᵛ⟨ ι l ⟩ u ∷ A ^ [ ! , ι l ] / [Γ] / [A])
     → Γ ⊩ᵛ⟨ ι l ⟩ Id A t u ^ [ % , ι l ] / [Γ]
Idᵛ-min [Γ] [A] [t] [u] ⊢Δ [σ] =
  ([Id] ⊢Δ (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ])) (proj₁ ([u] ⊢Δ [σ]))) ,
  (λ [σ′] [σ≡σ′] → [IdExt] ⊢Δ (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ′])) (proj₂ ([A] ⊢Δ [σ]) [σ′] [σ≡σ′])
                             (proj₁ ([t] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ′])) (proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′])
                             (proj₁ ([u] ⊢Δ [σ])) (proj₁ ([u] ⊢Δ [σ′])) (proj₂ ([u] ⊢Δ [σ]) [σ′] [σ≡σ′]))

Idᵛ : ∀ {A t u Γ l}
       ([Γ] : ⊩ᵛ Γ)
       ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ ! , ι l ] / [Γ])
       ([t] : Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ [ ! , ι l ] / [Γ] / [A])
       ([u] : Γ ⊩ᵛ⟨ ∞ ⟩ u ∷ A ^ [ ! , ι l ] / [Γ] / [A])
     → Γ ⊩ᵛ⟨ ∞ ⟩ Id A t u ^ [ % , ι l ] / [Γ]
Idᵛ [Γ] [A] [t] [u] ⊢Δ [σ] =
  ([Id] ⊢Δ (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ])) (proj₁ ([u] ⊢Δ [σ]))) ,
  (λ [σ′] [σ≡σ′] → [IdExt] ⊢Δ (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ′])) (proj₂ ([A] ⊢Δ [σ]) [σ′] [σ≡σ′])
                             (proj₁ ([t] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ′])) (proj₂ ([t] ⊢Δ [σ]) [σ′] [σ≡σ′])
                             (proj₁ ([u] ⊢Δ [σ])) (proj₁ ([u] ⊢Δ [σ′])) (proj₂ ([u] ⊢Δ [σ]) [σ′] [σ≡σ′]))

Idᵗᵛ-min : ∀ {A t u Γ l}
       ([Γ] : ⊩ᵛ Γ)
       ([A] : Γ ⊩ᵛ⟨ ι l ⟩ A ^ [ ! , ι l ] / [Γ])
       ([t] : Γ ⊩ᵛ⟨ ι l ⟩ t ∷ A ^ [ ! , ι l ] / [Γ] / [A])
       ([u] : Γ ⊩ᵛ⟨ ι l ⟩ u ∷ A ^ [ ! , ι l ] / [Γ] / [A])
     → Γ ⊩ᵛ⟨ next l ⟩ Id A t u ∷ SProp l ^ [ ! , next l ] / [Γ] / Uᵛgen (≡is≤ PE.refl) <next [Γ]
Idᵗᵛ-min {A} {t} {u} {_} {l} [Γ] [A] [t] [u] =
  let [U] = Uᵛgen (≡is≤ PE.refl) <next [Γ]
  in un-univᵛ {A = Id A t u} [Γ] [U] (Idᵛ-min {A} {t} {u} [Γ] [A] [t] [u])

Idᵗᵛ : ∀ {A t u Γ l}
       ([Γ] : ⊩ᵛ Γ) →
       let [UA] = maybeEmbᵛ {A = U _} [Γ] (Uᵛ <next [Γ])
           [U] = maybeEmbᵛ {A = SProp _} [Γ] (Uᵛ <next [Γ])
       in ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ ! , ι l ] / [Γ])
          ([t] : Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ [ ! , ι l ] / [Γ] / [A])
          ([u] : Γ ⊩ᵛ⟨ ∞ ⟩ u ∷ A ^ [ ! , ι l ] / [Γ] / [A])
          ([A]t : Γ ⊩ᵛ⟨ ∞ ⟩ A ∷ Univ ! l ^ [ ! , next l ] / [Γ] / [UA])
          → Γ ⊩ᵛ⟨ ∞ ⟩ Id A t u ∷ SProp l ^ [ ! , next l ] / [Γ] / [U]
Idᵗᵛ {A} {t} {u} {_} {l} [Γ] [A] [t] [u] [A]t =
  let [UA] = maybeEmbᵛ {A = U _} [Γ] (Uᵛ <next [Γ])
      [A]' = univᵛ {A = A} [Γ] (≡is≤ PE.refl) [UA] [A]t
      [t]' = S.irrelevanceTerm {A = A} {t = t} [Γ] [Γ] [A] [A]' [t]
      [u]' = S.irrelevanceTerm {A = A} {t = u} [Γ] [Γ] [A] [A]' [u]
      [Id] = Idᵗᵛ-min {A} {t} {u} [Γ] [A]' [t]' [u]'
  in maybeEmbTermᵛ {l = next l} {A = SProp _} {t = Id A t u} [Γ] (Uᵛgen (≡is≤ PE.refl) <next [Γ]) [Id]

Id-congᵛ-min : ∀ {A A' t t' u u' Γ l}
       ([Γ] : ⊩ᵛ Γ)
       ([A] : Γ ⊩ᵛ⟨ ι l ⟩ A ^ [ ! , ι l ] / [Γ])
       ([t] : Γ ⊩ᵛ⟨ ι l ⟩ t ∷ A ^ [ ! , ι l ] / [Γ] / [A])
       ([u] : Γ ⊩ᵛ⟨ ι l ⟩ u ∷ A ^ [ ! , ι l ] / [Γ] / [A])
       ([A'] : Γ ⊩ᵛ⟨ ι l ⟩ A' ^ [ ! , ι l ] / [Γ])
       ([t'] : Γ ⊩ᵛ⟨ ι l ⟩ t' ∷ A' ^ [ ! , ι l ] / [Γ] / [A'])
       ([u'] : Γ ⊩ᵛ⟨ ι l ⟩ u' ∷ A' ^ [ ! , ι l ] / [Γ] / [A'])
       ([A≡A'] : Γ ⊩ᵛ⟨ ι l ⟩ A ≡ A' ^ [ ! , ι l ] / [Γ] / [A])
       ([t≡t'] : Γ ⊩ᵛ⟨ ι l ⟩ t ≡ t' ∷ A ^ [ ! , ι l ] / [Γ] / [A])
       ([u≡u'] : Γ ⊩ᵛ⟨ ι l ⟩ u ≡ u' ∷ A ^ [ ! , ι l ] / [Γ] / [A])
     → Γ ⊩ᵛ⟨ ι l ⟩ Id A t u ≡ Id A' t' u' ^ [ % , ι l ] / [Γ] / Idᵛ-min {A} {t} {u} [Γ] [A] [t] [u] 
Id-congᵛ-min [Γ] [A] [t] [u] [A'] [t'] [u'] [A≡A'] [t≡t'] [u≡u'] ⊢Δ [σ] =
  [IdExt] ⊢Δ (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([A'] ⊢Δ [σ])) ([A≡A'] ⊢Δ [σ])
             (proj₁ ([t] ⊢Δ [σ])) (proj₁ ([t'] ⊢Δ [σ])) ([t≡t'] ⊢Δ [σ])
             (proj₁ ([u] ⊢Δ [σ])) (proj₁ ([u'] ⊢Δ [σ])) ([u≡u'] ⊢Δ [σ])

Id-cong-minᵗᵛ : ∀ {A A' t t' u u' Γ l}
       ([Γ] : ⊩ᵛ Γ)
       ([A] : Γ ⊩ᵛ⟨ ι l ⟩ A ^ [ ! , ι l ] / [Γ])
       ([t] : Γ ⊩ᵛ⟨ ι l ⟩ t ∷ A ^ [ ! , ι l ] / [Γ] / [A])
       ([u] : Γ ⊩ᵛ⟨ ι l ⟩ u ∷ A ^ [ ! , ι l ] / [Γ] / [A])
       ([A'] : Γ ⊩ᵛ⟨ ι l ⟩ A' ^ [ ! , ι l ] / [Γ])
       ([t'] : Γ ⊩ᵛ⟨ ι l ⟩ t' ∷ A' ^ [ ! , ι l ] / [Γ] / [A'])
       ([u'] : Γ ⊩ᵛ⟨ ι l ⟩ u' ∷ A' ^ [ ! , ι l ] / [Γ] / [A'])
       ([A≡A'] : Γ ⊩ᵛ⟨ ι l ⟩ A ≡ A' ^ [ ! , ι l ] / [Γ] / [A])
       ([t≡t'] : Γ ⊩ᵛ⟨ ι l ⟩ t ≡ t' ∷ A ^ [ ! , ι l ] / [Γ] / [A])
       ([u≡u'] : Γ ⊩ᵛ⟨ ι l ⟩ u ≡ u' ∷ A ^ [ ! , ι l ] / [Γ] / [A])
     → Γ ⊩ᵛ⟨ next l ⟩ Id A t u ≡ Id A' t' u' ∷ SProp l ^ [ ! , next l ] / [Γ] / Uᵛgen (≡is≤ PE.refl) <next [Γ]
Id-cong-minᵗᵛ {A} {A'} {t} {t'} {u} {u'} [Γ] [A] [t] [u] [A'] [t'] [u'] [A≡A'] [t≡t'] [u≡u'] =
  let [U] = Uᵛgen (≡is≤ PE.refl) <next [Γ]
  in un-univEqᵛ {A = Id A t u} {B = Id A' t' u'} [Γ] [U]
                (Idᵛ-min {A} {t} {u} [Γ] [A] [t] [u])
                (Idᵛ-min {A'} {t'} {u'} [Γ] [A'] [t'] [u'])
                (Id-congᵛ-min {A} {A'} {t} {t'} {u} {u'} [Γ] [A] [t] [u] [A'] [t'] [u'] [A≡A'] [t≡t'] [u≡u'])

Id-congᵗᵛ : ∀ {A A' t t' u u' Γ l}
       ([Γ] : ⊩ᵛ Γ) →
       let [UA] = maybeEmbᵛ {A = U _} [Γ] (Uᵛ <next [Γ])
           [U] = maybeEmbᵛ {A = SProp _} [Γ] (Uᵛ <next [Γ])
       in ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ ! , ι l ] / [Γ])
          ([t] : Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ [ ! , ι l ] / [Γ] / [A])
          ([u] : Γ ⊩ᵛ⟨ ∞ ⟩ u ∷ A ^ [ ! , ι l ] / [Γ] / [A])
          ([A]t : Γ ⊩ᵛ⟨ ∞ ⟩ A ∷ Univ ! l ^ [ ! , next l ] / [Γ] / [UA])
          ([A'] : Γ ⊩ᵛ⟨ ∞ ⟩ A' ^ [ ! , ι l ] / [Γ])
          ([t'] : Γ ⊩ᵛ⟨ ∞ ⟩ t' ∷ A' ^ [ ! , ι l ] / [Γ] / [A'])
          ([u'] : Γ ⊩ᵛ⟨ ∞ ⟩ u' ∷ A' ^ [ ! , ι l ] / [Γ] / [A'])
          ([A']t : Γ ⊩ᵛ⟨ ∞ ⟩ A' ∷ Univ ! l ^ [ ! , next l ] / [Γ] / [UA])
          ([A≡A']t : Γ ⊩ᵛ⟨ ∞ ⟩ A ≡ A' ∷ Univ ! l ^ [ ! , next l ] / [Γ] / [UA])
          ([t≡t'] : Γ ⊩ᵛ⟨ ∞ ⟩ t ≡ t' ∷ A ^ [ ! , ι l ] / [Γ] / [A])
          ([u≡u'] : Γ ⊩ᵛ⟨ ∞ ⟩ u ≡ u' ∷ A ^ [ ! , ι l ] / [Γ] / [A])
          → Γ ⊩ᵛ⟨ ∞ ⟩ Id A t u ≡ Id A' t' u' ∷ SProp l ^ [ ! , next l ] / [Γ] / [U]
Id-congᵗᵛ {A} {A'} {t} {t'} {u} {u'} {_} {l} [Γ] [A] [t] [u] [A]t [A'] [t'] [u'] [A']t [A≡A']t [t≡t'] [u≡u'] =
   let [UA] = maybeEmbᵛ {A = U _} [Γ] (Uᵛ <next [Γ])
       [A]' = univᵛ {A = A} [Γ] (≡is≤ PE.refl) [UA] [A]t
       [t]' = S.irrelevanceTerm {A = A} {t = t} [Γ] [Γ] [A] [A]' [t]
       [u]' = S.irrelevanceTerm {A = A} {t = u} [Γ] [Γ] [A] [A]' [u]
       [A']' = univᵛ {A = A'} [Γ] (≡is≤ PE.refl) [UA] [A']t
       [t']' = S.irrelevanceTerm {A = A'} {t = t'} [Γ] [Γ] [A'] [A']' [t']
       [u']' = S.irrelevanceTerm {A = A'} {t = u'} [Γ] [Γ] [A'] [A']' [u']
       [A≡A']' = univEqᵛ {A = A} {B = A'} [Γ] [UA] [A]' [A≡A']t       
       [t≡t']' = S.irrelevanceEqTerm {A = A} {t = t} {u = t'} [Γ] [Γ] [A] [A]' [t≡t']
       [u≡u']' = S.irrelevanceEqTerm {A = A} {t = u} {u = u'} [Γ] [Γ] [A] [A]' [u≡u']
       [Id] = Id-cong-minᵗᵛ {A} {A'} {t} {t'} {u} {u'} [Γ] [A]' [t]' [u]' [A']' [t']' [u']' [A≡A']' [t≡t']' [u≡u']'
   in maybeEmbEqTermᵛ {l = next l} {A = SProp _} {t = Id A t u} {u = Id A' t' u'} [Γ] (Uᵛgen (≡is≤ PE.refl) <next [Γ]) [Id]
