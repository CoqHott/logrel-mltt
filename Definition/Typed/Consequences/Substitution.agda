{-# OPTIONS --without-K  #-}

module Definition.Typed.Consequences.Substitution where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.EqRelInstance
open import Definition.Typed.Weakening
open import Definition.Typed.Consequences.Syntactic
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Irrelevance
open import Definition.LogicalRelation.Fundamental

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Well-formed substitution of types.
substitution : ∀ {A sA Γ Δ σ} → Γ ⊢ A ⦂ sA → Δ ⊢ˢ σ ∷ Γ → ⊢ Δ → Δ ⊢ subst σ A ⦂ sA
substitution A σ ⊢Δ with fundamental A | fundamentalSubst (wf A) ⊢Δ σ
substitution A σ ⊢Δ | [Γ] , [A] | [Γ]′ , [σ] =
  escape (proj₁ ([A] ⊢Δ (irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ])))

-- Well-formed substitution of type equality.
substitutionEq : ∀ {A B sA Γ Δ σ σ′}
               → Γ ⊢ A ≡ B ⦂ sA → Δ ⊢ˢ σ ≡ σ′ ∷ Γ → ⊢ Δ → Δ ⊢ subst σ A ≡ subst σ′ B ⦂ sA
substitutionEq A≡B σ ⊢Δ with fundamentalEq A≡B | fundamentalSubstEq (wfEq A≡B) ⊢Δ σ
substitutionEq A≡B σ ⊢Δ | [Γ] , [A] , [B] , [A≡B] | [Γ]′ , [σ] , [σ′] , [σ≡σ′]  =
  let [σ]′ = irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ]
      [σ′]′ = irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ′]
      [σ≡σ′]′ = irrelevanceSubstEq [Γ]′ [Γ] ⊢Δ ⊢Δ [σ] [σ]′ [σ≡σ′]
  in  escapeEq (proj₁ ([A] ⊢Δ [σ]′))
                   (transEq (proj₁ ([A] ⊢Δ [σ]′)) (proj₁ ([B] ⊢Δ [σ]′))
                            (proj₁ ([B] ⊢Δ [σ′]′)) ([A≡B] ⊢Δ [σ]′)
                            (proj₂ ([B] ⊢Δ [σ]′) [σ′]′ [σ≡σ′]′))

-- Well-formed substitution of terms.
substitutionTerm : ∀ {t A sA Γ Δ σ}
               → Γ ⊢ t ∷ A ⦂ sA → Δ ⊢ˢ σ ∷ Γ → ⊢ Δ → Δ ⊢ subst σ t ∷ subst σ A ⦂ sA
substitutionTerm t σ ⊢Δ with fundamentalTerm t | fundamentalSubst (wfTerm t) ⊢Δ σ
substitutionTerm t σ ⊢Δ | [Γ] , [A] , [t] | [Γ]′ , [σ] =
  let [σ]′ = irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ]
  in  escapeTerm (proj₁ ([A] ⊢Δ [σ]′)) (proj₁ ([t] ⊢Δ [σ]′))

-- Well-formed substitution of term equality.
substitutionEqTerm : ∀ {t u A sA Γ Δ σ σ′}
                   → Γ ⊢ t ≡ u ∷ A ⦂ sA → Δ ⊢ˢ σ ≡ σ′ ∷ Γ → ⊢ Δ
                   → Δ ⊢ subst σ t ≡ subst σ′ u ∷ subst σ A ⦂ sA
substitutionEqTerm t≡u σ≡σ′ ⊢Δ with fundamentalTermEq t≡u
                                  | fundamentalSubstEq (wfEqTerm t≡u) ⊢Δ σ≡σ′
... | [Γ] , modelsTermEq [A] [t] [u] [t≡u] | [Γ]′ , [σ] , [σ′] , [σ≡σ′] =
  let [σ]′ = irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ]
      [σ′]′ = irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ′]
      [σ≡σ′]′ = irrelevanceSubstEq [Γ]′ [Γ] ⊢Δ ⊢Δ [σ] [σ]′ [σ≡σ′]
  in  escapeTermEq (proj₁ ([A] ⊢Δ [σ]′))
                       (transEqTerm (proj₁ ([A] ⊢Δ [σ]′)) ([t≡u] ⊢Δ [σ]′)
                                    (proj₂ ([u] ⊢Δ [σ]′) [σ′]′ [σ≡σ′]′))

-- Reflexivity of well-formed substitution.
substRefl : ∀ {σ Γ Δ}
          → Δ ⊢ˢ σ ∷ Γ
          → Δ ⊢ˢ σ ≡ σ ∷ Γ
substRefl id = id
substRefl (σ , x) = substRefl σ , refl x

-- Weakening of well-formed substitution.
wkSubst′ : ∀ {ρ σ Γ Δ Δ′} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ) (⊢Δ′ : ⊢ Δ′)
           ([ρ] : ρ ∷ Δ′ ⊆ Δ)
           ([σ] : Δ ⊢ˢ σ ∷ Γ)
         → Δ′ ⊢ˢ ρ •ₛ σ ∷ Γ
wkSubst′ ε ⊢Δ ⊢Δ′ ρ id = id
wkSubst′ (_∙_ {Γ} {A} ⊢Γ ⊢A) ⊢Δ ⊢Δ′ ρ (tailσ , headσ) =
  wkSubst′ ⊢Γ ⊢Δ ⊢Δ′ ρ tailσ
  , PE.subst (λ x → _ ⊢ _ ∷ x ⦂ _) (wk-subst A) (wkTerm ρ ⊢Δ′ headσ)

-- Weakening of well-formed substitution by one.
wk1Subst′ : ∀ {F sF σ Γ Δ} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
            (⊢F : Δ ⊢ F ⦂ sF)
            ([σ] : Δ ⊢ˢ σ ∷ Γ)
          → (Δ ∙ F ⦂ sF) ⊢ˢ wk1Subst σ ∷ Γ
wk1Subst′ {F} {σ} {Γ} {Δ} ⊢Γ ⊢Δ ⊢F [σ] =
  wkSubst′ ⊢Γ ⊢Δ (⊢Δ ∙ ⊢F) (step id) [σ]

-- Lifting of well-formed substitution.
liftSubst′ : ∀ {F sF σ Γ Δ} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
             (⊢F  : Γ ⊢ F ⦂ sF)
             ([σ] : Δ ⊢ˢ σ ∷ Γ)
           → (Δ ∙ subst σ F ⦂ sF) ⊢ˢ liftSubst σ ∷ Γ ∙ F ⦂ sF
liftSubst′ {F} {sF} {σ} {Γ} {Δ} ⊢Γ ⊢Δ ⊢F [σ] =
  let ⊢Δ∙F = ⊢Δ ∙ substitution ⊢F [σ] ⊢Δ
  in  wkSubst′ ⊢Γ ⊢Δ ⊢Δ∙F (step id) [σ]
  ,   var ⊢Δ∙F (PE.subst (λ x → 0 ∷ x ⦂ sF ∈ (Δ ∙ subst σ F ⦂ sF))
                         (wk-subst F) here)

-- Well-formed identity substitution.
idSubst′ : ∀ {Γ} (⊢Γ : ⊢ Γ)
         → Γ ⊢ˢ idSubst ∷ Γ
idSubst′ ε = id
idSubst′ (_∙_ {Γ} {A} {sA} ⊢Γ ⊢A) =
  wk1Subst′ ⊢Γ ⊢Γ ⊢A (idSubst′ ⊢Γ)
  , PE.subst (λ x → Γ ∙ A ⦂ sA ⊢ _ ∷ x ⦂ sA) (wk1-tailId A) (var (⊢Γ ∙ ⊢A) here)

-- Well-formed substitution composition.
substComp′ : ∀ {σ σ′ Γ Δ Δ′} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ) (⊢Δ′ : ⊢ Δ′)
             ([σ] : Δ′ ⊢ˢ σ ∷ Δ)
             ([σ′] : Δ ⊢ˢ σ′ ∷ Γ)
           → Δ′ ⊢ˢ σ ₛ•ₛ σ′ ∷ Γ
substComp′ ε ⊢Δ ⊢Δ′ [σ] id = id
substComp′ (_∙_ {Γ} {A} {sA} ⊢Γ ⊢A) ⊢Δ ⊢Δ′ [σ] ([tailσ′] , [headσ′]) =
  substComp′ ⊢Γ ⊢Δ ⊢Δ′ [σ] [tailσ′]
  , PE.subst (λ x → _ ⊢ _ ∷ x ⦂ sA) (substCompEq A)
             (substitutionTerm [headσ′] [σ] ⊢Δ′)

-- Well-formed singleton substitution of terms.
singleSubst : ∀ {A t sA Γ} → Γ ⊢ t ∷ A ⦂ sA → Γ ⊢ˢ sgSubst t ∷ Γ ∙ A ⦂ sA
singleSubst {A} {sA = sA} t =
  let ⊢Γ = wfTerm t
  in  idSubst′ ⊢Γ , PE.subst (λ x → _ ⊢ _ ∷ x ⦂ sA) (PE.sym (subst-id A)) t

-- Well-formed singleton substitution of term equality.
singleSubstEq : ∀ {A t u sA Γ} → Γ ⊢ t ≡ u ∷ A ⦂ sA
              → Γ ⊢ˢ sgSubst t ≡ sgSubst u ∷ Γ ∙ A ⦂ sA
singleSubstEq {A} {sA = sA} t =
  let ⊢Γ = wfEqTerm t
  in  substRefl (idSubst′ ⊢Γ) , PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x ⦂ sA) (PE.sym (subst-id A)) t

-- Well-formed singleton substitution of terms with lifting.
singleSubst↑ : ∀ {A t sA Γ} → Γ ∙ A ⦂ sA ⊢ t ∷ wk1 A ⦂ sA
             → Γ ∙ A ⦂ sA ⊢ˢ consSubst (wk1Subst idSubst) t ∷ Γ ∙ A ⦂ sA
singleSubst↑ {A} {sA = sA} t with wfTerm t
... | ⊢Γ ∙ ⊢A = wk1Subst′ ⊢Γ ⊢Γ ⊢A (idSubst′ ⊢Γ)
              , PE.subst (λ x → _ ∙ A ⦂ sA ⊢ _ ∷ x ⦂ _) (wk1-tailId A) t

-- Well-formed singleton substitution of term equality with lifting.
singleSubst↑Eq : ∀ {A sA t u Γ} → Γ ∙ A ⦂ sA ⊢ t ≡ u ∷ wk1 A ⦂ sA
              → Γ ∙ A ⦂ sA ⊢ˢ consSubst (wk1Subst idSubst) t ≡ consSubst (wk1Subst idSubst) u ∷ Γ ∙ A ⦂ sA
singleSubst↑Eq {A} {sA} t with wfEqTerm t
... | ⊢Γ ∙ ⊢A = substRefl (wk1Subst′ ⊢Γ ⊢Γ ⊢A (idSubst′ ⊢Γ))
              , PE.subst (λ x → _ ∙ A ⦂ sA ⊢ _ ≡ _ ∷ x ⦂ sA) (wk1-tailId A) t

-- Helper lemmas for single substitution

substType : ∀ {t F sF G sG Γ} → Γ ∙ F ⦂ sF ⊢ G ⦂ sG → Γ ⊢ t ∷ F ⦂ sF → Γ ⊢ G [ t ] ⦂ sG
substType {t} {F} {G} ⊢G ⊢t =
  let ⊢Γ = wfTerm ⊢t
  in  substitution ⊢G (singleSubst ⊢t) ⊢Γ

substTypeEq : ∀ {t u F sF G E sG Γ} → Γ ∙ F ⦂ sF ⊢ G ≡ E ⦂ sG
            → Γ ⊢ t ≡ u ∷ F ⦂ sF
            → Γ ⊢ G [ t ] ≡ E [ u ] ⦂ sG
substTypeEq {F = F} ⊢G ⊢t =
  let ⊢Γ = wfEqTerm ⊢t
  in  substitutionEq ⊢G (singleSubstEq ⊢t) ⊢Γ

substTerm : ∀ {F sF G sG t f Γ} → Γ ∙ F ⦂ sF ⊢ f ∷ G ⦂ sG
          → Γ ⊢ t ∷ F ⦂ sF
          → Γ ⊢ f [ t ] ∷ G [ t ] ⦂ sG
substTerm {F} {G} {t} {f} ⊢f ⊢t =
  let ⊢Γ = wfTerm ⊢t
  in  substitutionTerm ⊢f (singleSubst ⊢t) ⊢Γ

substTypeΠ : ∀ {t F sF G sG Γ} → Γ ⊢ Π F ⦂ sF ▹ G ⦂ sG → Γ ⊢ t ∷ F ⦂ sF → Γ ⊢ G [ t ] ⦂ sG
substTypeΠ ΠFG t with syntacticΠ ΠFG
substTypeΠ ΠFG t | F , G = substType G t

subst↑Type : ∀ {t F sF G sG Γ}
           → Γ ∙ F ⦂ sF ⊢ G ⦂ sG
           → Γ ∙ F ⦂ sF ⊢ t ∷ wk1 F ⦂ sF
           → Γ ∙ F ⦂ sF ⊢ G [ t ]↑ ⦂ sG
subst↑Type ⊢G ⊢t = substitution ⊢G (singleSubst↑ ⊢t) (wfTerm ⊢t)

subst↑TypeEq : ∀ {t u F sF G E sG Γ}
             → Γ ∙ F ⦂ sF ⊢ G ≡ E ⦂ sG
             → Γ ∙ F ⦂ sF ⊢ t ≡ u ∷ wk1 F ⦂ sF
             → Γ ∙ F ⦂ sF ⊢ G [ t ]↑ ≡ E [ u ]↑ ⦂ sG
subst↑TypeEq ⊢G ⊢t = substitutionEq ⊢G (singleSubst↑Eq ⊢t) (wfEqTerm ⊢t)
