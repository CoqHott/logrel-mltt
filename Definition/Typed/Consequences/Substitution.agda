{-# OPTIONS --safe #-}

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
substitution : ∀ {A rA Γ Δ σ} → Γ ⊢ A ^ rA → Δ ⊢ˢ σ ∷ Γ → ⊢ Δ → Δ ⊢ subst σ A ^ rA
substitution A σ ⊢Δ =
    let X = fundamental A
        [Γ] = proj₁ X
        [A] = proj₂ X
        Y = fundamentalSubst (wf A) ⊢Δ σ
        [Γ]′ = proj₁ Y
        [σ] = proj₂ Y
    in escape (proj₁ ([A] ⊢Δ (irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ])))

-- Well-formed substitution of type equality.
substitutionEq : ∀ {A B rA Γ Δ σ σ′}
               → Γ ⊢ A ≡ B ^ rA → Δ ⊢ˢ σ ≡ σ′ ∷ Γ → ⊢ Δ → Δ ⊢ subst σ A ≡ subst σ′ B ^ rA
substitutionEq A≡B σ ⊢Δ =
  let X = fundamentalEq A≡B
      [Γ] = proj₁ X
      [A] = proj₁ (proj₂ X)
      [B] = proj₁ (proj₂ (proj₂ X))
      [A≡B] = proj₂ (proj₂ (proj₂ X))
      Y = fundamentalSubstEq (wfEq A≡B) ⊢Δ σ
      [Γ]′ = proj₁ Y
      [σ] = proj₁ (proj₂ Y)
      [σ′] = proj₁ (proj₂ (proj₂ Y))
      [σ≡σ′] = proj₂ (proj₂ (proj₂ Y))
      [σ]′ = irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ]
      [σ′]′ = irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ′]
      [σ≡σ′]′ = irrelevanceSubstEq [Γ]′ [Γ] ⊢Δ ⊢Δ [σ] [σ]′ [σ≡σ′]
  in  escapeEq (proj₁ ([A] ⊢Δ [σ]′))
                   (transEq (proj₁ ([A] ⊢Δ [σ]′)) (proj₁ ([B] ⊢Δ [σ]′))
                            (proj₁ ([B] ⊢Δ [σ′]′)) ([A≡B] ⊢Δ [σ]′)
                            (proj₂ ([B] ⊢Δ [σ]′) [σ′]′ [σ≡σ′]′))

-- Well-formed substitution of terms.
substitutionTerm : ∀ {t A rA Γ Δ σ}
               → Γ ⊢ t ∷ A ^ rA → Δ ⊢ˢ σ ∷ Γ → ⊢ Δ → Δ ⊢ subst σ t ∷ subst σ A ^ rA
substitutionTerm t σ ⊢Δ =
  let X = fundamentalTerm t
      [Γ] = proj₁ X
      [A] = proj₁ (proj₂ X)
      [t] = proj₂ (proj₂ X)
      Y = fundamentalSubst (wfTerm t) ⊢Δ σ
      [Γ]′ = proj₁ Y
      [σ] = proj₂ Y
      [σ]′ = irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ]
  in escapeTerm (proj₁ ([A] ⊢Δ [σ]′)) (proj₁ ([t] ⊢Δ [σ]′))

-- Well-formed substitution of term equality.
substitutionEqTerm : ∀ {t u A rA Γ Δ σ σ′}
                   → Γ ⊢ t ≡ u ∷ A ^ rA → Δ ⊢ˢ σ ≡ σ′ ∷ Γ → ⊢ Δ
                   → Δ ⊢ subst σ t ≡ subst σ′ u ∷ subst σ A ^ rA
substitutionEqTerm t≡u σ≡σ′ ⊢Δ with fundamentalTermEq t≡u
substitutionEqTerm t≡u σ≡σ′ ⊢Δ | [Γ] , modelsTermEq [A] [t] [u] [t≡u] =
  let Y = fundamentalSubstEq (wfEqTerm t≡u) ⊢Δ σ≡σ′
      [Γ]′ = proj₁ Y
      [σ] = proj₁ (proj₂ Y)
      [σ′] = proj₁ (proj₂ (proj₂ Y))
      [σ≡σ′] = proj₂ (proj₂ (proj₂ Y))      
      [σ]′ = irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ]
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
substRefl (σ , x) = substRefl σ , genRefl x

-- Weakening of well-formed substitution.
wkSubst′ : ∀ {ρ σ Γ Δ Δ′} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ) (⊢Δ′ : ⊢ Δ′)
           ([ρ] : ρ ∷ Δ′ ⊆ Δ)
           ([σ] : Δ ⊢ˢ σ ∷ Γ)
         → Δ′ ⊢ˢ ρ •ₛ σ ∷ Γ
wkSubst′ ε ⊢Δ ⊢Δ′ ρ id = id
wkSubst′ (_∙_ {Γ} {A} ⊢Γ ⊢A) ⊢Δ ⊢Δ′ ρ (tailσ , headσ) =
  wkSubst′ ⊢Γ ⊢Δ ⊢Δ′ ρ tailσ
  , PE.subst (λ x → _ ⊢ _ ∷ x ^ _) (wk-subst A) (wkTerm ρ ⊢Δ′ headσ)

-- Weakening of well-formed substitution by one.
wk1Subst′ : ∀ {F rF σ Γ Δ} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
            (⊢F : Δ ⊢ F ^ rF)
            ([σ] : Δ ⊢ˢ σ ∷ Γ)
          → (Δ ∙ F ^ rF) ⊢ˢ wk1Subst σ ∷ Γ
wk1Subst′ {F} {σ} {Γ} {Δ} ⊢Γ ⊢Δ ⊢F [σ] =
  wkSubst′ ⊢Γ ⊢Δ (⊢Δ ∙ ⊢F) (step id) [σ]

-- Lifting of well-formed substitution.
liftSubst′ : ∀ {F rF σ Γ Δ} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
             (⊢F  : Γ ⊢ F ^ rF)
             ([σ] : Δ ⊢ˢ σ ∷ Γ)
           → (Δ ∙ subst σ F ^ rF) ⊢ˢ liftSubst σ ∷ Γ ∙ F ^ rF
liftSubst′ {F} {rF} {σ} {Γ} {Δ} ⊢Γ ⊢Δ ⊢F [σ] =
  let ⊢Δ∙F = ⊢Δ ∙ substitution ⊢F [σ] ⊢Δ
  in  wkSubst′ ⊢Γ ⊢Δ ⊢Δ∙F (step id) [σ]
  ,   var ⊢Δ∙F (PE.subst (λ x → 0 ∷ x ^ rF ∈ (Δ ∙ subst σ F ^ rF))
                         (wk-subst F) here)

-- Well-formed identity substitution.
idSubst′ : ∀ {Γ} (⊢Γ : ⊢ Γ)
         → Γ ⊢ˢ idSubst ∷ Γ
idSubst′ ε = id
idSubst′ (_∙_ {Γ} {A} {rA} ⊢Γ ⊢A) =
  wk1Subst′ ⊢Γ ⊢Γ ⊢A (idSubst′ ⊢Γ)
  , PE.subst (λ x → Γ ∙ A ^ rA ⊢ _ ∷ x ^ rA) (wk1-tailId A) (var (⊢Γ ∙ ⊢A) here)

-- Well-formed substitution composition.
substComp′ : ∀ {σ σ′ Γ Δ Δ′} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ) (⊢Δ′ : ⊢ Δ′)
             ([σ] : Δ′ ⊢ˢ σ ∷ Δ)
             ([σ′] : Δ ⊢ˢ σ′ ∷ Γ)
           → Δ′ ⊢ˢ σ ₛ•ₛ σ′ ∷ Γ
substComp′ ε ⊢Δ ⊢Δ′ [σ] id = id
substComp′ (_∙_ {Γ} {A} {rA} ⊢Γ ⊢A) ⊢Δ ⊢Δ′ [σ] ([tailσ′] , [headσ′]) =
  substComp′ ⊢Γ ⊢Δ ⊢Δ′ [σ] [tailσ′]
  , PE.subst (λ x → _ ⊢ _ ∷ x ^ rA) (substCompEq A)
             (substitutionTerm [headσ′] [σ] ⊢Δ′)

-- Well-formed singleton substitution of terms.
singleSubst : ∀ {A t rA Γ} → Γ ⊢ t ∷ A ^ rA → Γ ⊢ˢ sgSubst t ∷ Γ ∙ A ^ rA
singleSubst {A} {rA = rA} t =
  let ⊢Γ = wfTerm t
  in  idSubst′ ⊢Γ , PE.subst (λ x → _ ⊢ _ ∷ x ^ rA) (PE.sym (subst-id A)) t

-- Well-formed singleton substitution of term equality.
singleSubstEq : ∀ {A t u rA Γ} → Γ ⊢ t ≡ u ∷ A ^ rA
              → Γ ⊢ˢ sgSubst t ≡ sgSubst u ∷ Γ ∙ A ^ rA
singleSubstEq {A} {rA = rA} t =
  let ⊢Γ = wfEqTerm t
  in  substRefl (idSubst′ ⊢Γ) , PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x ^ rA) (PE.sym (subst-id A)) t

-- Well-formed singleton substitution of terms with lifting.
singleSubst↑ : ∀ {A t rA Γ} → Γ ∙ A ^ rA ⊢ t ∷ wk1 A ^ rA
             → Γ ∙ A ^ rA ⊢ˢ consSubst (wk1Subst idSubst) t ∷ Γ ∙ A ^ rA
singleSubst↑ {A} {rA = rA} t with wfTerm t
... | ⊢Γ ∙ ⊢A = wk1Subst′ ⊢Γ ⊢Γ ⊢A (idSubst′ ⊢Γ)
              , PE.subst (λ x → _ ∙ A ^ rA ⊢ _ ∷ x ^ _) (wk1-tailId A) t

-- Well-formed singleton substitution of term equality with lifting.
singleSubst↑Eq : ∀ {A rA t u Γ} → Γ ∙ A ^ rA ⊢ t ≡ u ∷ wk1 A ^ rA
              → Γ ∙ A ^ rA ⊢ˢ consSubst (wk1Subst idSubst) t ≡ consSubst (wk1Subst idSubst) u ∷ Γ ∙ A ^ rA
singleSubst↑Eq {A} {rA} t with wfEqTerm t
... | ⊢Γ ∙ ⊢A = substRefl (wk1Subst′ ⊢Γ ⊢Γ ⊢A (idSubst′ ⊢Γ))
              , PE.subst (λ x → _ ∙ A ^ rA ⊢ _ ≡ _ ∷ x ^ rA) (wk1-tailId A) t

-- Helper lemmas for single substitution

substType : ∀ {t F rF G rG Γ} → Γ ∙ F ^ rF ⊢ G ^ rG → Γ ⊢ t ∷ F ^ rF → Γ ⊢ G [ t ] ^ rG
substType {t} {F} {G} ⊢G ⊢t =
  let ⊢Γ = wfTerm ⊢t
  in  substitution ⊢G (singleSubst ⊢t) ⊢Γ

substTypeEq : ∀ {t u F rF G E rG Γ} → Γ ∙ F ^ rF ⊢ G ≡ E ^ rG
            → Γ ⊢ t ≡ u ∷ F ^ rF
            → Γ ⊢ G [ t ] ≡ E [ u ] ^ rG
substTypeEq {F = F} ⊢G ⊢t =
  let ⊢Γ = wfEqTerm ⊢t
  in  substitutionEq ⊢G (singleSubstEq ⊢t) ⊢Γ

substTerm : ∀ {F rF G rG t f Γ} → Γ ∙ F ^ rF ⊢ f ∷ G ^ rG
          → Γ ⊢ t ∷ F ^ rF
          → Γ ⊢ f [ t ] ∷ G [ t ] ^ rG
substTerm {F} {G} {t} {f} ⊢f ⊢t =
  let ⊢Γ = wfTerm ⊢t
  in  substitutionTerm ⊢f (singleSubst ⊢t) ⊢Γ

substTypeΠ : ∀ {t F rF lF lG G rΠ lΠ Γ} → Γ ⊢ Π F ^ rF ° lF ▹ G ° lG ^ [ rΠ , ι lΠ ] → Γ ⊢ t ∷ F ^ [ rF , ι lF ]
                                     → Γ ⊢ G [ t ] ^ [ rΠ , ι lG ] 
substTypeΠ ΠFG t with syntacticΠ ΠFG
substTypeΠ ΠFG t | F , G = substType G t

subst↑Type : ∀ {t F rF G rG Γ}
           → Γ ∙ F ^ rF ⊢ G ^ rG
           → Γ ∙ F ^ rF ⊢ t ∷ wk1 F ^ rF
           → Γ ∙ F ^ rF ⊢ G [ t ]↑ ^ rG
subst↑Type ⊢G ⊢t = substitution ⊢G (singleSubst↑ ⊢t) (wfTerm ⊢t)

subst↑TypeEq : ∀ {t u F rF G E rG Γ}
             → Γ ∙ F ^ rF ⊢ G ≡ E ^ rG
             → Γ ∙ F ^ rF ⊢ t ≡ u ∷ wk1 F ^ rF
             → Γ ∙ F ^ rF ⊢ G [ t ]↑ ≡ E [ u ]↑ ^ rG
subst↑TypeEq ⊢G ⊢t = substitutionEq ⊢G (singleSubst↑Eq ⊢t) (wfEqTerm ⊢t)
