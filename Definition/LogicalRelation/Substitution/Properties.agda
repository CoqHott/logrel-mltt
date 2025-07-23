{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Properties {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Irrelevance
     using (irrelevanceSubst′)
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
import Definition.LogicalRelation.Weakening as LR

open import Tools.Unit
open import Tools.Product
import Tools.PropositionalEquality as PE


-- Valid substitutions are well-formed
wellformedSubst : ∀ {Γ σ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ ε)
      → ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ
      → ε ⊢ˢ σ ∷ Γ
wellformedSubst ε ⊢Δ [σ] = id
wellformedSubst ([Γ] ∙ [A]) ⊢Δ ([tailσ] , [headσ]) =
  wellformedSubst [Γ] ⊢Δ [tailσ]
  , escapeTerm (proj₁ ([A] ⊢Δ [tailσ])) [headσ]

-- Valid substitution equality is well-formed
wellformedSubstEq : ∀ {Γ σ σ′} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ ε)
      ([σ] : ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
      → ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ]
      → ε ⊢ˢ σ ≡ σ′ ∷ Γ
wellformedSubstEq ε ⊢Δ [σ] [σ≡σ′] = id
wellformedSubstEq ([Γ] ∙ [A]) ⊢Δ ([tailσ] , [headσ]) ([tailσ≡σ′] , [headσ≡σ′]) =
  wellformedSubstEq [Γ] ⊢Δ [tailσ] [tailσ≡σ′]
  , ≅ₜ-eq (escapeTermEq (proj₁ ([A] ⊢Δ [tailσ])) [headσ≡σ′])

-- Extend a valid substitution with a term
consSubstS : ∀ {l σ t A rA Γ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ ε)
           ([σ] : ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
           ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ rA / [Γ])
           ([t] : ε ⊩⟨ l ⟩ t ∷ subst σ A ^ rA / proj₁ ([A] ⊢Δ [σ]))
         → ⊩ˢ consSubst σ t ∷ Γ ∙ A ^ rA / [Γ] ∙ [A] / ⊢Δ
consSubstS [Γ] ⊢Δ [σ] [A] [t] = [σ] , [t]

-- Extend a valid substitution equality with a term
consSubstSEq : ∀ {l σ σ′ t A rA Γ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ ε)
             ([σ]    : ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
             ([σ≡σ′] : ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ])
             ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ rA / [Γ])
             ([t] : ε ⊩⟨ l ⟩ t ∷ subst σ A ^ rA / proj₁ ([A] ⊢Δ [σ]))
           → ⊩ˢ consSubst σ t ≡ consSubst σ′ t ∷ Γ ∙ A ^ rA / [Γ] ∙ [A] / ⊢Δ
               / consSubstS {t = t} {A = A} [Γ] ⊢Δ [σ] [A] [t]
consSubstSEq [Γ] ⊢Δ [σ] [σ≡σ′] [A] [t] =
  [σ≡σ′] , reflEqTerm (proj₁ ([A] ⊢Δ [σ])) [t]

-- Weakening of valid substitutions
wkSubstS : ∀ {ρ σ Γ } ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ ε) (⊢Δ′ : ⊢ ε)
           ([ρ] : ρ ∷ ε ⊆ ε)
           ([σ] : ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
         → ⊩ˢ ρ •ₛ σ ∷ Γ / [Γ] / ⊢Δ′
wkSubstS ε ⊢Δ ⊢Δ′ ρ [σ] = tt
wkSubstS {σ = σ} {Γ = Γ ∙ A ^ rA} ([Γ] ∙ x) ⊢Δ ⊢Δ′ ρ [σ] =
  let [tailσ] = wkSubstS [Γ] ⊢Δ ⊢Δ′ ρ (proj₁ [σ])
  in  [tailσ]
   ,  irrelevanceTerm′ (wk-subst A) PE.refl PE.refl
        (LR.wk ρ ⊢Δ′ (proj₁ (x ⊢Δ (proj₁ [σ]))))
        (proj₁ (x ⊢Δ′ [tailσ]))
        (LR.wkTerm ρ ⊢Δ′ (proj₁ (x ⊢Δ (proj₁ [σ]))) (proj₂ [σ]))

-- Weakening of valid substitution equality
wkSubstSEq : ∀ {ρ σ σ′ Γ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ ε) (⊢Δ′ : ⊢ ε)
             ([ρ] : ρ ∷ ε ⊆ ε)
             ([σ] : ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
             ([σ≡σ′] : ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ])
           → ⊩ˢ ρ •ₛ σ ≡ ρ •ₛ σ′ ∷ Γ / [Γ]
                / ⊢Δ′ / wkSubstS [Γ] ⊢Δ ⊢Δ′ [ρ] [σ]
wkSubstSEq ε ⊢Δ ⊢Δ′ ρ [σ] [σ≡σ′] = tt
wkSubstSEq {Γ = Γ ∙ A ^ rA} ([Γ] ∙ x) ⊢Δ ⊢Δ′ ρ [σ] [σ≡σ′] =
  wkSubstSEq [Γ] ⊢Δ ⊢Δ′ ρ (proj₁ [σ]) (proj₁ [σ≡σ′])
  , irrelevanceEqTerm′ (wk-subst A) PE.refl PE.refl (LR.wk ρ ⊢Δ′ (proj₁ (x ⊢Δ (proj₁ [σ]))))
                            (proj₁ (x ⊢Δ′ (wkSubstS [Γ] ⊢Δ ⊢Δ′ ρ (proj₁ [σ]))))
                            (LR.wkEqTerm ρ ⊢Δ′ (proj₁ (x ⊢Δ (proj₁ [σ]))) (proj₂ [σ≡σ′]))

{-
mutual
  -- Valid contexts are well-formed
  soundContext : ∀ {Γ} → ⊩ᵛ Γ → ⊢ Γ
  soundContext ε = ε
  soundContext (x ∙ x₁) =
    soundContext x ∙ escape (irrelevance′ (subst-id _)
                                             (proj₁ (x₁ (soundContext x)
                                                        (idSubstS x))))

  -- From a valid context we can constuct a valid identity substitution
  idSubstS : ∀ {Γ} ([Γ] : ⊩ᵛ Γ) → ⊩ˢ idSubst ∷ Γ / [Γ] / soundContext [Γ]
  idSubstS ε = tt
  idSubstS {Γ = Γ ∙ A ^ rA} ([Γ] ∙ [A]) =
    let ⊢Γ = soundContext [Γ]
        ⊢Γ∙A = soundContext ([Γ] ∙ [A])
        ⊢Γ∙A′ = ⊢Γ ∙ escape (proj₁ ([A] ⊢Γ (idSubstS [Γ])))
        [A]′ = wk1SubstS {F = subst idSubst A} [Γ] ⊢Γ
                         (escape (proj₁ ([A] (soundContext [Γ])
                                                (idSubstS [Γ]))))
                         (idSubstS [Γ])
        [tailσ] = irrelevanceSubst′ (PE.cong (λ x → Γ ∙ x ^ _) (subst-id A))
                                    [Γ] [Γ] ⊢Γ∙A′ ⊢Γ∙A [A]′
        var0 = var ⊢Γ∙A (PE.subst (λ x → 0 ∷ x ^ rA ∈ (Γ ∙ A ^ rA))
                                  (wk-subst A)
                                  (PE.subst (λ x → 0 ∷ wk1 (subst idSubst A) ^ rA
                                                     ∈ (Γ ∙ x ^ rA))
                                            (subst-id A) here))
    in  [tailσ]
    ,   neuTerm (proj₁ ([A] ⊢Γ∙A [tailσ]))
                (var 0)
                var0 (~-var var0)
-}

-- Reflexivity valid substitutions
reflSubst : ∀ {σ Γ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ ε)
            ([σ] : ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ)
          → ⊩ˢ σ ≡ σ ∷ Γ / [Γ] / ⊢Δ / [σ]
reflSubst ε ⊢Δ [σ] = tt
reflSubst ([Γ] ∙ x) ⊢Δ [σ] =
  reflSubst [Γ] ⊢Δ (proj₁ [σ]) , reflEqTerm (proj₁ (x ⊢Δ (proj₁ [σ]))) (proj₂ [σ])

-- Reflexivity of valid identity substitution
-- reflIdSubst : ∀ {Γ} ([Γ] : ⊩ᵛ Γ)
--             → Γ ⊩ˢ idSubst ≡ idSubst ∷ Γ / [Γ] / soundContext [Γ] / idSubstS [Γ]
-- reflIdSubst [Γ] = reflSubst [Γ] (soundContext [Γ]) (idSubstS [Γ])

-- Symmetry of valid substitution
symS : ∀ {σ σ′ Γ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ ε)
       ([σ]  : ⊩ˢ σ  ∷ Γ / [Γ] / ⊢Δ)
       ([σ′] : ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ)
     → ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ]
     → ⊩ˢ σ′ ≡ σ ∷ Γ / [Γ] / ⊢Δ / [σ′]
symS ε ⊢Δ [σ] [σ′] [σ≡σ′] = tt
symS ([Γ] ∙ x) ⊢Δ [σ] [σ′] [σ≡σ′] =
  symS [Γ] ⊢Δ (proj₁ [σ]) (proj₁ [σ′]) (proj₁ [σ≡σ′])
  , let [σA]           = proj₁ (x ⊢Δ (proj₁ [σ]))
        [σ′A]          = proj₁ (x ⊢Δ (proj₁ [σ′]))
        [σA≡σ′A]       = (proj₂ (x ⊢Δ (proj₁ [σ]))) (proj₁ [σ′]) (proj₁ [σ≡σ′])
        [headσ′≡headσ] = symEqTerm [σA] (proj₂ [σ≡σ′])
    in  convEqTerm₁ [σA] [σ′A] [σA≡σ′A] [headσ′≡headσ]

-- Transitivity of valid substitution
transS : ∀ {σ σ′ σ″ Γ} ([Γ] : ⊩ᵛ Γ) (⊢Δ : ⊢ ε)
         ([σ]   : ⊩ˢ σ   ∷ Γ / [Γ] / ⊢Δ)
         ([σ′]  : ⊩ˢ σ′  ∷ Γ / [Γ] / ⊢Δ)
         ([σ″] : ⊩ˢ σ″ ∷ Γ / [Γ] / ⊢Δ)
       → ⊩ˢ σ  ≡ σ′  ∷ Γ / [Γ] / ⊢Δ / [σ]
       → ⊩ˢ σ′ ≡ σ″ ∷ Γ / [Γ] / ⊢Δ / [σ′]
       → ⊩ˢ σ  ≡ σ″ ∷ Γ / [Γ] / ⊢Δ / [σ]
transS ε ⊢Δ [σ] [σ′] [σ″] [σ≡σ′] [σ′≡σ″] = tt
transS ([Γ] ∙ x) ⊢Δ [σ] [σ′] [σ″] [σ≡σ′] [σ′≡σ″] =
  transS [Γ] ⊢Δ (proj₁ [σ]) (proj₁ [σ′]) (proj₁ [σ″])
         (proj₁ [σ≡σ′]) (proj₁ [σ′≡σ″])
  , let [σA]   = proj₁ (x ⊢Δ (proj₁ [σ]))
        [σ′A]  = proj₁ (x ⊢Δ (proj₁ [σ′]))
        [σ″A] = proj₁ (x ⊢Δ (proj₁ [σ″]))
        [σ′≡σ″]′ = convEqTerm₂ [σA] [σ′A]
                                ((proj₂ (x ⊢Δ (proj₁ [σ]))) (proj₁ [σ′])
                                        (proj₁ [σ≡σ′])) (proj₂ [σ′≡σ″])
    in  transEqTerm [σA] (proj₂ [σ≡σ′]) [σ′≡σ″]′
