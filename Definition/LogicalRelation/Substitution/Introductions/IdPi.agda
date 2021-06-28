{-# OPTIONS --allow-unsolved-metas #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.IdPi {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening as T hiding (wk; wkTerm; wkEqTerm)
open import Definition.Typed.RedSteps
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Weakening
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Application
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Substitution.Irrelevance as S
open import Definition.LogicalRelation.Substitution.Reflexivity
open import Definition.LogicalRelation.Substitution.Introductions.Sigma
open import Definition.LogicalRelation.Substitution.Introductions.Fst
open import Definition.LogicalRelation.Substitution.Introductions.Snd
open import Definition.LogicalRelation.Substitution.Introductions.Pi
open import Definition.LogicalRelation.Substitution.Introductions.Lambda
open import Definition.LogicalRelation.Substitution.Introductions.Application
open import Definition.LogicalRelation.Substitution.Introductions.Cast
open import Definition.LogicalRelation.Substitution.Introductions.Id
open import Definition.LogicalRelation.Substitution.Introductions.IdUPiPi
open import Definition.LogicalRelation.Substitution.Introductions.Transp
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Definition.LogicalRelation.Substitution.MaybeEmbed
open import Definition.LogicalRelation.Substitution.Introductions.Universe
open import Definition.LogicalRelation.Substitution.Reduction
open import Definition.LogicalRelation.Substitution.Weakening
open import Definition.LogicalRelation.Substitution.Conversion
open import Definition.LogicalRelation.Substitution.ProofIrrelevance
open import Definition.LogicalRelation.Fundamental.Variable

open import Tools.Product
import Tools.PropositionalEquality as PE

abstract 
  Id-Πᵗᵛ : ∀ {A B rA lA lB l Γ t u} ([Γ] : ⊩ᵛ Γ) 
           → lA ≤ l
           → lB ≤ l →
             let [UA] = maybeEmbᵛ {A = Univ rA _} [Γ] (Uᵛ (proj₂ (levelBounded lA)) [Γ])
             in
             ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ rA , ι lA ] / [Γ])
             ([UB] : Γ ∙ A ^ [ rA , ι lA ] ⊩ᵛ⟨ ∞ ⟩ Univ ! lB ^ [ ! , next lB ] / [Γ] ∙ [A])
             ([A]ₜ : Γ ⊩ᵛ⟨ ∞ ⟩ A ∷ Univ rA lA ^ [ ! , next lA ] / [Γ] / [UA])
             ([B]ₜ : Γ ∙ A ^ [ rA , ι lA ] ⊩ᵛ⟨ ∞ ⟩ B ∷ Univ ! lB ^ [ ! , next lB ] / [Γ] ∙ [A] / (λ {Δ} {σ} → [UB] {Δ} {σ}))
             ([ΠAB] : Γ ⊩ᵛ⟨ ∞ ⟩ Π A ^ rA ° lA ▹ B ° lB ^ [ ! , ι l ] / [Γ])
             ([t]ₜ : Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ Π A ^ rA ° lA ▹ B ° lB ^ [ ! , ι l ] / [Γ] / [ΠAB]) →
             ([u]ₜ : Γ ⊩ᵛ⟨ ∞ ⟩ u ∷ Π A ^ rA ° lA ▹ B ° lB ^ [ ! , ι l ] / [Γ] / [ΠAB]) →
             [ Γ ⊩ᵛ⟨ ∞ ⟩ Id (Π A ^ rA ° lA ▹ B ° lB) t u ≡ Π A ^ rA ° lA ▹ (Id B ((wk1 t) ∘ (var 0)) ((wk1 u) ∘ (var 0))) ° lB ∷ SProp l ^ [ ! , next l ]  / [Γ] ]

  Id-Πᵗᵛ {A} {B} {rA} {lA} {lB} {l} {Γ} {t} {u} [Γ] lA≤ lB≤
            [A] [UB] [A]ₜ [B]ₜ [ΠAB] [t]ₜ [u]ₜ = 
    let [SProp] = maybeEmbᵛ {A = Univ _ _} [Γ] (Uᵛ {rU = %} (proj₂ (levelBounded l)) [Γ]) 
        [UA] = maybeEmbᵛ {A = Univ rA _} [Γ] (Uᵛ (proj₂ (levelBounded lA)) [Γ])
        [ΓA] = _∙_ {A = A} [Γ] [A]
        ⊢AₜΔ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([UA] {Δ} {σ} ⊢Δ [σ])) (proj₁ ([A]ₜ ⊢Δ [σ]))
        [B] = maybeEmbᵛ {A = B} (_∙_ {A = A} [Γ] [A]) (univᵛ {A = B} [ΓA] (≡is≤ PE.refl) (λ {Δ} {σ} → [UB] {Δ} {σ}) [B]ₜ)
        ⊢BΔ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([UB] {Δ} {σ} ⊢Δ [σ])) (proj₁ ([B]ₜ ⊢Δ [σ]))
        ⊢tΔ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([ΠAB] {Δ} {σ} ⊢Δ [σ])) (proj₁ ([t]ₜ ⊢Δ [σ]))
        ⊢uΔ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([ΠAB] {Δ} {σ} ⊢Δ [σ])) (proj₁ ([u]ₜ ⊢Δ [σ]))
        Id-Π-res = λ A B → Π A ^ rA ° lA ▹ (Id B ((wk1 t) ∘ (var 0)) ((wk1 u) ∘ (var 0))) ° lB
        [liftσ] = λ {Δ} {σ} ⊢Δ [σ] → liftSubstS {F = A} [Γ] ⊢Δ [A] [σ] 
        ⊢AΔ = λ {Δ} {σ} ⊢Δ [σ] → escape (proj₁ ([A] ⊢Δ [σ]))
        [SPropB] = maybeEmbᵛ {A = SProp lB} [ΓA] (Uᵛ (proj₂ (levelBounded lB)) [ΓA])
        [wA] = wk1ᵛ {A = A} {F = A} [Γ] [A] [A]
        [wΠ] = wk1ᵛ {A =  Π A ^ rA ° lA ▹ B ° lB} {F = A} [Γ] [A] [ΠAB]
        [wt] = wk1Termᵛ {F = A} {G = Π A ^ rA ° lA ▹ B ° lB} {t = t} [Γ] [A] [ΠAB] [t]ₜ
        [wu] = wk1Termᵛ {F = A} {G = Π A ^ rA ° lA ▹ B ° lB} {t = u} [Γ] [A] [ΠAB] [u]ₜ
        [Id-Π] : Γ ⊩ᵛ Id (Π A ^ rA ° lA ▹ B ° lB) t u ⇒ Id-Π-res A B ∷ SProp l ^ next l / [Γ]
        [Id-Π] = λ {Δ} {σ} ⊢Δ [σ] →
                   PE.subst (λ ret → Δ ⊢ Id (Π (subst σ A) ^ rA ° lA ▹ (subst (liftSubst σ) B) ° lB) (subst σ t) (subst σ u) ⇒ Π subst σ A ^ rA ° lA ▹ ret ° lB ∷ SProp l ^ next l)
                            (PE.cong₂ (λ a b → Id (subst (liftSubst σ) B) (a ∘ (var 0)) (b ∘ (var 0))) (PE.sym (Idsym-subst-lemma σ t)) (PE.sym (Idsym-subst-lemma σ u)))
                            (Id-Π {A = subst σ A} {rA} {lA} {lB} {l} {subst (liftSubst σ) B} {subst σ t} {subst σ u} lA≤ lB≤
                                  (⊢AₜΔ {Δ} {σ} ⊢Δ [σ]) (⊢BΔ (⊢Δ ∙ ⊢AΔ {Δ} {σ} ⊢Δ [σ]) ([liftσ] {Δ} {σ} ⊢Δ [σ])) (⊢tΔ {Δ} {σ} ⊢Δ [σ]) (⊢uΔ {Δ} {σ} ⊢Δ [σ]))
        [Id-Π-res] : Γ ⊩ᵛ⟨ ∞ ⟩ Id-Π-res A B ∷ SProp l ^ [ ! , next l ] / [Γ] / [SProp]
        [Id-Π-res] = Πᵗᵛ {F = A} {G = Id B ((wk1 t) ∘ (var 0)) ((wk1 u) ∘ (var 0))} lA≤ lB≤ [Γ] [A] (λ {Δ} {σ} → [SPropB] {Δ} {σ}) [A]ₜ
                         (Idᵗᵛ {A = B} {t = (wk1 t) ∘ (var 0)} {u = (wk1 u) ∘ (var 0)} [ΓA] [B] (appᵛ [ΓA] [wA] [wΠ] [wt] (proj₂ (fundamentalVar here [ΓA])) ) (appᵛ [ΓA] [wA] [wΠ] [wu] (proj₂ (fundamentalVar here [ΓA]))) ) 
        [id] , [eq] = redSubstTermᵛ {SProp l} {Id (Π A ^ rA ° lA ▹ B ° lB) t u} {Id-Π-res A B}
                                    [Γ] (λ {Δ} {σ} ⊢Δ [σ] → [Id-Π] {Δ} {σ} ⊢Δ [σ]) 
                                    [SProp] [Id-Π-res] 
    in modelsTermEq [SProp] [id] [Id-Π-res] [eq]
