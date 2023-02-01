{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Fst {{eqrel : EqRelSet}} where
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
open import Definition.LogicalRelation.Substitution.Reflexivity
open import Definition.LogicalRelation.Substitution.Introductions.Id
open import Definition.LogicalRelation.Substitution.Introductions.Pi
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Definition.LogicalRelation.Substitution.MaybeEmbed
open import Definition.LogicalRelation.Substitution.Introductions.Universe

open import Tools.Product
import Tools.PropositionalEquality as PE

-- Valid fst term construction.
fstᵛ : ∀ {A B A' B' e rA Γ}
       ([Γ] : ⊩ᵛ Γ) →
        let l    = ∞
            lΠ = ⁰
            [UA] = maybeEmbᵛ {A = Univ rA _} [Γ] (Uᵛ emb< [Γ])
        in
           ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ [ rA , ι lΠ ] / [Γ])
           ([A'] : Γ ⊩ᵛ⟨ l ⟩ A' ^ [ rA , ι lΠ ] / [Γ])
           ([UB] : Γ ∙ A ^ [ rA , ι lΠ ] ⊩ᵛ⟨ l ⟩ Univ ! lΠ ^ [ ! , next lΠ ] / [Γ] ∙ [A])
           ([UB'] : Γ ∙ A' ^ [ rA , ι lΠ ] ⊩ᵛ⟨ l ⟩ Univ ! lΠ ^ [ ! , next lΠ ] / [Γ] ∙ [A'])
           ([A]ₜ : Γ ⊩ᵛ⟨ l ⟩ A ∷ Univ rA lΠ ^ [ ! , next lΠ ] / [Γ] / [UA])
           ([B]ₜ : Γ ∙ A ^ [ rA , ι lΠ ] ⊩ᵛ⟨ l ⟩ B ∷ Univ ! lΠ ^ [ ! , next lΠ ] / [Γ] ∙ [A] / (λ {Δ} {σ} → [UB] {Δ} {σ}))
           ([A']ₜ : Γ ⊩ᵛ⟨ l ⟩ A' ∷ Univ rA lΠ ^ [ ! , next lΠ ] / [Γ] / [UA])
           ([B']ₜ :  Γ ∙ A' ^ [ rA , ι lΠ ] ⊩ᵛ⟨ l ⟩ B' ∷ Univ ! lΠ ^ [ ! , next lΠ ] / [Γ] ∙ [A'] / (λ {Δ} {σ} → [UB'] {Δ} {σ})) →
           ([Id] : Γ ⊩ᵛ⟨ l ⟩ Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ !) ^ [ % , ι ⁰ ] / [Γ])
           ([e]ₜ :  Γ ⊩ᵛ⟨ l ⟩ e ∷ Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ !) ^ [ % , ι ⁰ ] / [Γ] / [Id])
       →   let [IdAA'] = Idᵛ {A = Univ rA ⁰} {t = A} {u = A'} [Γ] (λ {Δ} {σ} → [UA] {Δ} {σ}) [A]ₜ [A']ₜ 
           in Γ ⊩ᵛ⟨ l ⟩ fst e ∷ Id (Univ rA ⁰) A A'  ^ [ % , ι ⁰ ] / [Γ] / [IdAA']

fstᵛ  {A} {B} {A'} {B'} {e} {rA} {Γ}
      [Γ] [A] [A'] [UB] [UB'] [A]ₜ [B]ₜ [A']ₜ [B']ₜ [Id] [e]ₜ {Δ = Δ} {σ = σ} ⊢Δ [σ] =
      let [UA] = maybeEmbᵛ {A = Univ rA _} [Γ] (Uᵛ emb< [Γ])
          [σUA] = proj₁ ([UA] ⊢Δ [σ])
          [σA] = proj₁ ([A] ⊢Δ [σ])
          ⊢A = escape [σA]
          [σA]ₜ = proj₁ ([A]ₜ ⊢Δ [σ])
          ⊢Aₜ = escapeTerm [σUA] [σA]ₜ
          [σA'] = proj₁ ([A'] ⊢Δ [σ])
          ⊢A' = escape [σA']
          [σA']ₜ = proj₁ ([A']ₜ ⊢Δ [σ])
          ⊢A'ₜ = escapeTerm [σUA] [σA']ₜ
          [σUB] = proj₁ ([UB] {σ = liftSubst σ} (⊢Δ ∙ ⊢A)
                        (liftSubstS {F = A} [Γ] ⊢Δ [A] [σ]))
          [σB]ₜ = proj₁ ([B]ₜ (⊢Δ ∙ ⊢A)
                        (liftSubstS {F = A} [Γ] ⊢Δ [A] [σ]))
          ⊢Bₜ = escapeTerm [σUB] [σB]ₜ
          [σUB'] = proj₁ ([UB'] {σ = liftSubst σ} (⊢Δ ∙ ⊢A')
                        (liftSubstS {F = A'} [Γ] ⊢Δ [A'] [σ]))
          [σB']ₜ = proj₁ ([B']ₜ (⊢Δ ∙ ⊢A')
                        (liftSubstS {F = A'} [Γ] ⊢Δ [A'] [σ]))
          ⊢B'ₜ = escapeTerm [σUB'] [σB']ₜ
          [IdAA'] = Idᵛ {A = Univ rA ⁰} {t = A} {u = A'} [Γ] (λ {Δ} {σ} → [UA] {Δ} {σ}) [A]ₜ [A']ₜ
          [σIdAA'] = proj₁ ([IdAA'] ⊢Δ [σ])
          [σId] = proj₁ ([Id] ⊢Δ [σ])
          [σe] = proj₁ ([e]ₜ (⊢Δ) [σ])
          ⊢e = escapeTerm [σId] [σe]
          ⊢fst = fstⱼ {A = subst σ A} {A' = subst σ A'} {B = subst (liftSubst σ) B} {B' = subst (liftSubst σ) B'} {e = subst σ e}
                      ⊢Aₜ ⊢Bₜ ⊢A'ₜ ⊢B'ₜ ⊢e
      in logRelIrr [σIdAA'] ⊢fst ,
         λ {σ′} [σ]′ [σ≡σ′] → logRelIrrEq [σIdAA'] ⊢fst
      let [σUA]′ = proj₁ ([UA] ⊢Δ [σ]′)
          [σA]′ = proj₁ ([A] ⊢Δ [σ]′)
          ⊢A′ = escape [σA]′
          [σA]ₜ′ = proj₁ ([A]ₜ ⊢Δ [σ]′)
          ⊢Aₜ′ = escapeTerm [σUA] [σA]ₜ′
          [σA']′ = proj₁ ([A'] ⊢Δ [σ]′)
          ⊢A'′ = escape [σA']′
          [σA']ₜ′ = proj₁ ([A']ₜ ⊢Δ [σ]′)
          ⊢A'ₜ′ = escapeTerm [σUA] [σA']ₜ′
          [σUB]′ = proj₁ ([UB] {σ = liftSubst σ′} (⊢Δ ∙ ⊢A′)
                        (liftSubstS {F = A} [Γ] ⊢Δ [A] [σ]′))
          [σB]ₜ′ = proj₁ ([B]ₜ (⊢Δ ∙ ⊢A′)
                        (liftSubstS {F = A} [Γ] ⊢Δ [A] [σ]′))
          ⊢Bₜ′ = escapeTerm [σUB]′ [σB]ₜ′
          [σUB']′ = proj₁ ([UB'] {σ = liftSubst σ′} (⊢Δ ∙ ⊢A'′)
                        (liftSubstS {F = A'} [Γ] ⊢Δ [A'] [σ]′))
          [σB']ₜ′ = proj₁ ([B']ₜ (⊢Δ ∙ ⊢A'′)
                        (liftSubstS {F = A'} [Γ] ⊢Δ [A'] [σ]′))
          ⊢B'ₜ′ = escapeTerm [σUB']′ [σB']ₜ′
          [σIdAA']′ = proj₁ ([IdAA'] ⊢Δ [σ]′)
          [σId]′ = proj₁ ([Id] ⊢Δ [σ]′)
          [σe]′ = proj₁ ([e]ₜ (⊢Δ) [σ]′)
          ⊢e′ = escapeTerm [σId]′ [σe]′
          ⊢fst′ = fstⱼ {A = subst σ′ A} {A' = subst σ′ A'} {B = subst (liftSubst σ′) B} {B' = subst (liftSubst σ′) B'} {e = subst σ′ e}
                      ⊢Aₜ′ ⊢Bₜ′ ⊢A'ₜ′ ⊢B'ₜ′ ⊢e′
          [σA≡σA′] = proj₂ ([A] ⊢Δ [σ]) [σ]′ [σ≡σ′]
          ⊢σA≡σA′ = ≅-un-univ (escapeEq [σA] [σA≡σA′])
          [σA≡σA'′] = proj₂ ([A'] ⊢Δ [σ]) [σ]′ [σ≡σ′]
          ⊢σA≡σA'′ = ≅-un-univ (escapeEq [σA'] [σA≡σA'′])
      in conv ⊢fst′ (univ (Id-cong (refl (un-univ (Ugenⱼ ⊢Δ))) (≅ₜ-eq (≅ₜ-sym ⊢σA≡σA′)) (≅ₜ-eq (≅ₜ-sym ⊢σA≡σA'′))))
