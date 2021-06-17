{-# OPTIONS --allow-unsolved-metas #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.IdUPiPi {{eqrel : EqRelSet}} where
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
open import Definition.LogicalRelation.Substitution.Introductions.Pi
open import Definition.LogicalRelation.Substitution.Introductions.Lambda
open import Definition.LogicalRelation.Substitution.Introductions.Application
open import Definition.LogicalRelation.Substitution.Introductions.Cast
open import Definition.LogicalRelation.Substitution.Introductions.CastPi
open import Definition.LogicalRelation.Substitution.Introductions.Id
open import Definition.LogicalRelation.Substitution.Introductions.Transp
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Definition.LogicalRelation.Substitution.MaybeEmbed
open import Definition.LogicalRelation.Substitution.Escape
open import Definition.LogicalRelation.Substitution.Introductions.Universe
open import Definition.LogicalRelation.Substitution.Reduction
open import Definition.LogicalRelation.Substitution.Weakening
open import Definition.LogicalRelation.Substitution.ProofIrrelevance

open import Tools.Product
import Tools.PropositionalEquality as PE

postulate lemma1 : ∀ {σ rA} A A' B → U.wk (lift (step id)) (subst (liftSubst σ) B) [
                        cast ⁰ (wk1 (wk1 (subst σ A'))) (wk1 (wk1 (subst σ A)))
                             (Idsym (Univ rA ⁰) (wk1 (wk1 (subst σ A))) (wk1 (wk1 (subst σ A')))
                             (var 1)) (var 0)]↑
                   PE.≡
                     subst (liftSubst (liftSubst σ))
                     (U.wk (lift (step id)) B [
                     cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A))
                     (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (var 1)) (var 0)]↑)

postulate lemma2 : ∀ {σ} B → U.wk (lift (step id)) (subst (liftSubst σ) B) PE.≡
                   subst (liftSubst (liftSubst σ)) (U.wk (lift (step id)) B)


Id-U-ΠΠᵗᵛ : ∀ {A B A' B' rA Γ} ([Γ] : ⊩ᵛ Γ) →
        let l    = ∞
            lΠ = ⁰
            [UA] = maybeEmbᵛ {A = Univ rA _} [Γ] (Uᵛ emb< [Γ])
            [UΠ] = maybeEmbᵛ {A = Univ ! _} [Γ] (Uᵛ emb< [Γ])
        in      
           ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ [ rA , ι lΠ ] / [Γ])
           ([A'] : Γ ⊩ᵛ⟨ l ⟩ A' ^ [ rA , ι lΠ ] / [Γ])
           ([UB] : Γ ∙ A ^ [ rA , ι lΠ ] ⊩ᵛ⟨ l ⟩ Univ ! lΠ ^ [ ! , next lΠ ] / [Γ] ∙ [A])
           ([UB'] : Γ ∙ A' ^ [ rA , ι lΠ ] ⊩ᵛ⟨ l ⟩ Univ ! lΠ ^ [ ! , next lΠ ] / [Γ] ∙ [A'])
           ([A]ₜ : Γ ⊩ᵛ⟨ l ⟩ A ∷ Univ rA lΠ ^ [ ! , next lΠ ] / [Γ] / [UA])
           ([B]ₜ : Γ ∙ A ^ [ rA , ι lΠ ] ⊩ᵛ⟨ l ⟩ B ∷ Univ ! lΠ ^ [ ! , next lΠ ] / [Γ] ∙ [A] / (λ {Δ} {σ} → [UB] {Δ} {σ}))
           ([A']ₜ : Γ ⊩ᵛ⟨ l ⟩ A' ∷ Univ rA lΠ ^ [ ! , next lΠ ] / [Γ] / [UA])
           ([B']ₜ :  Γ ∙ A' ^ [ rA , ι lΠ ] ⊩ᵛ⟨ l ⟩ B' ∷ Univ ! lΠ ^ [ ! , next lΠ ] / [Γ] ∙ [A'] / (λ {Δ} {σ} → [UB'] {Δ} {σ})) →
           let [IdAA'] = Idᵛ {A = Univ rA ⁰} {t = A} {u = A'} [Γ] (λ {Δ} {σ} → [UA] {Δ} {σ}) [A]ₜ [A']ₜ
               [ΓId] = _∙_ {A = Id (Univ rA ⁰) A A'} [Γ] [IdAA']
               [wA'] = wk1ᵗᵛ {F = Id (Univ rA ⁰) A A'} {G = A'} {lG = ⁰} [Γ] [IdAA'] [A']ₜ
               [wA']' = wk1ᵛ {A = A'} {F = Id (Univ rA ⁰) A A'} [Γ] [IdAA'] [A']
               [wA]' = wk1ᵛ {A = A} {F = Id (Univ rA ⁰) A A'} [Γ] [IdAA'] [A]
               [wA] = wk1ᵗᵛ {F = Id (Univ rA ⁰) A A'} {G = A} {lG = ⁰} [Γ] [IdAA'] [A]ₜ
               [ΓIdA'] = _∙_ {A = wk1 A'} [ΓId] [wA']'
               [wwA']' = wk1ᵛ {A = wk1 A'} {F = wk1 A'}  [ΓId] [wA']' [wA']'
               [wwA'] = wk1ᵗᵛ {F = wk1 A'} {G = wk1 A'} {lG = ⁰} [ΓId] [wA']' [wA']
               [wwA] = wk1ᵗᵛ {F = wk1 A'} {G = wk1 A} {lG = ⁰} [ΓId] [wA']' [wA]
               [wwUA'] = λ {Δ} {σ} r → maybeEmbᵛ {A = Univ r _ } [ΓIdA'] (λ {Δ} {σ} → Uᵛ emb< [ΓIdA'] {Δ} {σ}) {Δ} {σ}
               [wwIdAA'] = Idᵛ {A = Univ rA ⁰} {t = wk1 (wk1 A)} {u = wk1 (wk1 A')} [ΓIdA'] (λ {Δ} {σ} → [wwUA'] {Δ} {σ} rA) [wwA] [wwA'] 
           in
           ([var0]ₜ : (Γ ∙ Id (Univ rA ⁰) A A' ^ [ % , ι ¹ ] ∙ wk1 A' ^ [ rA , ι ⁰ ]) ⊩ᵛ⟨ ∞ ⟩ var 0 ∷ wk1 (wk1 A') ^ [ rA , ι ⁰ ] / [ΓIdA'] / [wwA']')
           ([var1]ₜ : (Γ ∙ Id (Univ rA ⁰) A A' ^ [ % , ι ¹ ] ∙ wk1 A' ^ [ rA , ι ⁰ ]) ⊩ᵛ⟨ ∞ ⟩ var 1 ∷  Id (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) ^ [ % , ι ¹ ] / [ΓIdA'] / [wwIdAA'])
         → [ Γ ⊩ᵛ⟨ l ⟩ (Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰))
                    ≡ ∃ (Id (Univ rA ⁰) A A') ▹
                      (Π (wk1 A') ^ rA ° ⁰ ▹ Id (U ⁰)
                        ((U.wk (lift (step id)) B) [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (var 1)) (var 0) ]↑)
                        (U.wk (lift (step id)) B') ° ¹)
                  ∷ SProp ¹ ^ [ ! , next ¹ ] / [Γ] ]
Id-U-ΠΠᵗᵛ {A} {B} {A'} {B'} {rA} {Γ} 
        [Γ] [A] [A'] [UB] [UB'] [A]ₜ [B]ₜ [A']ₜ [B']ₜ [var0]ₜ [var1]ₜ =
  let l = ∞
      lΠ = ⁰
      [SProp] = Uᵛ {rU = %} ∞< [Γ]
      [UA] = maybeEmbᵛ {A = Univ rA _} [Γ] (Uᵛ emb< [Γ])
      [UΠ] = maybeEmbᵛ {A = Univ ! _} [Γ] (Uᵛ emb< [Γ])
      ⊢AΔ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([UA] {Δ} {σ} ⊢Δ [σ])) (proj₁ ([A]ₜ ⊢Δ [σ]))
      ⊢A'Δ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([UA] {Δ} {σ} ⊢Δ [σ])) (proj₁ ([A']ₜ ⊢Δ [σ]))
      ⊢A = λ {Δ} {σ} ⊢Δ [σ] → escape (proj₁ ([A] {Δ} {σ} ⊢Δ [σ]))
      ⊢A' = λ {Δ} {σ} ⊢Δ [σ] → escape (proj₁ ([A'] {Δ} {σ} ⊢Δ [σ]))
      [ΓA]  = (_∙_ {Γ} {A} [Γ] [A])
      [ΓA'] = (_∙_ {Γ} {A'} [Γ]  [A'])
      ⊢BΔ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([UB] {Δ} {σ} ⊢Δ [σ])) (proj₁ ([B]ₜ {Δ} {σ} ⊢Δ [σ]))
      [A]'  = univᵛ {A = A} [Γ] (≡is≤ PE.refl) (λ {Δ} {σ} → [UA] {Δ} {σ}) [A]ₜ
      [A']'  = univᵛ {A = A'} [Γ] (≡is≤ PE.refl) (λ {Δ} {σ} → [UA] {Δ} {σ}) [A']ₜ
      [B]'  = univᵛ {A = B} [ΓA] (≡is≤ PE.refl) (λ {Δ} {σ} → [UB] {Δ} {σ}) [B]ₜ
      [B]  = maybeEmbᵛ {A = B} [ΓA] [B]'
      [B']'  = univᵛ {A = B'} [ΓA'] (≡is≤ PE.refl) (λ {Δ} {σ} → [UB'] {Δ} {σ}) [B']ₜ
      [B']  = maybeEmbᵛ {A = B'} [ΓA'] [B']'
      ⊢B'Δ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([UB'] {Δ} {σ} ⊢Δ [σ])) (proj₁ ([B']ₜ {Δ} {σ} ⊢Δ [σ]))
      [liftσ] = λ {Δ} {σ} ⊢Δ [σ] → liftSubstS {F = A} {σ = σ} {Δ = Δ} [Γ] ⊢Δ [A] [σ] 
      [liftσ'] = λ {Δ} {σ} ⊢Δ [σ] → liftSubstS {F = A'} {σ = σ} {Δ = Δ} [Γ] ⊢Δ [A'] [σ]
      [ΠAB] = Πᵗᵛ {A} {B} (≡is≤ PE.refl) (≡is≤ PE.refl) [Γ] [A] (λ {Δ} {σ} → [UB] {Δ} {σ}) [A]ₜ [B]ₜ
      [ΠA'B'] = Πᵗᵛ {A'} {B'} (≡is≤ PE.refl) (≡is≤ PE.refl) [Γ] [A'] (λ {Δ} {σ} → [UB'] {Δ} {σ}) [A']ₜ [B']ₜ
      [IdAA']ₜ = Idᵗᵛ {A = Univ rA ⁰} {t = A} {u = A'} [Γ] (λ {Δ} {σ} → [UA] {Δ} {σ}) [A]ₜ [A']ₜ 
      [IdAA'] = Idᵛ {A = Univ rA ⁰} {t = A} {u = A'} [Γ] (λ {Δ} {σ} → [UA] {Δ} {σ}) [A]ₜ [A']ₜ 
      Id-U-ΠΠ-res A A' B B' = ∃ (Id (Univ rA ⁰) A A') ▹
                      (Π (wk1 A') ^ rA ° ⁰ ▹ Id (U ⁰)
                        ((U.wk (lift (step id)) B) [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (var 1)) (var 0) ]↑)
                        (U.wk (lift (step id)) B') ° ¹)
      [ΓId] = _∙_ {A = Id (Univ rA ⁰) A A'} [Γ] [IdAA']
      [wSProp] = Uᵛ {rU = %} ∞< [ΓId]
      [wA'] = wk1ᵗᵛ {F = Id (Univ rA ⁰) A A'} {G = A'} {lG = ⁰} [Γ] [IdAA'] [A']ₜ
      [wA']' = wk1ᵛ {A = A'} {F = Id (Univ rA ⁰) A A'} [Γ] [IdAA'] [A']
      [wA]' = wk1ᵛ {A = A} {F = Id (Univ rA ⁰) A A'} [Γ] [IdAA'] [A]
      [wA] = wk1ᵗᵛ {F = Id (Univ rA ⁰) A A'} {G = A} {lG = ⁰} [Γ] [IdAA'] [A]ₜ
      [ΓIdA'] = _∙_ {A = wk1 A'} [ΓId] [wA']'
      [wwU¹] = λ {Δ} {σ} r → Uᵛ {rU = r} ∞< [ΓIdA'] {Δ} {σ}
      [wwUA'] = λ {Δ} {σ} r → maybeEmbᵛ {A = Univ r _ } [ΓIdA'] (λ {Δ} {σ} → Uᵛ emb< [ΓIdA'] {Δ} {σ}) {Δ} {σ}
      [wwUA']ᵗ = Uᵗᵛ [ΓIdA'] 
      [ΓIdA] = _∙_ {A = wk1 A} [ΓId] [wA]'
      [wwA'] = wk1ᵗᵛ {F = wk1 A'} {G = wk1 A'} {lG = ⁰} [ΓId] [wA']' [wA']
      [wwA] = wk1ᵗᵛ {F = wk1 A'} {G = wk1 A} {lG = ⁰} [ΓId] [wA']' [wA]
      [wwA']' = wk1ᵛ {A = wk1 A'} {F = wk1 A'}  [ΓId] [wA']' [wA']'
      [wwA]' = wk1ᵛ {A = wk1 A} {F = wk1 A'}  [ΓId] [wA']' [wA]'
      [wwU0A] = maybeEmbᵛ {A = Univ ! _ } [ΓIdA] (λ {Δ} {σ} → Uᵛ emb< [ΓIdA] {Δ} {σ})
      [wB'] = wk1dᵗᵛ {F = A'} {F' = Id (Univ rA ⁰) A A'} {G = B'} [Γ] [A'] [IdAA'] (λ {Δ} {σ} → [UB'] {Δ} {σ}) (λ {Δ} {σ} → [wwUA'] {Δ} {σ} !) [B']ₜ
      [wB] = wk1dᵗᵛ {F = A} {F' = Id (Univ rA ⁰) A A'} {G = B} [Γ] [A] [IdAA'] (λ {Δ} {σ} → [UB] {Δ} {σ}) (λ {Δ} {σ} → [wwU0A] {Δ} {σ}) [B]ₜ
      [wwIdAA'] = Idᵛ {A = Univ rA ⁰} {t = wk1 (wk1 A)} {u = wk1 (wk1 A')} [ΓIdA'] (λ {Δ} {σ} → [wwUA'] {Δ} {σ} rA) [wwA] [wwA'] 
      [wwIdA'A] = Idᵛ {A = Univ rA ⁰} {t = wk1 (wk1 A')} {u = wk1 (wk1 A)} [ΓIdA'] (λ {Δ} {σ} → [wwUA'] {Δ} {σ} rA) [wwA'] [wwA] 
      [Id-U-ΠΠ-res] : Γ ⊩ᵛ⟨ ∞ ⟩ Id-U-ΠΠ-res  A A' B B' ∷ SProp ¹ ^ [ ! , ∞ ] / [Γ] / [SProp]
      [Id-U-ΠΠ-res] = ∃ᵗᵛ {F = Id (Univ rA ⁰) A A'} {G = (Π (wk1 A') ^ rA ° ⁰ ▹ Id (U ⁰)
                        ((U.wk (lift (step id)) B) [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (var 1)) (var 0) ]↑)
                        (U.wk (lift (step id)) B') ° ¹)} [Γ] [IdAA'] (λ {Δ} {σ} → [wSProp] {Δ} {σ}) [IdAA']ₜ
                          (Πᵗᵛ {wk1 A'} {Id (U ⁰) (U.wk (lift (step id)) B [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A))
                                   (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (var 1)) (var 0) ]↑)
                                              (U.wk (lift (step id)) B')} (<is≤ 0<1) (≡is≤ PE.refl) [ΓId] [wA']' (λ {Δ} {σ} → [wwU¹] {Δ} {σ} %) [wA']
                            (Idᵗᵛ {A = U ⁰} {t = (U.wk (lift (step id)) B [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A))
                                      (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (var 1)) (var 0) ]↑)}
                                 {u = U.wk (lift (step id)) B'} [ΓIdA'] (λ {Δ} {σ} → [wwUA'] {Δ} {σ} !)
                            (subst↑STerm {F = wk1 A'} {F' = wk1 A} {G = wk1d B}
                                         {t = cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (var 1)) (var 0)}
                                         [ΓId] [wA']' [wA]' (λ {Δ} {σ} → [wwUA'] {Δ} {σ} !) (λ {Δ} {σ} → [wwU0A] {Δ} {σ}) [wB]
                                         (castᵗᵛ {A = wk1 (wk1 A')} {B = wk1 (wk1 A)} {t = var 0} {e = (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (var 1))}
                                                 [ΓIdA'] (λ {Δ} {σ} → [wwUA'] {Δ} {σ} rA) [wwA'] [wwA] [wwA']' [wwA]' [var0]ₜ
                                                 (Idᵛ {A = Univ rA ⁰} {t = wk1 (wk1 A')} {u = wk1 (wk1 A)} [ΓIdA'] (λ {Δ} {σ} → [wwUA'] {Δ} {σ} rA) [wwA'] [wwA])
                                                 (IdSymᵗᵛ {A = Univ rA ⁰} {t = wk1 (wk1 A)} {u = wk1 (wk1 A')} {e = var 1} [ΓIdA'] ((λ {Δ} {σ} → [wwU¹] {Δ} {σ} !))
                                                          (λ {Δ} {σ} → [wwUA']ᵗ {Δ} {σ}) (λ {Δ} {σ} → [wwUA'] {Δ} {σ} rA)
                                                          [wwA] [wwA'] [wwIdAA'] [wwIdA'A] [var1]ₜ))) [wB'] ))
      [Id-U-ΠΠ] : Γ ⊩ᵛ Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰) ⇒ Id-U-ΠΠ-res A A' B B' ∷ SProp ¹ ^ ∞  / [Γ]
      [Id-U-ΠΠ] = λ {Δ} {σ} ⊢Δ [σ] → let Aσ  = ⊢AΔ {Δ} {σ} ⊢Δ [σ]
                                         Bσ = ⊢BΔ {Δ ∙ subst σ A ^ _} {liftSubst σ} (⊢Δ ∙ ⊢A {Δ} {σ} ⊢Δ [σ]) ([liftσ] {Δ} {σ} ⊢Δ [σ])
                                         A'σ = ⊢A'Δ {Δ} {σ} ⊢Δ [σ]
                                         B'σ = ⊢B'Δ {Δ ∙ subst σ A' ^ _} {liftSubst σ} (⊢Δ ∙ ⊢A' {Δ} {σ} ⊢Δ [σ]) ([liftσ'] {Δ} {σ} ⊢Δ [σ])
                                         X : Δ ⊢ Id (U ⁰) (Π (subst σ A) ^ rA ° ⁰ ▹ (subst (liftSubst σ) B) ° ⁰) (Π (subst σ A') ^ rA ° ⁰ ▹ (subst (liftSubst σ) B') ° ⁰)
                                                  ⇒ Id-U-ΠΠ-res (subst σ A) (subst σ A') (subst (liftSubst σ) B) (subst (liftSubst σ) B') 
                                                  ∷ SProp ¹ ^ ∞
                                         X = Id-U-ΠΠ {Δ} {subst σ A} {subst σ A'} {rA} {subst (liftSubst σ) B} {subst (liftSubst σ) B'} Aσ Bσ A'σ B'σ
                                     in  PE.subst (λ BB → Δ ⊢ Id (U ⁰) (Π (subst σ A) ^ rA ° ⁰ ▹ (subst (liftSubst σ) B) ° ⁰) (Π (subst σ A') ^ rA ° ⁰ ▹ (subst (liftSubst σ) B') ° ⁰)
                                                                  ⇒ BB  ∷ SProp ¹ ^ ∞ )
                                                 (PE.cong₃ (λ X Y Z → ∃ Id (Univ rA ⁰) (subst σ A) (subst σ A') ▹ Π X ^ rA ° ⁰ ▹ Id (U ⁰) Y Z ° ¹)
                                                           ((PE.sym (Idsym-subst-lemma σ A'))) (lemma1 A A' B) (lemma2 B'))  X
      [id] , [eq] = redSubstTermᵛ {SProp ¹} {Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰)} {Id-U-ΠΠ-res A A' B B'}
                                  [Γ] [Id-U-ΠΠ]
                                  (λ {Δ} {σ} → [SProp] {Δ} {σ}) [Id-U-ΠΠ-res]
  in modelsTermEq [SProp] [id] [Id-U-ΠΠ-res] [eq]
