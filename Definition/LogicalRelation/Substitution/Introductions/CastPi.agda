{-# OPTIONS --allow-unsolved-metas #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.CastPi {{eqrel : EqRelSet}} where
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
open import Definition.LogicalRelation.Substitution.Introductions.Id
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Definition.LogicalRelation.Substitution.MaybeEmbed
open import Definition.LogicalRelation.Substitution.Introductions.Universe
open import Definition.LogicalRelation.Substitution.Reduction
open import Definition.LogicalRelation.Substitution.Weakening
open import Definition.LogicalRelation.Substitution.ProofIrrelevance

open import Tools.Product
import Tools.PropositionalEquality as PE

postulate wk1f-cast-subst : ∀ σ f A' A rA e →
                              (wk1 (subst σ f) ∘ cast ⁰ (wk1 (subst σ A')) (wk1 (subst σ A)) (Idsym (Univ rA ⁰) (wk1 (subst σ A)) (wk1 (subst σ A')) (fst (wk1 (subst σ e)))) (var 0))
                              PE.≡
                              subst (repeat liftSubst (repeat liftSubst σ 1) 0) (wk1 f ∘ cast ⁰ (wk1 A') (wk1 A) (Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0))

postulate B-cast-subst : ∀ σ A' A rA e B →
                         subst (liftSubst σ) B [ cast ⁰ (wk1 (subst σ A')) (wk1 (subst σ A)) (Idsym (Univ rA ⁰) (wk1 (subst σ A)) (wk1 (subst σ A')) (fst (wk1 (subst σ e)))) (var 0) ]↑
                         PE.≡
                         subst (repeat liftSubst (repeat liftSubst σ 1) 0) (B [ cast ⁰ (wk1 A') (wk1 A) (Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) ]↑)

postulate Beq : ∀ ρ σ a B → subst (sgSubst a ₛ• lift ρ ₛ•ₛ liftSubst σ) B PE.≡
                            U.wk (lift ρ) B [ a ]

postulate hardcore : ∀ {σ rA} A A' B →  wk1d (wk1d B) [ cast ⁰ (U.wk (step (step id)) (subst σ (wk1 A')))
                                            (U.wk (step (step id)) (subst σ (wk1 A)))
                                            (Idsym (Univ rA ⁰) (U.wk (step (step id)) (subst σ (wk1 A)))
                                            (U.wk (step (step id)) (subst σ (wk1 A'))) (var 1)) (var 0) ]↑
                                       PE.≡
                                       U.wk (lift (step id))
                                       (subst (repeat liftSubst (repeat liftSubst σ 0) 1)
                                       (U.wk (repeat lift (repeat lift (step id) 0) 1) B))
                                       [ cast ⁰ (wk1 (wk1 (subst (repeat liftSubst (repeat liftSubst σ 0) 0)
                                       (U.wk (repeat lift (repeat lift (step id) 0) 0) A'))))
                                       (wk1 (wk1 (subst (repeat liftSubst (repeat liftSubst σ 0) 0) (U.wk (repeat lift (repeat lift (step id) 0) 0) A))))
                                       (Idsym (Univ rA ⁰)
                                              (wk1 (wk1 (subst (repeat liftSubst (repeat liftSubst σ 0) 0) (U.wk (repeat lift (repeat lift (step id) 0) 0) A))))
                                              (wk1 (wk1 (subst (repeat liftSubst (repeat liftSubst σ 0) 0)(U.wk (repeat lift (repeat lift (step id) 0) 0) A'))))
                                              (var 1))
                                              (var 0)]↑
postulate hardcore2 : ∀ {σ} B' → wk1d (subst (liftSubst σ) (wk1d B')) PE.≡
                                        U.wk (lift (step id)) (subst (repeat liftSubst (repeat liftSubst σ 0) 1)
                                                                     (U.wk (repeat lift (repeat lift (step id) 0) 1) B'))


cast-Πᵗᵛ : ∀ {A B A' B' rA Γ e f} ([Γ] : ⊩ᵛ Γ) →
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
           ([B']ₜ :  Γ ∙ A' ^ [ rA , ι lΠ ] ⊩ᵛ⟨ l ⟩ B' ∷ Univ ! lΠ ^ [ ! , next lΠ ] / [Γ] ∙ [A'] / (λ {Δ} {σ} → [UB'] {Δ} {σ}))
           ([Id] : Γ ⊩ᵛ⟨ l ⟩ Id (U lΠ) (Π A ^ rA ° lΠ ▹ B ° lΠ) (Π A' ^ rA ° lΠ  ▹ B' ° lΠ) ^ [ % , next lΠ ] / [Γ])
           ([e]ₜ : Γ ⊩ᵛ⟨ l ⟩ e ∷ Id (U lΠ) (Π A ^ rA ° lΠ ▹ B ° lΠ) (Π A' ^ rA ° lΠ  ▹ B' ° lΠ) ^ [ % , next lΠ ] / [Γ] / [Id])
           ([ΠAB] : Γ ⊩ᵛ⟨ l ⟩ Π A ^ rA ° lΠ ▹ B ° lΠ ^ [ ! , ι lΠ ] / [Γ])
           ([f]ₜ : Γ ⊩ᵛ⟨ l ⟩ f ∷ Π A ^ rA ° lΠ ▹ B ° lΠ ^ [ ! , ι lΠ ] / [Γ] / [ΠAB]) →
           let [ΓA'] = (_∙_ {Γ} {A'} [Γ]  [A']) 
           in ([var]ₜ : Γ ∙ A' ^ [ rA , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ var 0 ∷ wk1 A' ^ [ rA , ι ⁰ ] / [ΓA'] / wk1ᵛ {A = A'} {F = A'} [Γ] [A'] [A'])
         → [ Γ ⊩ᵛ⟨ l ⟩ (cast lΠ (Π A ^ rA ° lΠ ▹ B ° lΠ) (Π A' ^ rA ° lΠ ▹ B' ° lΠ) e f) ≡
                       (lam A' ▹
                         let a = cast lΠ (wk1 A') (wk1 A) (Idsym (Univ rA lΠ) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) in
                         cast lΠ (B [ a ]↑) B' ((snd (wk1 e)) ∘ (var 0)) ((wk1 f) ∘ a))
                       ∷ Π A' ^ rA ° lΠ ▹ B' ° lΠ ^ [ ! , ι lΠ ] / [Γ] ]
cast-Πᵗᵛ {A} {B} {A'} {B'} {rA} {Γ} {e} {f}
        [Γ] [A] [A'] [UB] [UB'] [A]ₜ [B]ₜ [A']ₜ [B']ₜ [Id] [e]ₜ [ΠAB] [f]ₜ [var]ₜ =
  let l = ∞
      lΠ = ⁰
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
      ⊢e = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([Id] {Δ} {σ} ⊢Δ [σ])) (proj₁ ([e]ₜ {Δ} {σ} ⊢Δ [σ]))
      ⊢f = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([ΠAB] {Δ} {σ} ⊢Δ [σ])) (proj₁ ([f]ₜ {Δ} {σ} ⊢Δ [σ]))
      [ΠAB'] = Πᵛ {A'} {B'} (≡is≤ PE.refl) (≡is≤ PE.refl) [Γ] [A'] [B']
      [ΓA'] = _∙_ {A = A'} [Γ]  [A']
      [wUA] = maybeEmbᵛ {A = Univ rA _} [ΓA'] (λ {Δ} {σ} → Uᵛ emb< [ΓA'] {Δ} {σ})
      [wA] = wk1ᵗᵛ {F = A'} {G = A} {lG = ⁰} [Γ] [A'] [A]ₜ
      [wA]' = wk1ᵛ {A = A} {F = A'} [Γ] [A'] [A]
      [wA]⁰ = wk1ᵛ {A = A} {F = A'} [Γ] [A'] [A]'
      [wA'] = wk1ᵗᵛ {F = A'} {G = A'} {lG = ⁰} [Γ] [A'] [A']ₜ
      [wA']' = wk1ᵛ {A = A'} {F = A'} [Γ] [A'] [A']
      [wA']⁰ = wk1ᵛ {A = A'} {F = A'} [Γ] [A'] [A']'
      [wId] = wk1ᵛ {A = Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰ )} {F = A'} [Γ] [A'] [Id]
      [wIdAA'] : Γ ∙ A' ^ [ rA , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ Id (Univ rA ⁰) (wk1 A') (wk1 A) ^ [ % , ι ¹ ] / [ΓA']
      [wIdAA'] = Idᵛ {A = Univ rA ⁰} {t = wk1 A'} {u = wk1 A} [ΓA'] (λ {Δ} {σ} → [wUA] {Δ} {σ}) [wA'] [wA] 
      [SProp] = maybeEmbᵛ {A = Univ % _} [ΓA'] (λ {Δ} {σ} → Uᵛ ∞< [ΓA'] {Δ} {σ})
      [wIdAA']ₜ = Idᵗᵛ {A = Univ rA ⁰} {t = wk1 A} {u = wk1 A'} [ΓA'] (λ {Δ} {σ} → [wUA] {Δ} {σ}) [wA] [wA'] 
      [we] = wk1Termᵛ {F = A'} {G = Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰ )} {t = e} [Γ] [A'] [Id] [e]ₜ
      [wUB] = wk1dᵛ {F = A} {F' = A'} {G = U _} [Γ] [A] [A'] (λ {Δ} {σ} → [UB] {Δ} {σ})
      [wB] = wk1dᵗᵛ {F = A} {F' = A'} {G = B} [Γ] [A] [A'] (λ {Δ} {σ} → [UB] {Δ} {σ}) (λ {Δ} {σ} → [wUB] {Δ} {σ}) [B]ₜ
      [wB]' = wk1dᵛ {F = A} {F' = A'} {G = B} [Γ] [A] [A'] [B]
      [wB]⁰ = wk1dᵛ {F = A} {F' = A'} {G = B} [Γ] [A] [A'] [B]'
      [wUB'] = wk1dᵛ {F = A'} {F' = A'} {G = U _} [Γ] [A'] [A'] (λ {Δ} {σ} → [UB'] {Δ} {σ})
      [wB'] = wk1dᵗᵛ {F = A'} {F' = A'} {G = B'} [Γ] [A'] [A'] (λ {Δ} {σ} → [UB'] {Δ} {σ}) (λ {Δ} {σ} → [wUB'] {Δ} {σ}) [B']ₜ
      [wB']' = wk1dᵛ {F = A'} {F' = A'} {G = B'} [Γ] [A'] [A'] [B']
      [wfste] : Γ ∙ A' ^ [ rA , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e)) ∷ Id (Univ rA ⁰) (wk1 A') (wk1 A) ^ [ % , ι ¹ ] / [ΓA'] / [wIdAA']
      [wfste] = validityIrr {A = Id (Univ rA ⁰) (wk1 A') (wk1 A)} {t = Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))} [ΓA'] [wIdAA']
                λ {Δ} {σ} ⊢Δ [σ] → let ⊢wAₜ  = escapeTerm (proj₁ ([wUA] {Δ} {σ} ⊢Δ [σ])) (proj₁ ([wA] ⊢Δ [σ]))
                                       ⊢wA'ₜ = escapeTerm (proj₁ ([wUA] {Δ} {σ} ⊢Δ [σ])) (proj₁ ([wA'] ⊢Δ [σ]))
                                       ⊢wA   = escape (proj₁ ([wA]' ⊢Δ [σ]))
                                       ⊢wA'   = escape (proj₁ ([wA']' ⊢Δ [σ]))
                                       ⊢wB   = escape (proj₁ ([wB]' {Δ ∙ subst σ (U.wk (step id) A) ^ [ rA , ι ⁰ ]} {liftSubst σ}
                                                                    (⊢Δ ∙ ⊢wA) (liftSubstS {F = wk1 A} [ΓA'] ⊢Δ [wA]' [σ])))
                                       ⊢wB'   = escape (proj₁ ([wB']' {Δ ∙ subst σ (U.wk (step id) A') ^ [ rA , ι ⁰ ]} {liftSubst σ}
                                                                    (⊢Δ ∙ ⊢wA') (liftSubstS {F = wk1 A'} [ΓA'] ⊢Δ [wA']' [σ])))
                                       [wAρ] = λ {ρ} {Δ₁} [ρ] ⊢Δ₁ → irrelevance′ (PE.sym (wk-subst (wk1 A)))
                                                                     (proj₁ ([wA]⁰ {Δ₁} {ρ •ₛ σ} ⊢Δ₁ (wkSubstS {ρ = ρ} {σ = σ} [ΓA'] ⊢Δ ⊢Δ₁ [ρ] [σ])))
                                       ⊢sndId-U-ΠΠ = snd-Id-U-ΠΠⱼ {G = wk1d B} ⊢Δ ⊢wA [wAρ]                                                                 
                                                                  (λ {ρ} {Δ₁} {a} [ρ] ⊢Δ₁ [a] → irrelevance′ (PE.trans (PE.sym (cons-wk-subst ρ σ a (wk1d B)))
                                                                                                                       (Beq ρ σ a (wk1d B)))
                                                                    (proj₁ ([wB]⁰ {Δ₁} {consSubst (ρ •ₛ σ) a} ⊢Δ₁
                                                                      (let X = consSubstS {t = a} {A = wk1 A} [ΓA'] ⊢Δ₁
                                                                               (wkSubstS {ρ = ρ} {σ = σ} [ΓA'] ⊢Δ ⊢Δ₁ [ρ] [σ]) [wA]⁰
                                                                                 (irrelevanceTerm″ (wk-subst (wk1 A)) PE.refl PE.refl PE.refl ([wAρ] {ρ} {Δ₁} [ρ] ⊢Δ₁)
                                                                                                   (proj₁ ([wA]⁰ ⊢Δ₁ (wkSubstS {ρ = ρ} {σ = σ} [ΓA'] ⊢Δ ⊢Δ₁ [ρ] [σ]))) [a])
                                                                       in irrelevanceSubst {consSubst (ρ •ₛ σ) a}
                                                                                           (_∙_ {A = wk1 A} [ΓA'] [wA]⁰) (_∙_ {A = wk1 A} [ΓA'] [wA]')
                                                                                           ⊢Δ₁ ⊢Δ₁ X))))
                                                                  ⊢wA' ⊢wB'
                                                                  (λ {ρ} {Δ₁} [ρ] ⊢Δ₁ → irrelevance′ (PE.sym (wk-subst (wk1 A')))
                                                                     (proj₁ ([wA']⁰ {Δ₁} {ρ •ₛ σ} ⊢Δ₁ (wkSubstS {ρ = ρ} {σ = σ} [ΓA'] ⊢Δ ⊢Δ₁ [ρ] [σ]))))
                                   in PE.subst (λ X → Δ ⊢ X ∷ subst σ (Id (Univ rA ⁰) (wk1 A') (wk1 A)) ^ [ % , ι ¹ ] ) (PE.sym (subst-Idsym σ (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))))
                                            (Idsymⱼ (univ 0<1 ⊢Δ)
                                                    ⊢wAₜ ⊢wA'ₜ                                                    
                                                    (fstⱼ (escapeTerm (proj₁ ([SProp] {Δ} {σ} ⊢Δ [σ])) (proj₁ ([wIdAA']ₜ {Δ} {σ} ⊢Δ [σ])))
                                                          (let X = (un-univ ⊢sndId-U-ΠΠ) in PE.subst (λ X → Δ ∙ Id (Univ rA ⁰) (subst σ (wk1 A)) (subst σ (wk1 A')) ^ [ % , ι ¹ ] ⊢
                                                            Π wk1 (subst σ (wk1 A')) ^ rA ° ⁰ ▹ X ° ¹ ∷ SProp ¹ ^ [ ! , ∞ ]) (PE.cong₂ (λ X Y → Id (U ⁰) X Y) (hardcore A A' B) (hardcore2 B') ) X)
                                                          (conv (escapeTerm ((proj₁ ([wId] {Δ} {σ} ⊢Δ [σ]))) (proj₁ ([we] ⊢Δ [σ])))
                                                                (univ (Id-U-ΠΠ ⊢wAₜ
                                                                               (let X = proj₁ ([wB] {Δ ∙ subst σ (U.wk (step id) A) ^ [ rA , ι ⁰ ]} {liftSubst σ}
                                                                                                    (⊢Δ ∙ ⊢wA) (liftSubstS {F = wk1 A} [ΓA'] ⊢Δ [wA]' [σ]))
                                                                                    Y = proj₁ ([wUB] {Δ ∙ subst σ (U.wk (step id) A) ^ [ rA , ι ⁰ ]} {liftSubst σ}
                                                                                                    (⊢Δ ∙ ⊢wA) (liftSubstS {F = wk1 A} [ΓA'] ⊢Δ [wA]' [σ]))
                                                                                in escapeTerm Y X)
                                                                               ⊢wA'ₜ
                                                                               (let X = proj₁ ([wB'] {Δ ∙ subst σ (U.wk (step id) A') ^ [ rA , ι ⁰ ]} {liftSubst σ}
                                                                                                    (⊢Δ ∙ ⊢wA') (liftSubstS {F = wk1 A'} [ΓA'] ⊢Δ [wA']' [σ]))
                                                                                    Y = proj₁ ([wUB'] {Δ ∙ subst σ (U.wk (step id) A') ^ [ rA , ι ⁰ ]} {liftSubst σ}
                                                                                                    (⊢Δ ∙ ⊢wA') (liftSubstS {F = wk1 A'} [ΓA'] ⊢Δ [wA']' [σ]))
                                                                                in escapeTerm Y X))))))
      cast-Π-a A A' e = cast ⁰ (wk1 A') (wk1 A) (Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0)
      [cast-Π-a] : Γ ∙ A' ^ [ rA , ι ⁰ ]  ⊩ᵛ⟨ ∞ ⟩ cast-Π-a A A' e ∷ wk1 A ^ [ rA , ι ⁰ ] / [ΓA'] / wk1ᵛ {A = A} {F = A'} [Γ] [A'] [A]
      [cast-Π-a] = castᵗᵛ {wk1 A'} {wk1 A} {t = var 0} {e = Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))} [ΓA']
                          (λ {Δ} {σ} → [wUA] {Δ} {σ}) [wA'] [wA] 
                         (wk1ᵛ {A = A'} {F = A'} [Γ] [A'] [A'])   (wk1ᵛ {A = A} {F = A'} [Γ] [A'] [A])
                         [var]ₜ [wIdAA'] [wfste]
      B[cast-Π-a]↑ₜ = subst↑STerm {F = A'} {F' = A} {G = B} {t = cast-Π-a A A' e} [Γ] [A'] [A]
                                  (λ {Δ} {σ} → [UB'] {Δ} {σ}) (λ {Δ} {σ} → [UB] {Δ} {σ}) [B]ₜ [cast-Π-a]
      [f°cast-Π-a] = appᵛ↑ {F = A} {F' = A'} {G = B} {t = wk1 f} {u = cast-Π-a A A' e} (≡is≤ PE.refl) (≡is≤ PE.refl) [Γ] [A] [A'] [B] [ΠAB]
                          (wk1Termᵛ {F = A'} {G =  Π A ^ rA ° ⁰ ▹ B ° ⁰} {t = f} [Γ] [A'] [ΠAB] [f]ₜ)
                          [cast-Π-a]
      [wIdBB'] : Γ ∙ A' ^ [ rA , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ Id (Univ ! ⁰) (B [ cast-Π-a A A' e ]↑) B' ^ [ % , ι ¹ ] / [ΓA']
      [wIdBB'] = Idᵛ {A = Univ ! ⁰} {t = B [ cast-Π-a A A' e ]↑} {u = B'} [ΓA'] (λ {Δ} {σ} → [UB'] {Δ} {σ})
                     B[cast-Π-a]↑ₜ [B']ₜ 
      [wsnde] : Γ ∙ A' ^ [ rA , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ (snd (wk1 e)) ∘ (var 0) ∷ Id (Univ ! ⁰) (B [ cast-Π-a A A' e ]↑) B' ^ [ % , ι ¹ ] / [ΓA'] / [wIdBB']
      [wsnde] = {!!}
      cast-Π-res A A' B B' e f = 
                 cast ⁰ (B [ cast-Π-a A A' e ]↑) B' ((snd (wk1 e)) ∘ (var 0)) ((wk1 f) ∘ cast-Π-a A A' e)
      [cast-Π-res] : Γ ⊩ᵛ⟨ ∞ ⟩ lam A' ▹ cast-Π-res A A' B B' e f ∷ Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ^ [ ! , ι ⁰ ] / [Γ] / [ΠAB']
      [cast-Π-res] = lamᵛ {F = A'} {G = B'} {t = cast-Π-res A A' B B' e f} (≡is≤ PE.refl) (≡is≤ PE.refl) [Γ] [A'] [B']
                          (castᵗᵛ {B [ cast-Π-a A A' e ]↑} {B'} {t = (wk1 f) ∘ cast-Π-a A A' e} {e = (snd (wk1 e)) ∘ (var 0)}
                                  [ΓA'] (λ {Δ} {σ} → [UB'] {Δ} {σ}) B[cast-Π-a]↑ₜ [B']ₜ (subst↑S {F = A'} {G = B} {F' = A} [Γ] [A'] [A] [B] [cast-Π-a]) [B']
                                  [f°cast-Π-a] [wIdBB'] [wsnde])
      [cast-Π] : Γ ⊩ᵛ cast ⁰ (Π A ^ rA ° ⁰ ▹ B ° ⁰) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰) e f ⇒ lam A' ▹ cast-Π-res A A' B B' e f ∷ Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ^ ι ⁰ / [Γ]
      [cast-Π] = λ {Δ} {σ} ⊢Δ [σ] → let Aσ  = ⊢AΔ {Δ} {σ} ⊢Δ [σ]
                                        Bσ  = ⊢BΔ {Δ ∙ subst σ A ^ _} {liftSubst σ} (⊢Δ ∙ ⊢A {Δ} {σ} ⊢Δ [σ]) ([liftσ] {Δ} {σ} ⊢Δ [σ])
                                        A'σ = ⊢A'Δ {Δ} {σ} ⊢Δ [σ]
                                        B'σ = ⊢B'Δ {Δ ∙ subst σ A' ^ _} {liftSubst σ} (⊢Δ ∙ ⊢A' {Δ} {σ} ⊢Δ [σ]) ([liftσ'] {Δ} {σ} ⊢Δ [σ])
                                        eσ  = ⊢e {Δ} {σ} ⊢Δ [σ]
                                        fσ  = ⊢f {Δ} {σ} ⊢Δ [σ]
                                        X : Δ ⊢ (cast ⁰ (Π (subst σ A) ^ rA ° ⁰ ▹ (subst (liftSubst σ) B) ° ⁰) (Π (subst σ A') ^ rA ° ⁰ ▹ (subst (liftSubst σ) B') ° ⁰) (subst σ e) (subst σ f))
                                                  ⇒ lam (subst σ A') ▹ cast-Π-res (subst σ A) (subst σ A') (subst (liftSubst σ) B) (subst (liftSubst σ) B') (subst σ e) (subst σ f)
                                                  ∷ Π (subst σ A') ^ rA ° ⁰ ▹ (subst (liftSubst σ) B') ° ⁰ ^ ι ⁰
                                        X = cast-Π {Δ} {subst σ A} {subst σ A'} {rA} {subst (liftSubst σ) B} {subst (liftSubst σ) B'} {subst σ e} {subst σ f} Aσ Bσ A'σ B'σ eσ fσ
                                     in PE.subst (λ BB → Δ ⊢ subst σ (cast ⁰ (Π A ^ rA ° ⁰ ▹ B ° ⁰) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰) e f) ⇒ lam subst σ A' ▹ BB ∷ subst σ (Π A' ^ rA ° ⁰ ▹ B' ° ⁰) ^ ι ⁰ )
                                                 (PE.cong₄ (cast ⁰)
                                                           (B-cast-subst  σ A' A rA e B)
                                                           PE.refl (PE.cong₂ (λ X Y → snd X ∘ Y) (PE.sym (Idsym-subst-lemma σ e)) PE.refl) (wk1f-cast-subst σ f A' A rA e)) X
      [id] , [eq] = redSubstTermᵛ {Π A' ^ rA ° ⁰ ▹ B' ° ⁰} {cast ⁰ (Π A ^ rA ° ⁰ ▹ B ° ⁰) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰) e f} {lam A' ▹ cast-Π-res A A' B B' e f}
                                  [Γ] (λ {Δ} {σ} ⊢Δ [σ] → [cast-Π] {Δ} {σ} ⊢Δ [σ])
                                  [ΠAB'] [cast-Π-res] 

   in modelsTermEq [ΠAB'] [id] [cast-Π-res] [eq]
