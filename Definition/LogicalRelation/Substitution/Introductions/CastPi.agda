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
open import Definition.LogicalRelation.Substitution.Introductions.Cast
open import Definition.LogicalRelation.Substitution.Introductions.Id
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Definition.LogicalRelation.Substitution.MaybeEmbed
open import Definition.LogicalRelation.Substitution.Introductions.Universe
open import Definition.LogicalRelation.Substitution.Reduction
open import Definition.LogicalRelation.Substitution.Weakening

open import Tools.Product
import Tools.PropositionalEquality as PE

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
      [ΓA]'  = (_∙_ {Γ} {A} [Γ] [A]')
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
      [ΓA] = _∙_ {A = A} [Γ]  [A]
      [ΓA'] = _∙_ {A = A'} [Γ]  [A']
      [wUA] = maybeEmbᵛ {A = Univ rA _} [ΓA'] (λ {Δ} {σ} → Uᵛ emb< [ΓA'] {Δ} {σ})
      [wA] = wk1ᵗᵛ {F = A'} {G = A} {lG = ⁰} [Γ] [A'] [A]ₜ
      [wA'] = wk1ᵗᵛ {F = A'} {G = A'} {lG = ⁰} [Γ] [A'] [A']ₜ
      [wIdAA'] : Γ ∙ A' ^ [ rA , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ Id (Univ rA ⁰) (wk1 A') (wk1 A) ^ [ % , ι ¹ ] / [ΓA']
      [wIdAA'] = Idᵛ {A = Univ rA ⁰} {t = wk1 A'} {u = wk1 A} [ΓA'] (λ {Δ} {σ} → [wUA] {Δ} {σ}) [wA'] [wA] 
      [wfste] : Γ ∙ A' ^ [ rA , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e)) ∷ Id (Univ rA ⁰) (wk1 A') (wk1 A) ^ [ % , ι ¹ ] / [ΓA'] / [wIdAA']
      [wfste] = {!!}

      cast-Π-a A A' e = cast ⁰ (wk1 A') (wk1 A) (Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0)
      [wA'⁰] = wk1ᵛ {A = A'} {F = A'} [Γ] [A'] [A']'
      [wA⁰]  = wk1ᵛ {A = A} {F = A'} [Γ] [A'] [A]'
      [cast-Π-a] : Γ ∙ A' ^ [ rA , ι ⁰ ]  ⊩ᵛ⟨ ∞ ⟩ cast-Π-a A A' e ∷ wk1 A ^ [ rA , ι ⁰ ] / [ΓA'] / wk1ᵛ {A = A} {F = A'} [Γ] [A'] [A]
      [cast-Π-a] = castᵗᵛ {wk1 A'} {wk1 A} {t = var 0} {e = Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))} [ΓA'] [wA'⁰] [wA⁰] 
                         (wk1ᵛ {A = A'} {F = A'} [Γ] [A'] [A'])   (wk1ᵛ {A = A} {F = A'} [Γ] [A'] [A])
                         [var]ₜ [wIdAA'] [wfste]
      bar = univᵗᵛ {A = wk1 A} {t = cast-Π-a A A' e} [ΓA'] (λ {Δ} {σ} → [wUA] {Δ} {σ}) [wA]
                  (S.irrelevanceTerm {A = wk1 A} {t = cast-Π-a A A' e} [ΓA'] [ΓA'] (wk1ᵛ {A = A} {F = A'} [Γ] [A'] [A])
                                     (maybeEmbᵛ {A = wk1 A} [ΓA'] (univᵛ {A = wk1 A} [ΓA'] (≡is≤ PE.refl) (λ {Δ} {σ} → [wUA] {Δ} {σ}) [wA])) [cast-Π-a]) 
      B[cast-Π-a]↑ = subst↑S {F = A'} {G = B} {t = cast-Π-a A A' e} {F' = A} [Γ] [A']' [A]' (S.irrelevance {A = B} ([ΓA]) ([ΓA]') [B]')
                     (S.irrelevanceTerm {A = wk1 A} {t = cast-Π-a A A' e} [ΓA'] (_∙_ {A = A'} [Γ]  [A']')
                                       (univᵛ {A = wk1 A} [ΓA'] (≡is≤ PE.refl) (λ {Δ} {σ} → [wUA] {Δ} {σ}) [wA])
                                       (wk1ᵛ {A = A} {F = A'} [Γ] [A']' [A]') bar) 
      cast-Π-res A A' B B' e f = 
                 cast ⁰ (B [ cast-Π-a A A' e ]↑) B' ((snd (wk1 e)) ∘ (var 0)) ((wk1 f) ∘ cast-Π-a A A' e)
      [cast-Π-res] : Γ ⊩ᵛ⟨ ∞ ⟩ lam A' ▹ cast-Π-res A A' B B' e f ∷ Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ^ [ ! , ι ⁰ ] / [Γ] / [ΠAB']
      [cast-Π-res] = lamᵛ {F = A'} {G = B'} {t = cast-Π-res A A' B B' e f} (≡is≤ PE.refl) (≡is≤ PE.refl) [Γ] [A'] [B']
                          (castᵗᵛ {B [ cast-Π-a A A' e ]↑} {B'} {t = (wk1 f) ∘ cast-Π-a A A' e} {e = (snd (wk1 e)) ∘ (var 0)}
                                  [ΓA'] (S.irrelevance {A = B [ cast-Π-a A A' e ]↑} (_∙_ {A = A'} [Γ]  [A']') [ΓA'] B[cast-Π-a]↑) 
                                  [B']' (subst↑S {F = A'} {G = B} {F' = A} [Γ] [A'] [A] [B] [cast-Π-a]) [B'] {!!} {!!} {!!})
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
                                     in PE.subst (λ BB → Δ ⊢ _ ⇒ lam subst σ A' ▹ BB ∷ _ ^ _ )
                                                 (PE.cong₄ (cast ⁰)
                                                           {!!}
                                                           PE.refl (PE.cong₂ (λ X Y → snd X ∘ Y) (PE.sym (Idsym-subst-lemma σ e)) {!!}) {!!}) X 
      [id] , [eq] = redSubstTermᵛ {Π A' ^ rA ° ⁰ ▹ B' ° ⁰} {cast ⁰ (Π A ^ rA ° ⁰ ▹ B ° ⁰) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰) e f} {lam A' ▹ cast-Π-res A A' B B' e f}
                                  [Γ] (λ {Δ} {σ} ⊢Δ [σ] → [cast-Π] {Δ} {σ} ⊢Δ [σ])
                                  [ΠAB'] [cast-Π-res] 

   in modelsTermEq [ΠAB'] [id] [cast-Π-res] [eq]
