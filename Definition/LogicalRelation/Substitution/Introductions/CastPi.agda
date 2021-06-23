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

wk2d : Term → Term
wk2d = U.wk (lift (lift (step id)))

wk1f-cast-subst : ∀ σ f A' A rA e →
  (wk1 (subst σ f) ∘ cast ⁰ (wk1 (subst σ A')) (wk1 (subst σ A)) (Idsym (Univ rA ⁰) (wk1 (subst σ A)) (wk1 (subst σ A')) (fst (wk1 (subst σ e)))) (var 0))
  PE.≡
  subst (repeat liftSubst (repeat liftSubst σ 1) 0) (wk1 f ∘ cast ⁰ (wk1 A') (wk1 A) (Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0))
wk1f-cast-subst σ f A' A rA e = PE.cong₂ (λ X Y → X ∘ Y) (PE.sym (Idsym-subst-lemma σ f))
  (PE.cong₃ (λ X Y Z → cast ⁰ X Y Z (var 0)) (PE.sym (Idsym-subst-lemma σ A')) (PE.sym (Idsym-subst-lemma σ A))
    (PE.trans (PE.cong₃ (λ X Y Z → Idsym (Univ rA ⁰) X Y Z) (PE.sym (Idsym-subst-lemma σ A)) (PE.sym (Idsym-subst-lemma σ A')) (PE.sym (Idsym-subst-lemma σ (fst e))))
      (PE.sym (subst-Idsym (liftSubst σ) (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))))))

B-cast-subst : ∀ σ A' A rA e B →
  subst (liftSubst σ) B [ cast ⁰ (wk1 (subst σ A')) (wk1 (subst σ A)) (Idsym (Univ rA ⁰) (wk1 (subst σ A)) (wk1 (subst σ A')) (fst (wk1 (subst σ e)))) (var 0) ]↑
  PE.≡
  subst (repeat liftSubst (repeat liftSubst σ 1) 0) (B [ cast ⁰ (wk1 A') (wk1 A) (Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) ]↑)
B-cast-subst σ A′ A rA e B = PE.trans (PE.cong (λ X → (subst (liftSubst σ) B) [ X ]↑)
  (PE.cong₃ (λ X Y Z → cast ⁰ X Y Z (var 0)) (PE.sym (Idsym-subst-lemma σ A′)) (PE.sym (Idsym-subst-lemma σ A))
      (PE.trans (PE.cong₃ (λ X Y Z → Idsym (Univ rA ⁰) X Y Z) (PE.sym (Idsym-subst-lemma σ A)) (PE.sym (Idsym-subst-lemma σ A′)) (PE.sym (Idsym-subst-lemma σ (fst e))))
      (PE.sym (subst-Idsym (liftSubst σ) (Univ rA ⁰) (wk1 A) (wk1 A′) (fst (wk1 e)))))))
  (PE.sym ((singleSubstLift↑ σ B _)))

wk2d11-111 : ∀ A → wk2d (wk1 (wk1 A)) PE.≡ wk1 (wk1 (wk1 A))
wk2d11-111 A = PE.trans (wk-comp (lift (lift (step id))) (step id) (wk1 A))
               (PE.trans (wk-comp (step (lift (step id))) (step id) A)
               (PE.trans (PE.sym (wk-comp (step (step id)) (step id) A)) (PE.sym (wk-comp (step id) (step id) (wk1 A)))))

wk2d1d-1d1d : ∀ A → wk2d (wk1d A) PE.≡ wk1d (wk1d A)
wk2d1d-1d1d A = PE.trans (wk-comp (lift (lift (step id))) (lift (step id)) A)
                (PE.trans PE.refl (PE.sym (wk-comp (lift (step id)) (lift (step id)) A)))

wk1∃-aux : ∀ A A' rA B B' →  wk1 (∃ Id (Univ rA ⁰) A A' ▹ (Π wk1 A' ^ rA ° ⁰ ▹
                             Id (U ⁰) (wk1d B [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A))
                                                                (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (var 1)) (var 0) ]↑)
                                      (wk1d B') ° ¹))
                         PE.≡
                         ∃ Id (Univ rA ⁰) (wk1 A) (wk1 A') ▹ (Π wk1 (wk1 A') ^ rA ° ⁰ ▹
                           Id (U ⁰) (wk2d (wk1d B) [ cast ⁰ (wk2d (wk1 (wk1 A'))) (wk2d (wk1 (wk1 A)))
                                                                  (Idsym (Univ rA ⁰) (wk2d (wk1 (wk1 A))) (wk2d (wk1 (wk1 A'))) (var 1)) (var 0) ]↑)
                                    (wk1d (wk1d B')) ° ¹)
wk1∃-aux A A' rA B B' = PE.cong₃ (λ X Y Z → ∃ Id (Univ rA ⁰) (wk1 A) (wk1 A') ▹ Π X ^ rA ° ⁰ ▹ Id (U ⁰) Y Z ° ¹)
                             (PE.trans (wk-comp (lift (step id)) (step id) A') (PE.sym (wk-comp (step id) (step id) A')))
                             (PE.trans (wk-β↑ (wk1d B)) (PE.cong₃ (λ X Y Z → wk2d (wk1d B) [ cast ⁰ X Y Z (var 0) ]↑)
                             PE.refl PE.refl (wk-Idsym (lift (lift (step id))) (Univ rA ⁰) _ _ (var 1)) ))
                             (wk2d1d-1d1d B')

wk1∃ : ∀ A A' rA B B' → wk1 (∃ Id (Univ rA ⁰) A A' ▹ (Π wk1 A' ^ rA ° ⁰ ▹
                             Id (U ⁰) (wk1d B [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A))
                                                                (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (var 1)) (var 0) ]↑)
                                      (wk1d B') ° ¹))
                         PE.≡
                         ∃ Id (Univ rA ⁰) (wk1 A) (wk1 A') ▹ (Π wk1 (wk1 A') ^ rA ° ⁰ ▹
                           Id (U ⁰) (wk1d (wk1d B) [ cast ⁰ (wk1 (wk1 (wk1 A'))) (wk1 (wk1 (wk1 A)))
                                                                  (Idsym (Univ rA ⁰) (wk1 (wk1 (wk1 A))) (wk1 (wk1 (wk1 A'))) (var 1)) (var 0) ]↑)
                                    (wk1d (wk1d B')) ° ¹)

wk1∃ A A' rA B B' = PE.trans (wk1∃-aux A A' rA B B') (PE.cong₃ (λ X Y Z → ∃ Id (Univ rA ⁰) (wk1 A) (wk1 A') ▹ Π (wk1 (wk1 A')) ^ rA ° ⁰ ▹ Id (U ⁰) (X [ Y ]↑) Z ° ¹)
                             (wk2d1d-1d1d B) (PE.cong₃ (λ X Y Z → cast ⁰ X Y Z (var 0)) (wk2d11-111 A') (wk2d11-111 A)
                                             (PE.cong₂ (λ X Y →   Idsym (Univ rA ⁰)  X Y (var 1)) (wk2d11-111 A) (wk2d11-111 A'))) PE.refl )

snd-cast-subst : ∀ A A' rA B B' e → Π wk1 (wk1 A') ^ rA ° ⁰ ▹
                                        Id (U ⁰) (wk1d (wk1d B) [ cast ⁰ (wk1 (wk1 (wk1 A'))) (wk1 (wk1 (wk1 A))) (Idsym (Univ rA ⁰) (wk1 (wk1 (wk1 A))) (wk1 (wk1 (wk1 A'))) (var 1)) (var 0) ]↑)
                                                 (wk1d (wk1d B')) ° ¹ [ fst (wk1 e) ]
                                    PE.≡
                                      Π (wk1 A') ^ rA ° ⁰ ▹
                                        Id (U ⁰) (wk1d B [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (fst (wk1 (wk1 e)))) (var 0) ]↑)
                                                 (wk1d B') ° ¹
snd-cast-subst A A' rA B B' e = PE.cong₃ (λ X Y Z → Π X ^ rA ° ⁰ ▹ Id (U ⁰) Y Z ° ¹)
  (wk1-singleSubst (wk1 A') _)
  (PE.trans (singleSubstLift↑ (sgSubst (fst (wk1 e))) (wk1d (wk1d B)) _)
    (PE.cong₂ (λ X Y → X [ Y ]↑) (wk1d-singleSubst (wk1d B) (fst (wk1 e)))
      (PE.cong₃ (λ X Y Z → cast ⁰ X Y Z (var 0)) (subst3wk A' (fst (wk1 e))) (subst3wk A (fst (wk1 e)))
        (PE.trans (subst-Idsym (liftSubst (sgSubst (fst (wk1 e)))) (Univ rA ⁰) (wk1 (wk1 (wk1 A))) (wk1 (wk1 (wk1 A'))) (var 1))
          (PE.cong₂ (λ X Y → Idsym (Univ rA ⁰) X Y (fst (wk1 (wk1 e)))) (subst3wk A (fst (wk1 e))) (subst3wk A' (fst (wk1 e))))))))
  (wk1d-singleSubst (wk1d B') (fst (wk1 e)))
  where
    subst3wk : ∀ t u → subst (liftSubst (sgSubst u)) (wk1 (wk1 (wk1 t))) PE.≡ wk1 (wk1 t)
    subst3wk t u = PE.trans (Idsym-subst-lemma (sgSubst u) (wk1 (wk1 t))) (PE.cong wk1 (wk1-singleSubst (wk1 t) u))


Id-cast-subst : ∀ A A' rA B B' e → Id (U ⁰) (wk1d B [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (fst (wk1 (wk1 e)))) (var 0) ]↑)
                                            (wk1d B')
                                      [ var 0 ]
                                   PE.≡
                                   Id (U ⁰) (B [ cast ⁰ (wk1 A') (wk1 A) (Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) ]↑)
                                                  B'
Id-cast-subst A A' rA B B' e = PE.cong₂ (Id (U ⁰))
  (PE.trans
    (PE.cong (λ X → X [ var 0 ]) (wk1d[]-[]↑ (wk1d B) _))
    (PE.trans aux (PE.sym (wk1d[]-[]↑ B _))) )
  (wkSingleSubstId B')
  where
    aux : (wk1d (wk1d B) [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (fst (wk1 (wk1 e)))) (var 0) ]) [ var 0 ]
      PE.≡ wk1d B [ cast ⁰ (wk1 A') (wk1 A) (Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) ]
    aux = PE.trans (singleSubstLift (wk1d (wk1d B)) _)
      (PE.cong₄ (λ X Y Z T → X [ cast ⁰ Y Z T (var 0) ])
        (wk1d-singleSubst (wk1d B) (var 0)) (wk1-singleSubst (wk1 A') (var 0)) (wk1-singleSubst (wk1 A) (var 0))
        (PE.trans (subst-Idsym _ (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (wk1 (wk1 (fst e))))
          (PE.cong₃ (λ X Y Z → Idsym (Univ rA ⁰) X Y Z) (wk1-singleSubst (wk1 A) (var 0)) (wk1-singleSubst (wk1 A') (var 0)) (wk1-singleSubst (wk1 (fst e)) (var 0)))))


cast-Πᵗᵛ-aux : ∀ {A B A' B' rA Γ e f} ([Γ] : ⊩ᵛ Γ) →
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
           ([Id-U-ΠΠ] : [ Γ ⊩ᵛ⟨ l ⟩ (Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰))
                    ≡ ∃ (Id (Univ rA ⁰) A A') ▹
                      (Π (wk1 A') ^ rA ° ⁰ ▹ Id (U ⁰)
                        ((U.wk (lift (step id)) B) [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (var 1)) (var 0) ]↑)
                        (U.wk (lift (step id)) B') ° ¹)
                  ∷ SProp ¹ ^ [ ! , next ¹ ] / [Γ] ] )
           →
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
               [ΓA'] = (_∙_ {Γ} {A'} [Γ]  [A'])
               [w'A] = wk1ᵗᵛ {F = A'} {G = A} {lG = ⁰} [Γ] [A'] [A]ₜ
               [w'A'] = wk1ᵗᵛ {F = A'} {G = A'} {lG = ⁰} [Γ] [A'] [A']ₜ
               [w'A']' = wk1ᵛ {A = A'} {F = A'} [Γ] [A'] [A']
               [wUA] = maybeEmbᵛ {A = Univ rA _} [ΓA'] (λ {Δ} {σ} → Uᵛ emb< [ΓA'] {Δ} {σ})
               [wIdAA'] = Idᵛ {A = Univ rA ⁰} {t = wk1 A} {u = wk1 A'} [ΓA'] (λ {Δ} {σ} → [wUA] {Δ} {σ}) [w'A] [w'A']
               [ww'A']' = wk1ᵛ {A = wk1 A'} {F = Id (Univ rA ⁰) (wk1 A) (wk1 A')} [ΓA'] [wIdAA'] [w'A']'
               [ww'A'] = wk1ᵗᵛ {F = Id (Univ rA ⁰) (wk1 A) (wk1 A')} {G = wk1 A'} {lG = ⁰} [ΓA'] [wIdAA'] [w'A']
               [ΓA'Id] = _∙_ {A = Id (Univ rA ⁰) (wk1 A) (wk1 A')} [ΓA'] [wIdAA']
               [ΓA'IdA'] = _∙_ {A = wk1 (wk1 A')} [ΓA'Id] [ww'A']'
               [wwwUA'] = λ {Δ} {σ} r → maybeEmbᵛ {A = Univ r _ } [ΓA'IdA'] (λ {Δ} {σ} → Uᵛ emb< [ΓA'IdA'] {Δ} {σ}) {Δ} {σ}
               [www'A'] = wk1ᵗᵛ {F = wk1 (wk1 A')} {G = wk1 (wk1 A')} {lG = ⁰} [ΓA'Id] [ww'A']' [ww'A']
               [ww'A] = wk1ᵗᵛ {F = Id (Univ rA ⁰) (wk1 A) (wk1 A')} {G = wk1 A} {lG = ⁰} [ΓA'] [wIdAA'] [w'A]
               [www'A] = wk1ᵗᵛ {F = wk1 (wk1 A')} {G = wk1 (wk1 A)} {lG = ⁰} [ΓA'Id] [ww'A']' [ww'A]
               [wwwIdAA'] = Idᵛ {A = Univ rA ⁰} {t = wk1 (wk1 (wk1 A))} {u = wk1 (wk1 (wk1 A'))} [ΓA'IdA'] (λ {Δ} {σ} → [wwwUA'] {Δ} {σ} rA) [www'A] [www'A']
               [wwwU¹] = λ {Δ} {σ} r → Uᵛ {rU = r} ∞< [ΓA'Id] {Δ} {σ}
               Id-U-ΠΠ-res-end A A' B B' = Π (wk1 A') ^ rA ° ⁰ ▹ Id (U ⁰)
                                    ((wk1d B) [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (var 1)) (var 0) ]↑)
                                    (wk1d B') ° ¹
           in
           ([Id-U-ΠΠ-res-end] : Γ ∙ A' ^ [ rA , ι ⁰ ] ∙ Id (Univ rA ⁰) (wk1 A) (wk1 A') ^ [ % , ι ¹ ] ⊩ᵛ⟨ ∞ ⟩
                        Id-U-ΠΠ-res-end (wk1 A) (wk1 A') (wk1d B) (wk1d B') ∷ SProp ¹ ^ [ ! , ∞ ] / [ΓA'Id] / (λ {Δ} {σ} → [wwwU¹] {Δ} {σ} %))
           ([var]ₜ : Γ ∙ A' ^ [ rA , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ var 0 ∷ wk1 A' ^ [ rA , ι ⁰ ] / [ΓA'] / wk1ᵛ {A = A'} {F = A'} [Γ] [A'] [A'])
           ([var0']ₜ : Γ ∙ A' ^ [ rA , ι ⁰ ] ∙ Id (Univ rA ⁰) (wk1 A) (wk1 A') ^ [ % , ι ¹ ] ∙ wk1 (wk1 A') ^ [ rA , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ var 0 ∷
                         wk1 (wk1 (wk1 A')) ^ [ rA , ι ⁰ ] / [ΓA'IdA'] / wk1ᵛ {A = wk1 (wk1 A')} {F = wk1 (wk1 A')} [ΓA'Id] [ww'A']' [ww'A']')
           ([var1']ₜ : Γ ∙ A' ^ [ rA , ι ⁰ ] ∙ Id (Univ rA ⁰) (wk1 A) (wk1 A') ^ [ % , ι ¹ ] ∙ wk1 (wk1 A') ^ [ rA , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ var 1 ∷
                         Id (Univ rA ⁰) (wk1 (wk1 (wk1 A))) (wk1 (wk1 (wk1 A'))) ^ [ % , ι ¹ ] / [ΓA'IdA'] / [wwwIdAA'])
         → [ Γ ⊩ᵛ⟨ l ⟩ (cast lΠ (Π A ^ rA ° lΠ ▹ B ° lΠ) (Π A' ^ rA ° lΠ ▹ B' ° lΠ) e f) ≡
                       (lam A' ▹
                         let a = cast lΠ (wk1 A') (wk1 A) (Idsym (Univ rA lΠ) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) in
                         cast lΠ (B [ a ]↑) B' ((snd (wk1 e)) ∘ (var 0)) ((wk1 f) ∘ a))
                       ∷ Π A' ^ rA ° lΠ ▹ B' ° lΠ ^ [ ! , ι lΠ ] / [Γ] ]

cast-Πᵗᵛ-aux {A} {B} {A'} {B'} {rA} {Γ} {e} {f}
        [Γ] [A] [A'] [UB] [UB'] [A]ₜ [B]ₜ [A']ₜ [B']ₜ [Id] [e]ₜ [ΠAB] [f]ₜ [Id-U-ΠΠ] [Id-U-ΠΠ-res-end] [var]ₜ [var0']ₜ [var1']ₜ =
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
      [wUA]ᵗ = Uᵗᵛ [ΓA']
      [IdAA']ₜ = Idᵗᵛ {A = Univ rA ⁰} {t = A} {u = A'} [Γ] (λ {Δ} {σ} → [UA] {Δ} {σ}) [A]ₜ [A']ₜ
      [IdAA'] = Idᵛ {A = Univ rA ⁰} {t = A} {u = A'} [Γ] (λ {Δ} {σ} → [UA] {Δ} {σ}) [A]ₜ [A']ₜ
      [ΓId] = _∙_ {A = Id (Univ rA ⁰) A A'} [Γ] [IdAA']
      [wA'] = wk1ᵗᵛ {F = Id (Univ rA ⁰) A A'} {G = A'} {lG = ⁰} [Γ] [IdAA'] [A']ₜ
      [wA']' = wk1ᵛ {A = A'} {F = Id (Univ rA ⁰) A A'} [Γ] [IdAA'] [A']
      [wA]' = wk1ᵛ {A = A} {F = Id (Univ rA ⁰) A A'} [Γ] [IdAA'] [A]
      [wA] = wk1ᵗᵛ {F = Id (Univ rA ⁰) A A'} {G = A} {lG = ⁰} [Γ] [IdAA'] [A]ₜ
      [ΓIdA'] = _∙_ {A = wk1 A'} [ΓId] [wA']'
      [wwU¹] = λ {Δ} {σ} r → Uᵛ {rU = r} ∞< [ΓIdA'] {Δ} {σ}
      [wwUA'] = λ {Δ} {σ} r → maybeEmbᵛ {A = Univ r _ } [ΓIdA'] (λ {Δ} {σ} → Uᵛ emb< [ΓIdA'] {Δ} {σ}) {Δ} {σ}
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
      Id-U-ΠΠ-res-end A A' B B' = Π (wk1 A') ^ rA ° ⁰ ▹ Id (U ⁰)
                                    ((wk1d B) [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (var 1)) (var 0) ]↑)
                                    (wk1d B') ° ¹
      Id-U-ΠΠ-left = Id (U lΠ) (Π A ^ rA ° lΠ ▹ B ° lΠ) (Π A' ^ rA ° lΠ  ▹ B' ° lΠ)
      Id-U-ΠΠ-res A A' B B' = ∃ (Id (Univ rA ⁰) A A') ▹ Id-U-ΠΠ-res-end A A' B B'
      [wU¹] = λ {Δ} {σ} r → Uᵛ {rU = r} ∞< [ΓA'] {Δ} {σ}
      modelsTermEq [SProp] _ [Id-U-ΠΠ-res] [eq] = [Id-U-ΠΠ]
      [Id-U-ΠΠ-res]' = maybeEmbᵛ {A = Id-U-ΠΠ-res  A A' B B'}  [Γ] (univᵛ {A = Id-U-ΠΠ-res  A A' B B'} [Γ] (≡is≤ PE.refl) [SProp] [Id-U-ΠΠ-res])
      [conve]ₜ = convᵛ {t = e} {A = Id-U-ΠΠ-left} {B = Id-U-ΠΠ-res  A A' B B'}
                       [Γ] [Id] [Id-U-ΠΠ-res]'
                       (univEqᵛ {A = Id-U-ΠΠ-left} {B = Id-U-ΠΠ-res  A A' B B'} [Γ] [SProp] [Id] [eq]) [e]ₜ
      [we] = wk1Termᵛ {F = A'} {G = Id-U-ΠΠ-res A A' B B'} {t = e} [Γ] [A'] [Id-U-ΠΠ-res]' [conve]ₜ
      [w'A] = wk1ᵗᵛ {F = A'} {G = A} {lG = ⁰} [Γ] [A'] [A]ₜ
      [w'A]' = wk1ᵛ {A = A} {F = A'} [Γ] [A'] [A]
      [w'A]⁰ = wk1ᵛ {A = A} {F = A'} [Γ] [A'] [A]'
      [w'A'] = wk1ᵗᵛ {F = A'} {G = A'} {lG = ⁰} [Γ] [A'] [A']ₜ
      [w'A']' = wk1ᵛ {A = A'} {F = A'} [Γ] [A'] [A']
      [w'A']⁰ = wk1ᵛ {A = A'} {F = A'} [Γ] [A'] [A']'
      [wIdA'A] = Idᵛ {A = Univ rA ⁰} {t = wk1 A'} {u = wk1 A} [ΓA'] (λ {Δ} {σ} → [wUA] {Δ} {σ}) [w'A'] [w'A]
      [wIdAA'] = Idᵛ {A = Univ rA ⁰} {t = wk1 A} {u = wk1 A'} [ΓA'] (λ {Δ} {σ} → [wUA] {Δ} {σ}) [w'A] [w'A']
      [wIdAA']ᵗ = Idᵗᵛ {A = Univ rA ⁰} {t = wk1 A} {u = wk1 A'} [ΓA'] (λ {Δ} {σ} → [wUA] {Δ} {σ}) [w'A] [w'A']
      [wIdAA']ₜ = Idᵗᵛ {A = Univ rA ⁰} {t = wk1 A} {u = wk1 A'} [ΓA'] (λ {Δ} {σ} → [wUA] {Δ} {σ}) [w'A] [w'A']
      [ww'A']' = wk1ᵛ {A = wk1 A'} {F = Id (Univ rA ⁰) (wk1 A) (wk1 A')} [ΓA'] [wIdAA'] [w'A']'
      [ww'A'] = wk1ᵗᵛ {F = Id (Univ rA ⁰) (wk1 A) (wk1 A')} {G = wk1 A'} {lG = ⁰} [ΓA'] [wIdAA'] [w'A']
      [ww'A]' = wk1ᵛ {A = wk1 A} {F = Id (Univ rA ⁰) (wk1 A) (wk1 A')} [ΓA'] [wIdAA'] [w'A]'
      [ww'A] = wk1ᵗᵛ {F = Id (Univ rA ⁰) (wk1 A) (wk1 A')} {G = wk1 A} {lG = ⁰} [ΓA'] [wIdAA'] [w'A]
      [ΓA'A'] = _∙_ {A = wk1 A'} [ΓA'] [w'A']'
      [ww'UA'] = λ {Δ} {σ} r → maybeEmbᵛ {A = Univ r _ } [ΓA'A'] (λ {Δ} {σ} → Uᵛ emb< [ΓA'A'] {Δ} {σ}) {Δ} {σ}
      [ΓA'A] = _∙_ {A = wk1 A} [ΓA'] [w'A]'
      [ww'UA] = λ {Δ} {σ} r → maybeEmbᵛ {A = Univ r _ } [ΓA'A] (λ {Δ} {σ} → Uᵛ emb< [ΓA'A] {Δ} {σ}) {Δ} {σ}
      [ΓA'Id] = _∙_ {A = Id (Univ rA ⁰) (wk1 A) (wk1 A')} [ΓA'] [wIdAA']
      [ΓA'IdA'] = _∙_ {A = wk1 (wk1 A')} [ΓA'Id] [ww'A']'
      [www'UA'] = λ {Δ} {σ} r → maybeEmbᵛ {A = Univ r _ } [ΓA'IdA'] (λ {Δ} {σ} → Uᵛ emb< [ΓA'IdA'] {Δ} {σ}) {Δ} {σ}
      [ΓA'IdA] = _∙_ {A = wk1 (wk1 A)} [ΓA'Id] [ww'A]'
      [www'UA] = λ {Δ} {σ} r → maybeEmbᵛ {A = Univ r _ } [ΓA'IdA] (λ {Δ} {σ} → Uᵛ emb< [ΓA'IdA] {Δ} {σ}) {Δ} {σ}
      [w'B'] = wk1dᵗᵛ {F = A'} {F' = A'} {G = B'} [Γ] [A'] [A'] (λ {Δ} {σ} → [UB'] {Δ} {σ}) ((λ {Δ} {σ} → [ww'UA'] {Δ} {σ} !)) [B']ₜ
      [ww'B'] = wk1dᵗᵛ {F = wk1 A'} {F' = Id (Univ rA ⁰) (wk1 A) (wk1 A')} {G = wk1d B'} [ΓA'] [w'A']' [wIdAA'] (λ {Δ} {σ} → [ww'UA'] {Δ} {σ} !) (λ {Δ} {σ} → [www'UA'] {Δ} {σ} !) [w'B']
      [w'B] = wk1dᵗᵛ {F = A} {F' = A'} {G = B} [Γ] [A] [A'] (λ {Δ} {σ} → [UB] {Δ} {σ}) ((λ {Δ} {σ} → [ww'UA] {Δ} {σ} !)) [B]ₜ
      [ww'B] = wk1dᵗᵛ {F = wk1 A} {F' = Id (Univ rA ⁰) (wk1 A) (wk1 A')} {G = wk1d B} [ΓA'] [w'A]' [wIdAA'] (λ {Δ} {σ} → [ww'UA] {Δ} {σ} !) (λ {Δ} {σ} → [www'UA] {Δ} {σ} !) [w'B]
      [www'A']' = wk1ᵛ {A = wk1 (wk1 A')} {F = wk1 (wk1 A') } [ΓA'Id] [ww'A']' [ww'A']'
      [www'A'] = wk1ᵗᵛ {F = wk1 (wk1 A')} {G = wk1 (wk1 A')} {lG = ⁰} [ΓA'Id] [ww'A']' [ww'A']
      [www'A]' = wk1ᵛ {A = wk1 (wk1 A)} {F = wk1 (wk1 A')} [ΓA'Id] [ww'A']' [ww'A]'
      [www'A] = wk1ᵗᵛ {F = wk1 (wk1 A')} {G = wk1 (wk1 A)} {lG = ⁰} [ΓA'Id] [ww'A']' [ww'A]
      [wwU¹] = λ {Δ} {σ} r → Uᵛ {rU = r} ∞< [ΓA'A'] {Δ} {σ}
      [wwwU¹] = λ {Δ} {σ} r → Uᵛ {rU = r} ∞< [ΓA'Id] {Δ} {σ}
      Id-U-ΠΠ-res-end-wk1d = Id-U-ΠΠ-res-end (wk1 A) (wk1 A') (wk1d B) (wk1d B')
      Id-U-ΠΠ-res-wk1d = Id-U-ΠΠ-res (wk1 A) (wk1 A') (wk1d B) (wk1d B')
      [Id-U-ΠΠ-res-end]' = maybeEmbᵛ {A = Id-U-ΠΠ-res-end-wk1d} [ΓA'Id]
                                    (univᵛ {A = Id-U-ΠΠ-res-end-wk1d} [ΓA'Id] (≡is≤ PE.refl)
                                    (λ {Δ} {σ} → [wwwU¹] {Δ} {σ} %) [Id-U-ΠΠ-res-end])
      [we]' = S.irrelevanceTerm′ {A = wk1 (Id-U-ΠΠ-res A A' B B')} {A′ = Id-U-ΠΠ-res-wk1d} {t = wk1 e}
                                 (wk1∃ A A' rA B B')
                                 PE.refl [ΓA'] [ΓA'] (wk1ᵛ {A = Id-U-ΠΠ-res A A' B B'} {F = A'} [Γ] [A'] [Id-U-ΠΠ-res]')
                                 (∃ᵛ {F = Id (Univ rA ⁰) (wk1 A) (wk1 A')} {G = Id-U-ΠΠ-res-end-wk1d} [ΓA'] [wIdAA']
                                            [Id-U-ΠΠ-res-end]') [we]
      [fst] = fstᵛ {F = Id (Univ rA ⁰) (wk1 A) (wk1 A')} {G = Id-U-ΠΠ-res-end-wk1d} {tu = wk1 e}
                             [ΓA'] [wIdAA'] [Id-U-ΠΠ-res-end]'
                               (λ {Δ} {σ} → [wwwU¹] {Δ} {σ} %) [wIdAA']ᵗ [Id-U-ΠΠ-res-end]
                               [we]'
      [wfste] : Γ ∙ A' ^ [ rA , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e)) ∷ Id (Univ rA ⁰) (wk1 A') (wk1 A) ^ [ % , ι ¹ ] / [ΓA'] / [wIdA'A]
      [wfste] = IdSymᵗᵛ {A = Univ rA ⁰} {t = wk1 A} {u = wk1 A'} {e = fst (wk1 e)} [ΓA'] (λ {Δ} {σ} → [wU¹] {Δ} {σ} !)
                       (λ {Δ} {σ} → [wUA]ᵗ {Δ} {σ}) (λ {Δ} {σ} → [wUA] {Δ} {σ})
                       [w'A] [w'A'] [wIdAA'] [wIdA'A] [fst]

      cast-Π-a A A' e = cast ⁰ (wk1 A') (wk1 A) (Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0)
      [cast-Π-a] : Γ ∙ A' ^ [ rA , ι ⁰ ]  ⊩ᵛ⟨ ∞ ⟩ cast-Π-a A A' e ∷ wk1 A ^ [ rA , ι ⁰ ] / [ΓA'] / wk1ᵛ {A = A} {F = A'} [Γ] [A'] [A]
      [cast-Π-a] = castᵗᵛ {wk1 A'} {wk1 A} {t = var 0} {e = Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))} [ΓA']
                          (λ {Δ} {σ} → [wUA] {Δ} {σ}) [w'A'] [w'A]
                         (wk1ᵛ {A = A'} {F = A'} [Γ] [A'] [A'])   (wk1ᵛ {A = A} {F = A'} [Γ] [A'] [A])
                         [var]ₜ [wIdA'A] [wfste]
      B[cast-Π-a]↑ₜ = subst↑STerm {F = A'} {F' = A} {G = B} {t = cast-Π-a A A' e} [Γ] [A'] [A]
                                  (λ {Δ} {σ} → [UB'] {Δ} {σ}) (λ {Δ} {σ} → [UB] {Δ} {σ}) [B]ₜ [cast-Π-a]
      [f°cast-Π-a] = appᵛ↑ {F = A} {F' = A'} {G = B} {t = wk1 f} {u = cast-Π-a A A' e} (≡is≤ PE.refl) (≡is≤ PE.refl) [Γ] [A] [A'] [B] [ΠAB]
                          (wk1Termᵛ {F = A'} {G =  Π A ^ rA ° ⁰ ▹ B ° ⁰} {t = f} [Γ] [A'] [ΠAB] [f]ₜ)
                          [cast-Π-a]
      [wIdBB'] : Γ ∙ A' ^ [ rA , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ Id (Univ ! ⁰) (B [ cast-Π-a A A' e ]↑) B' ^ [ % , ι ¹ ] / [ΓA']
      [wIdBB'] = Idᵛ {A = Univ ! ⁰} {t = B [ cast-Π-a A A' e ]↑} {u = B'} [ΓA'] (λ {Δ} {σ} → [UB'] {Δ} {σ})
                     B[cast-Π-a]↑ₜ [B']ₜ
      [snd] = sndᵛ {F = Id (Univ rA ⁰) (wk1 A) (wk1 A')} {G = Id-U-ΠΠ-res-end-wk1d} {tu = wk1 e}
                             [ΓA'] [wIdAA'] [Id-U-ΠΠ-res-end]'
                               (λ {Δ} {σ} → [wwwU¹] {Δ} {σ} %) [wIdAA']ᵗ [Id-U-ΠΠ-res-end]
                               [we]'
      [sndType]' = S.irrelevance′ {A = Id-U-ΠΠ-res-end-wk1d [ fst (wk1 e) ]}
                                  {A′ = Π (wk1 A') ^ rA ° ⁰ ▹
                                        Id (U ⁰) ((wk1d B) [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (fst (wk1 (wk1 e)))) (var 0) ]↑)
                                                 (wk1d B') ° ¹}
                                  (snd-cast-subst A A' rA B B' e) [ΓA'] [ΓA']
                                  (substS {F = Id (Univ rA ⁰) (wk1 A) (wk1 A')} {G = Id-U-ΠΠ-res-end-wk1d} {fst (wk1 e)} [ΓA']
                                            [wIdAA'] [Id-U-ΠΠ-res-end]' [fst])
      [snd]' = S.irrelevanceTerm′ {A = Id-U-ΠΠ-res-end-wk1d [ fst (wk1 e) ]}
                                  {A′ = Π (wk1 A') ^ rA ° ⁰ ▹
                                        Id (U ⁰) ((wk1d B) [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (fst (wk1 (wk1 e)))) (var 0) ]↑)
                                                 (wk1d B') ° ¹}
                                  {t = snd (wk1 e)}
                                  (snd-cast-subst A A' rA B B' e) PE.refl [ΓA'] [ΓA']
                                  (substS {F = Id (Univ rA ⁰) (wk1 A) (wk1 A')} {G = Id-U-ΠΠ-res-end-wk1d} {fst (wk1 e)} [ΓA']
                                           [wIdAA'] [Id-U-ΠΠ-res-end]' [fst])
                                  [sndType]' [snd]
      [wsnde] : Γ ∙ A' ^ [ rA , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ (snd (wk1 e)) ∘ (var 0) ∷ Id (Univ ! ⁰) (B [ cast-Π-a A A' e ]↑) B' ^ [ % , ι ¹ ] / [ΓA'] / [wIdBB']
      [wsnde] = let X = appᵛ {F = wk1 A'}
                            {G = Id (U ⁰)
                                    ((wk1d B) [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (fst (wk1 (wk1 e)))) (var 0) ]↑)
                                    (wk1d B')}
                                    {t = snd (wk1 e)} {u = var 0} [ΓA'] [w'A']'
                                    [sndType]' [snd]' [var]ₜ
                 in S.irrelevanceTerm′ {A = (Id (U ⁰) ((wk1d B) [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (fst (wk1 (wk1 e)))) (var 0) ]↑)
                                                      (wk1d B'))  [ var 0 ]}
                                       {A′ = Id (Univ ! ⁰) (B [ cast-Π-a A A' e ]↑) B'}
                                       {t = (snd (wk1 e)) ∘ (var 0)}
                                       (Id-cast-subst A A' rA B B' e) PE.refl [ΓA'] [ΓA']
                                       (substSΠ {wk1 A'}
                                                {Id (U ⁰) (wk1d B [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (fst (wk1 (wk1 e)))) (var 0) ]↑)
                                                          (wk1d B')}
                                                {var 0} [ΓA'] [w'A']'
                                                [sndType]' [var]ₜ )
                                       [wIdBB'] X

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
           [ Γ ⊩ᵛ⟨ l ⟩ (cast lΠ (Π A ^ rA ° lΠ ▹ B ° lΠ) (Π A' ^ rA ° lΠ ▹ B' ° lΠ) e f) ≡
                       (lam A' ▹
                         let a = cast lΠ (wk1 A') (wk1 A) (Idsym (Univ rA lΠ) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) in
                         cast lΠ (B [ a ]↑) B' ((snd (wk1 e)) ∘ (var 0)) ((wk1 f) ∘ a))
                       ∷ Π A' ^ rA ° lΠ ▹ B' ° lΠ ^ [ ! , ι lΠ ] / [Γ] ]

abstract

  cast-Πᵗᵛ {A} {B} {A'} {B'} {rA} {Γ} {e} {f}
           [Γ] [A] [A'] [UB] [UB'] [A]ₜ [B]ₜ [A']ₜ [B']ₜ [Id] [e]ₜ [ΠAB] [f]ₜ =
    let l = ∞
        lΠ = ⁰
        [UA] = maybeEmbᵛ {A = Univ rA _} [Γ] (Uᵛ emb< [Γ])
        [IdAA'] = Idᵛ {A = Univ rA ⁰} {t = A} {u = A'} [Γ] (λ {Δ} {σ} → [UA] {Δ} {σ}) [A]ₜ [A']ₜ
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
        [ΓA'] = (_∙_ {Γ} {A'} [Γ]  [A'])
        [w'A] = wk1ᵗᵛ {F = A'} {G = A} {lG = ⁰} [Γ] [A'] [A]ₜ
        [w'A'] = wk1ᵗᵛ {F = A'} {G = A'} {lG = ⁰} [Γ] [A'] [A']ₜ
        [w'A']' = wk1ᵛ {A = A'} {F = A'} [Γ] [A'] [A']
        [wUA] = maybeEmbᵛ {A = Univ rA _} [ΓA'] (λ {Δ} {σ} → Uᵛ emb< [ΓA'] {Δ} {σ})
        [wIdAA'] = Idᵛ {A = Univ rA ⁰} {t = wk1 A} {u = wk1 A'} [ΓA'] (λ {Δ} {σ} → [wUA] {Δ} {σ}) [w'A] [w'A']
        [ww'A']' = wk1ᵛ {A = wk1 A'} {F = Id (Univ rA ⁰) (wk1 A) (wk1 A')} [ΓA'] [wIdAA'] [w'A']'
        [ww'A'] = wk1ᵗᵛ {F = Id (Univ rA ⁰) (wk1 A) (wk1 A')} {G = wk1 A'} {lG = ⁰} [ΓA'] [wIdAA'] [w'A']
        [ΓA'Id] = _∙_ {A = Id (Univ rA ⁰) (wk1 A) (wk1 A')} [ΓA'] [wIdAA']
        [ΓA'IdA'] = _∙_ {A = wk1 (wk1 A')} [ΓA'Id] [ww'A']'
        [wwwUA'] = λ {Δ} {σ} r → maybeEmbᵛ {A = Univ r _ } [ΓA'IdA'] (λ {Δ} {σ} → Uᵛ emb< [ΓA'IdA'] {Δ} {σ}) {Δ} {σ}
        [www'A'] = wk1ᵗᵛ {F = wk1 (wk1 A')} {G = wk1 (wk1 A')} {lG = ⁰} [ΓA'Id] [ww'A']' [ww'A']
        [ww'A] = wk1ᵗᵛ {F = Id (Univ rA ⁰) (wk1 A) (wk1 A')} {G = wk1 A} {lG = ⁰} [ΓA'] [wIdAA'] [w'A]
        [www'A] = wk1ᵗᵛ {F = wk1 (wk1 A')} {G = wk1 (wk1 A)} {lG = ⁰} [ΓA'Id] [ww'A']' [ww'A]
        [wwwIdAA'] = Idᵛ {A = Univ rA ⁰} {t = wk1 (wk1 (wk1 A))} {u = wk1 (wk1 (wk1 A'))} [ΓA'IdA'] (λ {Δ} {σ} → [wwwUA'] {Δ} {σ} rA) [www'A] [www'A']
        [wA]ₜ = wk1ᵗᵛ {F = A'} {G = A} {lG = ⁰} [Γ] [A'] [A]ₜ
        [wA] = wk1ᵛ {A = A} {F = A'} [Γ] [A'] [A]
        [wA']ₜ = wk1ᵗᵛ {F = A'} {G = A'} {lG = ⁰} [Γ] [A'] [A']ₜ
        [wA'] = wk1ᵛ {A = A'} {F = A'} [Γ] [A'] [A']
        [wA']' = wk1ᵛ {A = A'} {F = A'} [Γ] [A'] [A']
        [wA]' = wk1ᵛ {A = A} {F = A'} [Γ] [A'] [A]
        [ΓA'A'] = _∙_ {A = wk1 A'} [ΓA'] [wA']'
        [ΓA'A] = _∙_ {A = wk1 A} [ΓA'] [wA]'
        [wwUA'] = λ {Δ} {σ} r → maybeEmbᵛ {A = Univ r _ } [ΓA'A'] (λ {Δ} {σ} → Uᵛ emb< [ΓA'A'] {Δ} {σ}) {Δ} {σ}
        [wwUA] = λ {Δ} {σ} r → maybeEmbᵛ {A = Univ r _ } [ΓA'A] (λ {Δ} {σ} → Uᵛ emb< [ΓA'A] {Δ} {σ}) {Δ} {σ}
        [wB']ₜ = wk1dᵗᵛ {F = A'} {F' = A'} {G = B'} [Γ] [A'] [A'] (λ {Δ} {σ} → [UB'] {Δ} {σ}) ((λ {Δ} {σ} → [wwUA'] {Δ} {σ} !)) [B']ₜ
        [wB]ₜ = wk1dᵗᵛ {F = A} {F' = A'} {G = B} [Γ] [A] [A'] (λ {Δ} {σ} → [UB] {Δ} {σ}) ((λ {Δ} {σ} → [wwUA] {Δ} {σ} !)) [B]ₜ
        [var]ₜ : Γ ∙ A' ^ [ rA , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ var 0 ∷ wk1 A' ^ [ rA , ι ⁰ ] / [ΓA'] / wk1ᵛ {A = A'} {F = A'} [Γ] [A'] [A']
        [var]ₜ = proj₂ (fundamentalVar here [ΓA'])
        [var0']ₜ : Γ ∙ A' ^ [ rA , ι ⁰ ] ∙ Id (Univ rA ⁰) (wk1 A) (wk1 A') ^ [ % , ι ¹ ] ∙ wk1 (wk1 A') ^ [ rA , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ var 0 ∷
                          wk1 (wk1 (wk1 A')) ^ [ rA , ι ⁰ ] / [ΓA'IdA'] / wk1ᵛ {A = wk1 (wk1 A')} {F = wk1 (wk1 A')} [ΓA'Id] [ww'A']' [ww'A']'
        [var0']ₜ = proj₂ (fundamentalVar here [ΓA'IdA'])
        [var1']ₜ : Γ ∙ A' ^ [ rA , ι ⁰ ] ∙ Id (Univ rA ⁰) (wk1 A) (wk1 A') ^ [ % , ι ¹ ] ∙ wk1 (wk1 A') ^ [ rA , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ var 1 ∷
                          Id (Univ rA ⁰) (wk1 (wk1 (wk1 A))) (wk1 (wk1 (wk1 A'))) ^ [ % , ι ¹ ] / [ΓA'IdA'] / [wwwIdAA']
        [var1']ₜ = let X = fundamentalVar (there here) [ΓA'IdA'] in S.irrelevanceTerm {A = Id (Univ rA ⁰) (wk1 (wk1 (wk1 A))) (wk1 (wk1 (wk1 A')))} {t = var 1}
                                                                                      [ΓA'IdA'] [ΓA'IdA'] (proj₁ X) [wwwIdAA'] (proj₂ X)
    in cast-Πᵗᵛ-aux {A} {B} {A'} {B'} {rA} {Γ} {e} {f}
                    [Γ] [A] [A'] (λ {Δ} {σ} → [UB] {Δ} {σ}) (λ {Δ} {σ} → [UB'] {Δ} {σ}) [A]ₜ [B]ₜ [A']ₜ [B']ₜ [Id] [e]ₜ [ΠAB] [f]ₜ
                    (Id-U-ΠΠᵗᵛ {A} {B} {A'} {B'} {rA} {Γ}
                               [Γ] [A] [A'] (λ {Δ} {σ} → [UB] {Δ} {σ}) (λ {Δ} {σ} → [UB'] {Δ} {σ}) [A]ₜ [B]ₜ [A']ₜ [B']ₜ)
                    (Id-U-ΠΠ-resᵗᵛ {wk1 A} {wk1d B} {wk1 A'} {wk1d B'}
                                   [ΓA'] [wA] [wA'] (λ {Δ} {σ} → [wwUA] {Δ} {σ} !) (λ {Δ} {σ} → [wwUA'] {Δ} {σ} !) [wA]ₜ [wB]ₜ [wA']ₜ [wB']ₜ [var0']ₜ [var1']ₜ)
                    [var]ₜ [var0']ₜ [var1']ₜ
  
