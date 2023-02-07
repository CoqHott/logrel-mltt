{-# OPTIONS --safe #-}

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
open import Definition.LogicalRelation.Substitution.Introductions.Fst
open import Definition.LogicalRelation.Substitution.Introductions.Snd
open import Definition.LogicalRelation.Substitution.Introductions.Pi
open import Definition.LogicalRelation.Substitution.Introductions.Lambda
open import Definition.LogicalRelation.Substitution.Introductions.Application
open import Definition.LogicalRelation.Substitution.Introductions.Cast
open import Definition.LogicalRelation.Substitution.Introductions.Id
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
  (wk1 (subst σ f) ∘ cast ⁰ (wk1 (subst σ A')) (wk1 (subst σ A)) (Idsym (Univ rA ⁰) (wk1 (subst σ A)) (wk1 (subst σ A')) (fst (wk1 (subst σ e)))) (var 0) ^ ⁰)
  PE.≡
  subst (repeat liftSubst (repeat liftSubst σ 1) 0) (wk1 f ∘ cast ⁰ (wk1 A') (wk1 A) (Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) ^ ⁰)
wk1f-cast-subst σ f A' A rA e = PE.cong₂ (λ X Y → X ∘ Y ^ ⁰) (PE.sym (Idsym-subst-lemma σ f))
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

snd-cast-subst : ∀ A A' rA B B' e → wk1 (Π A' ^ rA ° ⁰ ▹ Id (U ⁰) (B [ cast ⁰ (wk1 A') (wk1 A) (Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) ]↑) B' ° ⁰ ° ⁰ ^ %)
                                    PE.≡
                                      Π (wk1 A') ^ rA ° ⁰ ▹
                                        Id (U ⁰) (wk1d B [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (fst (wk1 (wk1 e)))) (var 0) ]↑)
                                                 (wk1d B') ° ⁰ ° ⁰ ^ %
snd-cast-subst A A' rA B B' e = PE.cong (λ BB → Π (wk1 A') ^ rA ° ⁰ ▹ Id (U ⁰) BB  (wk1d B') ° ⁰ ° ⁰ ^ %) (PE.trans (wk-β↑ B)
               (PE.cong₃ (λ X Y Z → wk1d B [ cast ⁰ X Y Z (var 0) ]↑) (PE.sym (wk1-wk≡lift-wk1 _ _)) (PE.sym (wk1-wk≡lift-wk1 _ _))
                         (PE.trans (wk-Idsym _ _ _ _ _) (PE.cong₃ (λ X Y Z → Idsym (Univ rA ⁰) X Y (fst Z)) (PE.sym (wk1-wk≡lift-wk1 _ _)) (PE.sym (wk1-wk≡lift-wk1 _ _)) (PE.sym (wk1-wk≡lift-wk1 _ _))))))


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

[wIdBB'eq] : ∀ A rA A' B B' e →
      Id (U ⁰)
       (wk1d (B [
        cast ⁰ (wk1 A') (wk1 A)
        (Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0)
        ]↑))
       (wk1d B') PE.≡  Id (U ⁰)
                              ((wk1d B) [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (fst (wk1 (wk1 e)))) (var 0) ]↑)
                              (wk1d B')
[wIdBB'eq] A rA A' B B' e =
  let
    x = PE.cong₃ (λ X Y Z → Idsym (Univ rA ⁰) X Y Z) (PE.sym (wk1-wk≡lift-wk1 _ A)) (PE.sym (wk1-wk≡lift-wk1 _ A')) (PE.sym (wk1-wk≡lift-wk1 _ (fst e)))
    x₀ = PE.trans (wk-Idsym _ (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))) x
    x₁ = PE.cong₃ (λ X Y Z → wk1d B [ cast ⁰ X Y Z (var 0) ]↑) (PE.sym (wk1-wk≡lift-wk1 _ A')) (PE.sym (wk1-wk≡lift-wk1 _ A)) x₀
  in
  PE.cong (λ X → Id (U ⁰) X (wk1d B')) (PE.trans (wk-β↑ B) x₁)

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
           ([Id] : Γ ⊩ᵛ⟨ l ⟩ Id (U lΠ) (Π A ^ rA ° lΠ ▹ B ° lΠ ° lΠ ^ !) (Π A' ^ rA ° lΠ  ▹ B' ° lΠ ° lΠ ^ !) ^ [ % , ι ⁰ ] / [Γ])
           ([e]ₜ : Γ ⊩ᵛ⟨ l ⟩ e ∷ Id (U lΠ) (Π A ^ rA ° lΠ ▹ B ° lΠ ° lΠ ^ !) (Π A' ^ rA ° lΠ  ▹ B' ° lΠ ° lΠ ^ !) ^ [ % , ι ⁰ ] / [Γ] / [Id])
           ([ΠAB] : Γ ⊩ᵛ⟨ l ⟩ Π A ^ rA ° lΠ ▹ B ° lΠ ° lΠ ^ ! ^ [ ! , ι lΠ ] / [Γ])
           ([f]ₜ : Γ ⊩ᵛ⟨ l ⟩ f ∷ Π A ^ rA ° lΠ ▹ B ° lΠ ° lΠ ^ ! ^ [ ! , ι lΠ ] / [Γ] / [ΠAB])           
           →
           let [ΓA'] = (_∙_ {Γ} {A'} [Γ]  [A'])
           in
           ([var]ₜ : Γ ∙ A' ^ [ rA , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ var 0 ∷ wk1 A' ^ [ rA , ι ⁰ ] / [ΓA'] / wk1ᵛ {A = A'} {F = A'} [Γ] [A'] [A'])
         → [ Γ ⊩ᵛ⟨ l ⟩ (cast lΠ (Π A ^ rA ° lΠ ▹ B ° lΠ ° lΠ ^ !) (Π A' ^ rA ° lΠ ▹ B' ° lΠ ° lΠ ^ !) e f) ≡
                       (lam A' ▹
                         (let a = cast lΠ (wk1 A') (wk1 A) (Idsym (Univ rA lΠ) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) in
                         cast lΠ (B [ a ]↑) B' ((snd (wk1 e)) ∘ (var 0) ^ ⁰) ((wk1 f) ∘ a ^ lΠ)) ^ ⁰)
                       ∷ Π A' ^ rA ° lΠ ▹ B' ° lΠ ° lΠ ^ ! ^ [ ! , ι lΠ ] / [Γ] ]

cast-Πᵗᵛ-aux {A} {B} {A'} {B'} {rA} {Γ} {e} {f}
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
      [wUA]ᵗ = Uᵗᵛ [ΓA']
      [IdAA']ₜ = Idᵗᵛ {A = Univ rA ⁰} {t = A} {u = A'} [Γ] (λ {Δ} {σ} → [UA] {Δ} {σ}) [A]ₜ [A']ₜ (Uᵗᵛ [Γ])
      [IdAA'] = Idᵛ {A = Univ rA ⁰} {t = A} {u = A'} [Γ] (λ {Δ} {σ} → [UA] {Δ} {σ}) [A]ₜ [A']ₜ
      [wA'] = wk1ᵗᵛ {F = Id (Univ rA ⁰) A A'} {G = A'} {lG = ⁰} [Γ] [IdAA'] [A']ₜ
      [wA']' = wk1ᵛ {A = A'} {F = Id (Univ rA ⁰) A A'} [Γ] [IdAA'] [A']
      [wA]' = wk1ᵛ {A = A} {F = Id (Univ rA ⁰) A A'} [Γ] [IdAA'] [A]
      [wA] = wk1ᵗᵛ {F = Id (Univ rA ⁰) A A'} {G = A} {lG = ⁰} [Γ] [IdAA'] [A]ₜ
      [wU¹] = λ {Δ} {σ} r → Uᵛ {rU = r} ∞< [ΓA'] {Δ} {σ}
      [w'A] = wk1ᵗᵛ {F = A'} {G = A} {lG = ⁰} [Γ] [A'] [A]ₜ
      [w'A]' = wk1ᵛ {A = A} {F = A'} [Γ] [A'] [A]
      [w'A]⁰ = wk1ᵛ {A = A} {F = A'} [Γ] [A'] [A]'
      [w'A'] = wk1ᵗᵛ {F = A'} {G = A'} {lG = ⁰} [Γ] [A'] [A']ₜ
      [w'A']' = wk1ᵛ {A = A'} {F = A'} [Γ] [A'] [A']
      [w'A']⁰ = wk1ᵛ {A = A'} {F = A'} [Γ] [A'] [A']'
      [wIdA'A] = Idᵛ {A = Univ rA ⁰} {t = wk1 A'} {u = wk1 A} [ΓA'] (λ {Δ} {σ} → [wUA] {Δ} {σ}) [w'A'] [w'A]
      [wIdAA'] = Idᵛ {A = Univ rA ⁰} {t = wk1 A} {u = wk1 A'} [ΓA'] (λ {Δ} {σ} → [wUA] {Δ} {σ}) [w'A] [w'A']
      [wIdAA']ᵗ = Idᵗᵛ {A = Univ rA ⁰} {t = wk1 A} {u = wk1 A'} [ΓA'] (λ {Δ} {σ} → [wUA] {Δ} {σ}) [w'A] [w'A'] (λ {Δ} {σ} → Uᵗᵛ [ΓA'] {Δ} {σ})
      [wIdAA']ₜ = Idᵗᵛ {A = Univ rA ⁰} {t = wk1 A} {u = wk1 A'} [ΓA'] (λ {Δ} {σ} → [wUA] {Δ} {σ}) [w'A] [w'A'] (λ {Δ} {σ} → Uᵗᵛ [ΓA'] {Δ} {σ})
      [fst] = fstᵛ {A} {B} {A'} {B'} {e} [Γ] [A] [A'] (λ {Δ} {σ} → [UB] {Δ} {σ}) (λ {Δ} {σ} → [UB'] {Δ} {σ}) [A]ₜ [B]ₜ [A']ₜ [B']ₜ [Id] [e]ₜ
      [wfst] = wk1Termᵛ {F = A'} {G = Id (Univ rA ⁰) A A'} {t = fst e} [Γ] [A'] [IdAA'] [fst]
      [wfst]' = S.irrelevanceTerm {A = Id (Univ rA ⁰) (wk1 A) (wk1 A')} {t = fst (wk1 e)}
                                  [ΓA'] [ΓA'] (wk1ᵛ {A = Id (Univ rA ⁰) A A'} {F = A'} [Γ] [A'] [IdAA']) [wIdAA'] [wfst]
      [wfste] : Γ ∙ A' ^ [ rA , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e)) ∷ Id (Univ rA ⁰) (wk1 A') (wk1 A) ^ [ % , ι ⁰ ] / [ΓA'] / [wIdA'A]
      [wfste] = IdSymᵗᵛ {A = Univ rA ⁰} {t = wk1 A} {u = wk1 A'} {e = fst (wk1 e)} [ΓA'] (λ {Δ} {σ} → [wU¹] {Δ} {σ} !)
                       (λ {Δ} {σ} → [wUA]ᵗ {Δ} {σ}) (λ {Δ} {σ} → [wUA] {Δ} {σ})
                       [w'A] [w'A'] [wIdAA'] [wIdA'A] [wfst]'
      cast-Π-a A A' e = cast ⁰ (wk1 A') (wk1 A) (Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0)
      [cast-Π-a] : Γ ∙ A' ^ [ rA , ι ⁰ ]  ⊩ᵛ⟨ ∞ ⟩ cast-Π-a A A' e ∷ wk1 A ^ [ rA , ι ⁰ ] / [ΓA'] / wk1ᵛ {A = A} {F = A'} [Γ] [A'] [A]
      [cast-Π-a] = castᵗᵛ {wk1 A'} {wk1 A} {t = var 0} {e = Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))} [ΓA']
                          (λ {Δ} {σ} → [wUA] {Δ} {σ}) [w'A'] [w'A]
                         (wk1ᵛ {A = A'} {F = A'} [Γ] [A'] [A'])   (wk1ᵛ {A = A} {F = A'} [Γ] [A'] [A])
                         [var]ₜ [wIdA'A] [wfste]
      B[cast-Π-a]↑ₜ = subst↑STerm {F = A'} {F' = A} {G = B} {t = cast-Π-a A A' e} [Γ] [A'] [A]
                                  (λ {Δ} {σ} → [UB'] {Δ} {σ}) (λ {Δ} {σ} → [UB] {Δ} {σ}) [B]ₜ [cast-Π-a]
      [f°cast-Π-a] = appᵛ↑ {F = A} {F' = A'} {G = B} {t = wk1 f} {u = cast-Π-a A A' e} (≡is≤ PE.refl) (≡is≤ PE.refl) [Γ] [A] [A'] [B] [ΠAB]
                          (wk1Termᵛ {F = A'} {G =  Π A ^ rA ° ⁰ ▹ B ° ⁰ ° lΠ ^ !} {t = f} [Γ] [A'] [ΠAB] [f]ₜ)
                          [cast-Π-a]
      [wIdBB'] : Γ ∙ A' ^ [ rA , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ Id (U ⁰) (B [ cast-Π-a A A' e ]↑) B' ^ [ % , ι ⁰ ] / [ΓA']
      [wIdBB'] = Idᵛ {A = Univ ! ⁰} {t = B [ cast-Π-a A A' e ]↑} {u = B'} [ΓA'] (λ {Δ} {σ} → [UB'] {Δ} {σ})
                     B[cast-Π-a]↑ₜ [B']ₜ
      [snd] = sndᵛ {A} {B} {A'} {B'} {e} [Γ] [A] [A'] (λ {Δ} {σ} → [UB] {Δ} {σ}) (λ {Δ} {σ} → [UB'] {Δ} {σ}) [A]ₜ [B]ₜ [A']ₜ [B']ₜ [Id] [e]ₜ
      [var0]ₜ : Γ ∙ A' ^ [ rA , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ var 0 ∷ wk1 A' ^ [ rA , ι ⁰ ] / [ΓA'] / [w'A']'
      [var0]ₜ = proj₂ (fundamentalVar here [ΓA']) 
      Id-U-ΠΠ-res A A' B B' e =
              Π A' ^ rA ° ⁰ ▹ Id (U ⁰)
                        (B [ cast ⁰ (wk1 A') (wk1 A) (Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) ]↑)
                        B' ° ⁰ ° ⁰ ^ %
      [Id-U-ΠΠ-res-end] = Id-U-ΠΠ-resᵗᵛ {A} {B} {A'} {B'} {e} [Γ] [A] [A']
                                       (λ {Δ} {σ} → [UB] {Δ} {σ}) (λ {Δ} {σ} → [UB'] {Δ} {σ})
                                       [A]ₜ [B]ₜ [A']ₜ [B']ₜ [Id] [e]ₜ [var0]ₜ
      [wsnd] = wk1Termᵛ {F = A'} {G = Id-U-ΠΠ-res A A' B B' e} {t = snd e} [Γ] [A'] [Id-U-ΠΠ-res-end] [snd]
      [wId-U-ΠΠ-res-end] = wk1ᵛ {A = Id-U-ΠΠ-res A A' B B' e} {F = A'} [Γ] [A'] [Id-U-ΠΠ-res-end]
      [sndType]' = S.irrelevance′ {A = wk1 (Π A' ^ rA ° ⁰ ▹ Id (U ⁰) (B [ cast ⁰ (wk1 A') (wk1 A) (Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) ]↑) B' ° ⁰ ° ⁰ ^ %)}
                                  {A′ = Π (wk1 A') ^ rA ° ⁰ ▹
                                        Id (U ⁰) ((wk1d B) [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (fst (wk1 (wk1 e)))) (var 0) ]↑)
                                                 (wk1d B') ° ⁰ ° ⁰ ^ %}
                                  (snd-cast-subst A A' rA B B' e) [ΓA'] [ΓA']
                                  [wId-U-ΠΠ-res-end]
      [snd]' = S.irrelevanceTerm′ {A = wk1 (Π A' ^ rA ° ⁰ ▹ Id (U ⁰) (B [ cast ⁰ (wk1 A') (wk1 A) (Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) ]↑) B' ° ⁰ ° ⁰ ^ %)}
                                  {A′ = Π (wk1 A') ^ rA ° ⁰ ▹
                                        Id (U ⁰) ((wk1d B) [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (fst (wk1 (wk1 e)))) (var 0) ]↑)
                                                 (wk1d B') ° ⁰ ° ⁰ ^ %}
                                  {t = snd (wk1 e)}
                                  (snd-cast-subst A A' rA B B' e) PE.refl [ΓA'] [ΓA']
                                  [wId-U-ΠΠ-res-end]
                                  [sndType]' [wsnd]
      [wwIdBB'] = wk1dᵛ {F = A'} {F' = A'} {G = Id (U ⁰) (B [ cast-Π-a A A' e ]↑) B'} [Γ] [A'] [A'] (λ {Δ} {σ} → [wIdBB'] {Δ} {σ})
      [wsnde] : Γ ∙ A' ^ [ rA , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ (snd (wk1 e)) ∘ (var 0) ^ ⁰ ∷ Id (U ⁰) (B [ cast-Π-a A A' e ]↑) B' ^ [ % , ι ⁰ ] / [ΓA'] / [wIdBB']
      [wsnde] = let X = appirrᵛ {F = wk1 A'}
                                {G = Id (U ⁰) ((wk1d B) [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (fst (wk1 (wk1 e)))) (var 0) ]↑) (wk1d B')}
                                {t = snd (wk1 e)} {u = var 0}
                                [ΓA'] [w'A']' (S.irrelevance′ {A = Id (U ⁰) (wk1d (B [ cast ⁰ (wk1 A') (wk1 A) (Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0)  ]↑)) (wk1d B')}
                                                              {A′ = Id (U ⁰) ((wk1d B) [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (fst (wk1 (wk1 e)))) (var 0) ]↑) (wk1d B')}
                                                               ([wIdBB'eq] A rA A' B B' e) ( _∙_ {A = wk1 A'} (_∙_ {A = A'} [Γ] [A']) (wk1ᵛ {A = A'} {F = A'} [Γ] [A'] [A']))
                                                                                           ( _∙_ {A = wk1 A'} (_∙_ {A = A'} [Γ] [A']) (wk1ᵛ {A = A'} {F = A'} [Γ] [A'] [A'])) [wwIdBB'])
                                  [sndType]' [snd]'
                                  [var]ₜ
                in S.irrelevanceTerm′ {A = (Id (U ⁰) ((wk1d B) [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (fst (wk1 (wk1 e)))) (var 0) ]↑)
                                                      (wk1d B'))  [ var 0 ]}
                                       {A′ = Id (Univ ! ⁰) (B [ cast-Π-a A A' e ]↑) B'}
                                       {t = (snd (wk1 e)) ∘ (var 0) ^ ⁰}
                                       (Id-cast-subst A A' rA B B' e) PE.refl [ΓA'] [ΓA']
                                       (substS {wk1 A'}
                                               {Id (U ⁰) (wk1d B [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (fst (wk1 (wk1 e)))) (var 0) ]↑)
                                                         (wk1d B')}
                                               {var 0} [ΓA'] [w'A']'
                                               (S.irrelevance′ {A = Id (U ⁰) (wk1d (B [ cast ⁰ (wk1 A') (wk1 A) (Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0)  ]↑)) (wk1d B')}
                                                              {A′ = Id (U ⁰) ((wk1d B) [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (fst (wk1 (wk1 e)))) (var 0) ]↑) (wk1d B')}
                                                               ([wIdBB'eq] A rA A' B B' e) ( _∙_ {A = wk1 A'} (_∙_ {A = A'} [Γ] [A']) (wk1ᵛ {A = A'} {F = A'} [Γ] [A'] [A']))
                                                                                           ( _∙_ {A = wk1 A'} (_∙_ {A = A'} [Γ] [A']) (wk1ᵛ {A = A'} {F = A'} [Γ] [A'] [A'])) [wwIdBB']) [var]ₜ )
                                       [wIdBB'] X
      cast-Π-res A A' B B' e f =
                 cast ⁰ (B [ cast-Π-a A A' e ]↑) B' ((snd (wk1 e)) ∘ (var 0) ^ ⁰) ((wk1 f) ∘ cast-Π-a A A' e ^ ⁰)
      [cast-Π-res] : Γ ⊩ᵛ⟨ ∞ ⟩ lam A' ▹ cast-Π-res A A' B B' e f ^ ⁰ ∷ Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ° ⁰  ^ ! ^ [ ! , ι ⁰ ] / [Γ] / [ΠAB']
      [cast-Π-res] = lamᵛ {F = A'} {G = B'} {t = cast-Π-res A A' B B' e f} (≡is≤ PE.refl) (≡is≤ PE.refl) [Γ] [A'] [B']
                          (castᵗᵛ {B [ cast-Π-a A A' e ]↑} {B'} {t = (wk1 f) ∘ cast-Π-a A A' e ^ ⁰} {e = (snd (wk1 e)) ∘ (var 0) ^ ⁰}
                                  [ΓA'] (λ {Δ} {σ} → [UB'] {Δ} {σ}) B[cast-Π-a]↑ₜ [B']ₜ (subst↑S {F = A'} {G = B} {F' = A} [Γ] [A'] [A] [B] [cast-Π-a]) [B']
                                  [f°cast-Π-a] [wIdBB'] [wsnde])
      [cast-Π] : Γ ⊩ᵛ cast ⁰ (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ !) e f ⇒ lam A' ▹ cast-Π-res A A' B B' e f ^ ⁰ ∷ Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ ! ^ ι ⁰ / [Γ]
      [cast-Π] = λ {Δ} {σ} ⊢Δ [σ] → let Aσ  = ⊢AΔ {Δ} {σ} ⊢Δ [σ]
                                        Bσ  = ⊢BΔ {Δ ∙ subst σ A ^ _} {liftSubst σ} (⊢Δ ∙ ⊢A {Δ} {σ} ⊢Δ [σ]) ([liftσ] {Δ} {σ} ⊢Δ [σ])
                                        A'σ = ⊢A'Δ {Δ} {σ} ⊢Δ [σ]
                                        B'σ = ⊢B'Δ {Δ ∙ subst σ A' ^ _} {liftSubst σ} (⊢Δ ∙ ⊢A' {Δ} {σ} ⊢Δ [σ]) ([liftσ'] {Δ} {σ} ⊢Δ [σ])
                                        eσ  = ⊢e {Δ} {σ} ⊢Δ [σ]
                                        fσ  = ⊢f {Δ} {σ} ⊢Δ [σ]
                                        X : Δ ⊢ (cast ⁰ (Π (subst σ A) ^ rA ° ⁰ ▹ (subst (liftSubst σ) B) ° ⁰ ° ⁰ ^ !) (Π (subst σ A') ^ rA ° ⁰ ▹ (subst (liftSubst σ) B') ° ⁰ ° ⁰ ^ !) (subst σ e) (subst σ f))
                                                  ⇒ lam (subst σ A') ▹ cast-Π-res (subst σ A) (subst σ A') (subst (liftSubst σ) B) (subst (liftSubst σ) B') (subst σ e) (subst σ f) ^ ⁰
                                                  ∷ Π (subst σ A') ^ rA ° ⁰ ▹ (subst (liftSubst σ) B') ° ⁰  ° ⁰ ^ ! ^ ι ⁰
                                        X = cast-Π {Δ} {subst σ A} {subst σ A'} {rA} {subst (liftSubst σ) B} {subst (liftSubst σ) B'} {subst σ e} {subst σ f} Aσ Bσ A'σ B'σ eσ fσ
                                     in PE.subst (λ BB → Δ ⊢ subst σ (cast ⁰ (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ !) e f) ⇒ lam subst σ A' ▹ BB ^ ⁰ ∷ subst σ (Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ !) ^ ι ⁰ )
                                                 (PE.cong₄ (cast ⁰)
                                                           (B-cast-subst  σ A' A rA e B)
                                                           PE.refl (PE.cong₂ (λ X Y → snd X ∘ Y ^ ⁰) (PE.sym (Idsym-subst-lemma σ e)) PE.refl) (wk1f-cast-subst σ f A' A rA e)) X
      [id] , [eq] = redSubstTermᵛ {Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ !} {cast ⁰ (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ !) e f} {lam A' ▹ cast-Π-res A A' B B' e f ^ ⁰}
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
           ([Id] : Γ ⊩ᵛ⟨ l ⟩ Id (U lΠ) (Π A ^ rA ° lΠ ▹ B ° lΠ ° lΠ ^ !) (Π A' ^ rA ° lΠ  ▹ B' ° lΠ ° lΠ ^ !) ^ [ % , ι ⁰ ] / [Γ])
           ([e]ₜ : Γ ⊩ᵛ⟨ l ⟩ e ∷ Id (U lΠ) (Π A ^ rA ° lΠ ▹ B ° lΠ ° lΠ ^ !) (Π A' ^ rA ° lΠ  ▹ B' ° lΠ ° lΠ ^ !) ^ [ % , ι ⁰ ] / [Γ] / [Id])
           ([ΠAB] : Γ ⊩ᵛ⟨ l ⟩ Π A ^ rA ° lΠ ▹ B ° lΠ ° lΠ ^ ! ^ [ ! , ι lΠ ] / [Γ])
           ([f]ₜ : Γ ⊩ᵛ⟨ l ⟩ f ∷ Π A ^ rA ° lΠ ▹ B ° lΠ ° lΠ ^ ! ^ [ ! , ι lΠ ] / [Γ] / [ΠAB]) →
           [ Γ ⊩ᵛ⟨ l ⟩ (cast lΠ (Π A ^ rA ° lΠ ▹ B ° lΠ ° lΠ ^ !) (Π A' ^ rA ° lΠ ▹ B' ° lΠ ° lΠ ^ !) e f) ≡
                       (lam A' ▹
                         (let a = cast lΠ (wk1 A') (wk1 A) (Idsym (Univ rA lΠ) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) in
                         cast lΠ (B [ a ]↑) B' ((snd (wk1 e)) ∘ (var 0) ^ ⁰) ((wk1 f) ∘ a ^ ⁰)) ^ ⁰)
                       ∷ Π A' ^ rA ° lΠ ▹ B' ° lΠ ° lΠ ^ ! ^ [ ! , ι lΠ ] / [Γ] ]

abstract

  cast-Πᵗᵛ {A} {B} {A'} {B'} {rA} {Γ} {e} {f}
           [Γ] [A] [A'] [UB] [UB'] [A]ₜ [B]ₜ [A']ₜ [B']ₜ [Id] [e]ₜ [ΠAB] [f]ₜ =
    let l = ∞
        lΠ = ⁰
        [ΓA'] = (_∙_ {Γ} {A'} [Γ]  [A'])
        [var]ₜ : Γ ∙ A' ^ [ rA , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ var 0 ∷ wk1 A' ^ [ rA , ι ⁰ ] / [ΓA'] / wk1ᵛ {A = A'} {F = A'} [Γ] [A'] [A']
        [var]ₜ = proj₂ (fundamentalVar here [ΓA'])
    in cast-Πᵗᵛ-aux {A} {B} {A'} {B'} {rA} {Γ} {e} {f}
                    [Γ] [A] [A'] (λ {Δ} {σ} → [UB] {Δ} {σ}) (λ {Δ} {σ} → [UB'] {Δ} {σ}) [A]ₜ [B]ₜ [A']ₜ [B']ₜ [Id] [e]ₜ [ΠAB] [f]ₜ
                    [var]ₜ
                   
