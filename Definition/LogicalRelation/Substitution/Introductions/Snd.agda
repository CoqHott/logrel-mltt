{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.Snd {{eqrel : EqRelSet}} where
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
open import Definition.LogicalRelation.Substitution.Introductions.Fst
open import Definition.LogicalRelation.Substitution.Introductions.Id
open import Definition.LogicalRelation.Substitution.Introductions.Pi
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Definition.LogicalRelation.Substitution.Introductions.Cast
open import Definition.LogicalRelation.Substitution.MaybeEmbed
open import Definition.LogicalRelation.Substitution.Introductions.Universe
open import Definition.LogicalRelation.Substitution.Weakening
open import Definition.LogicalRelation.Substitution.Introductions.Transp
open import Definition.LogicalRelation.Fundamental.Variable
open import Definition.LogicalRelation.Substitution.Irrelevance as S

open import Tools.Product
import Tools.PropositionalEquality as PE

lemma1 : ∀ {σ rA} A A' B e →
                   subst (liftSubst σ) B [
                        cast ⁰ (wk1 (subst σ A'))
                               (wk1 (subst σ A))
                               (Idsym (Univ rA ⁰) (wk1 (subst σ A)) (wk1 (subst σ A')) (fst (wk1 (subst σ e))))
                               (var 0)]↑
                   PE.≡
                     subst (liftSubst σ) (B [
                     cast ⁰ (wk1 A')
                            (wk1 A)
                            (Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e)))
                            (var 0)]↑)
lemma1 {σ} {rA} A A' B e = PE.trans (PE.cong (λ X → subst (liftSubst σ) B [ X ]↑)
  (PE.cong₃ (λ X Y Z → cast ⁰ X Y Z (var 0)) (PE.sym (Idsym-subst-lemma σ A')) (PE.sym (Idsym-subst-lemma σ A))
    (PE.trans (PE.cong₃ (λ X Y Z → Idsym (Univ rA ⁰) X Y (fst Z)) (PE.sym (Idsym-subst-lemma σ A)) (PE.sym (Idsym-subst-lemma σ A')) (PE.sym (Idsym-subst-lemma σ e)))
      (PE.sym (subst-Idsym (liftSubst σ) (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e)))))))
  (PE.sym (singleSubstLift↑ σ B _))


Id-U-ΠΠ-resᵗᵛ : ∀ {A B A' B' e rA Γ} ([Γ] : ⊩ᵛ Γ) →
        let l    = ∞
            lΠ = ⁰
            [UA] = maybeEmbᵛ {A = Univ rA _} [Γ] (Uᵛ emb< [Γ])
            Id-U-ΠΠ-res A A' B B' e =
              Π A' ^ rA ° ⁰ ▹ Id (U ⁰)
                        (B [ cast ⁰ (wk1 A') (wk1 A) (Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) ]↑)
                        B' ° ⁰ ° ⁰ ^ %
                        -- (Π (wk1 A') ^ rA ° ⁰ ▹ Id (U ⁰)
                        --     (wk1d B [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (var 1)) (var 0) ]↑)
                        --     (wk1d B') ° ⁰ ° ⁰ ^ %)

        in
           ([A] : Γ ⊩ᵛ⟨ l ⟩ A ^ [ rA , ι lΠ ] / [Γ])
           ([A'] : Γ ⊩ᵛ⟨ l ⟩ A' ^ [ rA , ι lΠ ] / [Γ])
           ([UB] : Γ ∙ A ^ [ rA , ι lΠ ] ⊩ᵛ⟨ l ⟩ Univ ! lΠ ^ [ ! , next lΠ ] / [Γ] ∙ [A])
           ([UB'] : Γ ∙ A' ^ [ rA , ι lΠ ] ⊩ᵛ⟨ l ⟩ Univ ! lΠ ^ [ ! , next lΠ ] / [Γ] ∙ [A'])
           ([A]ₜ : Γ ⊩ᵛ⟨ l ⟩ A ∷ Univ rA lΠ ^ [ ! , next lΠ ] / [Γ] / [UA])
           ([B]ₜ : Γ ∙ A ^ [ rA , ι lΠ ] ⊩ᵛ⟨ l ⟩ B ∷ Univ ! lΠ ^ [ ! , next lΠ ] / [Γ] ∙ [A] / (λ {Δ} {σ} → [UB] {Δ} {σ}))
           ([A']ₜ : Γ ⊩ᵛ⟨ l ⟩ A' ∷ Univ rA lΠ ^ [ ! , next lΠ ] / [Γ] / [UA])
           ([B']ₜ :  Γ ∙ A' ^ [ rA , ι lΠ ] ⊩ᵛ⟨ l ⟩ B' ∷ Univ ! lΠ ^ [ ! , next lΠ ] / [Γ] ∙ [A'] / (λ {Δ} {σ} → [UB'] {Δ} {σ}))
           ([Id] : Γ ⊩ᵛ⟨ l ⟩ Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ !) ^ [ % , ι ⁰ ] / [Γ])
           ([e]ₜ :  Γ ⊩ᵛ⟨ l ⟩ e ∷ Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° ⁰ ^ !) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰ ° ⁰ ^ !) ^ [ % , ι ⁰ ] / [Γ] / [Id]) →
           let [IdAA'] = Idᵛ {A = Univ rA ⁰} {t = A} {u = A'} [Γ] (λ {Δ} {σ} → [UA] {Δ} {σ}) [A]ₜ [A']ₜ
               [ΓA'] = _∙_ {A = A'} [Γ] [A']
               [wA'] = wk1ᵛ {A = A'} {F = A'} [Γ] [A'] [A']
           in
           ([var0]ₜ : Γ ∙ A' ^ [ rA , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ var 0 ∷ wk1 A' ^ [ rA , ι ⁰ ] / [ΓA'] / [wA'])
         →  Γ ⊩ᵛ⟨ ∞ ⟩ Id-U-ΠΠ-res  A A' B B' e ^ [ % , ι ⁰ ] / [Γ]
Id-U-ΠΠ-resᵗᵛ {A} {B} {A'} {B'} {e} {rA} {Γ}
        [Γ] [A] [A'] [UB] [UB'] [A]ₜ [B]ₜ [A']ₜ [B']ₜ [Id] [e]ₜ [var0]ₜ =
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
      [IdAA']ₜ = Idᵗᵛ {A = Univ rA ⁰} {t = A} {u = A'} [Γ] (λ {Δ} {σ} → [UA] {Δ} {σ}) [A]ₜ [A']ₜ (Uᵗᵛ [Γ])
      [IdAA'] = Idᵛ {A = Univ rA ⁰} {t = A} {u = A'} [Γ] (λ {Δ} {σ} → [UA] {Δ} {σ}) [A]ₜ [A']ₜ 
      [ΓId] = _∙_ {A = Id (Univ rA ⁰) A A'} [Γ] [IdAA']
      [wSProp] = Uᵛ {rU = %} ∞< [ΓA']
      [wA'] = wk1ᵗᵛ {F = A'} {G = A'} {lG = ⁰} [Γ] [A'] [A']ₜ
      [wA']' = wk1ᵛ {A = A'} {F = A'} [Γ] [A'] [A']
      [wA]' = wk1ᵛ {A = A} {F = A'} [Γ] [A'] [A]
      [wA] = wk1ᵗᵛ {F = A'} {G = A} {lG = ⁰} [Γ] [A'] [A]ₜ
      [wU⁰] = λ {Δ} {σ} r → Uᵛgen {rU = r} (<is≤ 0<1) ∞< [ΓA'] {Δ} {σ}
      [wUA'] = λ {Δ} {σ} r → maybeEmbᵛ {A = Univ r _ } [ΓA'] (λ {Δ} {σ} → Uᵛ emb< [ΓA'] {Δ} {σ}) {Δ} {σ}
      [wU¹] = λ {Δ} {σ} r → Uᵛ {rU = r} ∞< [ΓA'] {Δ} {σ}
      [wUA']ᵗ = Uᵗᵛ [ΓA']
      [wIdAA'] = Idᵛ {A = Univ rA ⁰} {t = wk1 A} {u = wk1 A'} [ΓA'] (λ {Δ} {σ} → [wUA'] {Δ} {σ} rA) [wA] [wA']
      [wIdA'A] = Idᵛ {A = Univ rA ⁰} {t = wk1 A'} {u = wk1 A} [ΓA'] (λ {Δ} {σ} → [wUA'] {Δ} {σ} rA) [wA'] [wA]
      [fst] = fstᵛ {A} {B} {A'} {B'} {e} {rA} {Γ} [Γ] [A] [A'] (λ {Δ} {σ} → [UB] {Δ} {σ}) (λ {Δ} {σ} → [UB'] {Δ} {σ}) [A]ₜ [B]ₜ [A']ₜ [B']ₜ [Id] [e]ₜ
      wfst = wk1Termᵛ {F = A'} {G = Id (Univ rA ⁰) A A'} {t = fst e} [Γ] [A'] [IdAA'] [fst]
   in Πirrᵛ {A'} {Id (U ⁰) (B [ cast ⁰ (wk1 A') (wk1 A) (Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) ]↑)
                                B'} [Γ] [A']
                                (Idᵛ {A = U ⁰} {t = B [ cast ⁰ (wk1 A') (wk1 A) (Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) ]↑}
                                  {u = B'} [ΓA'] (λ {Δ} {σ} → [UB'] {Δ} {σ})
                                (subst↑STerm {F = A'} {F' = A} {G = B}
                                         {t = cast ⁰ (wk1 A') (wk1 A) (Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0)}
                                         [Γ] [A'] [A] (λ {Δ} {σ} → [UB'] {Δ} {σ}) (λ {Δ} {σ} → [UB] {Δ} {σ}) [B]ₜ
                                         (castᵗᵛ {A = wk1 A'} {B = wk1 A} {t = var 0} {e = Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))}
                                                 [ΓA'] (λ {Δ} {σ} → [wUA'] {Δ} {σ} rA) [wA'] [wA] [wA']' [wA]' [var0]ₜ
                                                 (Idᵛ {A = Univ rA ⁰} {t = wk1 A'} {u = wk1 A} [ΓA'] (λ {Δ} {σ} → [wUA'] {Δ} {σ} rA) [wA'] [wA])
                                                 (IdSymᵗᵛ {A = Univ rA ⁰} {t = wk1 A} {u = wk1 A'} {e = fst (wk1 e)} [ΓA'] (λ {Δ} {σ} → [wU¹] {Δ} {σ} !)
                                                          (λ {Δ} {σ} → [wUA']ᵗ {Δ} {σ}) (λ {Δ} {σ} → [wUA'] {Δ} {σ} rA)
                                                          [wA] [wA'] [wIdAA'] [wIdA'A]
                                                          (S.irrelevanceTerm {A = Id (Univ rA ⁰) (wk1 A) (wk1 A')} {t = fst (wk1 e)}
                                                                                   [ΓA'] [ΓA'] (wk1ᵛ {A = Id (Univ rA ⁰) A A'} {F = A'} [Γ] [A'] [IdAA']) [wIdAA'] wfst) )))
                                [B']ₜ )


-- Valid snd term construction.
sndᵛ : ∀ {A B A' B' e rA Γ}
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
       →   let [ΓA'] = (_∙_ {Γ} {A'} [Γ]  [A'])
               [wA']' = wk1ᵛ {A = A'} {F = A'} [Γ] [A'] [A']
               [var0]ₜ : Γ ∙ A' ^ [ rA , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ var 0 ∷ wk1 A' ^ [ rA , ι ⁰ ] / [ΓA'] / [wA']'
               [var0]ₜ = proj₂ (fundamentalVar here [ΓA']) 
               [IdAA'] = Id-U-ΠΠ-resᵗᵛ {A} {B} {A'} {B'} {e} [Γ] [A] [A']
                                       (λ {Δ} {σ} → [UB] {Δ} {σ}) (λ {Δ} {σ} → [UB'] {Δ} {σ})
                                       [A]ₜ [B]ₜ [A']ₜ [B']ₜ [Id] [e]ₜ [var0]ₜ
           in Γ ⊩ᵛ⟨ l ⟩ snd e ∷ Π A' ^ rA ° ⁰ ▹ Id (U ⁰)
                        (B [ cast ⁰ (wk1 A') (wk1 A) (Idsym (Univ rA ⁰) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) ]↑)
                        B' ° ⁰ ° ⁰ ^ % ^ [ % , ι ⁰ ] / [Γ] / [IdAA']

sndᵛ  {A} {B} {A'} {B'} {e} {rA} {Γ}
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
          [ΓA'] = (_∙_ {Γ} {A'} [Γ]  [A'])
          [wA']' = wk1ᵛ {A = A'} {F = A'} [Γ] [A'] [A']
          [var0]ₜ : Γ ∙ A' ^ [ rA , ι ⁰ ] ⊩ᵛ⟨ ∞ ⟩ var 0 ∷ wk1 A' ^ [ rA , ι ⁰ ] / [ΓA'] / [wA']'
          [var0]ₜ = proj₂ (fundamentalVar here [ΓA']) 
          [IdAA'] = Id-U-ΠΠ-resᵗᵛ {A} {B} {A'} {B'} {e} [Γ] [A] [A']
                                 (λ {Δ} {σ} → [UB] {Δ} {σ}) (λ {Δ} {σ} → [UB'] {Δ} {σ})
                                 [A]ₜ [B]ₜ [A']ₜ [B']ₜ [Id] [e]ₜ [var0]ₜ
          [σIdAA'] = proj₁ ([IdAA'] ⊢Δ [σ])
          [σId] = proj₁ ([Id] ⊢Δ [σ])
          [σe] = proj₁ ([e]ₜ (⊢Δ) [σ])
          ⊢e = escapeTerm [σId] [σe]
          ⊢snd = sndⱼ {A = subst σ A} {A' = subst σ A'} {B = subst (liftSubst σ) B} {B' = subst (liftSubst σ) B'} {e = subst σ e}
                      ⊢Aₜ ⊢Bₜ ⊢A'ₜ ⊢B'ₜ ⊢e
          ⊢snd' = PE.subst (λ X → Δ ⊢ subst σ (snd e) ∷ Π _ ^ rA ° ⁰ ▹ Id (U ⁰) X _ ° ⁰ ° ⁰ ^ % ^ [ % , _ ]) (lemma1 A A' B e) ⊢snd
      in logRelIrr [σIdAA'] ⊢snd' ,
         λ {σ′} [σ]′ [σ≡σ′] → logRelIrrEq [σIdAA'] ⊢snd'
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
          ⊢snd′ = sndⱼ {A = subst σ′ A} {A' = subst σ′ A'} {B = subst (liftSubst σ′) B} {B' = subst (liftSubst σ′) B'} {e = subst σ′ e}
                      ⊢Aₜ′ ⊢Bₜ′ ⊢A'ₜ′ ⊢B'ₜ′ ⊢e′
          ⊢snd'′ = PE.subst (λ X → Δ ⊢ subst σ′ (snd e) ∷ Π _ ^ rA ° ⁰ ▹ Id (U ⁰) X _ ° ⁰ ° ⁰ ^ % ^ [ % , _ ]) (lemma1 A A' B e) ⊢snd′
          [σIdAA'≡σIdAA']′ = proj₂ ([IdAA'] ⊢Δ [σ]) [σ]′ [σ≡σ′]
          ⊢σIdAA'≡σIdAA'′ = escapeEq [σIdAA'] [σIdAA'≡σIdAA']′
      in conv ⊢snd'′ (≅-eq (≅-sym ⊢σIdAA'≡σIdAA'′))
