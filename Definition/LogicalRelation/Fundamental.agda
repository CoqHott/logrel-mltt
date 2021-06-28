{-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Fundamental {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped hiding (tt)
open import Definition.Untyped.Properties
open import Definition.Typed 
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Substitution.Conversion
open import Definition.LogicalRelation.Substitution.Reduction
open import Definition.LogicalRelation.Substitution.Reflexivity
open import Definition.LogicalRelation.Substitution.ProofIrrelevance
open import Definition.LogicalRelation.Substitution.MaybeEmbed
open import Definition.LogicalRelation.Substitution.Introductions.Nat
open import Definition.LogicalRelation.Substitution.Introductions.Natrec
open import Definition.LogicalRelation.Substitution.Introductions.Empty
open import Definition.LogicalRelation.Substitution.Introductions.Emptyrec
open import Definition.LogicalRelation.Substitution.Introductions.Universe
open import Definition.LogicalRelation.Substitution.Introductions.Pi
open import Definition.LogicalRelation.Substitution.Introductions.Sigma
open import Definition.LogicalRelation.Substitution.Introductions.Id
open import Definition.LogicalRelation.Substitution.Introductions.IdUPiPi
open import Definition.LogicalRelation.Substitution.Introductions.Cast
open import Definition.LogicalRelation.Substitution.Introductions.CastPi
open import Definition.LogicalRelation.Substitution.Introductions.IdPi
open import Definition.LogicalRelation.Substitution.Introductions.Lambda
open import Definition.LogicalRelation.Substitution.Introductions.Application
open import Definition.LogicalRelation.Substitution.Introductions.Pair
open import Definition.LogicalRelation.Substitution.Introductions.Fst
open import Definition.LogicalRelation.Substitution.Introductions.Snd
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Definition.LogicalRelation.Substitution.Introductions.Transp
open import Definition.LogicalRelation.Substitution.Introductions.IdRefl
open import Definition.LogicalRelation.Fundamental.Variable
import Definition.LogicalRelation.Substitution.ProofIrrelevance as PI
import Definition.LogicalRelation.Substitution.Irrelevance as S
open import Definition.LogicalRelation.Substitution.Weakening

open import Tools.Product
open import Tools.Unit
open import Tools.Nat
import Tools.PropositionalEquality as PE

mutual
  -- Fundamental theorem for contexts.
  valid : ∀ {Γ} → ⊢ Γ → ⊩ᵛ Γ
  valid ε = ε
  valid (⊢Γ ∙ A) = let [Γ] , [A] = fundamental A in [Γ] ∙ [A]


  -- Fundamental theorem for types.
  fundamental : ∀ {Γ A rA} (⊢A : Γ ⊢ A ^ rA) → Σ (⊩ᵛ Γ) (λ [Γ] → Γ ⊩ᵛ⟨ ∞ ⟩ A ^ rA / [Γ])
  fundamental (Uⱼ x) = valid x , maybeEmbᵛ {A = Univ _ _} (valid x) (Uᵛ ∞< (valid x))
  fundamental (univ {A} ⊢A) with fundamentalTerm ⊢A
  fundamental (univ {A} ⊢A) | [Γ] , [U] , [A] =
    [Γ] , maybeEmbᵛ {A = A} [Γ] (univᵛ {A} [Γ] (≡is≤ PE.refl) [U] [A])

  -- Fundamental theorem for type equality.
  fundamentalEq : ∀{Γ A B rA} → Γ ⊢ A ≡ B ^ rA
    → ∃  λ ([Γ] : ⊩ᵛ Γ)
    → ∃₂ λ ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ rA / [Γ]) ([B] : Γ ⊩ᵛ⟨ ∞ ⟩ B ^ rA / [Γ])
    → Γ ⊩ᵛ⟨ ∞ ⟩ A ≡ B ^ rA / [Γ] / [A]

  fundamentalEq (univ {A} {B} x) with fundamentalTermEq x
  fundamentalEq (univ {A} {B} x) | [Γ] , modelsTermEq [U] [t] [u] [t≡u] =
    let [A] = maybeEmbᵛ {A = A} [Γ] (univᵛ {A} [Γ] (≡is≤ PE.refl) [U] [t])
        [B] = maybeEmbᵛ {A = B} [Γ] (univᵛ {B} [Γ] (≡is≤ PE.refl) [U] [u])
    in  [Γ] , [A] , [B]
    ,   (λ ⊢Δ [σ] → univEqEq (proj₁ ([U] ⊢Δ [σ]))
                             (proj₁ ([A] ⊢Δ [σ]))
                             ([t≡u] ⊢Δ [σ]))
  fundamentalEq (refl D) =
    let [Γ] , [B] = fundamental D
    in  [Γ] , [B] , [B] , (λ ⊢Δ [σ] → reflEq (proj₁ ([B] ⊢Δ [σ])))
  fundamentalEq (sym A≡B) with fundamentalEq A≡B
  fundamentalEq (sym A≡B) | [Γ] , [B] , [A] , [B≡A] =
    [Γ] , [A] , [B]
        , (λ ⊢Δ [σ] → symEq (proj₁ ([B] ⊢Δ [σ]))
                            (proj₁ ([A] ⊢Δ [σ]))
                            ([B≡A] ⊢Δ [σ]))
  fundamentalEq (trans {A} {B₁} {B} A≡B₁ B₁≡B)
    with fundamentalEq A≡B₁ | fundamentalEq B₁≡B
  fundamentalEq (trans {A} {B₁} {B} A≡B B≡C) | [Γ] , [A] , [B₁] , [A≡B₁]
    | [Γ]₁ , [B₁]₁ , [B] , [B₁≡B] =
      [Γ] , [A] , S.irrelevance {A = B} [Γ]₁ [Γ] [B]
          , (λ ⊢Δ [σ] →
               let [σ]′ = S.irrelevanceSubst [Γ] [Γ]₁ ⊢Δ ⊢Δ [σ]
               in  transEq (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([B₁] ⊢Δ [σ]))
                           (proj₁ ([B] ⊢Δ [σ]′)) ([A≡B₁] ⊢Δ [σ])
                           (irrelevanceEq (proj₁ ([B₁]₁ ⊢Δ [σ]′))
                                          (proj₁ ([B₁] ⊢Δ [σ]))
                                          ([B₁≡B] ⊢Δ [σ]′)))

  -- Fundamental theorem for terms.
  fundamentalTerm : ∀{Γ A rA t} → Γ ⊢ t ∷ A ^ rA
    → ∃ λ ([Γ] : ⊩ᵛ Γ)
    → ∃ λ ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ rA / [Γ])
    → Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ rA / [Γ] / [A]

  fundamentalTerm (ℕⱼ x) = valid x , maybeEmbᵛ {A = Univ _ _} (valid x) (Uᵛ emb< (valid x)) ,  maybeEmbTermᵛ {A = Univ _ _} {t = ℕ} (valid x) (Uᵛ emb< (valid x)) (ℕᵗᵛ (valid x))
  fundamentalTerm (Emptyⱼ {l} ⊢Γ) = let [Γ] = valid ⊢Γ
                                        [U] = Uᵛ (proj₂ (levelBounded _)) [Γ]
                                    in [Γ] , maybeEmbᵛ {A = Univ _ _} [Γ] [U] , maybeEmbTermᵛ {A = Univ _ _} {t = Empty} [Γ] [U] (Emptyᵗᵛ {ll = l} [Γ] (proj₂ (levelBounded _)))
  fundamentalTerm (Πⱼ_▹_▹_▹_ {F} {rF} {lF} {G} {lG} {rΠ} {lΠ} lF< lG< ⊢F ⊢G)
    with fundamentalTerm ⊢F | fundamentalTerm ⊢G
  ... | [Γ] , [UF] , [F]ₜ | [Γ]₁ ∙ [F] , [UG] , [G]ₜ =
    let [UF]′ = maybeEmbᵛ {A = Univ rF _} [Γ]₁ (Uᵛ (proj₂ (levelBounded lF)) [Γ]₁)
        [UΠ]  = maybeEmbᵛ {A = Univ rΠ _} [Γ]₁ (Uᵛ (proj₂ (levelBounded lΠ)) [Γ]₁)
        [F]′  = maybeEmbᵛ {A = F} [Γ]₁ [F]
        [UG]′ : _ ⊩ᵛ⟨ ∞ ⟩ Univ rΠ lG ^ [ ! , next lG ] / _∙_ {A = F} [Γ]₁ [F]′
        [UG]′ = S.irrelevance {A = Univ rΠ lG} (_∙_ {A = F} [Γ]₁ [F]) (_∙_ {A = F} [Γ]₁ [F]′) (λ {Δ} {σ} → [UG] {Δ} {σ})
        [F]ₜ′ = S.irrelevanceTerm {A = Univ rF _} {t = F} [Γ] [Γ]₁ [UF] [UF]′ [F]ₜ
        [G]ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = G} (_∙_ {A = F} [Γ]₁ [F]) (_∙_ {A = F} [Γ]₁ [F]′) (λ {Δ} {σ} → [UG] {Δ} {σ}) (λ {Δ} {σ} → [UG]′ {Δ} {σ}) [G]ₜ
    in  [Γ]₁ , [UΠ] 
    , 
      Πᵗᵛ {F} {G} {rF} {lF} {lG} {rΠ} {lΠ} lF< lG< [Γ]₁ [F]′ (λ {Δ} {σ} → [UG]′ {Δ} {σ}) [F]ₜ′ [G]ₜ′
  fundamentalTerm (∃ⱼ_▹_ {F} {G} {l} ⊢F ⊢G)
    with fundamentalTerm ⊢F | fundamentalTerm ⊢G
  ... | [Γ] , [UF] , [F]ₜ | [Γ]₁ ∙ [F] , [UG] , [G]ₜ =
    let [UF]′ = maybeEmbᵛ {A = SProp _} [Γ]₁ (Uᵛ (proj₂ (levelBounded l)) [Γ]₁)
        [UΠ]  = maybeEmbᵛ {A = SProp _} [Γ]₁ (Uᵛ (proj₂ (levelBounded l)) [Γ]₁)
        [F]′  = maybeEmbᵛ {A = F} [Γ]₁ [F]
        [UG]′ : _ ⊩ᵛ⟨ ∞ ⟩ SProp l ^ [ ! , next l ] / _∙_ {A = F} [Γ]₁ [F]′
        [UG]′ = S.irrelevance {A = Univ % l} (_∙_ {A = F} [Γ]₁ [F]) (_∙_ {A = F} [Γ]₁ [F]′) (λ {Δ} {σ} → [UG] {Δ} {σ})
        [F]ₜ′ = S.irrelevanceTerm {A = SProp _} {t = F} [Γ] [Γ]₁ [UF] [UF]′ [F]ₜ
        [G]ₜ′ = S.irrelevanceTerm {A = SProp _} {t = G} (_∙_ {A = F} [Γ]₁ [F]) (_∙_ {A = F} [Γ]₁ [F]′) (λ {Δ} {σ} → [UG] {Δ} {σ}) (λ {Δ} {σ} → [UG]′ {Δ} {σ}) [G]ₜ
    in  [Γ]₁ , [UΠ] 
    , 
      ∃ᵗᵛ {F} {G} {l} [Γ]₁ [F]′ (λ {Δ} {σ} → [UG]′ {Δ} {σ}) [F]ₜ′ [G]ₜ′

  fundamentalTerm (Idⱼ {A} {l} {t} {u} ⊢A ⊢t ⊢u)
    with fundamentalTerm ⊢A | fundamentalTerm ⊢t | fundamentalTerm ⊢u
  ... | [Γ] , [UA] , [A]ₜ | [Γt] , [At] , [t]ₜ | [Γu] , [Au] , [u]ₜ =
    let [SProp] = maybeEmbᵛ {A = SProp _} [Γu] (Uᵛ (proj₂ (levelBounded l)) [Γu])
        [t]ₜ′ = S.irrelevanceTerm {A = A} {t = t} [Γt] [Γu] [At] [Au] [t]ₜ
    in [Γu] , [SProp] , Idᵗᵛ {A = A} {t = t} {u = u } [Γu] [Au] [t]ₜ′ [u]ₜ

  fundamentalTerm (var ⊢Γ x∷A) = valid ⊢Γ , fundamentalVar x∷A (valid ⊢Γ)
  fundamentalTerm (lamⱼ {F} {r} {l} {rF} {lF} {G} {lG} {t} lF< lG< ⊢F ⊢t)
    with fundamental ⊢F | fundamentalTerm ⊢t
  ... | [Γ] , [F] | [Γ]₁ , [G] , [t] =
    let [G]′ = S.irrelevance {A = G} [Γ]₁ ([Γ] ∙ [F]) [G]
        [t]′ = S.irrelevanceTerm {A = G} {t = t} [Γ]₁ ([Γ] ∙ [F]) [G] [G]′ [t]
    in  [Γ] , Πᵛ {F} {G} lF< lG< [Γ] [F] [G]′
    ,   lamᵛ {F} {G} {rF} {lF} {lG} {l} {r} {t} lF< lG< [Γ] [F] [G]′ [t]′
  fundamentalTerm (_∘ⱼ_ {g} {a} {F} {rF} {lF} {G} {lG} {r} {l} Dt Du)
    with fundamentalTerm Dt | fundamentalTerm Du
  ... | [Γ] , [ΠFG] , [t] | [Γ]₁ , [F] , [u] =
    let [ΠFG]′ = S.irrelevance {A = Π F ^ rF ° lF ▹ G ° lG } [Γ] [Γ]₁ [ΠFG]
        [t]′ = S.irrelevanceTerm {A = Π F ^ rF ° lF ▹ G ° lG} {t = g} [Γ] [Γ]₁ [ΠFG] [ΠFG]′ [t]
        [G[t]] = substSΠ {F} {G} {a} [Γ]₁ [F] [ΠFG]′ [u]
        [t∘u] = appᵛ {F} {G} {rF} {lF} {lG} {r} {l} {g} {a} [Γ]₁ [F] [ΠFG]′ [t]′ [u]
    in  [Γ]₁ , [G[t]] , [t∘u]
  fundamentalTerm (zeroⱼ x) = valid x , ℕᵛ (valid x) , zeroᵛ {l = ∞} (valid x)
  fundamentalTerm (sucⱼ {n} t) with fundamentalTerm t
  fundamentalTerm (sucⱼ {n} t) | [Γ] , [ℕ] , [n] =
    [Γ] , [ℕ] , sucᵛ {n = n} [Γ] [ℕ] [n]
  fundamentalTerm (natrecⱼ {G} {rG} {lG} {s} {z} {n} ⊢G ⊢z ⊢s ⊢n)
    with fundamental ⊢G | fundamentalTerm ⊢z | fundamentalTerm ⊢s
       | fundamentalTerm ⊢n
  ... | [Γ] , [G] | [Γ]₁ , [G₀] , [z] | [Γ]₂ , [G₊] , [s] | [Γ]₃ , [ℕ] , [n] =
    let sType = Π ℕ ^ ! ° ⁰ ▹ (G ^ rG ° _  ▹▹ G [ suc (var 0) ]↑ ° _) ° _
        [Γ]′ = [Γ]₃
        [G]′ = S.irrelevance {A = G} [Γ] ([Γ]′ ∙ [ℕ]) [G]
        [G₀]′ = S.irrelevance {A = G [ zero ]} [Γ]₁ [Γ]′ [G₀]
        [G₊]′ = S.irrelevance {A = sType} [Γ]₂ [Γ]′ [G₊]
        [Gₙ]′ = substS {F = ℕ} {G = G} {t = n} [Γ]′ [ℕ] [G]′ [n]
        [z]′ = S.irrelevanceTerm {A = G [ zero ]} {t = z} [Γ]₁ [Γ]′
                                 [G₀] [G₀]′ [z]
        [s]′ = S.irrelevanceTerm {A = sType} {t = s} [Γ]₂ [Γ]′ [G₊] [G₊]′ [s]
    in  [Γ]′ , [Gₙ]′
    ,   natrecᵛ {G} {rG} {lG} {z} {s} {n} [Γ]′ [ℕ] [G]′ [G₀]′ [G₊]′ [Gₙ]′ [z]′ [s]′ [n]
  fundamentalTerm (⦅_,_,_,_⦆ⱼ {l} {F} {G} {t} {u} ⊢F ⊢G ⊢t ⊢u) with fundamental ⊢F | fundamental ⊢G | fundamentalTerm ⊢t | fundamentalTerm ⊢u
  ... | [ΓF] , [F]' | [ΓG] , [G] | [Γ] , [F] , [t]ₜ | [Γ]₁ , [G[t]] , [u]ₜ =
     let  [F]′ = S.irrelevance {A = F} [Γ] [Γ]₁ [F]
          [G]′ = S.irrelevance {A = G} [ΓG] ([Γ]₁ ∙ [F]′) [G]
          [t]ₜ′ = S.irrelevanceTerm {A = F} {t = t} [Γ] [Γ]₁ [F] [F]′ [t]ₜ
          [u]ₜ′ = S.irrelevanceTerm {A = G [ t ]} {t = u} [Γ]₁ [Γ]₁ [G[t]] (substS {F} {G} {t} [Γ]₁ [F]′ [G]′ [t]ₜ′) [u]ₜ
     in  [Γ]₁ , ∃ᵛ {F} {G} {l∃ = l} [Γ]₁ [F]′ [G]′ , ⦅⦆ᵛ {F = F} {G = G} {t = t} {u = u} [Γ]₁ [F]′ [G]′ [t]ₜ′ [u]ₜ′
  fundamentalTerm (fstⱼ {F} {G} {tu} {l} ⊢F ⊢G ⊢tu)
    with fundamentalTerm ⊢F | fundamentalTerm ⊢G | fundamentalTerm ⊢tu
  ... | [ΓF] , [UF] , [F]ₜ | [ΓG] ∙ [F] , [UG] , [G]ₜ | [Γ] , [∃FG] , [tu]ₜ =
    let [UF]′ = maybeEmbᵛ {A = Univ % _} [Γ] (Uᵛ (proj₂ (levelBounded l)) [Γ])
        [F]ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = F} [ΓF] [Γ] [UF] [UF]′ [F]ₜ
        [F]′ = maybeEmbᵛ {A = F} [Γ] (univᵛ {A = F} [Γ] (≡is≤ PE.refl) [UF]′ [F]ₜ′)
        [UG]′ = S.irrelevance {A = Univ _ _} (_∙_ {A = F} [ΓG] [F]) (_∙_ {A = F} [Γ] [F]′) (λ {Δ} {σ} → [UG] {Δ} {σ})
        [G]ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = G} (_∙_ {A = F} [ΓG] [F])
                                     (_∙_ {A = F} [Γ] [F]′) (λ {Δ} {σ} → [UG] {Δ} {σ})
                                     (λ {Δ} {σ} → [UG]′ {Δ} {σ}) [G]ₜ
        [G]′ = maybeEmbᵛ {A = G} (_∙_ {A = F} [Γ] [F]′)
               (univᵛ {A = G} (_∙_ {A = F} [Γ] [F]′) (≡is≤ PE.refl)
               (λ {Δ} {σ} → [UG]′ {Δ} {σ}) [G]ₜ′)
        [tu]ₜ′ = S.irrelevanceTerm {A = ∃ F ▹ G} {t = tu} [Γ] [Γ] [∃FG]
                                   (∃ᵛ {F} {G} [Γ] [F]′ [G]′) [tu]ₜ
    in [Γ] , [F]′ , fstᵛ {F = F} {G = G} {tu = tu} [Γ] [F]′ [G]′
                         (λ {Δ} {σ} → [UG]′ {Δ} {σ}) [F]ₜ′ [G]ₜ′ [tu]ₜ′
  fundamentalTerm (sndⱼ {F} {G} {tu} {l} ⊢F ⊢G ⊢tu)
    with fundamentalTerm ⊢F | fundamentalTerm ⊢G | fundamentalTerm ⊢tu
  ... | [ΓF] , [UF] , [F]ₜ | [ΓG] ∙ [F] , [UG] , [G]ₜ | [Γ] , [∃FG] , [tu]ₜ =
    let [UF]′ = maybeEmbᵛ {A = Univ % _} [Γ] (Uᵛ (proj₂ (levelBounded l)) [Γ])
        [F]ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = F} [ΓF] [Γ] [UF] [UF]′ [F]ₜ
        [F]′ = maybeEmbᵛ {A = F} [Γ] (univᵛ {A = F} [Γ] (≡is≤ PE.refl) [UF]′ [F]ₜ′)
        [UG]′ = S.irrelevance {A = Univ _ _} (_∙_ {A = F} [ΓG] [F]) (_∙_ {A = F} [Γ] [F]′) (λ {Δ} {σ} → [UG] {Δ} {σ})
        [G]ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = G} (_∙_ {A = F} [ΓG] [F])
                                     (_∙_ {A = F} [Γ] [F]′) (λ {Δ} {σ} → [UG] {Δ} {σ})
                                     (λ {Δ} {σ} → [UG]′ {Δ} {σ}) [G]ₜ
        [G]′ = maybeEmbᵛ {A = G} (_∙_ {A = F} [Γ] [F]′)
               (univᵛ {A = G} (_∙_ {A = F} [Γ] [F]′) (≡is≤ PE.refl)
               (λ {Δ} {σ} → [UG]′ {Δ} {σ}) [G]ₜ′)
        [tu]ₜ′ = S.irrelevanceTerm {A = ∃ F ▹ G} {t = tu} [Γ] [Γ] [∃FG]
                                   (∃ᵛ {F} {G} [Γ] [F]′ [G]′) [tu]ₜ
    in [Γ] ,
       substS {F} {G} {fst tu} [Γ] [F]′ [G]′ (fstᵛ {F = F} {G = G} {tu = tu} [Γ] [F]′ [G]′ (λ {Δ} {σ} → [UG]′ {Δ} {σ}) [F]ₜ′ [G]ₜ′ [tu]ₜ′) ,
       sndᵛ {F = F} {G = G} {tu = tu} [Γ] [F]′ [G]′ (λ {Δ} {σ} → [UG]′ {Δ} {σ}) [F]ₜ′ [G]ₜ′ [tu]ₜ′

  fundamentalTerm {Γ} (Idreflⱼ {A} {l} {t} ⊢t)
    with fundamentalTerm ⊢t 
  ... | [Γ] , [A] , [t]  =
    let [Id] = Idᵛ {A = A} {t = t} {u = t } [Γ] [A] [t] [t]
    in [Γ] , [Id] , Idreflᵛ {Γ} {A} {l} {t} [Γ] [A] [t]

  fundamentalTerm (transpⱼ {A} {l} {P} {t} {s} {u} {e} ⊢A ⊢P ⊢t ⊢s ⊢u ⊢e)
    with fundamental ⊢A | fundamental ⊢P  | fundamentalTerm ⊢t | fundamentalTerm ⊢s | fundamentalTerm ⊢u | fundamentalTerm ⊢e
  ... | [ΓA] , [A] | [ΓP] ∙ [A]' , [P] | [Γt] , [At] , [t] | [Γs] , [Pt] , [s] | [Γu] , [Au] , [u] | [Γe] , [Id] , [e] =
    let [A]′ = S.irrelevance {A = A} [ΓA] [Γe] [A]
        [P]′ = S.irrelevance {A = P} (_∙_ {A = A} [ΓP] [A]') (_∙_ {A = A} [Γe] [A]′) [P]
        [t]′ = S.irrelevanceTerm {A = A} {t = t} [Γt] [Γe] [At] [A]′ [t]
        [u]′ = S.irrelevanceTerm {A = A} {t = u} [Γu] [Γe] [Au] [A]′ [u]
        [Pt]′ = substS {A} {P} {t} [Γe] [A]′ [P]′ [t]′
        [s]′ = S.irrelevanceTerm {A = P [ t ] } {t = s} [Γs] [Γe] [Pt] [Pt]′ [s]
    in [Γe] ,  substS {A} {P} {u} [Γe] [A]′ [P]′ [u]′ , transpᵗᵛ {A} {P} {l} {t} {s} {u} {e} [Γe] [A]′ [P]′ [t]′ [s]′ [u]′ [Id] [e]
  fundamentalTerm (castⱼ {A} {B} {r} {e} {t} ⊢A ⊢B ⊢e ⊢t)
    with fundamentalTerm ⊢A | fundamentalTerm ⊢B  | fundamentalTerm ⊢e  | fundamentalTerm ⊢t
  ... | [ΓA] , [UA] , [A]ₜ | [ΓB] , [UB] , [B]ₜ | [Γe] , [Id] , [e]ₜ | [Γ]₁ , [At] , [t]ₜ =
    let [UA]′ = S.irrelevance {A = Univ _ _} [ΓA] [Γ]₁ [UA] 
        [A]ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = A} [ΓA] [Γ]₁ [UA] [UA]′ [A]ₜ
        [B]ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = B} [ΓB] [Γ]₁ [UB] [UA]′ [B]ₜ
        [B] = maybeEmbᵛ {A = B} [Γ]₁ (univᵛ {A = B} [Γ]₁ (≡is≤ PE.refl) [UA]′ [B]ₜ′)
        [Id]′ = S.irrelevance {A = Id (Univ r _) A B} [Γe] [Γ]₁ [Id] 
        [e]ₜ′  = S.irrelevanceTerm {A = Id (Univ r _) A B} {t = e} [Γe] [Γ]₁ [Id] [Id]′ [e]ₜ
     in [Γ]₁ , [B] , castᵗᵛ {A} {B} {r} {t} {e} [Γ]₁ [UA]′ [A]ₜ′ [B]ₜ′ [At] [B] [t]ₜ [Id]′ [e]ₜ′

  fundamentalTerm {Γ} (castreflⱼ {A} {t} ⊢A ⊢t)
    with fundamentalTerm ⊢A | fundamentalTerm ⊢t
  ... | [ΓA] , [UA] , [A]ₜ | [Γ] , [A] , [t]ₜ =
    let [UA]′ = S.irrelevance {A = Univ _ _} [ΓA] [Γ] [UA] 
        [A]ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = A} [ΓA] [Γ] [UA] [UA]′ [A]ₜ
        [Id] = Idᵛ {A = A} {t = t} {u = cast ⁰ A A (Idrefl (U ⁰) A) t} [Γ] [A] [t]ₜ
                   (castᵗᵛ {A = A} {B = A} {t = t} {e = Idrefl (U ⁰) A} [Γ] [UA]′ [A]ₜ′ [A]ₜ′ [A] [A] [t]ₜ
                           (Idᵛ {A = U _} {t = A} {u = A} [Γ] [UA]′ [A]ₜ′ [A]ₜ′)
                           (Idreflᵛ {A = U _} {t = A} [Γ] [UA]′ [A]ₜ′))
    in  [Γ] , [Id] , castreflᵛ {Γ} {A} {t} [Γ] [UA]′ [A]ₜ′ [A] [t]ₜ

  fundamentalTerm (Emptyrecⱼ {A} {lEmpty} {[ rA , lA ]} {n} ⊢A ⊢n)
    with fundamental ⊢A | fundamentalTerm ⊢n
  ... | [Γ] , [A] | [Γ]′ , [Empty] , [n] =
    let [A]′ = S.irrelevance {A = A} [Γ] [Γ]′ [A]
    in [Γ]′ , [A]′ , Emptyrecᵛ {A} {rA} {lA} {lEmpty} {n} [Γ]′ [Empty] [A]′ [n]
  fundamentalTerm (conv {t} {A} {B} ⊢t A′≡A)
    with fundamentalTerm ⊢t | fundamentalEq A′≡A
  fundamentalTerm (conv {t} {A} {B} ⊢t A′≡A) | [Γ] , [A′] , [t]
    | [Γ]₁ , [A′]₁ , [A] , [A′≡A] =
      let [Γ]′ = [Γ]₁
          [t]′ = S.irrelevanceTerm {A = A} {t = t} [Γ] [Γ]′ [A′] [A′]₁ [t]
      in  [Γ]′ , [A]
      ,   convᵛ {t} {A} {B} [Γ]′ [A′]₁ [A] [A′≡A] [t]′
  fundamentalTerm (univ 0<1 ⊢Γ) = let [Γ] = valid ⊢Γ
                                  in [Γ] , (Uᵛ ∞< [Γ] , Uᵗᵛ [Γ])
                                  
  -- Fundamental theorem for term equality.
  fundamentalTermEq : ∀{Γ A t t′ rA} → Γ ⊢ t ≡ t′ ∷ A ^ rA
                    → ∃ λ ([Γ] : ⊩ᵛ Γ)
                    → [ Γ ⊩ᵛ⟨ ∞ ⟩ t ≡ t′ ∷ A ^ rA / [Γ] ]


  fundamentalTermEq (refl D) with fundamentalTerm D
  ... | [Γ] , [A] , [t] =
    [Γ] , modelsTermEq [A] [t] [t]
                       (λ ⊢Δ [σ] → reflEqTerm (proj₁ ([A] ⊢Δ [σ]))
                                              (proj₁ ([t] ⊢Δ [σ])))
  fundamentalTermEq (sym D) with fundamentalTermEq D
  fundamentalTermEq (sym D) | [Γ] , modelsTermEq [A] [t′] [t] [t′≡t] =
    [Γ] , modelsTermEq [A] [t] [t′]
                       (λ ⊢Δ [σ] → symEqTerm (proj₁ ([A] ⊢Δ [σ]))
                                             ([t′≡t] ⊢Δ [σ]))
  fundamentalTermEq (trans {t} {u} {r} {A} t≡u u≡t′)
    with fundamentalTermEq t≡u | fundamentalTermEq u≡t′
  fundamentalTermEq (trans {t} {u} {r} {A} t≡u u≡t′)
    | [Γ] , modelsTermEq [A] [t] [u] [t≡u]
    | [Γ]₁ , modelsTermEq [A]₁ [t]₁ [u]₁ [t≡u]₁ =
      let [r]′ = S.irrelevanceTerm {A = A} {t = r} [Γ]₁ [Γ] [A]₁ [A] [u]₁
      in  [Γ] , modelsTermEq [A] [t] [r]′
                  (λ ⊢Δ [σ] →
                     let [σ]′ = S.irrelevanceSubst [Γ] [Γ]₁ ⊢Δ ⊢Δ [σ]
                         [t≡u]₁′ = irrelevanceEqTerm (proj₁ ([A]₁ ⊢Δ [σ]′))
                                                     (proj₁ ([A] ⊢Δ [σ]))
                                                     ([t≡u]₁ ⊢Δ [σ]′)
                     in  transEqTerm (proj₁ ([A] ⊢Δ [σ]))
                                     ([t≡u] ⊢Δ [σ]) [t≡u]₁′)
  fundamentalTermEq (conv {A} {B} {r} {t} {u} t≡u A′≡A)
    with fundamentalTermEq t≡u | fundamentalEq A′≡A
  fundamentalTermEq (conv {A} {B} {r} {t} {u} t≡u A′≡A)
    | [Γ] , modelsTermEq [A′] [t] [u] [t≡u] | [Γ]₁ , [A′]₁ , [A] , [A′≡A] =
      let [t]′ = S.irrelevanceTerm {A = A} {t = t} [Γ] [Γ]₁ [A′] [A′]₁ [t]
          [u]′ = S.irrelevanceTerm {A = A} {t = u} [Γ] [Γ]₁ [A′] [A′]₁ [u]
          [t]″ = convᵛ {t} {A} {B} [Γ]₁ [A′]₁ [A] [A′≡A] [t]′
          [u]″ = convᵛ {u} {A} {B} [Γ]₁ [A′]₁ [A] [A′≡A] [u]′
      in  [Γ]₁
      ,   modelsTermEq [A] [t]″ [u]″
            (λ ⊢Δ [σ] →
               let [σ]′ = S.irrelevanceSubst [Γ]₁ [Γ] ⊢Δ ⊢Δ [σ]
                   [t≡u]′ = irrelevanceEqTerm (proj₁ ([A′] ⊢Δ [σ]′))
                                              (proj₁ ([A′]₁ ⊢Δ [σ]))
                                              ([t≡u] ⊢Δ [σ]′)
               in  convEqTerm₁ (proj₁ ([A′]₁ ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ]))
                               ([A′≡A] ⊢Δ [σ]) [t≡u]′)
  fundamentalTermEq (Π-cong {E} {F} {G} {H} {rF} {lF} {rG} {lG} {lΠ} lF< lG< ⊢F F≡H G≡E)
    with fundamental ⊢F | fundamentalTermEq F≡H | fundamentalTermEq G≡E
  ... | [Γ] , [F] | [Γ]₁ , modelsTermEq [U] [F]ₜ [H]ₜ [F≡H]ₜ
      | [Γ]₂ , modelsTermEq [U]₁ [G]ₜ [E]ₜ [G≡E]ₜ =
    let [U]′  = maybeEmbᵛ {A = Univ _ _} [Γ] (Uᵛ (proj₂ (levelBounded lF)) [Γ]) 
        [UΠ] = maybeEmbᵛ {A = Univ _ _} [Γ] (Uᵛ (proj₂ (levelBounded lΠ)) [Γ])
        [F]ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = F} [Γ]₁ [Γ] [U] [U]′ [F]ₜ
        [H]ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = H} [Γ]₁ [Γ] [U] [U]′ [H]ₜ
        [F]′  = S.irrelevance {A = F} [Γ] [Γ]₁ [F]
        [H]   = maybeEmbᵛ {A = H} [Γ] (univᵛ {A = H} [Γ] (≡is≤ PE.refl) [U]′ [H]ₜ′)
        [F≡H] = S.irrelevanceEq {A = F} {B = H} [Γ]₁ [Γ] [F]′ [F]
                  (univEqᵛ {F} {H} [Γ]₁ [U] [F]′ [F≡H]ₜ)
        [U]₁′ = S.irrelevance {A = Univ _ _} [Γ]₂ ([Γ] ∙ [F]) [U]₁ 
        [U]₂′ = S.irrelevanceLift {A = Univ _ _} {F = F} {H = H} [Γ] [F] [H] [F≡H] (λ {Δ} {σ} → [U]₁′ {Δ} {σ})
        [G]ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = G} [Γ]₂ ([Γ] ∙ [F])
                                  [U]₁ (λ {Δ} {σ} → [U]₁′ {Δ} {σ}) [G]ₜ
        [E]ₜ′ = S.irrelevanceTermLift {A = Univ _ _} {F = F} {H = H} {t = E}
                                      [Γ] [F] [H] [F≡H]
                                      (λ {Δ} {σ} → [U]₁′ {Δ} {σ})
                  (S.irrelevanceTerm {A = Univ _ _} {t = E} [Γ]₂ ([Γ] ∙ [F])
                                     [U]₁ (λ {Δ} {σ} → [U]₁′ {Δ} {σ}) [E]ₜ)
        [F≡H]ₜ′ = S.irrelevanceEqTerm {A = Univ _ _} {t = F} {u = H}
                                      [Γ]₁ [Γ] [U] [U]′ [F≡H]ₜ
        [G≡E]ₜ′ = S.irrelevanceEqTerm {A = Univ _ _} {t = G} {u = E} [Γ]₂
                                      (_∙_ {A = F} [Γ] [F]) [U]₁
                                      (λ {Δ} {σ} → [U]₁′ {Δ} {σ}) [G≡E]ₜ
    in  [Γ]
    ,   modelsTermEq
          [UΠ] -- looks like [U]′ but the implicits are different
          (Πᵗᵛ {F} {G} lF< lG< [Γ] [F] (λ {Δ} {σ} → [U]₁′ {Δ} {σ}) [F]ₜ′ [G]ₜ′ ) 
          (Πᵗᵛ {H} {E} lF< lG< [Γ] [H] (λ {Δ} {σ} → [U]₂′ {Δ} {σ}) [H]ₜ′ [E]ₜ′) 
          (Π-congᵗᵛ {F} {G} {H} {E} lF< lG< [Γ] [F] [H]
                    (λ {Δ} {σ} → [U]₁′ {Δ} {σ}) (λ {Δ} {σ} → [U]₂′ {Δ} {σ})
                    [F]ₜ′ [G]ₜ′ [H]ₜ′ [E]ₜ′ [F≡H]ₜ′ [G≡E]ₜ′) 

  fundamentalTermEq (app-cong {a} {b} {f} {g} {F} {G} {rF} {lF} {lG} {l} f≡g a≡b)
    with fundamentalTermEq f≡g | fundamentalTermEq a≡b
  ... | [Γ] , modelsTermEq [ΠFG] [f] [g] [f≡g]
      | [Γ]₁ , modelsTermEq [F] [a] [b] [a≡b] =
    let [ΠFG]′ = S.irrelevance {A = Π F ^ rF ° lF ▹ G ° lG} [Γ] [Γ]₁ [ΠFG]
        [f]′ = S.irrelevanceTerm {A = Π F ^ rF ° lF ▹ G ° lG} {t = f} [Γ] [Γ]₁ [ΠFG] [ΠFG]′ [f]
        [g]′ = S.irrelevanceTerm {A = Π F ^ rF ° lF ▹ G ° lG} {t = g} [Γ] [Γ]₁ [ΠFG] [ΠFG]′ [g]
        [f≡g]′ = S.irrelevanceEqTerm {A = Π F ^ rF ° lF ▹ G ° lG} {t = f} {u = g}
                                     [Γ] [Γ]₁ [ΠFG] [ΠFG]′ [f≡g]
        [G[a]] = substSΠ {F} {G} {a} [Γ]₁ [F] [ΠFG]′ [a]
        [G[b]] = substSΠ {F} {G} {b} [Γ]₁ [F] [ΠFG]′ [b]
        [G[a]≡G[b]] = substSΠEq {F} {G} {F} {G} {a} {b} [Γ]₁ [F] [F] [ΠFG]′
                                [ΠFG]′ (reflᵛ {Π F ^ rF ° lF ▹ G ° lG} [Γ]₁ [ΠFG]′) [a] [b] [a≡b]
    in  [Γ]₁ , modelsTermEq [G[a]]
                            (appᵛ {F} {G} {rF} {lF} {lG} { ! } {l} {f} {a} [Γ]₁ [F] [ΠFG]′ [f]′ [a])
                            (conv₂ᵛ {g ∘ b} {G [ a ]} {G [ b ]} [Γ]₁
                                    [G[a]] [G[b]] [G[a]≡G[b]]
                                    (appᵛ {F} {G} {rF} {lF} {lG} { ! } {l} {g} {b}
                                          [Γ]₁ [F] [ΠFG]′ [g]′ [b]))
                            (app-congᵛ {F} {G} {rF} {lF} {lG} { ! } {l} {f} {g} {a} {b}
                                       [Γ]₁ [F] [ΠFG]′ [f≡g]′ [a] [b] [a≡b])
  fundamentalTermEq (β-red {a} {b} {F} {rF} {lF} {G} {lG} ⊢F ⊢b ⊢a)
    with fundamental ⊢F | fundamentalTerm ⊢b | fundamentalTerm ⊢a
  ... | [Γ] , [F] | [Γ]₁ , [G] , [b] | [Γ]₂ , [F]₁ , [a] =
    let [G]′ = S.irrelevance {A = G} [Γ]₁ ([Γ]₂ ∙ [F]₁) [G]
        [b]′ = S.irrelevanceTerm {A = G} {t = b} [Γ]₁ ([Γ]₂ ∙ [F]₁) [G] [G]′ [b]
        [G[a]] = substS {F} {G} {a} [Γ]₂ [F]₁ [G]′ [a]
        [b[a]] = substSTerm {F} {G} {a} {b} [Γ]₂ [F]₁ [G]′ [b]′ [a]
        [lam] , [eq] =
          redSubstTermᵛ {G [ a ]} {(lam F ▹ b) ∘ a} {b [ a ]} [Γ]₂
            (λ {Δ} {σ} ⊢Δ [σ] →
               let [liftσ] = liftSubstS {F = F} [Γ]₂ ⊢Δ [F]₁ [σ]
                   ⊢σF = escape (proj₁ ([F]₁ ⊢Δ [σ]))
                   ⊢σb = escapeTerm (proj₁ ([G]′ (⊢Δ ∙ ⊢σF) [liftσ]))
                                       (proj₁ ([b]′ (⊢Δ ∙ ⊢σF) [liftσ]))
                   ⊢σa = escapeTerm (proj₁ ([F]₁ ⊢Δ [σ]))
                                       (proj₁ ([a] ⊢Δ [σ]))
               in  PE.subst₂ (λ x y → _ ⊢ (lam (subst σ F) ▹ (subst (liftSubst σ) b))
                                          ∘ (subst σ a) ⇒ x ∷ y ^ _)
                             (PE.sym (singleSubstLift b a))
                             (PE.sym (singleSubstLift G a))
                             (β-red ⊢σF ⊢σb ⊢σa))
                         [G[a]] [b[a]]
    in  [Γ]₂ , modelsTermEq [G[a]] [lam] [b[a]] [eq]
  fundamentalTermEq (η-eq {f} {g} {F} {rF} {lF} {lG} {l} {G} lF< lG< ⊢F ⊢t ⊢t′ t≡t′) with
    fundamental ⊢F | fundamentalTerm ⊢t |
    fundamentalTerm ⊢t′ | fundamentalTermEq t≡t′
  ... | [Γ] , [F] | [Γ]₁ , [ΠFG] , [t] | [Γ]₂ , [ΠFG]₁ , [t′]
      | [Γ]₃ , modelsTermEq [G] [t0] [t′0] [t0≡t′0] = 
    let [F]′ = S.irrelevance {A = F} [Γ] [Γ]₁ [F]
        [G]′ = S.irrelevance {A = G} [Γ]₃ ([Γ]₁ ∙ [F]′) [G]
        [t′]′ = S.irrelevanceTerm {A = Π F ^ rF ° lF ▹ G ° lG} {t = g}
                                  [Γ]₂ [Γ]₁ [ΠFG]₁ [ΠFG] [t′]
        [ΠFG]″ = Πᵛ {F} {G} lF< lG< [Γ]₁ [F]′ [G]′
        [t]″ = S.irrelevanceTerm {A = Π F ^ rF ° lF ▹ G ° lG} {t = f}
                                  [Γ]₁ [Γ]₁ [ΠFG] [ΠFG]″ [t]
        [t′]″ = S.irrelevanceTerm {A = Π F ^ rF ° lF ▹ G ° lG} {t = g}
                                   [Γ]₂ [Γ]₁ [ΠFG]₁ [ΠFG]″ [t′]
        [t0≡t′0]′ = S.irrelevanceEqTerm {A = G} {t = wk1 f ∘ var 0}
                                        {u = wk1 g ∘ var 0}
                                        [Γ]₃ ([Γ]₁ ∙ [F]′) [G] [G]′ [t0≡t′0]
        [t≡t′] = η-eqᵛ {f} {g} {F} {G} lF< lG< [Γ]₁ [F]′ [G]′ [t]″ [t′]″ [t0≡t′0]′
        [t≡t′]′ = S.irrelevanceEqTerm {A = Π F ^ rF ° lF ▹ G ° lG} {t = f} {u = g}
                                      [Γ]₁ [Γ]₁ [ΠFG]″ [ΠFG] [t≡t′] 
    in [Γ]₁ , modelsTermEq [ΠFG] [t] [t′]′ [t≡t′]′ 
  fundamentalTermEq (suc-cong x) with fundamentalTermEq x
  fundamentalTermEq (suc-cong {t} {u} x)
    | [Γ] , modelsTermEq [A] [t] [u] [t≡u] =
      let [suct] = sucᵛ {n = t} [Γ] [A] [t]
          [sucu] = sucᵛ {n = u} [Γ] [A] [u]
      in  [Γ] , modelsTermEq [A] [suct] [sucu]
                             (λ ⊢Δ [σ] →
                                sucEqTerm (proj₁ ([A] ⊢Δ [σ])) ([t≡u] ⊢Δ [σ]))
  fundamentalTermEq (natrec-cong {z} {z′} {s} {s′} {n} {n′} {F} {F′}
                                 F≡F′ z≡z′ s≡s′ n≡n′)
    with fundamentalEq F≡F′ |
         fundamentalTermEq z≡z′      |
         fundamentalTermEq s≡s′      |
         fundamentalTermEq n≡n′
  fundamentalTermEq (natrec-cong {z} {z′} {s} {s′} {n} {n′} {F} {F′} {l}
                                 F≡F′ z≡z′ s≡s′ n≡n′) |
    [Γ]  , [F] , [F′] , [F≡F′] |
    [Γ]₁ , modelsTermEq [F₀] [z] [z′] [z≡z′] |
    [Γ]₂ , modelsTermEq [F₊] [s] [s′] [s≡s′] |
    [Γ]₃ , modelsTermEq [ℕ] [n] [n′] [n≡n′] =
      let sType = Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc (var 0) ]↑ ° l) ° l
          s′Type = Π ℕ ^ ! ° ⁰ ▹ (F′ ^ ! ° l ▹▹ F′ [ suc (var 0) ]↑ ° l) ° l
          [0] = S.irrelevanceTerm {l = ∞} {A = ℕ} {t = zero}
                                  [Γ]₃ [Γ]₃ (ℕᵛ [Γ]₃) [ℕ] (zeroᵛ {l = ∞} [Γ]₃)
          [F]′ = S.irrelevance {A = F} [Γ] ([Γ]₃ ∙ [ℕ]) [F]
          [F₀]′ = S.irrelevance {A = F [ zero ]} [Γ]₁ [Γ]₃ [F₀]
          [F₊]′ = S.irrelevance {A = sType} [Γ]₂ [Γ]₃ [F₊]
          [Fₙ]′ = substS {ℕ} {F} {n} [Γ]₃ [ℕ] [F]′ [n]
          [F′]′ = S.irrelevance {A = F′} [Γ] ([Γ]₃ ∙ [ℕ]) [F′]
          [F₀]″ = substS {ℕ} {F} {zero} [Γ]₃ [ℕ] [F]′ [0]
          [F′₀]′ = substS {ℕ} {F′} {zero} [Γ]₃ [ℕ] [F′]′ [0]
          [F′₊]′ = sucCase {F′} [Γ]₃ [ℕ] [F′]′
          [F′ₙ′]′ = substS {ℕ} {F′} {n′} [Γ]₃ [ℕ] [F′]′ [n′]
          [ℕ≡ℕ] = reflᵛ {ℕ} [Γ]₃ [ℕ]
          [0≡0] = reflᵗᵛ {ℕ} {zero} [Γ]₃ [ℕ] [0]
          [F≡F′]′ = S.irrelevanceEq {A = F} {B = F′}
                                    [Γ] ([Γ]₃ ∙ [ℕ]) [F] [F]′ [F≡F′]
          [F₀≡F′₀] = substSEq {ℕ} {ℕ} {F} {F′} {zero} {zero}
                              [Γ]₃ [ℕ] [ℕ] [ℕ≡ℕ]
                              [F]′ [F′]′ [F≡F′]′ [0] [0] [0≡0]
          [F₀≡F′₀]′ = S.irrelevanceEq {A = F [ zero ]} {B = F′ [ zero ]}
                                      [Γ]₃ [Γ]₃ [F₀]″ [F₀]′ [F₀≡F′₀]
          [F₊≡F′₊] = sucCaseCong {F} {F′} [Γ]₃ [ℕ] [F]′ [F′]′ [F≡F′]′
          [F₊≡F′₊]′ = S.irrelevanceEq {A = sType} {B = s′Type}
                                      [Γ]₃ [Γ]₃ (sucCase {F} [Γ]₃ [ℕ] [F]′)
                                      [F₊]′ [F₊≡F′₊]
          [Fₙ≡F′ₙ′]′ = substSEq {ℕ} {ℕ} {F} {F′} {n} {n′}
                                [Γ]₃ [ℕ] [ℕ] [ℕ≡ℕ] [F]′ [F′]′ [F≡F′]′
                                [n] [n′] [n≡n′]
          [z]′ = S.irrelevanceTerm {A = F [ zero ]} {t = z}
                                   [Γ]₁ [Γ]₃ [F₀] [F₀]′ [z]
          [z′]′ = convᵛ {z′} {F [ zero ]} {F′ [ zero ]}
                        [Γ]₃ [F₀]′ [F′₀]′ [F₀≡F′₀]′
                        (S.irrelevanceTerm {A = F [ zero ]} {t = z′}
                                           [Γ]₁ [Γ]₃ [F₀] [F₀]′ [z′])
          [z≡z′]′ = S.irrelevanceEqTerm {A = F [ zero ]} {t = z} {u = z′}
                                        [Γ]₁ [Γ]₃ [F₀] [F₀]′ [z≡z′]
          [s]′ = S.irrelevanceTerm {A = sType} {t = s} [Γ]₂ [Γ]₃ [F₊] [F₊]′ [s]
          [s′]′ = convᵛ {s′} {sType} {s′Type} [Γ]₃ [F₊]′ [F′₊]′ [F₊≡F′₊]′
                        (S.irrelevanceTerm {A = sType} {t = s′}
                                           [Γ]₂ [Γ]₃ [F₊] [F₊]′ [s′])
          [s≡s′]′ = S.irrelevanceEqTerm {A = sType} {t = s} {u = s′}
                                        [Γ]₂ [Γ]₃ [F₊] [F₊]′ [s≡s′]
      in  [Γ]₃
      ,   modelsTermEq [Fₙ]′
                       (natrecᵛ {F} { ! } {l} {z} {s} {n}
                                [Γ]₃ [ℕ] [F]′ [F₀]′ [F₊]′ [Fₙ]′ [z]′ [s]′ [n])
                       (conv₂ᵛ {natrec F′ z′ s′ n′} {F [ n ]} {F′ [ n′ ]}
                               [Γ]₃ [Fₙ]′ [F′ₙ′]′ [Fₙ≡F′ₙ′]′
                               (natrecᵛ {F′} { ! } {l} {z′} {s′} {n′}
                                        [Γ]₃ [ℕ] [F′]′ [F′₀]′ [F′₊]′ [F′ₙ′]′
                                        [z′]′ [s′]′ [n′]))
                       (natrec-congᵛ {F} {F′} { ! } {l} {z} {z′} {s} {s′} {n} {n′}
                                     [Γ]₃ [ℕ] [F]′ [F′]′ [F≡F′]′
                                     [F₀]′ [F′₀]′ [F₀≡F′₀]′
                                     [F₊]′ [F′₊]′ [F₊≡F′₊]′ [Fₙ]′
                                     [z]′ [z′]′ [z≡z′]′
                                     [s]′ [s′]′ [s≡s′]′ [n] [n′] [n≡n′]) 
  fundamentalTermEq (natrec-zero {z} {s} {F} ⊢F ⊢z ⊢s)
    with fundamental ⊢F | fundamentalTerm ⊢z | fundamentalTerm ⊢s
  fundamentalTermEq (natrec-zero {z} {s} {F} {l} ⊢F ⊢z ⊢s) | [Γ] , [F]
    | [Γ]₁ , [F₀] , [z] | [Γ]₂ , [F₊] , [s] =
    let sType = Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° l ▹▹ F [ suc (var 0) ]↑ ° l) ° l
        [Γ]′ = [Γ]₁
        [ℕ]′ = ℕᵛ {l = ∞} [Γ]′
        [F₊]′ = S.irrelevance {A = sType} [Γ]₂ [Γ]′ [F₊]
        [s]′ = S.irrelevanceTerm {A = sType} {t = s} [Γ]₂ [Γ]′ [F₊] [F₊]′ [s]
        [F]′ = S.irrelevance {A = F} [Γ] ([Γ]′ ∙ [ℕ]′) [F]
        d , r =
          redSubstTermᵛ {F [ zero ]} {natrec F z s zero} {z} [Γ]′
            (λ {Δ} {σ} ⊢Δ [σ] →
               let ⊢ℕ = escape (proj₁ ([ℕ]′ ⊢Δ [σ]))
                   ⊢F = escape (proj₁ ([F]′ (⊢Δ ∙ ⊢ℕ)
                                               (liftSubstS {F = ℕ}
                                                           [Γ]′ ⊢Δ [ℕ]′ [σ])))
                   ⊢z = PE.subst (λ x → Δ ⊢ subst σ z ∷ x ^ _)
                                 (singleSubstLift F zero)
                                 (escapeTerm (proj₁ ([F₀] ⊢Δ [σ]))
                                                (proj₁ ([z] ⊢Δ [σ])))
                   ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x ^ [ ! , ι l ] )
                                 (natrecSucCase σ F ! l)
                                 (escapeTerm (proj₁ ([F₊]′ ⊢Δ [σ]))
                                                (proj₁ ([s]′ ⊢Δ [σ])))
               in PE.subst (λ x → Δ ⊢ subst σ (natrec F z s zero)
                                    ⇒ subst σ z ∷ x ^ _)
                           (PE.sym (singleSubstLift F zero))
                           (natrec-zero ⊢F ⊢z ⊢s))
                        [F₀] [z]
    in  [Γ]′ , modelsTermEq [F₀] d [z] r
  fundamentalTermEq (natrec-suc {n} {z} {s} {F} {lF} ⊢n ⊢F ⊢z ⊢s)
    with fundamentalTerm ⊢n | fundamental ⊢F
       | fundamentalTerm ⊢z | fundamentalTerm ⊢s
  ... | [Γ] , [ℕ] , [n] | [Γ]₁ , [F] | [Γ]₂ , [F₀] , [z] | [Γ]₃ , [F₊] , [s] =
    let [ℕ]′ = S.irrelevance {A = ℕ} [Γ] [Γ]₃ [ℕ]
        [n]′ = S.irrelevanceTerm {A = ℕ} {t = n} [Γ] [Γ]₃ [ℕ] [ℕ]′ [n]
        [sucn] = sucᵛ {n = n} [Γ]₃ [ℕ]′ [n]′
        [F₀]′ = S.irrelevance {A = F [ zero ]} [Γ]₂ [Γ]₃ [F₀]
        [z]′ = S.irrelevanceTerm {A = F [ zero ]} {t = z}
                                 [Γ]₂ [Γ]₃ [F₀] [F₀]′ [z]
        [F]′ = S.irrelevance {A = F} [Γ]₁ ([Γ]₃ ∙ [ℕ]′) [F]
        [F[sucn]] = substS {ℕ} {F} {suc n} [Γ]₃ [ℕ]′ [F]′ [sucn]
        [Fₙ]′ = substS {ℕ} {F} {n} [Γ]₃ [ℕ]′ [F]′ [n]′
        [natrecₙ] = natrecᵛ {F} { ! } {lF} {z} {s} {n}
                            [Γ]₃ [ℕ]′ [F]′ [F₀]′ [F₊] [Fₙ]′ [z]′ [s] [n]′
        t = (s ∘ n) ∘ (natrec F z s n)
        q = subst (liftSubst (sgSubst n))
                  (wk1 (F [ suc (var 0) ]↑))
        y = S.irrelevanceTerm′
              {A = q [ natrec F z s n ]} {A′ = F [ suc n ]} {t = t}
              (natrecIrrelevantSubst′ F z s n) PE.refl [Γ]₃ [Γ]₃
              (substSΠ {F [ n ]} {q} {natrec F z s n} [Γ]₃
                (substS {ℕ} {F} {n} [Γ]₃ [ℕ]′ [F]′ [n]′)
                (substSΠ {ℕ} {F ^ ! ° lF ▹▹ F [ suc (var 0) ]↑ ° lF} {n}
                         [Γ]₃ [ℕ]′ [F₊] [n]′)
                [natrecₙ])
              [F[sucn]]
              (appᵛ {F [ n ]} {q} { ! } {lF} {lF} { ! } {lF} {s ∘ n} {natrec F z s n} [Γ]₃ [Fₙ]′
                (substSΠ {ℕ} {F ^ ! ° lF ▹▹ F [ suc (var 0) ]↑ ° lF} {n}
                         [Γ]₃ [ℕ]′ [F₊] [n]′)
                (appᵛ {ℕ} {F ^ ! ° lF ▹▹ F [ suc (var 0) ]↑ ° lF} { ! } {⁰} {lF} { ! } {lF} {s} {n}
                      [Γ]₃ [ℕ]′ [F₊] [s] [n]′)
                [natrecₙ])
        d , r =
          redSubstTermᵛ {F [ suc n ]} {natrec F z s (suc n)} {t } {∞} {_} [Γ]₃
            (λ {Δ} {σ} ⊢Δ [σ] →
               let ⊢n = escapeTerm (proj₁ ([ℕ]′ ⊢Δ [σ]))
                                      (proj₁ ([n]′ ⊢Δ [σ]))
                   ⊢ℕ = escape (proj₁ ([ℕ]′ ⊢Δ [σ]))
                   ⊢F = escape (proj₁ ([F]′ (⊢Δ ∙ ⊢ℕ)
                                               (liftSubstS {F = ℕ}
                                                           [Γ]₃ ⊢Δ [ℕ]′ [σ])))
                   ⊢z = PE.subst (λ x → Δ ⊢ subst σ z ∷ x ^ _)
                                 (singleSubstLift F zero)
                                 (escapeTerm (proj₁ ([F₀]′ ⊢Δ [σ]))
                                                (proj₁ ([z]′ ⊢Δ [σ])))
                   ⊢s = PE.subst (λ x → Δ ⊢ subst σ s ∷ x ^ [ ! , ι lF ])
                                 (natrecSucCase σ F ! lF)
                                 (escapeTerm (proj₁ ([F₊] ⊢Δ [σ]))
                                                (proj₁ ([s] ⊢Δ [σ])))
                   r = _⊢_⇒_∷_^_.natrec-suc {n = subst σ n}
                                          {z = subst σ z} {s = subst σ s}
                                          {F = subst (liftSubst σ) F}
                                          ⊢n ⊢F ⊢z ⊢s 
               in PE.subst (λ x → Δ ⊢ subst σ (natrec F z s (suc n))
                                    ⇒ (subst σ t) ∷ x ^ _)
                           (PE.trans (PE.trans (substCompEq F)
                             (substVar-to-subst (λ { 0 → PE.refl
                                         ; (1+ x) → PE.trans (subst-wk (σ x))
                                                              (subst-id (σ x))
                                         })
                                      F))
                             (PE.sym (substCompEq F)))
                           r)
                        [F[sucn]] y
    in  [Γ]₃ , modelsTermEq [F[sucn]] d y r
  fundamentalTermEq (Emptyrec-cong {F} {F′} {n} {n′}
                                 F≡F′ ⊢n ⊢n′)
    with fundamentalEq F≡F′ | fundamentalTerm ⊢n | fundamentalTerm ⊢n′
  fundamentalTermEq (Emptyrec-cong {F} {F′} {lF} {lEmpty} {n} {n′}
                                 F≡F′ ⊢n ⊢n′) |
    [Γ]  , [F] , [F′] , [F≡F′] |
    [Γn]  , [Empty] ,  [n] | [Γn′] , [Empty]′ , [n′]
    =
    let [F]′ = S.irrelevance {A = F} [Γ] [Γn′] [F]
        [F′]′ = S.irrelevance {A = F′} [Γ] [Γn′] [F′]
        [n]′ = S.irrelevanceTerm {A = Empty} {t = n} [Γn] [Γn′] [Empty] [Empty]′ [n]
        [F≡F′]′ = S.irrelevanceEq {A = F} {B = F′} [Γ] [Γn′] [F] [F]′ [F≡F′]
    in [Γn′]
      , modelsTermEq [F]′ (Emptyrecᵛ {F} { ! } {lF} {lEmpty} {n} [Γn′] [Empty]′ [F]′ [n]′)
                     (conv₂ᵛ {Emptyrec F′ n′} {F} {F′} { [ ! , lF ] } [Γn′] [F]′ [F′]′ [F≡F′]′
                       (Emptyrecᵛ {F′} { ! } {lF} {lEmpty} {n′} [Γn′] [Empty]′ [F′]′ [n′]))
                     (Emptyrec-congᵛ {F} {F′} { ! } {lF} {lEmpty} {n} {n′}
                        [Γn′] [Empty]′ [F]′ [F′]′ [F≡F′]′ [n]′ [n′])
  fundamentalTermEq (proof-irrelevance ⊢t ⊢u) with fundamentalTerm ⊢t | fundamentalTerm ⊢u
  fundamentalTermEq {A = A} {t = t} {t′ = t′} (proof-irrelevance ⊢t ⊢u) | [Γ] , [A] , [t] | [Γ]′ , [A]′ , [u] =
    let [u]′ = S.irrelevanceTerm {A = A} {t = t′} [Γ]′ [Γ] [A]′ [A] [u]
    in [Γ] , modelsTermEq [A] [t] [u]′
                           (PI.proof-irrelevanceᵛ {A = A} {t = t} {u = t′} [Γ] [A] [t] [u]′)

  fundamentalTermEq (∃-cong {E} {F} {G} {H} {l} ⊢F F≡H G≡E) 
    with fundamental ⊢F | fundamentalTermEq F≡H | fundamentalTermEq G≡E
  ... | [Γ] , [F] | [Γ]₁ , modelsTermEq [U] [F]ₜ [H]ₜ [F≡H]ₜ
      | [Γ]₂ , modelsTermEq [U]₁ [G]ₜ [E]ₜ [G≡E]ₜ =
    let [U]′  = maybeEmbᵛ {A = Univ _ _} [Γ] (Uᵛ (proj₂ (levelBounded l)) [Γ]) 
        [UΠ] = maybeEmbᵛ {A = Univ _ _} [Γ] (Uᵛ (proj₂ (levelBounded l)) [Γ])
        [F]ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = F} [Γ]₁ [Γ] [U] [U]′ [F]ₜ
        [H]ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = H} [Γ]₁ [Γ] [U] [U]′ [H]ₜ
        [F]′  = S.irrelevance {A = F} [Γ] [Γ]₁ [F]
        [H]   = maybeEmbᵛ {A = H} [Γ] (univᵛ {A = H} [Γ] (≡is≤ PE.refl) [U]′ [H]ₜ′)
        [F≡H] = S.irrelevanceEq {A = F} {B = H} [Γ]₁ [Γ] [F]′ [F]
                  (univEqᵛ {F} {H} [Γ]₁ [U] [F]′ [F≡H]ₜ)
        [U]₁′ = S.irrelevance {A = Univ _ _} [Γ]₂ ([Γ] ∙ [F]) [U]₁ 
        [U]₂′ = S.irrelevanceLift {A = Univ _ _} {F = F} {H = H} [Γ] [F] [H] [F≡H] (λ {Δ} {σ} → [U]₁′ {Δ} {σ})
        [G]ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = G} [Γ]₂ ([Γ] ∙ [F])
                                  [U]₁ (λ {Δ} {σ} → [U]₁′ {Δ} {σ}) [G]ₜ
        [E]ₜ′ = S.irrelevanceTermLift {A = Univ _ _} {F = F} {H = H} {t = E}
                                      [Γ] [F] [H] [F≡H]
                                      (λ {Δ} {σ} → [U]₁′ {Δ} {σ})
                  (S.irrelevanceTerm {A = Univ _ _} {t = E} [Γ]₂ ([Γ] ∙ [F])
                                     [U]₁ (λ {Δ} {σ} → [U]₁′ {Δ} {σ}) [E]ₜ)
        [F≡H]ₜ′ = S.irrelevanceEqTerm {A = Univ _ _} {t = F} {u = H}
                                      [Γ]₁ [Γ] [U] [U]′ [F≡H]ₜ
        [G≡E]ₜ′ = S.irrelevanceEqTerm {A = Univ _ _} {t = G} {u = E} [Γ]₂
                                      (_∙_ {A = F} [Γ] [F]) [U]₁
                                      (λ {Δ} {σ} → [U]₁′ {Δ} {σ}) [G≡E]ₜ
    in  [Γ]
    ,   modelsTermEq
          [UΠ] -- looks like [U]′ but the implicits are different
          (∃ᵗᵛ {F} {G} [Γ] [F] (λ {Δ} {σ} → [U]₁′ {Δ} {σ}) [F]ₜ′ [G]ₜ′ ) 
          (∃ᵗᵛ {H} {E} [Γ] [H] (λ {Δ} {σ} → [U]₂′ {Δ} {σ}) [H]ₜ′ [E]ₜ′) 
          (∃-congᵗᵛ {F} {G} {H} {E} [Γ] [F] [H]
                   (λ {Δ} {σ} → [U]₁′ {Δ} {σ}) (λ {Δ} {σ} → [U]₂′ {Δ} {σ})
                   [F]ₜ′ [G]ₜ′ [H]ₜ′ [E]ₜ′ [F≡H]ₜ′ [G≡E]ₜ′) 
  fundamentalTermEq (Id-cong A≡A' t≡t' u≡u') 
    with fundamentalTermEq A≡A' | fundamentalTermEq t≡t' | fundamentalTermEq u≡u'
  ... | [ΓA] , modelsTermEq [UA] [A]ₜ [A']ₜ [A≡A']ₜ | [Γt] , modelsTermEq [A] [t]ₜ [t']ₜ [t≡t']ₜ  | [Γu] , modelsTermEq [A'] [u]ₜ [u']ₜ [u≡u']ₜ =
    {!!}
    
  fundamentalTermEq {Γ} (Id-Π {A} {rA} {lA} {lB} {l} {B} {t} {u} lA≤ lB≤ ⊢A ⊢B ⊢t ⊢u) 
    with fundamentalTerm ⊢A | fundamentalTerm ⊢B | fundamentalTerm ⊢t | fundamentalTerm ⊢u
  ... | [ΓA] , [UA] , [A]ₜ  | [ΓB] ∙ [AB] , [UB] , [B]ₜ | [Γt] , [Πt] , [t]ₜ | [Γu] , [Πu] , [u]ₜ =
    let [SProp] = maybeEmbᵛ {A = Univ _ _} [Γu] (Uᵛ {rU = %} (proj₂ (levelBounded l)) [Γu]) 
        [UA]′ =  maybeEmbᵛ {A = Univ _ _} [Γu] (Uᵛ (proj₂ (levelBounded lA)) [Γu])
        [A]ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = A} [ΓA] [Γu] [UA] [UA]′ [A]ₜ
        [A] = maybeEmbᵛ {A = A} [Γu] (univᵛ {A = A} [Γu] (≡is≤ PE.refl) [UA]′ [A]ₜ′)
        [ΓuA] = _∙_ {A = A} [Γu] [A]
        [UB]′  = S.irrelevance {A = Univ _ _} (_∙_ {A = A} [ΓB] [AB]) (_∙_ {A = A} [Γu] [A]) (λ {Δ} {σ} → [UB] {Δ} {σ})
        [B]ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = B} (_∙_ {A = A} [ΓB] [AB]) [ΓuA] (λ {Δ} {σ} → [UB] {Δ} {σ}) (λ {Δ} {σ} → [UB]′ {Δ} {σ}) [B]ₜ
        [t]ₜ′  = S.irrelevanceTerm {A = Π A ^ rA ° lA ▹ B ° lB} {t = t} [Γt] [Γu] [Πt] [Πu] [t]ₜ
    in  [Γu] , Id-Πᵗᵛ [Γu] lA≤ lB≤ [A] (λ {Δ} {σ} → [UB]′ {Δ} {σ}) [A]ₜ′ [B]ₜ′ [Πu] [t]ₜ′ [u]ₜ


  fundamentalTermEq {Γ} (Id-ℕ-00 ⊢Γ) =
    let [Γ] = valid ⊢Γ
        [SProp] = Uᵛ emb< [Γ]
        [Unit] = Unitᵗᵛ {l = ⁰} [Γ]
        [id] , [eq] = redSubstTermᵛ {SProp ⁰} {Id ℕ zero zero} {Unit} [Γ] (λ ⊢Δ [σ] → Id-ℕ-00 ⊢Δ) [SProp] [Unit]
    in [Γ] , modelsTermEq (maybeEmbᵛ {A = SProp _} [Γ] [SProp]) [id] [Unit] [eq]
  fundamentalTermEq (Id-ℕ-SS ⊢n ⊢m) with fundamentalTerm ⊢n | fundamentalTerm ⊢m
  fundamentalTermEq (Id-ℕ-SS {n} {m} ⊢n ⊢m) | [Γ] , [ℕ] , [n] | [Γ]′ , [ℕ]′ , [m]  =
    let [SProp] = maybeEmbᵛ {A = SProp ⁰} [Γ]′ (Uᵛ emb< [Γ]′)
        [Unit] = Unitᵗᵛ {l = ⁰} [Γ]′
        ⊢Γ = soundContext [Γ]′
        [n]′ = S.irrelevanceTerm {A = ℕ} {t = n} [Γ] [Γ]′ [ℕ] [ℕ]′ [n]
        Idnm = Idᵗᵛ {A = ℕ} {t = n} {u = m} [Γ]′ [ℕ]′ [n]′ [m]
        ⊢n′ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([ℕ]′ ⊢Δ [σ])) (proj₁ ([n]′ ⊢Δ [σ]))
        ⊢m′ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([ℕ]′ ⊢Δ [σ])) (proj₁ ([m] ⊢Δ [σ]))
        [id] , [eq] = redSubstTermᵛ {SProp ⁰} {t = Id ℕ (suc n) (suc m)} {u = Id ℕ n m} [Γ]′ (λ {Δ} {σ} ⊢Δ [σ] → Id-ℕ-SS (⊢n′ {Δ} {σ} ⊢Δ [σ]) (⊢m′ {Δ} {σ} ⊢Δ [σ])) [SProp] Idnm
    in [Γ]′ , modelsTermEq [SProp] [id] Idnm [eq] 
  fundamentalTermEq (Id-U-ℕℕ ⊢Γ) =
    let [Γ] = valid ⊢Γ
        [SProp] = Uᵛ ∞< [Γ]
        [Unit] = Unitᵗᵛ {l = ¹} [Γ] 
        [id] , [eq] = redSubstTermᵛ {SProp ¹} {Id (U ⁰) ℕ ℕ} {Unit} [Γ] (λ ⊢Δ [σ] → Id-U-ℕℕ ⊢Δ) [SProp] [Unit]
    in [Γ] , modelsTermEq (maybeEmbᵛ {A = SProp ¹} [Γ] [SProp]) [id] [Unit] [eq] 
  fundamentalTermEq (Id-ℕ-0S ⊢n) with fundamentalTerm ⊢n 
  fundamentalTermEq {Γ} (Id-ℕ-0S {n} ⊢n) | [Γ] , [ℕ] , [n] =
    let [SProp] = maybeEmbᵛ {A = SProp ⁰} [Γ] (Uᵛ emb< [Γ])
        [Empty] = Emptyᵗᵛ {ll = ⁰} [Γ] emb<
        ⊢n′ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([ℕ] ⊢Δ [σ])) (proj₁ ([n] ⊢Δ [σ]))
        [id] , [eq] = redSubstTermᵛ {SProp ⁰} {t = Id ℕ zero (suc n)} {u = Empty} [Γ] (λ {Δ} {σ} ⊢Δ [σ] → Id-ℕ-0S (⊢n′ {Δ} {σ} ⊢Δ [σ])) [SProp] [Empty]
    in  [Γ] , modelsTermEq [SProp] [id] [Empty] [eq] 
  fundamentalTermEq (Id-ℕ-S0 ⊢n) with fundamentalTerm ⊢n 
  fundamentalTermEq {Γ} (Id-ℕ-S0 {n} ⊢n) | [Γ] , [ℕ] , [n] =
    let [SProp] = maybeEmbᵛ {A = SProp ⁰} [Γ] (Uᵛ emb< [Γ])
        [Empty] = Emptyᵗᵛ {ll = ⁰} [Γ] emb<
        ⊢n′ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([ℕ] ⊢Δ [σ])) (proj₁ ([n] ⊢Δ [σ]))
        [id] , [eq] = redSubstTermᵛ {SProp ⁰} {t = Id ℕ (suc n) zero} {u = Empty} [Γ] (λ {Δ} {σ} ⊢Δ [σ] → Id-ℕ-S0 (⊢n′ {Δ} {σ} ⊢Δ [σ])) [SProp] [Empty]
    in  [Γ] , modelsTermEq [SProp] [id] [Empty] [eq] 
  fundamentalTermEq (Id-U-ℕΠ ⊢A ⊢B) with fundamentalTerm ⊢A | fundamentalTerm ⊢B
  fundamentalTermEq {Γ} (Id-U-ℕΠ {A} {rA} {B} ⊢A ⊢B) | [Γ] , [UA] , [A]ᵗ | [Γ]₁ ∙ [A]₁ , [UB] , [B]ᵗ =
    let [SProp] = Uᵛ {rU = %} ∞< [Γ]
        [Empty] = Emptyᵗᵛ {ll = ¹} [Γ] ∞<
        ⊢AΔ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([UA] ⊢Δ [σ])) (proj₁ ([A]ᵗ ⊢Δ [σ]))
        [A] = univᵛ {A = A} [Γ] (≡is≤ PE.refl) [UA] [A]ᵗ
        ⊢A = λ {Δ} {σ} ⊢Δ [σ] → escape (proj₁ ([A] {Δ} {σ} ⊢Δ [σ]))
        [Γ∙A] :  ⊩ᵛ (Γ ∙ A ^ [ rA , ι ⁰ ])
        [Γ∙A] = [Γ] ∙ [A]
        [UB]′ = S.irrelevance {A = Univ _ _} ([Γ]₁ ∙ [A]₁) [Γ∙A] (λ {Δ} {σ} → [UB] {Δ} {σ}) 
        [B]ᵗ′  = S.irrelevanceTerm {A = Univ _ _} {t = B} ([Γ]₁ ∙ [A]₁) [Γ∙A] (λ {Δ} {σ} → [UB] {Δ} {σ}) (λ {Δ} {σ} → [UB]′ {Δ} {σ}) [B]ᵗ
        ⊢BΔ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([UB]′ {Δ} {σ} ⊢Δ [σ])) (proj₁ ([B]ᵗ′ {Δ} {σ} ⊢Δ [σ]))
        [liftσ] = λ {Δ} {σ} ⊢Δ [σ] → liftSubstS {F = A} [Γ] ⊢Δ [A] [σ] 
        [id] , [eq] = redSubstTermᵛ {SProp ¹} {t = Id (U ⁰) ℕ (Π A ^ rA ° ⁰ ▹ B ° ⁰)} {u = Empty} [Γ]
                                    (λ {Δ} {σ} ⊢Δ [σ] → Id-U-ℕΠ (⊢AΔ {Δ} {σ} ⊢Δ [σ]) (⊢BΔ (⊢Δ ∙ ⊢A {Δ} {σ} ⊢Δ [σ]) ([liftσ] {Δ} {σ} ⊢Δ [σ])))
                                    [SProp] [Empty]
    in [Γ] , modelsTermEq [SProp] [id] [Empty] [eq]
  fundamentalTermEq (Id-U-Πℕ ⊢A ⊢B) with fundamentalTerm ⊢A | fundamentalTerm ⊢B
  fundamentalTermEq {Γ} (Id-U-Πℕ {A} {rA} {B} ⊢A ⊢B) | [Γ] , [UA] , [A]ᵗ | [Γ]₁ ∙ [A]₁ , [UB] , [B]ᵗ =
    let [SProp] = Uᵛ {rU = %} ∞< [Γ]
        [Empty] = Emptyᵗᵛ {ll = ¹} [Γ] ∞<
        ⊢AΔ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([UA] ⊢Δ [σ])) (proj₁ ([A]ᵗ ⊢Δ [σ]))
        [A] = univᵛ {A = A} [Γ] (≡is≤ PE.refl) [UA] [A]ᵗ
        ⊢A = λ {Δ} {σ} ⊢Δ [σ] → escape (proj₁ ([A] {Δ} {σ} ⊢Δ [σ]))
        [Γ∙A] :  ⊩ᵛ (Γ ∙ A ^ [ rA , ι ⁰ ])
        [Γ∙A] = [Γ] ∙ [A]
        [UB]′ = S.irrelevance {A = Univ _ _} ([Γ]₁ ∙ [A]₁) [Γ∙A] (λ {Δ} {σ} → [UB] {Δ} {σ}) 
        [B]ᵗ′  = S.irrelevanceTerm {A = Univ _ _} {t = B} ([Γ]₁ ∙ [A]₁) [Γ∙A] (λ {Δ} {σ} → [UB] {Δ} {σ}) (λ {Δ} {σ} → [UB]′ {Δ} {σ}) [B]ᵗ
        ⊢BΔ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([UB]′ {Δ} {σ} ⊢Δ [σ])) (proj₁ ([B]ᵗ′ {Δ} {σ} ⊢Δ [σ]))
        [liftσ] = λ {Δ} {σ} ⊢Δ [σ] → liftSubstS {F = A} [Γ] ⊢Δ [A] [σ] 
        [id] , [eq] = redSubstTermᵛ {SProp ¹} {t = Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰) ℕ} {u = Empty} [Γ]
                                    (λ {Δ} {σ} ⊢Δ [σ] → Id-U-Πℕ (⊢AΔ {Δ} {σ} ⊢Δ [σ]) (⊢BΔ (⊢Δ ∙ ⊢A {Δ} {σ} ⊢Δ [σ]) ([liftσ] {Δ} {σ} ⊢Δ [σ])))
                                    [SProp] [Empty]
    in [Γ] , modelsTermEq [SProp] [id] [Empty] [eq]

  fundamentalTermEq {Γ} (Id-U-ΠΠ!% {A} {rA} {B} {A'} {rA'} {B'} eq ⊢A ⊢B ⊢A' ⊢B')
    with fundamentalTerm ⊢A | fundamentalTerm ⊢B | fundamentalTerm ⊢A' | fundamentalTerm ⊢B'
  ... | [Γ] , [UA] , [A]ᵗ | [ΓB] , [UB] , [B]ᵗ | [ΓA'] , [UA'] , [A']ᵗ | [ΓB'] , [UB'] , [B']ᵗ =
    let [SProp] = Uᵛ {rU = %} ∞< [Γ]
        [Empty] = Emptyᵗᵛ {ll = ¹} [Γ] ∞<
        ⊢AΔ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([UA] ⊢Δ [σ])) (proj₁ ([A]ᵗ ⊢Δ [σ]))
        [A] = univᵛ {A = A} [Γ] (≡is≤ PE.refl) [UA] [A]ᵗ
        ⊢A = λ {Δ} {σ} ⊢Δ [σ] → escape (proj₁ ([A] ⊢Δ [σ]))
        [Γ∙A] :  ⊩ᵛ (Γ ∙ A ^ [ rA , ι ⁰ ])
        [Γ∙A] = [Γ] ∙ [A]
        [UB]′ = S.irrelevance {A = Univ _ _} [ΓB] [Γ∙A] (λ {Δ} {σ} → [UB] {Δ} {σ}) 
        [B]ᵗ′  = S.irrelevanceTerm {A = Univ _ _} {t = B} [ΓB] [Γ∙A] (λ {Δ} {σ} → [UB] {Δ} {σ}) (λ {Δ} {σ} → [UB]′ {Δ} {σ}) [B]ᵗ
        ⊢BΔ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([UB]′ {Δ} {σ} ⊢Δ [σ])) (proj₁ ([B]ᵗ′ {Δ} {σ} ⊢Δ [σ]))
        [UA']′ = S.irrelevance {A = Univ _ _} ([ΓA']) [Γ] [UA'] 
        [A']ᵗ′ = S.irrelevanceTerm {A = Univ _ _} {t = A'} ([ΓA']) [Γ] [UA'] [UA']′ [A']ᵗ 
        ⊢AΔ' = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([UA']′ ⊢Δ [σ])) (proj₁ ([A']ᵗ′ ⊢Δ [σ]))
        [A'] = univᵛ {A = A'} [Γ] (≡is≤ PE.refl) [UA']′ [A']ᵗ′
        ⊢A' = λ {Δ} {σ} ⊢Δ [σ] → escape (proj₁ ([A'] ⊢Δ [σ]))
        [Γ∙A'] :  ⊩ᵛ (Γ ∙ A' ^ [ rA' , ι ⁰ ])
        [Γ∙A'] = [Γ] ∙ [A']
        [UB']′ = S.irrelevance {A = Univ _ _} [ΓB'] [Γ∙A'] (λ {Δ} {σ} → [UB'] {Δ} {σ}) 
        [B']ᵗ′  = S.irrelevanceTerm {A = Univ _ _} {t = B'} [ΓB'] [Γ∙A'] (λ {Δ} {σ} → [UB'] {Δ} {σ}) (λ {Δ} {σ} → [UB']′ {Δ} {σ}) [B']ᵗ
        ⊢BΔ' = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([UB']′ {Δ} {σ} ⊢Δ [σ])) (proj₁ ([B']ᵗ′ {Δ} {σ} ⊢Δ [σ]))
        [id] , [eq] = redSubstTermᵛ {SProp ¹} {t = Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰) (Π A' ^ rA' ° ⁰ ▹ B' ° ⁰)} {u = Empty} [Γ]
                                    (λ {Δ} {σ} ⊢Δ [σ] → Id-U-ΠΠ!% eq (⊢AΔ {Δ} {σ} ⊢Δ [σ]) (⊢BΔ (⊢Δ ∙ ⊢A {Δ} {σ} ⊢Δ [σ]) (liftSubstS {F = A} [Γ] ⊢Δ [A] [σ]))
                                                                     (⊢AΔ' {Δ} {σ} ⊢Δ [σ]) (⊢BΔ' (⊢Δ ∙ ⊢A' {Δ} {σ} ⊢Δ [σ]) (liftSubstS {F = A'} [Γ] ⊢Δ [A'] [σ])))
                                    [SProp] [Empty]
    in [Γ] , modelsTermEq [SProp] [id] [Empty] [eq]
  fundamentalTermEq (cast-cong {A} {A'} {B} {B'} {e} {e'} {t} {t'} A≡A' B≡B' t≡t' ⊢e ⊢e')
    with fundamentalTermEq A≡A' | fundamentalTermEq B≡B' | fundamentalTermEq t≡t' | fundamentalTerm ⊢e | fundamentalTerm ⊢e'
  ... | [Γ] , modelsTermEq [UA] [A]ₜ [A']ₜ [A≡A']ₜ | [Γ]₁ , modelsTermEq [UB] [B]ₜ [B']ₜ [B≡B']ₜ
      | [Γ]₂ , modelsTermEq [A]₁ [t]ₜ [t']ₜ [t≡t']ₜ | [Γe] , [IdAB] , [e]ₜ
      | [Γe'] , [IdAB'] , [e']ₜ = 
    let [A] = maybeEmbᵛ {A = A} [Γ] (univᵛ {A = A} [Γ] (≡is≤ PE.refl) [UA] [A]ₜ)
        [B] = maybeEmbᵛ {A = B} [Γ]₁ (univᵛ {A = B} [Γ]₁ (≡is≤ PE.refl) [UB] [B]ₜ)
        [UA]′  = S.irrelevance {A = Univ _ _} [Γ] [Γ]₂ [UA]
        [A]ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = A} [Γ] [Γ]₂ [UA] [UA]′ [A]ₜ
        [A']ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = A'} [Γ] [Γ]₂ [UA] [UA]′ [A']ₜ
        [UB]′  = S.irrelevance {A = Univ _ _} [Γ]₁ [Γ]₂ [UB]
        [B]ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = B} [Γ]₁ [Γ]₂ [UB] [UB]′ [B]ₜ
        [B]ₜ′′ = S.irrelevanceTerm {A = Univ _ _} {t = B} [Γ]₁ [Γ]₂ [UB] [UA]′ [B]ₜ
        [B']ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = B'} [Γ]₁ [Γ]₂ [UB] [UB]′ [B']ₜ
        [B']ₜ′′ = S.irrelevanceTerm {A = Univ _ _} {t = B'} [Γ]₁ [Γ]₂ [UB] [UA]′ [B']ₜ
        [A]′ = maybeEmbᵛ {A = A} [Γ]₂ (univᵛ {A = A} [Γ]₂ (≡is≤ PE.refl) [UA]′ [A]ₜ′)
        [t]ₜ′ = S.irrelevanceTerm {A = A} {t = t} [Γ]₂ [Γ]₂ [A]₁ [A]′ [t]ₜ
        [A']′ = maybeEmbᵛ {A = A'} [Γ]₂ (univᵛ {A = A'} [Γ]₂ (≡is≤ PE.refl) [UA]′ [A']ₜ′)
        [t']ₜ′ = S.irrelevanceTerm {A = A} {t = t'} [Γ]₂ [Γ]₂ [A]₁ [A]′ [t']ₜ
        [A≡A']ₜ′ = S.irrelevanceEqTerm {A = Univ _ _} {t = A} {u = A'} [Γ] [Γ]₂ [UA] [UA]′ [A≡A']ₜ
        [A≡A']′ = S.irrelevanceEq {A = A} {B = A'} [Γ] [Γ]₂ [A] [A]′ (univEqᵛ {A = A} {B = A'} [Γ] [UA] [A] [A≡A']ₜ)
        [t'A]ₜ = convᵛ {t'} {A} {A'} [Γ]₂ [A]′ [A']′ [A≡A']′ [t']ₜ′
        [t≡t']ₜ′ = S.irrelevanceEqTerm {A = A} {t = t} {u = t'} [Γ]₂ [Γ]₂ [A]₁ [A]′ [t≡t']ₜ
        [B]′ = maybeEmbᵛ {A = B} [Γ]₂ (univᵛ {A = B} [Γ]₂ (≡is≤ PE.refl) [UB]′ [B]ₜ′)
        [B']′ = maybeEmbᵛ {A = B'} [Γ]₂ (univᵛ {A = B'} [Γ]₂ (≡is≤ PE.refl) [UB]′ [B']ₜ′)
        [B≡B']ₜ′ = S.irrelevanceEqTerm {A = Univ _ _} {t = B} {u = B'} [Γ]₁ [Γ]₂ [UB] [UB]′ [B≡B']ₜ
        [B≡B']′ = S.irrelevanceEq {A = B} {B = B'} [Γ]₁ [Γ]₂ [B] [B]′ (univEqᵛ {A = B} {B = B'} [Γ]₁ [UB] [B] [B≡B']ₜ)
        [IdAB]′  = S.irrelevance {A = Id (Univ _ _) A B} [Γe] [Γ]₂ [IdAB]
        [e]ₜ′ = S.irrelevanceTerm {A = Id (Univ _ _) A B} {t = e} [Γe] [Γ]₂ [IdAB] [IdAB]′ [e]ₜ
        [IdAB']′  = S.irrelevance {A = Id (Univ _ _) A' B'} [Γe'] [Γ]₂ [IdAB']
        [e']ₜ′ = S.irrelevanceTerm {A = Id (Univ _ _) A' B'} {t = e'} [Γe'] [Γ]₂ [IdAB'] [IdAB']′ [e']ₜ
    in  [Γ]₂
    ,   modelsTermEq [B]′ (castᵗᵛ {A} {B} { ! } {t} {e} [Γ]₂ [UA]′ [A]ₜ′ [B]ₜ′′ [A]′ [B]′ [t]ₜ′ [IdAB]′ [e]ₜ′)
                          (conv₂ᵛ {cast _ A' B' e' t'} {B} {B'} [Γ]₂ [B]′ [B']′ [B≡B']′
                            (castᵗᵛ {A'} {B'} { ! } {t'} {e'} [Γ]₂ [UA]′ [A']ₜ′ [B']ₜ′′ [A']′ [B']′ [t'A]ₜ [IdAB']′ [e']ₜ′))
                          (cast-congᵗᵛ {A} {A'} {B} {B'} {t} {t'} {e} {e'} [Γ]₂ [UA]′ [UB]′ [A]ₜ′ [A']ₜ′ [B]ₜ′ [B']ₜ′ [A≡A']ₜ′ [B≡B']ₜ′ [A]′ [A']′ [B]′ [B']′ [t]ₜ′ [t'A]ₜ [t≡t']ₜ′
                                       [IdAB]′ [e]ₜ′ [IdAB']′ [e']ₜ′)

  fundamentalTermEq (cast-ℕ-0 {e} ⊢e) with fundamentalTerm ⊢e
  ... | [Γ] , [Id] , [e]ₜ =
    let ⊢eΔ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([Id] {Δ} {σ} ⊢Δ [σ])) (proj₁ ([e]ₜ {Δ} {σ} ⊢Δ [σ]))
        [zero] = zeroᵛ {l = ∞} [Γ]
        [id] , [eq] = redSubstTermᵛ {ℕ} {cast ⁰ ℕ ℕ e zero} {zero} {∞} [Γ]
                                    (λ {Δ} {σ} ⊢Δ [σ] → cast-ℕ-0 (⊢eΔ {Δ} {σ} ⊢Δ [σ]))
                                    (ℕᵛ [Γ]) [zero]
    in [Γ] , modelsTermEq (ℕᵛ [Γ]) [id] [zero] [eq] 
  fundamentalTermEq (cast-ℕ-S {e} {n} ⊢e ⊢n) with fundamentalTerm ⊢e | fundamentalTerm ⊢n 
  ... | [Γ] , [Id] , [e]ₜ | [Γ]₁ , [ℕ] , [n]ₜ =
    let [Id]′  = S.irrelevance {A = Id (U _) ℕ ℕ} [Γ] [Γ]₁ [Id]
        [e]ₜ′ = S.irrelevanceTerm {A = Id (U _) ℕ ℕ} {t = e} [Γ] [Γ]₁ [Id] [Id]′ [e]ₜ
        ⊢eΔ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([Id]′ {Δ} {σ} ⊢Δ [σ])) (proj₁ ([e]ₜ′ {Δ} {σ} ⊢Δ [σ]))
        ⊢nΔ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([ℕ] {Δ} {σ} ⊢Δ [σ])) (proj₁ ([n]ₜ {Δ} {σ} ⊢Δ [σ]))
        [suc-cast] = sucᵛ {n = cast ⁰ ℕ ℕ e n} [Γ]₁ [ℕ] (castᵗᵛ {ℕ} {ℕ} { ! } {n} {e} [Γ]₁ (maybeEmbᵛ {A = Univ _ _} [Γ]₁ (Uᵛ emb< [Γ]₁))
                                                                (ℕᵗᵛ [Γ]₁) (ℕᵗᵛ [Γ]₁) [ℕ] [ℕ] [n]ₜ [Id]′ [e]ₜ′)
        [id] , [eq] = redSubstTermᵛ {ℕ} {cast ⁰ ℕ ℕ e (suc n)} {suc (cast ⁰ ℕ ℕ e n)} {∞} [Γ]₁
                                    (λ {Δ} {σ} ⊢Δ [σ] → cast-ℕ-S (⊢eΔ {Δ} {σ} ⊢Δ [σ]) (⊢nΔ {Δ} {σ} ⊢Δ [σ]))
                                    [ℕ] [suc-cast]
    in [Γ]₁ , modelsTermEq [ℕ] [id] [suc-cast] [eq] 
  fundamentalTermEq {Γ} (cast-Π {A} {A'} {rA} {B} {B'} {e} {f} ⊢A ⊢B ⊢A' ⊢B' ⊢e ⊢f)
    with fundamentalTerm ⊢A | fundamentalTerm ⊢B | fundamentalTerm ⊢A' | fundamentalTerm ⊢B' | fundamentalTerm ⊢e | fundamentalTerm ⊢f 
  ... | [ΓA] , [UA] , [A]ₜ | [ΓB] ∙ [AB] , [UB] , [B]ₜ | [ΓA'] , [UA'] , [A']ₜ | [ΓB'] ∙ [AB'] , [UB'] , [B']ₜ | [Γ] , [Id] , [e]ₜ | [Γ]₁ , [ΠAB] , [f]ₜ =
    let [UA]′ = maybeEmbᵛ {A = Univ rA _} [Γ]₁ (Uᵛ emb< [Γ]₁) 
        [A]ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = A} [ΓA] [Γ]₁ [UA] [UA]′ [A]ₜ
        [A']ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = A'} [ΓA'] [Γ]₁ [UA'] [UA]′ [A']ₜ
        [A] = maybeEmbᵛ {A = A} [Γ]₁ (univᵛ {A = A} [Γ]₁ (≡is≤ PE.refl) [UA]′ [A]ₜ′)
        [A'] = maybeEmbᵛ {A = A'} [Γ]₁ (univᵛ {A = A'} [Γ]₁ (≡is≤ PE.refl) [UA]′ [A']ₜ′)
        [ΓB]₁ = [Γ]₁ ∙ [A]
        [UB]′ = S.irrelevance {A = Univ _ _} {Γ = Γ ∙ A ^ _} ([ΓB] ∙ [AB]) [ΓB]₁ (λ {Δ} {σ} → [UB] {Δ} {σ}) 
        [B]ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = B} ([ΓB] ∙ [AB]) [ΓB]₁ (λ {Δ} {σ} → [UB] {Δ} {σ}) (λ {Δ} {σ} → [UB]′ {Δ} {σ}) [B]ₜ
        [ΓB']₁ = [Γ]₁ ∙ [A']
        [UB']′ = S.irrelevance {A = Univ _ _} {Γ = Γ ∙ A' ^ _} ([ΓB'] ∙ [AB']) [ΓB']₁ (λ {Δ} {σ} → [UB'] {Δ} {σ}) 
        [B']ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = B'} ([ΓB'] ∙ [AB']) [ΓB']₁ (λ {Δ} {σ} → [UB'] {Δ} {σ}) (λ {Δ} {σ} → [UB']′ {Δ} {σ}) [B']ₜ
        [B']  = maybeEmbᵛ {A = B'} [ΓB']₁ (univᵛ {A = B'} [ΓB']₁ (≡is≤ PE.refl) (λ {Δ} {σ} → [UB']′ {Δ} {σ}) [B']ₜ′)
        [Id]′  = S.irrelevance {A = Id (Univ _ _) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰ )} [Γ] [Γ]₁ [Id]
        [e]ₜ′ = S.irrelevanceTerm {A = Id (Univ _ _)  (Π A ^ rA ° ⁰ ▹ B ° ⁰ ) (Π A' ^ rA ° ⁰ ▹ B' ° ⁰ )} {t = e} [Γ] [Γ]₁ [Id] [Id]′ [e]ₜ
     in [Γ]₁ , cast-Πᵗᵛ {A} {B} {A'} {B'} {rA} {Γ} {e} {f} [Γ]₁ [A] [A'] (λ {Δ} {σ} → [UB]′ {Δ} {σ}) (λ {Δ} {σ} → [UB']′ {Δ} {σ})
                      [A]ₜ′ [B]ₜ′ [A']ₜ′ [B']ₜ′ [Id]′ [e]ₜ′ [ΠAB] [f]ₜ
  fundamentalTermEq {Γ} (Id-SProp {A} {B} ⊢A ⊢B) with fundamentalTerm ⊢A | fundamentalTerm ⊢B
  ... | [ΓA] , [UA] , [A]ₜ | [ΓB] , [UB] , [B]ₜ =
    let [SProp] = Uᵛ {rU = %} ∞< [ΓB]
        [UA]′ =  maybeEmbᵛ {A = Univ _ _} [ΓB] (Uᵛ emb< [ΓB])
        [A]ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = A} [ΓA] [ΓB] [UA] [UA]′ [A]ₜ
        [B]ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = B} [ΓB] [ΓB] [UB] [UA]′ [B]ₜ
        ⊢AΔ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([UA]′ {Δ} {σ} ⊢Δ [σ])) (proj₁ ([A]ₜ′ ⊢Δ [σ]))
        [A] = maybeEmbᵛ {A = A} [ΓB] (univᵛ {A = A} [ΓB] (≡is≤ PE.refl) [UA]′ [A]ₜ′)
        [B] = maybeEmbᵛ {A = B} [ΓB] (univᵛ {A = B} [ΓB] (≡is≤ PE.refl) [UB] [B]ₜ)
        ⊢BΔ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([UB] {Δ} {σ} ⊢Δ [σ])) (proj₁ ([B]ₜ ⊢Δ [σ]))
        _▹▹⁰_ = λ A B → A ^ % ° ⁰ ▹▹ B ° ⁰
        Id-SProp-res = λ A B → (A ▹▹⁰ B) ×× (B ▹▹⁰ A)
        [Id-SProp] : Γ ⊩ᵛ Id (SProp ⁰) A B ⇒ Id-SProp-res A B ∷ SProp ¹ ^ ∞ / [ΓB]
        [Id-SProp] = λ {Δ} {σ} ⊢Δ [σ] → PE.subst (λ ret → Δ ⊢ Id (SProp ⁰) (subst σ A) (subst σ B) ⇒ ret ∷ SProp ¹ ^ ∞ )
                                                 (PE.cong₄ (λ a b c d → ∃ (Π a ^ % ° ⁰ ▹ b ° ⁰) ▹ (Π c ^ % ° ⁰ ▹ d ° ⁰))
                                                           PE.refl (PE.sym (Idsym-subst-lemma σ B)) (PE.sym (Idsym-subst-lemma σ B))
                                                           (PE.trans (PE.cong wk1d (PE.sym (Idsym-subst-lemma σ A))) (PE.sym (Idsym-subst-lemma-wk1d σ (wk1 A)))))
                                                 (Id-SProp {A = subst σ A} {B = subst σ B} (⊢AΔ {Δ} {σ} ⊢Δ [σ]) (⊢BΔ {Δ} {σ} ⊢Δ [σ]))       
        [A▹▹B]ₜ = ▹▹ᵗᵛ {F = A} {G = B} (<is≤ 0<1) (<is≤ 0<1) [ΓB] [A] [UA]′ [A]ₜ′ [B]ₜ′
        [A▹▹B] = maybeEmbᵛ {A = A ▹▹⁰ B} [ΓB] (univᵛ {A = A ▹▹⁰ B} [ΓB] (≡is≤ PE.refl) [SProp] [A▹▹B]ₜ)
        [B▹▹A]ₜ = ▹▹ᵗᵛ {F = B} {G = A} (<is≤ 0<1) (<is≤ 0<1) [ΓB] [B] [UA]′ [B]ₜ′ [A]ₜ′
        [Id-SProp-res] : Γ ⊩ᵛ⟨ ∞ ⟩ Id-SProp-res A B ∷ SProp ¹ ^ [ ! , ∞ ] / [ΓB] / [SProp]
        [Id-SProp-res] = ××ᵗᵛ {F = A ▹▹⁰ B} {G = B ▹▹⁰ A} [ΓB] [A▹▹B] [A▹▹B]ₜ [B▹▹A]ₜ
        [id] , [eq] = redSubstTermᵛ {SProp ¹} {Id (SProp ⁰) A B} {Id-SProp-res A B}
                                    [ΓB] (λ {Δ} {σ} ⊢Δ [σ] → [Id-SProp] {Δ} {σ} ⊢Δ [σ]) 
                                    [SProp] [Id-SProp-res] 
    in [ΓB] , modelsTermEq [SProp] [id] [Id-SProp-res] [eq]
  fundamentalTermEq (Id-U-ΠΠ ⊢A ⊢B ⊢A' ⊢B') with fundamentalTerm ⊢A | fundamentalTerm ⊢B | fundamentalTerm ⊢A' | fundamentalTerm ⊢B'
  fundamentalTermEq (Id-U-ΠΠ {A} {A'} {rA} {B} {B'} ⊢A ⊢B ⊢A' ⊢B') | [Γ] , [UA] , [A]ₜ | [Γ]₁ ∙ [A]₁ , [UB] , [B]ₜ | [Γ]' , [UA'] , [A']ₜ | [Γ]₁' ∙ [A']₁ , [UB'] , [B']ₜ =
    let [A]′  = S.irrelevance {A = A} [Γ] [Γ]₁' (maybeEmbᵛ {A = A} [Γ] (univᵛ {A = A} [Γ] (≡is≤ PE.refl) [UA] [A]ₜ))
        [A']′  = S.irrelevance {A = A'} [Γ]' [Γ]₁' (maybeEmbᵛ {A = A'} [Γ]' (univᵛ {A = A'} [Γ]' (≡is≤ PE.refl) [UA'] [A']ₜ))
        [UB]′ = S.irrelevance {A = Univ _ _} (_∙_ {A = A} [Γ]₁  [A]₁) (_∙_ {A = A} [Γ]₁' [A]′) (λ {Δ} {σ} → [UB] {Δ} {σ}) 
        [UB']′ = S.irrelevance {A = Univ _ _} (_∙_ {A = A'} [Γ]₁' [A']₁) (_∙_ {A = A'} [Γ]₁' [A']′) (λ {Δ} {σ} → [UB'] {Δ} {σ})
        [U] = maybeEmbᵛ {A = Univ rA _} [Γ]₁' (Uᵛ emb< [Γ]₁')
        [A]ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = A} [Γ] [Γ]₁' [UA] [U] [A]ₜ
        [A']ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = A'} [Γ]' [Γ]₁' [UA'] [U] [A']ₜ
        [B]ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = B}  (_∙_ {A = A} [Γ]₁  [A]₁) (_∙_ {A = A} [Γ]₁' [A]′) (λ {Δ} {σ} → [UB] {Δ} {σ}) (λ {Δ} {σ} → [UB]′ {Δ} {σ}) [B]ₜ
        [B']ₜ′  = S.irrelevanceTerm {A = Univ _ _} {t = B'} (_∙_ {A = A'} [Γ]₁' [A']₁) (_∙_ {A = A'} [Γ]₁' [A']′) (λ {Δ} {σ} → [UB'] {Δ} {σ}) (λ {Δ} {σ} → [UB']′ {Δ} {σ}) [B']ₜ
    in [Γ]₁' , Id-U-ΠΠᵗᵛ [Γ]₁' [A]′ [A']′ (λ {Δ} {σ} → [UB]′ {Δ} {σ}) (λ {Δ} {σ} → [UB']′ {Δ} {σ}) [A]ₜ′ [B]ₜ′ [A']ₜ′ [B']ₜ′

-- Fundamental theorem for substitutions.
fundamentalSubst : ∀ {Γ Δ σ} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
      → Δ ⊢ˢ σ ∷ Γ
      → ∃ λ [Γ] → Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ
fundamentalSubst ε ⊢Δ [σ] = ε , tt
fundamentalSubst (⊢Γ ∙ ⊢A) ⊢Δ ([tailσ] , [headσ]) =
  let [Γ] , [A] = fundamental ⊢A
      [Δ] , [A]′ , [t] = fundamentalTerm [headσ]
      [Γ]′ , [σ] = fundamentalSubst ⊢Γ ⊢Δ [tailσ]
      [tailσ]′ = S.irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ]
      [idA]  = proj₁ ([A]′ (soundContext [Δ]) (idSubstS [Δ]))
      [idA]′ = proj₁ ([A] ⊢Δ [tailσ]′)
      [idt]  = proj₁ ([t] (soundContext [Δ]) (idSubstS [Δ]))
  in  [Γ] ∙ [A] , ([tailσ]′
  ,   irrelevanceTerm″ (subst-id _) PE.refl PE.refl (subst-id _) [idA] [idA]′ [idt])

-- Fundamental theorem for substitution equality.
fundamentalSubstEq : ∀ {Γ Δ σ σ′} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
      → Δ ⊢ˢ σ ≡ σ′ ∷ Γ
      → ∃₂ λ [Γ] [σ]
      → ∃  λ ([σ′] : Δ ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ)
      → Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ]
fundamentalSubstEq ε ⊢Δ σ = ε , tt , tt , tt
fundamentalSubstEq (⊢Γ ∙ ⊢A) ⊢Δ (tailσ≡σ′ , headσ≡σ′) =
  let [Γ] , [A] = fundamental ⊢A
      [Γ]′ , [tailσ] , [tailσ′] , [tailσ≡σ′] = fundamentalSubstEq ⊢Γ ⊢Δ tailσ≡σ′
      [Δ] , modelsTermEq [A]′ [t] [t′] [t≡t′] = fundamentalTermEq headσ≡σ′
      [tailσ]′ = S.irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [tailσ]
      [tailσ′]′ = S.irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [tailσ′]
      [tailσ≡σ′]′ = S.irrelevanceSubstEq [Γ]′ [Γ] ⊢Δ ⊢Δ [tailσ] [tailσ]′ [tailσ≡σ′]
      [idA]  = proj₁ ([A]′ (soundContext [Δ]) (idSubstS [Δ]))
      [idA]′ = proj₁ ([A] ⊢Δ [tailσ]′)
      [idA]″ = proj₁ ([A] ⊢Δ [tailσ′]′)
      [idt]  = proj₁ ([t] (soundContext [Δ]) (idSubstS [Δ]))
      [idt′] = proj₁ ([t′] (soundContext [Δ]) (idSubstS [Δ]))
      [idt≡t′]  = [t≡t′] (soundContext [Δ]) (idSubstS [Δ])
  in  [Γ] ∙ [A]
  ,   ([tailσ]′ , irrelevanceTerm″ (subst-id _) PE.refl PE.refl (subst-id _) [idA] [idA]′ [idt])
  ,   ([tailσ′]′ , convTerm₁ [idA]′ [idA]″
                             (proj₂ ([A] ⊢Δ [tailσ]′) [tailσ′]′ [tailσ≡σ′]′)
                             (irrelevanceTerm″ (subst-id _) PE.refl PE.refl (subst-id _)
                                                [idA] [idA]′ [idt′]))
  ,   ([tailσ≡σ′]′ , irrelevanceEqTerm″ PE.refl PE.refl (subst-id _) (subst-id _) (subst-id _)
                                         [idA] [idA]′ [idt≡t′])
