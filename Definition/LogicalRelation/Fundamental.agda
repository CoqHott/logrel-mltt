{-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Fundamental {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed hiding (tt)
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Substitution.Conversion
open import Definition.LogicalRelation.Substitution.Reduction
open import Definition.LogicalRelation.Substitution.Reflexivity
open import Definition.LogicalRelation.Substitution.MaybeEmbed
open import Definition.LogicalRelation.Substitution.Introductions.Nat
open import Definition.LogicalRelation.Substitution.Introductions.Natrec
open import Definition.LogicalRelation.Substitution.Introductions.Empty
open import Definition.LogicalRelation.Substitution.Introductions.Emptyrec
open import Definition.LogicalRelation.Substitution.Introductions.Universe
open import Definition.LogicalRelation.Substitution.Introductions.Pi
open import Definition.LogicalRelation.Substitution.Introductions.Id
open import Definition.LogicalRelation.Substitution.Introductions.Cast
open import Definition.LogicalRelation.Substitution.Introductions.Lambda
open import Definition.LogicalRelation.Substitution.Introductions.Application
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
import Definition.LogicalRelation.Substitution.ProofIrrelevance as PI
import Definition.LogicalRelation.Substitution.Irrelevance as S

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
  fundamentalEq = {!!}
{-
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
-}

-- Fundamental theorem for variables.
  fundamentalVar : ∀ {Γ A rA x}
                 → x ∷ A ^ rA ∈ Γ
                 → ([Γ] : ⊩ᵛ Γ)
                 → ∃ λ ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ rA / [Γ])
                 → Γ ⊩ᵛ⟨ ∞ ⟩ var x ∷ A ^ rA / [Γ] / [A]
  fundamentalVar here (_∙_ {A = A} {rA = rA} {l = l} [Γ] [A]) =
    (λ ⊢Δ [σ] →
       let [σA]  = proj₁ ([A] ⊢Δ (proj₁ [σ]))
           [σA′] = maybeEmb (irrelevance′ (PE.sym (subst-wk A)) [σA])
       in  [σA′]
       ,   (λ [σ′] [σ≡σ′] →
              irrelevanceEq″ (PE.sym (subst-wk A)) (PE.sym (subst-wk A)) PE.refl PE.refl 
                              [σA] [σA′] (proj₂ ([A] ⊢Δ (proj₁ [σ]))
                                                (proj₁ [σ′]) (proj₁ [σ≡σ′]))))
    , (λ ⊢Δ [σ] →
         let [σA]  = proj₁ ([A] ⊢Δ (proj₁ [σ]))
             [σA′] = maybeEmb (irrelevance′ (PE.sym (subst-wk A)) [σA])
         in  irrelevanceTerm′ (PE.sym (subst-wk A)) PE.refl PE.refl [σA] [σA′] (proj₂ [σ])
    , (λ [σ′] [σ≡σ′] → irrelevanceEqTerm′ (PE.sym (subst-wk A)) PE.refl PE.refl 
                                          [σA] [σA′] (proj₂ [σ≡σ′])))
  fundamentalVar (there {A = A} h) ([Γ] ∙ [B]) =
    (λ ⊢Δ [σ] →
       let [h]   = proj₁ (fundamentalVar h [Γ]) ⊢Δ (proj₁ [σ])
           [σA]  = proj₁ [h]
           [σA′] = irrelevance′ (PE.sym (subst-wk A)) [σA]
       in  [σA′]
       ,   (λ [σ′] [σ≡σ′] →
              irrelevanceEq″ (PE.sym (subst-wk A)) (PE.sym (subst-wk A)) PE.refl PE.refl
                              [σA] [σA′]
                              (proj₂ [h] (proj₁ [σ′]) (proj₁ [σ≡σ′]))))
    , (λ ⊢Δ [σ] →
         let [h]   = (proj₁ (fundamentalVar h [Γ])) ⊢Δ (proj₁ [σ])
             [σA]  = proj₁ [h]
             [σA′] = irrelevance′ (PE.sym (subst-wk A)) [σA]
             [h′] = (proj₂ (fundamentalVar h [Γ])) ⊢Δ (proj₁ [σ])
         in  irrelevanceTerm′ (PE.sym (subst-wk A)) PE.refl PE.refl [σA] [σA′] (proj₁ [h′])
         ,   (λ [σ′] [σ≡σ′] →
                irrelevanceEqTerm′ (PE.sym (subst-wk A)) PE.refl PE.refl [σA] [σA′]
                                   (proj₂ [h′] (proj₁ [σ′]) (proj₁ [σ≡σ′]))))

  -- Fundamental theorem for terms.
  fundamentalTerm : ∀{Γ A rA t} → Γ ⊢ t ∷ A ^ rA
    → ∃ λ ([Γ] : ⊩ᵛ Γ)
    → ∃ λ ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ rA / [Γ])
    → Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ rA / [Γ] / [A]
  fundamentalTerm  = {!!}
{- 
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
  fundamentalTerm (∃ⱼ_▹_ {F} {G} ⊢F ⊢G)
    with fundamentalTerm ⊢F | fundamentalTerm ⊢G
  ... | [Γ] , [U] , [F]ₜ | [Γ]₁ , [U]₁ , [G]ₜ = {!!}
  fundamentalTerm (Idⱼ x x₁ x₂) = {!!}
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
  fundamentalTerm ⦅ x , x₁ ⦆ⱼ = {!!}
  fundamentalTerm (fstⱼ x x₁ x₂) = {!!}
  fundamentalTerm (sndⱼ x x₁ x₂) = {!!}
  fundamentalTerm (Idreflⱼ x) = {!!}
  fundamentalTerm (transpⱼ x x₁ x₂ x₃ x₄ x₅) = {!!}
  fundamentalTerm (castⱼ x x₁ x₂ x₃) = {!!}
  fundamentalTerm (castreflⱼ x x₁) = {!!}
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
-}

  -- Fundamental theorem for term equality.
  fundamentalTermEq : ∀{Γ A t t′ rA} → Γ ⊢ t ≡ t′ ∷ A ^ rA
                    → ∃ λ ([Γ] : ⊩ᵛ Γ)
                    → [ Γ ⊩ᵛ⟨ ∞ ⟩ t ≡ t′ ∷ A ^ rA / [Γ] ]
{-
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
  fundamentalTermEq (∃-cong x x₁ x₂) = {!!}
  fundamentalTermEq (Id-cong x x₁ x₂) = {!!}
  fundamentalTermEq (Id-Π lF< lG< x x₁ x₂ x₃) = {!!}
  fundamentalTermEq {Γ} (Id-ℕ-00 ⊢Γ) =
    let [Γ] = valid ⊢Γ
        [SProp] = Uᵛ emb< [Γ]
        [Unit] = Unitᵗᵛ [Γ]
        [id] , [eq] = redSubstTermᵛ {SProp ⁰} {Id ℕ zero zero} {Unit} [Γ] (λ ⊢Δ [σ] → Id-ℕ-00 ⊢Δ) [SProp] [Unit]
    in [Γ] , modelsTermEq (maybeEmbᵛ {A = SProp _} [Γ] [SProp]) [id] [Unit] [eq]
  fundamentalTermEq (Id-ℕ-SS ⊢n ⊢m) with fundamentalTerm ⊢n | fundamentalTerm ⊢m
  fundamentalTermEq (Id-ℕ-SS {n} {m} ⊢n ⊢m) | [Γ] , [ℕ] , [n] | [Γ]′ , [ℕ]′ , [m]  =
    let [SProp] = maybeEmbᵛ {A = SProp ⁰} [Γ]′ (Uᵛ emb< [Γ]′)
        [Unit] = Unitᵗᵛ [Γ]′
        ⊢Γ = soundContext [Γ]′
        [n]′ = S.irrelevanceTerm {A = ℕ} {t = n} [Γ] [Γ]′ [ℕ] [ℕ]′ [n]
        Idnm = Idᵗᵛ {A = ℕ} {t = n} {u = m} [Γ]′ [ℕ]′ [n]′ [m]
        ⊢n′ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([ℕ]′ ⊢Δ [σ])) (proj₁ ([n]′ ⊢Δ [σ]))
        ⊢m′ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([ℕ]′ ⊢Δ [σ])) (proj₁ ([m] ⊢Δ [σ]))
        [id] , [eq] = redSubstTermᵛ {SProp ⁰} {t = Id ℕ (suc n) (suc m)} {u = Id ℕ n m} [Γ]′ (λ {Δ} {σ} ⊢Δ [σ] → Id-ℕ-SS (⊢n′ {Δ} {σ} ⊢Δ [σ]) (⊢m′ {Δ} {σ} ⊢Δ [σ])) [SProp] Idnm
    in [Γ]′ , modelsTermEq [SProp] [id] Idnm [eq] 
-}
  fundamentalTermEq (Id-U-ΠΠ ⊢A ⊢B ⊢A' ⊢B') with fundamentalTerm ⊢A | fundamentalTerm ⊢B | fundamentalTerm ⊢A' | fundamentalTerm ⊢B'
  fundamentalTermEq (Id-U-ΠΠ {A} {B} {rA} {A'} {B'} ⊢A ⊢B ⊢A' ⊢B') | [Γ] , [UA] , [A] | [Γ]₁ ∙ [A]₁ , [UB] , [B] | [Γ]' , [UA'] , [A'] | [Γ]₁' ∙ [A']₁ , [UB'] , [B'] =
    {!!}
{-    let [U] = Uᵛ ∞< [Γ]'
        [UA]′ = S.irrelevance {A = Univ _ _} [Γ] [Γ]' [UA] 
        [A]′  = S.irrelevanceTerm {A = Univ _ _} {t = A} [Γ] [Γ]' [UA] [UA]′ [A]
        ⊢AΔ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([UA]′ ⊢Δ [σ])) (proj₁ ([A]′ ⊢Δ [σ]))
        -- [UB]′ = S.irrelevance {A = Univ _ _} ([Γ]₁ ∙ [A]₁) ([Γ]' ∙ (maybeEmbᵛ {A = A} [Γ]' (univᵛ {A = A} [Γ]' (≡is≤ PE.refl) [A]′))) [UB] 
        -- [B]′  = S.irrelevanceTerm {A = Univ _ _} {t = B} [Γ] [Γ]' [UB] [UB]′ [B]
        -- ⊢BΔ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([UB]′ ⊢Δ [σ])) (proj₁ ([B]′ ⊢Δ [σ]))
        ⊢A'Δ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([UA'] ⊢Δ [σ])) (proj₁ ([A'] ⊢Δ [σ]))
        [id] , [eq] = redSubstTermᵛ [Γ]' (λ {Δ} {σ} ⊢Δ [σ] → Id-U-ΠΠ (⊢AΔ {Δ} {σ} ⊢Δ [σ]) {!!} (⊢A'Δ {Δ} {σ} ⊢Δ [σ]) {!!}) [U] {!!}
    in [Γ]' , modelsTermEq [U] [id] {!!} [eq]
-}
{-
  fundamentalTermEq (Id-U-ℕℕ ⊢Γ) =
    let [Γ] = valid ⊢Γ
        [SProp] = Uᵛ ∞< [Γ]
        [Unit] = Unitᵗᵛ {l = ¹} [Γ] 
        [id] , [eq] = redSubstTermᵛ {SProp ¹} {Id (U ⁰) ℕ ℕ} {Unit} [Γ] (λ ⊢Δ [σ] → Id-U-ℕℕ ⊢Δ) [SProp] [Unit]
    in [Γ] , modelsTermEq (maybeEmbᵛ {A = SProp ¹} [Γ] [SProp]) [id] [Unit] [eq] 
-}
        
  fundamentalTermEq (Id-SProp x x₁) = {!!}
{- 
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
  fundamentalTermEq (cast-cong {A} {A'} {B} {B'} {e} {e'} {t} {t'} A≡A' B≡B' t≡t' ⊢e ⊢e')
    with fundamentalTermEq A≡A' | fundamentalTermEq B≡B' | fundamentalTermEq t≡t' | fundamentalTerm ⊢e | fundamentalTerm ⊢e'
  ... | [Γ] , modelsTermEq [UA] [A]ₜ [A']ₜ [A≡A']ₜ | [Γ]₁ , modelsTermEq [UB] [B]ₜ [B']ₜ [B≡B']ₜ
      | [Γ]₂ , modelsTermEq [A]₁ [t]ₜ [t']ₜ [t≡t']ₜ | [Γe] , [IdAB] , [e]ₜ
      | [Γe'] , [IdAB'] , [e']ₜ = 
        [A] = maybeEmbᵛ {A = A} [Γ] (univᵛ {A = A} [Γ] (≡is≤ PE.refl) [UA] [A]ₜ)
        [B] = maybeEmbᵛ {A = B} [Γ]₁ (univᵛ {A = B} [Γ]₁ (≡is≤ PE.refl) [UB] [B]ₜ)
        [UA]′  = S.irrelevance {A = Univ _ _} [Γ] [Γ]₂ [UA]
        [A]ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = A} [Γ] [Γ]₂ [UA] [UA]′ [A]ₜ
        [A']ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = A'} [Γ] [Γ]₂ [UA] [UA]′ [A']ₜ
        [UB]′  = S.irrelevance {A = Univ _ _} [Γ]₁ [Γ]₂ [UB]
        [B]ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = B} [Γ]₁ [Γ]₂ [UB] [UB]′ [B]ₜ
        [B']ₜ′ = S.irrelevanceTerm {A = Univ _ _} {t = B'} [Γ]₁ [Γ]₂ [UB] [UB]′ [B']ₜ
        [A]′ = maybeEmbᵛ {A = A} [Γ]₂ (univᵛ {A = A} [Γ]₂ (≡is≤ PE.refl) [UA]′ [A]ₜ′)
        [t]ₜ′ = S.irrelevanceTerm {A = A} {t = t} [Γ]₂ [Γ]₂ [A]₁ [A]′ [t]ₜ
        [A']′ = maybeEmbᵛ {A = A'} [Γ]₂ (univᵛ {A = A'} [Γ]₂ (≡is≤ PE.refl) [UA]′ [A']ₜ′)
        [t']ₜ′ = S.irrelevanceTerm {A = A} {t = t'} [Γ]₂ [Γ]₂ [A]₁ [A]′ [t']ₜ
        [A≡A']′ = S.irrelevanceEq {A = A} {B = A'} [Γ] [Γ]₂ [A] [A]′ (univEqᵛ {A = A} {B = A'} [Γ] [UA] [A] [A≡A']ₜ)
        [t'A]ₜ = convᵛ {t'} {A} {A'} [Γ]₂ [A]′ [A']′ [A≡A']′ [t']ₜ′
        [t≡t']ₜ′ = S.irrelevanceEqTerm {A = A} {t = t} {u = t'} [Γ]₂ [Γ]₂ [A]₁ [A]′ [t≡t']ₜ
        [B]′ = maybeEmbᵛ {A = B} [Γ]₂ (univᵛ {A = B} [Γ]₂ (≡is≤ PE.refl) [UB]′ [B]ₜ′)
        [B']′ = maybeEmbᵛ {A = B'} [Γ]₂ (univᵛ {A = B'} [Γ]₂ (≡is≤ PE.refl) [UB]′ [B']ₜ′)
        [B≡B']′ = S.irrelevanceEq {A = B} {B = B'} [Γ]₁ [Γ]₂ [B] [B]′ (univEqᵛ {A = B} {B = B'} [Γ]₁ [UB] [B] [B≡B']ₜ)
        [IdAB]′  = S.irrelevance {A = Id (Univ _ _) A B} [Γe] [Γ]₂ [IdAB]
        [e]ₜ′ = S.irrelevanceTerm {A = Id (Univ _ _) A B} {t = e} [Γe] [Γ]₂ [IdAB] [IdAB]′ [e]ₜ
        [IdAB']′  = S.irrelevance {A = Id (Univ _ _) A' B'} [Γe'] [Γ]₂ [IdAB']
        [e']ₜ′ = S.irrelevanceTerm {A = Id (Univ _ _) A' B'} {t = e'} [Γe'] [Γ]₂ [IdAB'] [IdAB']′ [e']ₜ
    in  [Γ]₂
    ,   modelsTermEq [B]′ (castᵗᵛ {A} {B} {t} {e} [Γ]₂ [A]′ [B]′ [t]ₜ′ [IdAB]′ [e]ₜ′)
                          (conv₂ᵛ {cast _ A' B' e' t'} {B} {B'} [Γ]₂ [B]′ [B']′ [B≡B']′
                            (castᵗᵛ {A'} {B'} {t'} {e'} [Γ]₂ [A']′ [B']′ [t'A]ₜ [IdAB']′ [e']ₜ′))
                          (cast-congᵗᵛ {A} {A'} {B} {B'} {t} {t'} {e} {e'} [Γ]₂ [A]′ [A']′ [A≡A']′ [B]′ [B']′ [B≡B']′ [t]ₜ′ [t≡t']ₜ′
                                       [IdAB]′ [e]ₜ′ [IdAB']′ [e']ₜ′)
  fundamentalTermEq (cast-ℕ-0 {e} ⊢e) with fundamentalTerm ⊢e
  ... | [Γ] , [Id] , [e]ₜ =
    let ⊢eΔ = λ {Δ} {σ} ⊢Δ [σ] → escapeTerm (proj₁ ([Id] {Δ} {σ} ⊢Δ [σ])) (proj₁ ([e]ₜ {Δ} {σ} ⊢Δ [σ]))
        [id] , [eq] = redSubstTermᵛ {ℕ} {cast ⁰ ℕ ℕ e zero} {zero} {∞} [Γ]
                                    (λ {Δ} {σ} ⊢Δ [σ] → cast-ℕ-0 (⊢eΔ {Δ} {σ} ⊢Δ [σ]))
                                    (ℕᵛ [Γ]) (zeroᵛ {l = ∞} [Γ])
    in [Γ] , modelsTermEq (ℕᵛ [Γ]) [id] (zeroᵛ {l = ∞} [Γ]) [eq] 
-}

  fundamentalTermEq (cast-Π x x₁ x₂ x₃ x₄ x₅) = {!!}
  fundamentalTermEq (cast-ℕ-S x x₁) = {!!}

  fundamentalTermEq = {!!}

{-
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
-}
