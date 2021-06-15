{-# OPTIONS --without-K  #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.cstr {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Introductions.Universe
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst

open import Tools.Product
open import Tools.Empty
import Tools.PropositionalEquality as PE

-- looks like agda is not happy with the weakening stuff wrt inference
-- Πcstr : ∀ {Γ k l}
--         ([Γ] : ⊩ᵛ Γ)
--         ([dom] : Γ ⊩ᵛ⟨ l ⟩ wkAll Γ (cstr-dom k) ⦂ cstr-dom-sort k / [Γ])
--         ([cod] : Γ ∙ wkAll Γ (cstr-dom k) ⦂ cstr-dom-sort k ⊩ᵛ⟨ l ⟩ wk (lift (empty-wk Γ)) (cstr-cod k) ⦂ cstr-cod-sort k / [Γ] ∙ [dom])
--         → Γ ⊩ᵛ⟨ l ⟩ cstr-type Γ k ⦂ cstr-cod-sort k / [Γ]
-- Πcstr {Γ} {k} {l} [Γ] [dom] [cod] =
--   Πᵛ {F = wkAll Γ (cstr-dom k)}
--      {G = wk (lift (empty-wk Γ)) (cstr-cod k)}
--      {sF = cstr-dom-sort k}
--      {sG = cstr-cod-sort k}
--      {l = l}
--      [Γ] [dom] [cod]

-- cstrᵛ : ∀ {Γ k l}
--         ([Γ] : ⊩ᵛ Γ)
--         ([dom] : Γ ⊩ᵛ⟨ l ⟩ wkAll Γ (cstr-dom k) ⦂ cstr-dom-sort k / [Γ])
--         ([cod] : Γ ∙ wkAll Γ (cstr-dom k) ⦂ cstr-dom-sort k ⊩ᵛ⟨ l ⟩ wk (lift (empty-wk Γ)) (cstr-cod k) ⦂ cstr-cod-sort k / [Γ] ∙ [dom])
--         ([domi] : ∀ ki → [ k ]-cstr (cstr-cod ki)
--                        → Γ ⊩ᵛ⟨ l ⟩ wkAll Γ (cstr-dom ki) ⦂ cstr-dom-sort ki / [Γ])
--       → Γ ⊩ᵛ⟨ l ⟩ cstr k ∷ cstr-type Γ k ⦂ cstr-𝕊 k / [Γ] / Πcstr [Γ] [dom] [cod]
-- cstrᵛ [Γ] [dom] [cod] [domi] ⊢Δ [σ] =
--   Πₜ {!!} {!!} {!!} {!!} {!!} {!!} ,
--   {!!}




-- 1) reduce the problem to the fully applied case cstr k ∘ a
-- 2) do a case analysis on cod k:
-- if it is:
--   - Univ s : use the corresponding constructor in the universe
--   - cstr K ∘ ... : provide an instance of ⊩cstr k ∘ a ∷ cstr K ∘ .. ⦂ ..
--   - Otherwise ?? do we need to assume that we are given a proof ?

cstr-cod-subst :  ∀ {Γ k a l}
                    ([Γ] : ⊩ᵛ Γ)
                    ([dom] : Γ ⊩ᵛ⟨ l ⟩ cstr-dom-ctx Γ k ⦂ cstr-dom-sort k / [Γ])
                    ([cod] : Γ ∙ cstr-dom-ctx Γ k ⦂ cstr-dom-sort k
                            ⊩ᵛ⟨ l ⟩ cstr-cod-ctx Γ k ⦂ cstr-cod-sort k / [Γ] ∙ [dom])

                    ([a] : Γ ⊩ᵛ⟨ l ⟩ a ∷ cstr-dom-ctx Γ k ⦂ cstr-dom-sort k / [Γ] / [dom])
               → Γ ⊩ᵛ⟨ l ⟩ (cstr-cod-ctx Γ k) [ a ] ⦂ cstr-cod-sort k / [Γ]
cstr-cod-subst {Γ} {k} {a} {l} [Γ] [dom] [cod] [a] =
  substS {F = cstr-dom-ctx Γ k} {G = cstr-cod-ctx Γ k} {t = a} [Γ] [dom] [cod] [a]


-- cstrᵛ-aux : ∀ {Γ k a l dom cod coda}
--         ([Γ] : ⊩ᵛ Γ)
--         ([dom] : Γ ⊩ᵛ⟨ l ⟩ cstr-dom-ctx Γ k ⦂ cstr-dom-sort k / [Γ])
--         ([cod] : Γ ∙ cstr-dom-ctx Γ k ⦂ cstr-dom-sort k
--                  ⊩ᵛ⟨ l ⟩ cstr-cod-ctx Γ k ⦂ cstr-cod-sort k / [Γ] ∙ [dom])
--         ([domi] : ∀ ki → [ k ]-cstr (cstr-cod ki)
--                        → Γ ⊩ᵛ⟨ l ⟩ cstr-dom-ctx Γ ki ⦂ cstr-dom-sort ki / [Γ])
--         ([a] : Γ ⊩ᵛ⟨ l ⟩ a ∷ cstr-dom-ctx Γ k ⦂ cstr-dom-sort k / [Γ] / [dom])
--         ([coda] : Γ ⊩ )
--       → Γ ⊩ᵛ⟨ l ⟩ cstr k ∘ a ∷ (cstr-cod-ctx Γ k) [ a ] ⦂ cstr-𝕊 k / [Γ] / cstr-cod-subst [Γ] [dom] [cod] [a]
-- cstrᵛ-aux [Γ] [dom] [cod] [domi] [a] ⊢Δ [σ] = {!!}


cstrᵛ-univ : ∀ {Γ k a s}
             ([dom] : Γ ⊩⟨ ¹ ⟩ cstr-dom-ctx Γ k ⦂ cstr-dom-sort k)
             ([a] : Γ ⊩⟨ ¹ ⟩ a ∷ cstr-dom-ctx Γ k ⦂ cstr-dom-sort k / [dom])
             ([domi] : ∀ ki → [ k ]-cstr (cstr-cod ki)
                       → Γ ⊩⟨ ¹ ⟩ cstr-dom-ctx Γ ki ⦂ cstr-dom-sort ki)
             (D : Γ ⊩′⟨ ¹ ⟩U s)
             (kdomU : cstr-cod k PE.≡ Univ s)
             (ksort𝕥y : cstr-cod-sort k PE.≡ 𝕥y)
           → Γ ⊩⟨ ¹ ⟩ cstr k ∘ a ∷ Univ s ⦂ 𝕥y / Uᵣ D
           -- → Γ ⊩⟨ ¹ ⟩ cstr k ∘ a ∷ (cstr-cod-ctx Γ k) [ a ] ⦂ cstr-𝕊 k / Uᵣ D
cstrᵛ-univ {Γ} {k} {a} {s} [dom] [a] [domi] D kdomU ksort𝕥y =
  let ⊢Γ = wf (escape [dom])
      ⊢ka : Γ ⊢ cstr k ∘ a ∷ Univ s ⦂ 𝕥y
      ⊢ka = PE.subst₂ (λ x y → Γ ⊢ cstr k ∘ a ∷ x ⦂ y)
                      (cstr-codU-substS kdomU)
                      ksort𝕥y
                      (cstrⱼ (cstr-dom-ctx-wty ⊢Γ)
                             (cstr-cod-ctx-wty ⊢Γ)
                             (λ ki kiK → escape ([domi] ki kiK))
                             (escapeTerm [dom] [a]))
  in Uₜ (cstr k ∘ a)
        (idRedTerm:*: ⊢ka)
        cstrₙ
        (PE.subst₂ (λ x y → Γ ⊢ cstr k ∘ a ≅ cstr k ∘ a ∷ x ⦂ y)
                   (cstr-codU-substS kdomU) ksort𝕥y
                   (≅ₜ-cstr-cong ⊢Γ (escapeTermEq [dom] (reflEqTerm  [dom] [a]))))
        {! (cstrᵣ ?) !}


cstrᵛ-cstr : ∀ {Γ k x} →
             let l = ¹ in
             ([dom] : Γ ⊩⟨ l ⟩ cstr-dom-ctx Γ k ⦂ cstr-dom-sort k)
             ([x] : Γ ⊩⟨ l ⟩ x ∷ cstr-dom-ctx Γ k ⦂ cstr-dom-sort k / [dom])
             (D : Γ ⊩′⟨ l ⟩cstr (cstr-cod-ctx Γ k) [ x ] ⦂ cstr-cod-sort k)
           → Γ ⊩⟨ l ⟩ cstr k ∘ x ∷ (cstr-cod-ctx Γ k) [ x ] ⦂ cstr-cod-sort k / cstrᵣ D
cstrᵛ-cstr {Γ} {k = k} {x = x} [dom] [x] (cstrᵣ K KcodU a D ⊢a A≡A [domK] [a] [Yi]) =
  let codk≡Ka = whnfRed* (red D) {!!}
      ⊢Γ     = wf (escape [dom])
      ⊢kx    = cstrⱼ (cstr-dom-ctx-wty ⊢Γ)
                     (cstr-cod-ctx-wty ⊢Γ)
                     (λ ki x₁ → ⊥-elim {!!})
                     (escapeTerm [dom] [x])
      kK : [ K ]-cstr (cstr-cod k)
      kK = {!!}
  in cstrₜ (cstr k ∘ x)
           (idRedTerm:*: (PE.subst (λ A → Γ ⊢ cstr k ∘ x ∷ A ⦂ cstr-cod-sort k) codk≡Ka ⊢kx))
           (PE.subst (λ A → Γ ⊢ cstr k ∘ x ≅ cstr k ∘ x ∷ A ⦂ cstr-cod-sort k)
                     codk≡Ka
                     (≅ₜ-cstr-cong ⊢Γ (escapeTermEq [dom] (reflEqTerm  [dom] [x]))))
           (cstrᵣ kK (irrelevanceTerm [dom] ([Yi] k kK) [x]))

data CstrCod : Term → Set where
  univₖ : (s : 𝕊) → CstrCod (Univ s)
  cstrₖ : (K : constructors) (a : Term) → CstrCod (cstr K ∘ a)

postulate cstr-cod-classify : (k : constructors) → CstrCod (cstr-cod k)

CstrCod-wk : ∀ {ρ t} → CstrCod t → CstrCod (U.wk ρ t)
CstrCod-wk d = ?

CstrCod-wk-subst : ∀ {ρ t} → CstrCod t → CstrCod (U.subst ρ t)
CstrCod-wk-subst d = ?

cstr-cod-ctx-subst-classify : ∀ Γ k a → CstrCod ((cstr-cod-ctx Γ k) [ a ])
cstr-cod-ctx-subst-classify Γ k a = {!!}

cstrᵛ-aux : ∀ {Γ l k a A sA} → ([A] : Γ ⊩⟨ l ⟩ A ⦂ sA) → (d : CstrCod A) → Γ ⊩⟨ l ⟩ cstr k ∘ a ∷ A ⦂ sA / [A]
cstrᵛ-aux (Uᵣ x) (univₖ _) = {!!}
cstrᵛ-aux (ℕᵣ D) (univₖ s) = ⊥-elim (U≢ℕ (whrDet* ((id (Uⱼ {! !})) , Uₙ) (red D , ℕₙ)))
cstrᵛ-aux (ℕᵣ D) (cstrₖ K a) = ⊥-elim (ℕ≢cstr (whrDet* (red D , ℕₙ) (id {!!} , cstrₙ) ))
cstrᵛ-aux (Emptyᵣ D) (univₖ s) = ⊥-elim (U≢Empty (whrDet* ((id (Uⱼ {! !})) , Uₙ) (red D , Emptyₙ)))
cstrᵛ-aux (Emptyᵣ x) (cstrₖ K a) = {!!}
cstrᵛ-aux (ne′ K D neK K≡K) (univₖ s) = {!!}
cstrᵛ-aux (ne x) (cstrₖ K a) = {!!}
cstrᵛ-aux (Πᵣ x) d = {!!}
cstrᵛ-aux (cstrᵣ x) d = {!!}
cstrᵛ-aux (emb l< [A]) d = {!!} -- {!cstrᵛ-aux [A] ?!}

cstrᵛ : ∀ {Γ k a l}
        ([Γ] : ⊩ᵛ Γ)
        ([dom] : Γ ⊩ᵛ⟨ l ⟩ cstr-dom-ctx Γ k ⦂ cstr-dom-sort k / [Γ])
        ([cod] : Γ ∙ cstr-dom-ctx Γ k ⦂ cstr-dom-sort k
                 ⊩ᵛ⟨ l ⟩ cstr-cod-ctx Γ k ⦂ cstr-cod-sort k / [Γ] ∙ [dom])
        ([domi] : ∀ ki → [ k ]-cstr (cstr-cod ki)
                       → Γ ⊩ᵛ⟨ l ⟩ cstr-dom-ctx Γ ki ⦂ cstr-dom-sort ki / [Γ])
        ([a] : Γ ⊩ᵛ⟨ l ⟩ a ∷ cstr-dom-ctx Γ k ⦂ cstr-dom-sort k / [Γ] / [dom])
      → Γ ⊩ᵛ⟨ l ⟩ cstr k ∘ a ∷ (cstr-cod-ctx Γ k) [ a ] ⦂ cstr-𝕊 k / [Γ] / cstr-cod-subst [Γ] [dom] [cod] [a]
cstrᵛ [Γ] [dom] [cod] [domi] [a] ⊢Δ [σ] =
  {!!} ,
  (λ [σ'] [σ≡σ'] → {!!})
