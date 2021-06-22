{-# OPTIONS --without-K  #-}

module Definition.Typed.Weakening where

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties
open import Definition.Typed

import Tools.PropositionalEquality as PE
open import Tools.Bool


-- Weakening type

data _∷_⊆_ : Wk → Con Term → Con Term → Set where
  id   : ∀ {Γ}       → id ∷ Γ ⊆ Γ
  step : ∀ {Γ Δ A s ρ} → ρ  ∷ Δ ⊆ Γ → step ρ ∷ Δ ∙ A ⦂ s ⊆ Γ
  lift : ∀ {Γ Δ A s ρ} → ρ  ∷ Δ ⊆ Γ → lift ρ ∷ Δ ∙ U.wk ρ A ⦂ s ⊆ Γ ∙ A ⦂ s


-- -- Weakening composition

_•ₜ_ : ∀ {ρ ρ′ Γ Δ Δ′} → ρ ∷ Γ ⊆ Δ → ρ′ ∷ Δ ⊆ Δ′ → ρ • ρ′ ∷ Γ ⊆ Δ′
id     •ₜ η′ = η′
step η •ₜ η′ = step (η •ₜ η′)
lift η •ₜ id = lift η
lift η •ₜ step η′ = step (η •ₜ η′)
_•ₜ_ {lift ρ} {lift ρ′} {Δ′ = Δ′ ∙ A ⦂ sA} (lift η) (lift η′) =
  PE.subst (λ x → lift (ρ • ρ′) ∷ x ⊆ Δ′ ∙ A ⦂ sA)
           (PE.cong₂ (λ x y → x ∙ y ⦂ sA) PE.refl (PE.sym (wk-comp ρ ρ′ A)))
           (lift (η •ₜ η′))


-- Weakening of judgements

wkIndex : ∀ {Γ Δ n A s ρ} → ρ ∷ Δ ⊆ Γ →
        let ρA = U.wk ρ A
            ρn = wkVar ρ n
        in  ⊢ Δ → n ∷ A ⦂ s ∈ Γ → ρn ∷ ρA ⦂ s ∈ Δ
wkIndex id ⊢Δ i = PE.subst (λ x → _ ∷ x ⦂ _ ∈ _) (PE.sym (wk-id _)) i
wkIndex (step ρ) (⊢Δ ∙ A) i = PE.subst (λ x → _ ∷ x ⦂ _ ∈ _)
                                       (wk1-wk _ _)
                                       (there (wkIndex ρ ⊢Δ i))
wkIndex (lift ρ) (⊢Δ ∙ A) (there i) = PE.subst (λ x → _ ∷ x ⦂ _ ∈ _)
                                               (wk1-wk≡lift-wk1 _ _)
                                               (there (wkIndex ρ ⊢Δ i))
wkIndex (lift ρ) ⊢Δ here =
  let G = _
      n = _
  in  PE.subst (λ x → n ∷ x ⦂ _ ∈ G)
               (wk1-wk≡lift-wk1 _ _)
               here

wk-comp-empty : ∀ {ρ} {Δ Γ : Con Term} (d : ρ ∷ Δ ⊆ Γ) → ρ U.• empty-wk Γ PE.≡ empty-wk Δ
wk-comp-empty id = PE.refl
wk-comp-empty (step d) = PE.cong step (wk-comp-empty d)
wk-comp-empty (lift d) = PE.cong step (wk-comp-empty d)

wk-wkAll : ∀ {ρ Δ Γ t} (d : ρ ∷ Δ ⊆ Γ) → U.wk ρ (wkAll Γ t) PE.≡ wkAll Δ t
wk-wkAll {ρ} {Δ} {Γ} {t} d rewrite wk-comp ρ (empty-wk Γ) t rewrite wk-comp-empty d = PE.refl

-- KM: there might be a way to merge with previous lemma
wk-lift-wkAll : ∀ {ρ Δ Γ t} (d : ρ ∷ Δ ⊆ Γ) → U.wk (lift ρ) (U.wk (lift (empty-wk Γ)) t) PE.≡ U.wk (lift (empty-wk Δ)) t
wk-lift-wkAll {ρ} {Δ} {Γ} {t} d rewrite wk-comp (lift ρ) (lift (empty-wk Γ)) t rewrite wk-comp-empty d = PE.refl

wk-lift-lift-wkAll : ∀ {ρ Δ Γ t} (d : ρ ∷ Δ ⊆ Γ) → U.wk (lift (lift ρ)) (U.wk (lift (lift (empty-wk Γ))) t) PE.≡ U.wk (lift (lift (empty-wk Δ))) t
wk-lift-lift-wkAll {ρ} {Δ} {Γ} {t} d rewrite wk-comp (lift (lift ρ)) (lift (lift (empty-wk Γ))) t rewrite wk-comp-empty d = PE.refl

wk-lift3-wkAll : ∀ {ρ Δ Γ t} (d : ρ ∷ Δ ⊆ Γ) → U.wk (lift (lift (lift ρ))) (U.wk (lift (lift (lift (empty-wk Γ)))) t) PE.≡ U.wk (lift (lift (lift (empty-wk Δ)))) t
wk-lift3-wkAll {ρ} {Δ} {Γ} {t} d rewrite wk-comp (lift (lift (lift ρ))) (lift (lift (lift (empty-wk Γ)))) t rewrite wk-comp-empty d = PE.refl

wk-step-wkAll : ∀ {ρ Δ Γ A s t} (d : ρ ∷ Δ ⊆ Γ) → U.wk (step ρ) (U.wk (empty-wk Γ) t) PE.≡ U.wk (empty-wk (Δ ∙ A ⦂ s)) t
wk-step-wkAll {ρ} {Δ} {Γ} {t = t} d = PE.trans (wk-comp (step ρ) (empty-wk Γ) t) (PE.cong (λ s → U.wk (step s) t) (wk-comp-empty d))

lift-wkAll : ∀ {ρ Δ Γ A s} (d : ρ ∷ Δ ⊆ Γ) → lift ρ ∷ Δ ∙ wkAll Δ A ⦂ s ⊆ Γ ∙ wkAll Γ A ⦂ s
lift-wkAll {A = A} d rewrite PE.sym (wk-wkAll {t = A} d) = lift d

wk-cstr-dom : ∀ {ρ Γ Δ t s k} ([ρ] : ρ ∷ Δ ⊆ Γ) (d : Δ ⊢ t ∷ U.wk ρ (cstr-dom-ctx Γ k) ⦂ s) → Δ ⊢ t ∷ cstr-dom-ctx Δ k ⦂ s
wk-cstr-dom {ρ} {Γ} {Δ} {t} {s} [ρ] d = PE.subst (λ x → Δ ⊢ t ∷ x ⦂ s) (wk-wkAll [ρ]) d

wk-cstr-cod : ∀ {ρ a k Δ Γ} ([ρ] : ρ ∷ Δ ⊆ Γ)  → subst (sgSubst (U.wk ρ a)) (U.wk (lift (empty-wk Δ)) (cstr-cod k)) PE.≡ U.wk ρ (cstr-cod-ctx Γ k [ a ])
wk-cstr-cod {k = k} [ρ] rewrite (PE.sym  (wk-lift-wkAll {t = cstr-cod k} [ρ])) = wk-sgSubst (U.wk (lift (empty-wk _)) (cstr-cod k))

wk-cstr-type : ∀ {ρ Γ Δ k a} ([ρ] : ρ ∷ Δ ⊆ Γ) → cstr-type Δ k (U.wk ρ a) PE.≡ U.wk ρ (cstr-type Γ k a)
wk-cstr-type {ρ} {Γ} {Δ} {k} {a} [ρ] =
  PE.sym (PE.trans
    (wk-β (cstr-cod-ctx Γ k))
    (PE.cong (λ t → t [ U.wk ρ a ]) (wk-lift-wkAll {t = cstr-cod k} [ρ])))

module WkDstr {ρ : Wk} {Γ Δ : Con Term} (d : destructors) ([ρ] : ρ ∷ Δ ⊆ Γ) where

  module D = Dstr Γ d
  module D' = Dstr Δ d

  param-ctx : D'.param-ctx PE.≡ U.wk ρ D.param-ctx
  param-ctx = PE.sym (wk-wkAll [ρ])

  ctx-dom : lift ρ ∷ D'.ctx-dom ⊆ D.ctx-dom
  ctx-dom = lift-wkAll [ρ]

  dom-ctx : D'.dom-ctx PE.≡ U.wk (lift ρ) D.dom-ctx
  dom-ctx = PE.sym (wk-lift-wkAll [ρ])

  ctx-cod : lift (lift ρ) ∷ D'.ctx-cod ⊆ D.ctx-cod
  ctx-cod rewrite dom-ctx = lift ctx-dom

  cod-ctx : D'.cod-ctx PE.≡ U.wk (lift (lift ρ)) D.cod-ctx
  cod-ctx = PE.sym (wk-lift-lift-wkAll [ρ])

  param-type : D'.param-type PE.≡ U.wk ρ D.param-type
  param-type = param-ctx

  dom-type : {p : Term} → D'.dom-type (U.wk ρ p) PE.≡ U.wk ρ (D.dom-type p)
  dom-type rewrite dom-ctx = PE.sym (wk-β D.dom-ctx)

  cod-type : {p a : Term} → U.wk ρ (D.cod-type p a) PE.≡ D'.cod-type (U.wk ρ p) (U.wk ρ a) 
  cod-type {p} {a} rewrite dom-ctx rewrite cod-ctx =
    PE.trans (wk-β (D.cod-ctx [ wk1 a ]))
      (PE.cong (λ t → t [ U.wk ρ p ])
        (PE.trans (wk-β D.cod-ctx) (PE.cong (λ a → U.wk (lift (lift ρ)) D.cod-ctx [ a ])
          (PE.sym (wk1-wk≡lift-wk1 ρ a)))))

wk-rew-lhs-helper : ∀ {ρ Γ Δ l u} ([ρ] : ρ ∷ Δ ⊆ Γ) → (U.wk (lift (empty-wk Δ)) l) [ U.wk ρ u ] PE.≡ U.wk ρ ((U.wk (lift (empty-wk Γ)) l) [ u ])
wk-rew-lhs-helper {ρ} {Γ} {Δ} {l} {u} [ρ] =
  PE.sym (wk-β-eq {a = u} {t = U.wk (lift (empty-wk Γ)) l} (wk-lift-wkAll [ρ]) PE.refl)

wk-rew-lhs : ∀ {ρ Γ Δ d l r p u} (rule : Rew⊢ d ⊚ l ⇒ r) ([ρ] : ρ ∷ Δ ⊆ Γ) → Rew.lhs-ctx rule Δ (U.wk ρ p) (U.wk ρ u) PE.≡ U.wk ρ (Rew.lhs-ctx rule Γ p u) 
wk-rew-lhs {ρ} {Γ} {Δ} {d} {l} {r} {p} {u} rule [ρ] =
  PE.cong (dstr d (U.wk ρ p)) (wk-rew-lhs-helper {l = l} {u = u} [ρ])

wk-rew-rhs : ∀ {ρ Γ Δ d l r p u} (rule : Rew⊢ d ⊚ l ⇒ r) ([ρ] : ρ ∷ Δ ⊆ Γ) → Rew.rhs-ctx rule Δ (U.wk ρ p) (U.wk ρ u) PE.≡ U.wk ρ (Rew.rhs-ctx rule Γ p u)
wk-rew-rhs {ρ} {Γ} {Δ} {d} {l} {r} {p} {u} rule [ρ] with Rew.is-recursive rule
... | true =
  let v = U.wk (lift (lift (lift (empty-wk Γ)))) r in
  PE.sym (wk-β-eq {a = p}
                  {t = v [ wk1 (wk1 (dstr d p u)) ] [ wk1 u ]}
                  (wk-β-eq {t = v [ wk1 (wk1 (dstr d p u)) ] }
                          (wk-β-eq {t = v}
                                    (wk-lift3-wkAll [ρ])
                                    (PE.sym (wk12-wk≡lift2-wk12 ρ (dstr d p u))))
                          (PE.sym (wk1-wk≡lift-wk1 ρ u)))
                  PE.refl)
... | false =
  let v = U.wk (lift (lift (empty-wk Γ))) r in
  PE.sym (wk-β-eq {a = p}
                  {t = v [ wk1 u ]}
                  (wk-β-eq {t = v }
                           (wk-lift-lift-wkAll [ρ])
                           (PE.sym (wk1-wk≡lift-wk1 ρ u)))
                  PE.refl)


mutual
  wk : ∀ {Γ Δ A s ρ} → ρ ∷ Δ ⊆ Γ →
     let ρA = U.wk ρ A
     in  ⊢ Δ → Γ ⊢ A ⦂ s → Δ ⊢ ρA ⦂ s
  wk ρ ⊢Δ (ℕⱼ ⊢Γ) = ℕⱼ ⊢Δ
  wk ρ ⊢Δ (Emptyⱼ ⊢Γ) = Emptyⱼ ⊢Δ
  wk ρ ⊢Δ (Uⱼ ⊢Γ) = Uⱼ ⊢Δ
  wk ρ ⊢Δ (Πⱼ F ▹ G) = let ρF = wk ρ ⊢Δ F
                       in  Πⱼ ρF ▹ (wk (lift ρ) (⊢Δ ∙ ρF) G)
  wk ρ ⊢Δ (univ A) = univ (wkTerm ρ ⊢Δ A)
  wk ρ ⊢Δ (Boxⱼ A) = Boxⱼ (wk ρ ⊢Δ A)

  wkTerm : ∀ {Γ Δ A t s ρ} → ρ ∷ Δ ⊆ Γ →
         let ρA = U.wk ρ A
             ρt = U.wk ρ t
         in ⊢ Δ → Γ ⊢ t ∷ A ⦂ s → Δ ⊢ ρt ∷ ρA ⦂ s
  wkTerm ρ ⊢Δ (ℕⱼ ⊢Γ) = ℕⱼ ⊢Δ
  wkTerm ρ ⊢Δ (Emptyⱼ ⊢Γ) = Emptyⱼ ⊢Δ
  wkTerm ρ ⊢Δ (Πⱼ F ▹ G) = let ρF = wkTerm ρ ⊢Δ F
                          in  Πⱼ ρF ▹ (wkTerm (lift ρ) (⊢Δ ∙ univ ρF) G)
  wkTerm ρ ⊢Δ (var ⊢Γ x) = var ⊢Δ (wkIndex ρ ⊢Δ x)
  wkTerm ρ ⊢Δ (lamⱼ F t) = let ρF = wk ρ ⊢Δ F
                          in lamⱼ ρF (wkTerm (lift ρ) (⊢Δ ∙ ρF) t)
  wkTerm ρ ⊢Δ (_∘ⱼ_ {G = G} g a) = PE.subst (λ x → _ ⊢ _ ∷ x ⦂ _)
                                           (PE.sym (wk-β G))
                                           (wkTerm ρ ⊢Δ g ∘ⱼ wkTerm ρ ⊢Δ a)
  wkTerm ρ ⊢Δ (zeroⱼ ⊢Γ) = zeroⱼ ⊢Δ
  wkTerm ρ ⊢Δ (sucⱼ n) = sucⱼ (wkTerm ρ ⊢Δ n)
  wkTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrecⱼ {G = G} {sG = sG} {s = s} ⊢G ⊢z ⊢s ⊢n) =
    PE.subst (λ x → _ ⊢ natrec _ _ _ _ ∷ x ⦂ _) (PE.sym (wk-β G))
             (natrecⱼ (wk (lift [ρ]) (⊢Δ ∙ ℕⱼ ⊢Δ) ⊢G)
                      (PE.subst (λ x → _ ⊢ _ ∷ x ⦂ _) (wk-β G) (wkTerm [ρ] ⊢Δ ⊢z))
                      (PE.subst (λ x → Δ ⊢ U.wk ρ s ∷ x ⦂ sG)
                                (wk-β-natrec ρ G sG)
                                (wkTerm [ρ] ⊢Δ ⊢s))
                      (wkTerm [ρ] ⊢Δ ⊢n))
  wkTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (Emptyrecⱼ {A = A} {e = e} ⊢A ⊢e) =
    (Emptyrecⱼ (wk [ρ] ⊢Δ ⊢A) (wkTerm [ρ] ⊢Δ ⊢e))
  wkTerm ρ ⊢Δ (conv t A≡B) = conv (wkTerm ρ ⊢Δ t) (wkEq ρ ⊢Δ A≡B)
  wkTerm ρ ⊢Δ (Boxⱼ ⊢A) = Boxⱼ (wkTerm ρ ⊢Δ ⊢A)
  wkTerm ρ ⊢Δ (boxⱼ ⊢t) = boxⱼ (wkTerm ρ ⊢Δ ⊢t)
  wkTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (Boxrecⱼ {sA = sA} {sC = sC} {A = A} {C = C} {u = u} ⊢A ⊢C  ⊢u ⊢t) =
    let [ρA] = wk [ρ] ⊢Δ ⊢A in
    PE.subst (λ x → _ ⊢ Boxrec _ _ _ _ _ ∷ x ⦂ _)
             (PE.sym (wk-β C))
             (Boxrecⱼ [ρA]
                      (wk (lift [ρ]) (⊢Δ ∙ Boxⱼ [ρA]) ⊢C)
                      (PE.subst (λ x → Δ ⊢ U.wk ρ u ∷ x ⦂ sC)
                                (wk-β-Boxrec ρ (U.wk ρ A) sA C)
                                (wkTerm [ρ] ⊢Δ ⊢u))
                      (wkTerm [ρ] ⊢Δ ⊢t))
  wkTerm {Δ = Δ} ρ ⊢Δ (cstrⱼ {k = k} {a = a} ⊢domk ⊢codk ⊢domki ⊢a) =
    let ρdomk      = PE.subst (λ x → Δ ⊢ x ⦂ _) (wk-wkAll ρ) (wk ρ ⊢Δ ⊢domk) in
    PE.subst (λ x → Δ ⊢ cstr k (U.wk _ a) ∷ x ⦂ cstr-𝕊 k) (wk-cstr-cod ρ)
             (cstrⱼ ρdomk
                    (PE.subst (λ x → Δ ∙ wkAll Δ _ ⦂ _ ⊢ x ⦂ _) (wk-lift-wkAll ρ) (wk (lift-wkAll ρ) (⊢Δ ∙ ρdomk) ⊢codk))
                    ⊢domki
                    (wk-cstr-dom ρ (wkTerm ρ ⊢Δ ⊢a)))
  wkTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (dstrⱼ {d = d} {p = p} {a = a} par dom cod ⊢p ⊢a rrules) =
    let module W = WkDstr d [ρ] in
    let ρpar = PE.subst (λ x → Δ ⊢ x ⦂ _) (PE.sym W.param-ctx) (wk [ρ] ⊢Δ par)
        ρdom = PE.subst (λ x → W.D'.ctx-dom ⊢ x ⦂ _) (PE.sym W.dom-ctx) (wk W.ctx-dom (⊢Δ ∙ ρpar) dom)
        ρcod = PE.subst (λ x → W.D'.ctx-cod ⊢ x ⦂ _) (PE.sym W.cod-ctx) (wk W.ctx-cod (⊢Δ ∙ ρpar ∙ ρdom) cod)
    in
    PE.subst (λ x → Δ ⊢ dstr d (U.wk ρ p) (U.wk ρ a) ∷ x ⦂ dstr-𝕊 d)
             (PE.sym W.cod-type)
             (dstrⱼ ρpar ρdom ρcod
               (PE.subst (λ x → Δ ⊢ U.wk ρ p ∷ x ⦂ _) (PE.sym W.param-type) (wkTerm [ρ] ⊢Δ ⊢p))
               (PE.subst (λ x → Δ ⊢ U.wk ρ a ∷ x ⦂ _) (PE.sym W.dom-type) (wkTerm [ρ] ⊢Δ ⊢a))
               rrules)
  wkEq : ∀ {Γ Δ A B s ρ} → ρ ∷ Δ ⊆ Γ →
       let ρA = U.wk ρ A
           ρB = U.wk ρ B
       in ⊢ Δ → Γ ⊢ A ≡ B ⦂ s → Δ ⊢ ρA ≡ ρB ⦂ s
  wkEq ρ ⊢Δ (univ A≡B) = univ (wkEqTerm ρ ⊢Δ A≡B)
  wkEq ρ ⊢Δ (refl A) = refl (wk ρ ⊢Δ A)
  wkEq ρ ⊢Δ (sym A≡B) = sym (wkEq ρ ⊢Δ A≡B)
  wkEq ρ ⊢Δ (trans A≡B B≡C) = trans (wkEq ρ ⊢Δ A≡B) (wkEq ρ ⊢Δ B≡C)
  wkEq ρ ⊢Δ (Π-cong F F≡H G≡E) = let ρF = wk ρ ⊢Δ F
                                 in  Π-cong ρF (wkEq ρ ⊢Δ F≡H)
                                               (wkEq (lift ρ) (⊢Δ ∙ ρF) G≡E)
  wkEq ρ ⊢Δ (Box-cong x d) = Box-cong (wk ρ ⊢Δ x) (wkEq ρ ⊢Δ d)

  wkEqTerm : ∀ {Γ Δ A t u s ρ} → ρ ∷ Δ ⊆ Γ →
           let ρA = U.wk ρ A
               ρt = U.wk ρ t
               ρu = U.wk ρ u
           in ⊢ Δ → Γ ⊢ t ≡ u ∷ A ⦂ s → Δ ⊢ ρt ≡ ρu ∷ ρA ⦂ s
  wkEqTerm ρ ⊢Δ (refl t) = refl (wkTerm ρ ⊢Δ t)
  wkEqTerm ρ ⊢Δ (sym t≡u) = sym (wkEqTerm ρ ⊢Δ t≡u)
  wkEqTerm ρ ⊢Δ (trans t≡u u≡s) = trans (wkEqTerm ρ ⊢Δ t≡u) (wkEqTerm ρ ⊢Δ u≡s)
  wkEqTerm ρ ⊢Δ (conv t≡u A≡B) = conv (wkEqTerm ρ ⊢Δ t≡u) (wkEq ρ ⊢Δ A≡B)
  wkEqTerm ρ ⊢Δ (Π-cong F F≡H G≡E) =
    let ρF = wk ρ ⊢Δ F
    in  Π-cong ρF (wkEqTerm ρ ⊢Δ F≡H)
                  (wkEqTerm (lift ρ) (⊢Δ ∙ ρF) G≡E)
  wkEqTerm ρ ⊢Δ (app-cong {G = G} f≡g a≡b) =
    PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x ⦂ _)
             (PE.sym (wk-β G))
             (app-cong (wkEqTerm ρ ⊢Δ f≡g) (wkEqTerm ρ ⊢Δ a≡b))
  wkEqTerm ρ ⊢Δ (β-red {a = a} {t = t} {G = G} F ⊢t ⊢a) =
    let ρF = wk ρ ⊢Δ F
    in  PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x ⦂ _)
                 (PE.sym (wk-β G))
                 (PE.subst (λ x → _ ⊢ U.wk _ ((lam _ ▹ t) ∘ a) ≡ x ∷ _ ⦂ _)
                           (PE.sym (wk-β t))
                           (β-red ρF (wkTerm (lift ρ) (⊢Δ ∙ ρF) ⊢t)
                                     (wkTerm ρ ⊢Δ ⊢a)))
  wkEqTerm ρ ⊢Δ (η-eq F f g f0≡g0) =
    let ρF = wk ρ ⊢Δ F
    in  η-eq ρF (wkTerm ρ ⊢Δ f)
                (wkTerm ρ ⊢Δ g)
                (PE.subst (λ t → _ ⊢ t ∘ _ ≡ _ ∷ _ ⦂ _)
                          (PE.sym (wk1-wk≡lift-wk1 _ _))
                          (PE.subst (λ t → _ ⊢ _ ≡ t ∘ _ ∷ _ ⦂ _)
                                    (PE.sym (wk1-wk≡lift-wk1 _ _))
                                    (wkEqTerm (lift ρ) (⊢Δ ∙ ρF) f0≡g0)))
  wkEqTerm ρ ⊢Δ (suc-cong m≡n) = suc-cong (wkEqTerm ρ ⊢Δ m≡n)
  wkEqTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-cong {s = s} {s′ = s′} {F = F} {sF = sF}
                                     F≡F′ z≡z′ s≡s′ n≡n′) =
    PE.subst (λ x → Δ ⊢ natrec _ _ _ _ ≡ _ ∷ x ⦂ _) (PE.sym (wk-β F))
             (natrec-cong (wkEq (lift [ρ]) (⊢Δ ∙ ℕⱼ ⊢Δ) F≡F′)
                          (PE.subst (λ x → Δ ⊢ _ ≡ _ ∷ x ⦂ _) (wk-β F)
                                    (wkEqTerm [ρ] ⊢Δ z≡z′))
                          (PE.subst (λ x → Δ ⊢ U.wk ρ s
                                             ≡ U.wk ρ s′ ∷ x ⦂ sF)
                                    (wk-β-natrec _ F sF)
                                    (wkEqTerm [ρ] ⊢Δ s≡s′))
                          (wkEqTerm [ρ] ⊢Δ n≡n′))
  wkEqTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-zero {z} {s} {F} {sF} ⊢F ⊢z ⊢s) =
    PE.subst (λ x → Δ ⊢ natrec (U.wk (lift _) F) _ _ _ ≡ _ ∷ x ⦂ _)
             (PE.sym (wk-β F))
             (natrec-zero (wk (lift [ρ]) (⊢Δ ∙ ℕⱼ ⊢Δ) ⊢F)
                          (PE.subst (λ x → Δ ⊢ U.wk ρ z ∷ x ⦂ _)
                                    (wk-β F)
                                    (wkTerm [ρ] ⊢Δ ⊢z))
                          (PE.subst (λ x → Δ ⊢ U.wk ρ s ∷ x ⦂ sF)
                                    (wk-β-natrec _ F sF)
                                    (wkTerm [ρ] ⊢Δ ⊢s)))
  wkEqTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-suc {n} {z} {s} {F} {sF} ⊢n ⊢F ⊢z ⊢s) =
    PE.subst (λ x → Δ ⊢ natrec (U.wk (lift _) F) _ _ _
                      ≡ _ ∘ (natrec _ _ _ _) ∷ x ⦂ _)
             (PE.sym (wk-β F))
             (natrec-suc (wkTerm [ρ] ⊢Δ ⊢n)
                         (wk (lift [ρ]) (⊢Δ ∙ ℕⱼ ⊢Δ) ⊢F)
                         (PE.subst (λ x → Δ ⊢ U.wk ρ z ∷ x ⦂ _)
                                   (wk-β F)
                                   (wkTerm [ρ] ⊢Δ ⊢z))
                         (PE.subst (λ x → Δ ⊢ U.wk ρ s ∷ x ⦂ sF)
                                   (wk-β-natrec _ F sF)
                                   (wkTerm [ρ] ⊢Δ ⊢s)))
  wkEqTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (Emptyrec-cong {A = A} {A' = A'} {e = e} {e' = e'}
                                  A≡A' e≡e') =
    (Emptyrec-cong (wkEq [ρ] ⊢Δ A≡A')
      (wkEqTerm [ρ] ⊢Δ e≡e'))
  wkEqTerm ρ ⊢Δ (Box-cong x d) = Box-cong (wkTerm ρ ⊢Δ x) (wkEqTerm ρ ⊢Δ d)
  wkEqTerm ρ ⊢Δ (box-cong ⊢F ⊢a ⊢a' d) =
    box-cong (wk ρ ⊢Δ ⊢F)
             (wkTerm ρ ⊢Δ ⊢a)
             (wkTerm ρ ⊢Δ ⊢a')
             (wkEqTerm ρ ⊢Δ d)
  wkEqTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (Boxrec-cong {sF} {sE} {E} {F = F} {u = u} {u'} ⊢F F≡F' E≡E' u≡u' t≡t') =
    let [ρF] = wk [ρ] ⊢Δ ⊢F in
    PE.subst (λ x → _ ⊢ Boxrec _ _ _ _ _ ≡ _ ∷ x ⦂ _)
             (PE.sym (wk-β E))
             (Boxrec-cong [ρF]
                          (wkEq [ρ] ⊢Δ F≡F')
                          (wkEq (lift [ρ]) (⊢Δ ∙ Boxⱼ [ρF]) E≡E')
                          (PE.subst (λ x → Δ ⊢ U.wk ρ u ≡ U.wk ρ u' ∷ x ⦂ sE)
                                    (wk-β-Boxrec ρ (U.wk ρ F) sF E)
                                    (wkEqTerm [ρ] ⊢Δ u≡u'))
                          (wkEqTerm [ρ] ⊢Δ t≡t')
                          )
  wkEqTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (Boxrec-box {sF} {sE} {E} {F} {u = u} ⊢F ⊢E ⊢u ⊢a) =
    let [ρF] = wk [ρ] ⊢Δ ⊢F in
    PE.subst (λ x → _ ⊢ Boxrec _ _ _ _ _ ≡ _ ∷ x ⦂ _)
             (PE.sym (wk-β E))
             (Boxrec-box [ρF]
                         (wk (lift [ρ]) (⊢Δ ∙ Boxⱼ [ρF]) ⊢E)
                         (PE.subst (λ x → Δ ⊢ U.wk ρ u ∷ x ⦂ sE)
                                   (wk-β-Boxrec ρ (U.wk ρ F) sF E)
                                   (wkTerm [ρ] ⊢Δ ⊢u))
                         (wkTerm [ρ] ⊢Δ ⊢a))
  wkEqTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (cstr-cong {a = a} {a' = a'} {k = k} a≡a') =
    PE.subst (λ x → Δ ⊢ cstr k (U.wk ρ a) ≡ cstr k (U.wk ρ a') ∷ x ⦂ cstr-𝕊 k)
             (wk-cstr-type [ρ])
             (cstr-cong (PE.subst (λ x → Δ ⊢ U.wk ρ a ≡ U.wk ρ a' ∷ x ⦂ cstr-dom-sort k)
                                  (wk-wkAll [ρ])
                                  (wkEqTerm [ρ] ⊢Δ a≡a')))
  wkEqTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (dstr-cong {a = a} {a' = a'} {p = p} {p' = p'} {k = k} a≡a' p≡p') =
    let module W = WkDstr k [ρ] in
    PE.subst (λ x → Δ ⊢ dstr k (U.wk ρ p) (U.wk ρ a) ≡ dstr k (U.wk ρ p') (U.wk ρ a') ∷ x ⦂ dstr-𝕊 k)
              (PE.sym W.cod-type)
              (dstr-cong (PE.subst (λ x → Δ ⊢ U.wk ρ p ≡ U.wk ρ p' ∷ x ⦂ dstr-param-sort k)
                                   (PE.sym W.param-type)
                                   (wkEqTerm [ρ] ⊢Δ a≡a'))
                         (PE.subst (λ x → Δ ⊢ U.wk ρ a ≡ U.wk ρ a' ∷ x ⦂ dstr-dom-sort k)
                                   (PE.sym W.dom-type)
                                   (wkEqTerm [ρ] ⊢Δ p≡p')))
  wkEqTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (rew {A} {s} {p = p} {u = u} {l = l} rule ⊢u ⊢ka) =
    PE.subst₂ (λ l r → Δ ⊢ l ≡ r ∷ U.wk ρ A ⦂ s)
              (wk-rew-lhs rule [ρ])
              (wk-rew-rhs rule [ρ])
             (rew rule (PE.subst (λ A → Δ ⊢ U.wk ρ u ∷ A ⦂ _) (wk-wkAll [ρ]) (wkTerm [ρ] ⊢Δ ⊢u))
                       (PE.subst (λ l → Δ ⊢ l ∷ U.wk ρ A ⦂ s) (PE.sym (wk-rew-lhs rule [ρ])) (wkTerm [ρ] ⊢Δ ⊢ka)))
mutual
  wkRed : ∀ {Γ Δ A B s ρ} → ρ ∷ Δ ⊆ Γ →
           let ρA = U.wk ρ A
               ρB = U.wk ρ B
           in ⊢ Δ → Γ ⊢ A ⇒ B ⦂ s → Δ ⊢ ρA ⇒ ρB ⦂ s
  wkRed ρ ⊢Δ (univ A⇒B) = univ (wkRedTerm ρ ⊢Δ A⇒B)

  wkRedTerm : ∀ {Γ Δ A t u s ρ} → ρ ∷ Δ ⊆ Γ →
           let ρA = U.wk ρ A
               ρt = U.wk ρ t
               ρu = U.wk ρ u
           in ⊢ Δ → Γ ⊢ t ⇒ u ∷ A ⦂ s → Δ ⊢ ρt ⇒ ρu ∷ ρA ⦂ s
  wkRedTerm ρ ⊢Δ (conv t⇒u A≡B) = conv (wkRedTerm ρ ⊢Δ t⇒u) (wkEq ρ ⊢Δ A≡B)
  wkRedTerm ρ ⊢Δ (app-subst {B = B} t⇒u a) =
    PE.subst (λ x → _ ⊢ _ ⇒ _ ∷ x ⦂ _) (PE.sym (wk-β B))
             (app-subst (wkRedTerm ρ ⊢Δ t⇒u) (wkTerm ρ ⊢Δ a))
  wkRedTerm ρ ⊢Δ (β-red {A} {B} {a} {t} ⊢A ⊢t ⊢a) =
    let ⊢ρA = wk ρ ⊢Δ ⊢A
    in  PE.subst (λ x → _ ⊢ _ ⇒ _ ∷ x ⦂ _) (PE.sym (wk-β B))
                 (PE.subst (λ x → _ ⊢ U.wk _ ((lam _ ▹ t) ∘ a) ⇒ x ∷ _ ⦂ _)
                           (PE.sym (wk-β t))
                           (β-red ⊢ρA (wkTerm (lift ρ) (⊢Δ ∙ ⊢ρA) ⊢t)
                                      (wkTerm ρ ⊢Δ ⊢a)))
  wkRedTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-subst {s = s} {F = F} {sF} ⊢F ⊢z ⊢s n⇒n′) =
    PE.subst (λ x → _ ⊢ natrec _ _ _ _ ⇒ _ ∷ x ⦂ _) (PE.sym (wk-β F))
             (natrec-subst (wk (lift [ρ]) (⊢Δ ∙ ℕⱼ ⊢Δ) ⊢F)
                           (PE.subst (λ x → _ ⊢ _ ∷ x ⦂ _) (wk-β F)
                                     (wkTerm [ρ] ⊢Δ ⊢z))
                           (PE.subst (λ x → Δ ⊢ U.wk ρ s ∷ x ⦂ sF)
                                     (wk-β-natrec _ F sF)
                                     (wkTerm [ρ] ⊢Δ ⊢s))
                           (wkRedTerm [ρ] ⊢Δ n⇒n′))
  wkRedTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-zero {s = s} {F = F} {sF} ⊢F ⊢z ⊢s) =
    PE.subst (λ x → _ ⊢ natrec (U.wk (lift ρ) F) _ _ _ ⇒ _ ∷ x ⦂ _)
             (PE.sym (wk-β F))
             (natrec-zero (wk (lift [ρ]) (⊢Δ ∙ ℕⱼ ⊢Δ) ⊢F)
                          (PE.subst (λ x → _ ⊢ _ ∷ x ⦂ _)
                                    (wk-β F)
                                    (wkTerm [ρ] ⊢Δ ⊢z))
                          (PE.subst (λ x → Δ ⊢ U.wk ρ s ∷ x ⦂ sF)
                                    (wk-β-natrec ρ F sF)
                                    (wkTerm [ρ] ⊢Δ ⊢s)))
  wkRedTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-suc {s = s} {F = F} {sF} ⊢n ⊢F ⊢z ⊢s) =
    PE.subst (λ x → _ ⊢ natrec _ _ _ _ ⇒ _ ∘ natrec _ _ _ _ ∷ x ⦂ _)
             (PE.sym (wk-β F))
             (natrec-suc (wkTerm [ρ] ⊢Δ ⊢n)
                         (wk (lift [ρ]) (⊢Δ ∙ ℕⱼ ⊢Δ) ⊢F)
                         (PE.subst (λ x → _ ⊢ _ ∷ x ⦂ _)
                                   (wk-β F)
                                   (wkTerm [ρ] ⊢Δ ⊢z))
                         (PE.subst (λ x → Δ ⊢ U.wk ρ s ∷ x ⦂ sF)
                                   (wk-β-natrec ρ F sF)
                                   (wkTerm [ρ] ⊢Δ ⊢s)))
  wkRedTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (Emptyrec-subst {A = A} ⊢A n⇒n′) =
    (Emptyrec-subst (wk [ρ] ⊢Δ ⊢A)
                    (wkRedTerm [ρ] ⊢Δ n⇒n′))
  wkRedTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (rew {A} {s} {p = p} {u = u} {l = l} rule ⊢u  ⊢ka eqrhs eqlhs) =
    rew rule
        (PE.subst (λ A → Δ ⊢ U.wk ρ u ∷ A ⦂ _) (wk-wkAll [ρ]) (wkTerm [ρ] ⊢Δ ⊢u))
        (PE.subst (λ l → Δ ⊢ l ∷ U.wk ρ A ⦂ s) (PE.sym (wk-rew-lhs rule [ρ])) (wkTerm [ρ] ⊢Δ ⊢ka))
        (PE.trans (PE.cong (U.wk ρ) eqrhs) (PE.sym (wk-rew-rhs rule [ρ])))
        (PE.trans (PE.cong (U.wk ρ) eqlhs) (PE.sym (wk-rew-lhs-helper {l = l} {u = u} [ρ])))
  wkRedTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (Boxrec-subst {sF} {sE} {E} {F = F} {u = u} ⊢F ⊢E ⊢u t⇒t') =
    let [ρF] = wk [ρ] ⊢Δ ⊢F in
    PE.subst (λ x → _ ⊢ Boxrec _ _ _ _ _ ⇒ _ ∷ x ⦂ _)
             (PE.sym (wk-β E))
             (Boxrec-subst [ρF]
                          (wk (lift [ρ]) (⊢Δ ∙ Boxⱼ [ρF]) ⊢E)
                          (PE.subst (λ x → Δ ⊢ U.wk ρ u ∷ x ⦂ sE)
                                    (wk-β-Boxrec ρ (U.wk ρ F) sF E)
                                    (wkTerm [ρ] ⊢Δ ⊢u))
                          (wkRedTerm [ρ] ⊢Δ t⇒t')
                          )
  wkRedTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (Boxrec-box {sF} {sE} {E} {F} {u = u} ⊢F ⊢E ⊢u ⊢a) =
    let [ρF] = wk [ρ] ⊢Δ ⊢F in
    PE.subst (λ x → _ ⊢ Boxrec _ _ _ _ _ ⇒ _ ∷ x ⦂ _)
             (PE.sym (wk-β E))
             (Boxrec-box [ρF]
                         (wk (lift [ρ]) (⊢Δ ∙ Boxⱼ [ρF]) ⊢E)
                         (PE.subst (λ x → Δ ⊢ U.wk ρ u ∷ x ⦂ sE)
                                   (wk-β-Boxrec ρ (U.wk ρ F) sF E)
                                   (wkTerm [ρ] ⊢Δ ⊢u))
                         (wkTerm [ρ] ⊢Δ ⊢a)
                         )

wkRed* : ∀ {Γ Δ A B s ρ} → ρ ∷ Δ ⊆ Γ →
           let ρA = U.wk ρ A
               ρB = U.wk ρ B
           in ⊢ Δ → Γ ⊢ A ⇒* B ⦂ s → Δ ⊢ ρA ⇒* ρB ⦂ s
wkRed* ρ ⊢Δ (id A) = id (wk ρ ⊢Δ A)
wkRed* ρ ⊢Δ (A⇒A′ ⇨ A′⇒*B) = wkRed ρ ⊢Δ A⇒A′ ⇨ wkRed* ρ ⊢Δ A′⇒*B

wkRed*Term : ∀ {Γ Δ A t u s ρ} → ρ ∷ Δ ⊆ Γ →
           let ρA = U.wk ρ A
               ρt = U.wk ρ t
               ρu = U.wk ρ u
           in ⊢ Δ → Γ ⊢ t ⇒* u ∷ A ⦂ s → Δ ⊢ ρt ⇒* ρu ∷ ρA ⦂ s
wkRed*Term ρ ⊢Δ (id t) = id (wkTerm ρ ⊢Δ t)
wkRed*Term ρ ⊢Δ (t⇒t′ ⇨ t′⇒*u) = wkRedTerm ρ ⊢Δ t⇒t′ ⇨ wkRed*Term ρ ⊢Δ t′⇒*u

wkRed:*: : ∀ {Γ Δ A B s ρ} → ρ ∷ Δ ⊆ Γ →
         let ρA = U.wk ρ A
             ρB = U.wk ρ B
         in ⊢ Δ → Γ ⊢ A :⇒*: B ⦂ s → Δ ⊢ ρA :⇒*: ρB ⦂ s
wkRed:*: ρ ⊢Δ [ ⊢A , ⊢B , D ] = [ wk ρ ⊢Δ ⊢A , wk ρ ⊢Δ ⊢B , wkRed* ρ ⊢Δ D ]

wkRed:*:Term : ∀ {Γ Δ A t u s ρ} → ρ ∷ Δ ⊆ Γ →
             let ρA = U.wk ρ A
                 ρt = U.wk ρ t
                 ρu = U.wk ρ u
             in ⊢ Δ → Γ ⊢ t :⇒*: u ∷ A ⦂ s → Δ ⊢ ρt :⇒*: ρu ∷ ρA ⦂ s
wkRed:*:Term ρ ⊢Δ [ ⊢t , ⊢u , d ] =
  [ wkTerm ρ ⊢Δ ⊢t , wkTerm ρ ⊢Δ ⊢u , wkRed*Term ρ ⊢Δ d ]



-- interaction between cstr-cod and weakening/substitutions

cstr-codU-ctx : ∀ {Γ k s} → cstr-cod k PE.≡ Univ s → cstr-cod-ctx Γ k PE.≡ Univ s
cstr-codU-ctx {Γ} e = PE.cong (λ x → U.wk (lift (empty-wk Γ)) x) e

cstr-codU-substS : ∀ {Γ k s a} → cstr-cod k PE.≡ Univ s → (cstr-cod-ctx Γ k) [ a ] PE.≡ Univ s
cstr-codU-substS {Γ} {a = a} e = PE.cong (λ x → x [ a ]) (cstr-codU-ctx e)

-- KM : Are the 2 following lemmas useful ?
[]-cstr-ctx-PE-wk : ∀ {k K t ρ}
                  → cstr-cod k PE.≡ cstr K t
                  → U.wk ρ (cstr-cod k) PE.≡ cstr K (U.wk ρ t)
[]-cstr-ctx-PE-wk {ρ = ρ} e = PE.cong (λ x → U.wk ρ x) e

[]-cstr-ctx-PE-subst : ∀ {k K t ρ}
                  → cstr-cod k PE.≡ cstr K t
                  → U.subst ρ (cstr-cod k) PE.≡ cstr K (U.subst ρ t)
[]-cstr-ctx-PE-subst {ρ = ρ} e = PE.cong (λ x → U.subst ρ x) e


[]-cstr-wk : ∀ {t K ρ} → [ K ]-cstr t → [ K ]-cstr (U.wk ρ t)
[]-cstr-wk {.(cstr _ _)} is-K-cstr = is-K-cstr

[]-cstr-subst : ∀ {t K ρ} → [ K ]-cstr t → [ K ]-cstr (U.subst ρ t)
[]-cstr-subst {.(cstr _ _)} is-K-cstr = is-K-cstr

[]-cstr-cod-ctx : ∀ {Γ k K} → [ K ]-cstr (cstr-cod k) → [ K ]-cstr (cstr-cod-ctx Γ k)
[]-cstr-cod-ctx {Γ} d = []-cstr-wk d

[]-cstr-cod-subst : ∀ {Γ k K a} → [ K ]-cstr (cstr-cod k) → [ K ]-cstr ((cstr-cod-ctx Γ k) [ a ])
[]-cstr-cod-subst {Γ} d = []-cstr-subst ([]-cstr-cod-ctx d)

-- cstr-codU-substS : ∀ {Γ k s a} → cstr-cod k PE.≡ Univ s → (cstr-cod-ctx Γ k) [ a ] PE.≡ Univ s
-- cstr-codU-substS {Γ} {a = a} e = PE.cong (λ x → x [ a ]) (cstr-codU-ctx e)


empty-wk-⊆ : ∀ {Γ} → ⊢ Γ → empty-wk Γ ∷ Γ ⊆ ε
empty-wk-⊆ ε = id
empty-wk-⊆ (d ∙ x) = step (empty-wk-⊆ d)

cstr-dom-ctx-wty : ∀ {Γ k} → ⊢ Γ → Γ ⊢ cstr-dom-ctx Γ k ⦂ cstr-dom-sort k
cstr-dom-ctx-wty {k = k} ⊢Γ = wk (empty-wk-⊆ ⊢Γ) ⊢Γ (cstr-dom-wty k)

cstr-cod-ctx-wty : ∀ {Γ k} → ⊢ Γ → Γ ∙ cstr-dom-ctx Γ k ⦂ cstr-dom-sort k ⊢ cstr-cod-ctx Γ k ⦂ cstr-cod-sort k
cstr-cod-ctx-wty {k = k} d = wk (lift (empty-wk-⊆ d)) (d ∙ cstr-dom-ctx-wty d) (cstr-cod-wty k)
