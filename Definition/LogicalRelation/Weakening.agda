{-# OPTIONS --without-K --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Weakening {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Weakening as T hiding (wk; wkEq; wkTerm; wkEqTerm)
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Weakening of neutrals in WHNF

wkTermNe : ∀ {ρ Γ Δ k A rA} → ρ ∷ Δ ⊆ Γ → (⊢Δ : ⊢ Δ)
         → Γ ⊩neNf k ∷ A ^ rA → Δ ⊩neNf U.wk ρ k ∷ U.wk ρ A ^ rA
wkTermNe {ρ} [ρ] ⊢Δ (neNfₜ neK ⊢k k≡k) =
  neNfₜ (wkNeutral ρ neK) (T.wkTerm [ρ] ⊢Δ ⊢k) (~-wk [ρ] ⊢Δ k≡k)

wkEqTermNe : ∀ {ρ Γ Δ k k′ A rA} → ρ ∷ Δ ⊆ Γ → (⊢Δ : ⊢ Δ)
           → Γ ⊩neNf k ≡ k′ ∷ A ^ rA → Δ ⊩neNf U.wk ρ k ≡ U.wk ρ k′ ∷ U.wk ρ A ^ rA
wkEqTermNe {ρ} [ρ] ⊢Δ (neNfₜ₌ neK neM k≡m) =
  neNfₜ₌ (wkNeutral ρ neK) (wkNeutral ρ neM) (~-wk [ρ] ⊢Δ k≡m)

-- Weakening of reducible natural numbers

mutual
  wkTermℕ : ∀ {ρ Γ Δ n} → ρ ∷ Δ ⊆ Γ → (⊢Δ : ⊢ Δ)
          → Γ ⊩ℕ n ∷ℕ → Δ ⊩ℕ U.wk ρ n ∷ℕ
  wkTermℕ {ρ} [ρ] ⊢Δ (ℕₜ n d n≡n prop) =
    ℕₜ (U.wk ρ n) (wkRed:*:Term [ρ] ⊢Δ d)
       (≅ₜ-wk [ρ] ⊢Δ n≡n)
       (wkNatural-prop [ρ] ⊢Δ prop)

  wkNatural-prop : ∀ {ρ Γ Δ n} → ρ ∷ Δ ⊆ Γ → (⊢Δ : ⊢ Δ)
                 → Natural-prop Γ n
                 → Natural-prop Δ (U.wk ρ n)
  wkNatural-prop ρ ⊢Δ (sucᵣ n) = sucᵣ (wkTermℕ ρ ⊢Δ n)
  wkNatural-prop ρ ⊢Δ zeroᵣ = zeroᵣ
  wkNatural-prop ρ ⊢Δ (ne nf) = ne (wkTermNe ρ ⊢Δ nf)

mutual
  wkEqTermℕ : ∀ {ρ Γ Δ t u} → ρ ∷ Δ ⊆ Γ → (⊢Δ : ⊢ Δ)
            → Γ ⊩ℕ t ≡ u ∷ℕ
            → Δ ⊩ℕ U.wk ρ t ≡ U.wk ρ u ∷ℕ
  wkEqTermℕ {ρ} [ρ] ⊢Δ (ℕₜ₌ k k′ d d′ t≡u prop) =
    ℕₜ₌ (U.wk ρ k) (U.wk ρ k′) (wkRed:*:Term [ρ] ⊢Δ d)
        (wkRed:*:Term [ρ] ⊢Δ d′) (≅ₜ-wk [ρ] ⊢Δ t≡u)
        (wk[Natural]-prop [ρ] ⊢Δ prop)

  wk[Natural]-prop : ∀ {ρ Γ Δ n n′} → ρ ∷ Δ ⊆ Γ → (⊢Δ : ⊢ Δ)
                   → [Natural]-prop Γ n n′
                   → [Natural]-prop Δ (U.wk ρ n) (U.wk ρ n′)
  wk[Natural]-prop ρ ⊢Δ (sucᵣ [n≡n′]) = sucᵣ (wkEqTermℕ ρ ⊢Δ [n≡n′])
  wk[Natural]-prop ρ ⊢Δ zeroᵣ = zeroᵣ
  wk[Natural]-prop ρ ⊢Δ (ne x) = ne (wkEqTermNe ρ ⊢Δ x)

-- Empty
wkTermEmpty : ∀ {ρ Γ Δ n} → ρ ∷ Δ ⊆ Γ → (⊢Δ : ⊢ Δ)
  → Γ ⊩Empty n ∷Empty → Δ ⊩Empty U.wk ρ n ∷Empty
wkTermEmpty {ρ} [ρ] ⊢Δ (Emptyₜ (ne d)) = Emptyₜ (ne (T.wkTerm [ρ] ⊢Δ d))
  -- Emptyₜ (U.wk ρ n) (wkRed:*:Term [ρ] ⊢Δ d)
  --    (≅ₜ-wk [ρ] ⊢Δ n≡n)
  --    (ne (wkTermNe [ρ] ⊢Δ prop))

wk[Empty]-prop : ∀ {ρ Γ Δ n n′} → ρ ∷ Δ ⊆ Γ → (⊢Δ : ⊢ Δ)
  → [Empty]-prop Γ n n′
  → [Empty]-prop Δ (U.wk ρ n) (U.wk ρ n′)
wk[Empty]-prop {ρ} [ρ] ⊢Δ (ne d d') = ne (T.wkTerm [ρ] ⊢Δ d) (T.wkTerm [ρ] ⊢Δ d') -- ne (wkEqTermNe ρ ⊢Δ x)

wkEqTermEmpty : ∀ {ρ Γ Δ t u} → ρ ∷ Δ ⊆ Γ → (⊢Δ : ⊢ Δ)
  → Γ ⊩Empty t ≡ u ∷Empty
  → Δ ⊩Empty U.wk ρ t ≡ U.wk ρ u ∷Empty
wkEqTermEmpty {ρ} [ρ] ⊢Δ (Emptyₜ₌ (ne d d')) = Emptyₜ₌ (ne (T.wkTerm [ρ] ⊢Δ d) (T.wkTerm [ρ] ⊢Δ d'))
  -- Emptyₜ₌ (U.wk ρ k) (U.wk ρ k′) (wkRed:*:Term [ρ] ⊢Δ d)
  --     (wkRed:*:Term [ρ] ⊢Δ d′) (≅ₜ-wk [ρ] ⊢Δ t≡u)
  --     (wk[Empty]-prop [ρ] ⊢Δ prop)


-- Weakening of the logical relation

wk : ∀ {ρ Γ Δ A rA l} → ρ ∷ Δ ⊆ Γ → ⊢ Δ → Γ ⊩⟨ l ⟩ A ^ rA → Δ ⊩⟨ l ⟩ U.wk ρ A ^ rA
wk ρ ⊢Δ (Uᵣ′ r l′ l< ⊢Γ) = Uᵣ′ r l′ l< ⊢Δ
wk ρ ⊢Δ (ℕᵣ D) = ℕᵣ (wkRed:*: ρ ⊢Δ D)
wk ρ ⊢Δ (Emptyᵣ D) = Emptyᵣ (wkRed:*: ρ ⊢Δ D)
wk {ρ} [ρ] ⊢Δ (ne′ K D neK K≡K) =
  ne′ (U.wk ρ K) (wkRed:*: [ρ] ⊢Δ D) (wkNeutral ρ neK) (~-wk [ρ] ⊢Δ K≡K)
wk {ρ} {Γ} {Δ} {A} {rA} {l} [ρ] ⊢Δ (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) =
  let ⊢ρF = T.wk [ρ] ⊢Δ ⊢F
      [F]′ : ∀ {ρ ρ′ E} ([ρ] : ρ ∷ E ⊆ Δ) ([ρ′] : ρ′ ∷ Δ ⊆ Γ) (⊢E : ⊢ E)
           → E ⊩⟨ l ⟩ U.wk ρ (U.wk ρ′ F) ^ rF
      [F]′ {ρ} {ρ′} [ρ] [ρ′] ⊢E = irrelevance′
                              (PE.sym (wk-comp ρ ρ′ F))
                              ([F] ([ρ] •ₜ [ρ′]) ⊢E)
      [a]′ : ∀ {ρ ρ′ E a} ([ρ] : ρ ∷ E ⊆ Δ) ([ρ′] : ρ′ ∷ Δ ⊆ Γ) (⊢E : ⊢ E)
             ([a] : E ⊩⟨ l ⟩ a ∷ U.wk ρ (U.wk ρ′ F) ^ rF / [F]′ [ρ] [ρ′] ⊢E)
           → E ⊩⟨ l ⟩ a ∷ U.wk (ρ • ρ′) F ^ rF / [F] ([ρ] •ₜ [ρ′]) ⊢E
      [a]′ {ρ} {ρ′} [ρ] [ρ′] ⊢E [a] = irrelevanceTerm′ (wk-comp ρ ρ′ F) PE.refl
                                          ([F]′ [ρ] [ρ′] ⊢E) ([F] ([ρ] •ₜ [ρ′]) ⊢E) [a]
      [G]′ : ∀ {ρ ρ′ E a} ([ρ] : ρ ∷ E ⊆ Δ) ([ρ′] : ρ′ ∷ Δ ⊆ Γ) (⊢E : ⊢ E)
             ([a] : E ⊩⟨ l ⟩ a ∷ U.wk ρ (U.wk ρ′ F) ^ rF / [F]′ [ρ] [ρ′] ⊢E)
           → E ⊩⟨ l ⟩ U.wk (lift (ρ • ρ′)) G [ a ] ^ rA
      [G]′ η η′ ⊢E [a] = [G] (η •ₜ η′) ⊢E ([a]′ η η′ ⊢E [a])
  in  Πᵣ′ rF (U.wk ρ F) (U.wk (lift ρ) G) (T.wkRed:*: [ρ] ⊢Δ D) ⊢ρF
           (T.wk (lift [ρ]) (⊢Δ ∙ ⊢ρF) ⊢G)
           (≅-wk [ρ] ⊢Δ A≡A)
           (λ {ρ₁} [ρ₁] ⊢Δ₁ → irrelevance′ (PE.sym (wk-comp ρ₁ ρ F))
                                    ([F] ([ρ₁] •ₜ [ρ]) ⊢Δ₁))
           (λ {ρ₁} [ρ₁] ⊢Δ₁ [a] → irrelevance′ (wk-comp-subst ρ₁ ρ G)
                                        ([G]′ [ρ₁] [ρ] ⊢Δ₁ [a]))
           (λ {ρ₁} [ρ₁] ⊢Δ₁ [a] [b] [a≡b] →
              let [a≡b]′ = irrelevanceEqTerm′ (wk-comp ρ₁ ρ F) PE.refl
                                              ([F]′ [ρ₁] [ρ] ⊢Δ₁)
                                              ([F] ([ρ₁] •ₜ [ρ]) ⊢Δ₁)
                                              [a≡b]
              in  irrelevanceEq″ (wk-comp-subst ρ₁ ρ G)
                                  (wk-comp-subst ρ₁ ρ G)
                                  ([G]′ [ρ₁] [ρ] ⊢Δ₁ [a])
                                  (irrelevance′
                                            (wk-comp-subst ρ₁ ρ G)
                                            ([G]′ [ρ₁] [ρ] ⊢Δ₁ [a]))
                                  (G-ext ([ρ₁] •ₜ [ρ]) ⊢Δ₁
                                         ([a]′ [ρ₁] [ρ] ⊢Δ₁ [a])
                                         ([a]′ [ρ₁] [ρ] ⊢Δ₁ [b])
                                         [a≡b]′))
wk ρ ⊢Δ (emb 0<1 x) = emb 0<1 (wk ρ ⊢Δ x)

wkEq : ∀ {ρ Γ Δ A B r l} → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
       ([A] : Γ ⊩⟨ l ⟩ A ^ r)
     → Γ ⊩⟨ l ⟩ A ≡ B ^ r / [A]
     → Δ ⊩⟨ l ⟩ U.wk ρ A ≡ U.wk ρ B ^ r / wk [ρ] ⊢Δ [A]
wkEq ρ ⊢Δ (Uᵣ′ _ _ _ _) PE.refl = PE.refl
wkEq ρ ⊢Δ (ℕᵣ D) A≡B = wkRed* ρ ⊢Δ A≡B
wkEq ρ ⊢Δ (Emptyᵣ D) A≡B = wkRed* ρ ⊢Δ A≡B
wkEq {ρ} [ρ] ⊢Δ (ne′ _ _ _ _) (ne₌ M D′ neM K≡M) =
  ne₌ (U.wk ρ M) (wkRed:*: [ρ] ⊢Δ D′)
      (wkNeutral ρ neM) (~-wk [ρ] ⊢Δ K≡M)
wkEq {ρ} [ρ] ⊢Δ (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) =
  Π₌ (U.wk ρ F′) (U.wk (lift ρ) G′) (T.wkRed* [ρ] ⊢Δ D′) (≅-wk [ρ] ⊢Δ A≡B)
     (λ {ρ₁} [ρ₁] ⊢Δ₁ → irrelevanceEq″ (PE.sym (wk-comp ρ₁ ρ F))
                                 (PE.sym (wk-comp ρ₁ ρ F′))
                                 ([F] ([ρ₁] •ₜ [ρ]) ⊢Δ₁)
                                 (irrelevance′ (PE.sym (wk-comp ρ₁ ρ F))
                                               ([F] ([ρ₁] •ₜ [ρ]) ⊢Δ₁))
                                 ([F≡F′] ([ρ₁] •ₜ [ρ]) ⊢Δ₁))
     (λ {ρ₁} [ρ₁] ⊢Δ₁ [a] →
        let [a]′ = irrelevanceTerm′ (wk-comp ρ₁ ρ F) PE.refl
                                    (irrelevance′ (PE.sym (wk-comp ρ₁ ρ F))
                                                  ([F] ([ρ₁] •ₜ [ρ]) ⊢Δ₁))
                                    ([F] ([ρ₁] •ₜ [ρ]) ⊢Δ₁) [a]
        in  irrelevanceEq″ (wk-comp-subst ρ₁ ρ G)
                            (wk-comp-subst ρ₁ ρ G′)
                            ([G] ([ρ₁] •ₜ [ρ]) ⊢Δ₁ [a]′)
                            (irrelevance′ (wk-comp-subst ρ₁ ρ G)
                                          ([G] ([ρ₁] •ₜ [ρ]) ⊢Δ₁ [a]′))
                            ([G≡G′] ([ρ₁] •ₜ [ρ]) ⊢Δ₁ [a]′))
wkEq ρ ⊢Δ (emb 0<1 x) A≡B = wkEq ρ ⊢Δ x A≡B

wkTerm : ∀ {ρ Γ Δ A t r l} ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
         ([A] : Γ ⊩⟨ l ⟩ A ^ r)
       → Γ ⊩⟨ l ⟩ t ∷ A ^ r / [A]
       → Δ ⊩⟨ l ⟩ U.wk ρ t ∷ U.wk ρ A ^ r / wk [ρ] ⊢Δ [A]
wkTerm {ρ} [ρ] ⊢Δ (Uᵣ′ ru .⁰ 0<1 ⊢Γ) (Uₜ A d typeA A≡A [t]) =
  Uₜ (U.wk ρ A) (wkRed:*:Term [ρ] ⊢Δ d)
     (wkType ρ typeA) (≅ₜ-wk [ρ] ⊢Δ A≡A) (wk [ρ] ⊢Δ [t])
wkTerm ρ ⊢Δ (ℕᵣ D) [t] = wkTermℕ ρ ⊢Δ [t]
wkTerm ρ ⊢Δ (Emptyᵣ D) [t] = wkTermEmpty ρ ⊢Δ [t]
wkTerm {ρ} [ρ] ⊢Δ (ne′ K D neK K≡K) (neₜ k d nf) =
  neₜ (U.wk ρ k) (wkRed:*:Term [ρ] ⊢Δ d) (wkTermNe [ρ] ⊢Δ nf)
wkTerm {ρ} [ρ] ⊢Δ (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Πₜ f d funcF f≡f [f] [f]₁) =
  Πₜ (U.wk ρ f) (wkRed:*:Term [ρ] ⊢Δ d) (wkFunction ρ funcF)
     (≅ₜ-wk [ρ] ⊢Δ f≡f)
     (λ {ρ₁} [ρ₁] ⊢Δ₁ [a] [b] [a≡b] →
        let F-compEq = wk-comp ρ₁ ρ F
            G-compEq = wk-comp-subst ρ₁ ρ G
            [F]₁ = [F] ([ρ₁] •ₜ [ρ]) ⊢Δ₁
            [F]₂ = irrelevance′ (PE.sym (wk-comp ρ₁ ρ F)) [F]₁
            [a]′ = irrelevanceTerm′ F-compEq PE.refl [F]₂ [F]₁ [a]
            [b]′ = irrelevanceTerm′ F-compEq PE.refl [F]₂ [F]₁ [b]
            [G]₁ = [G] ([ρ₁] •ₜ [ρ]) ⊢Δ₁ [a]′
            [G]₂ = irrelevance′ G-compEq [G]₁
            [a≡b]′ = irrelevanceEqTerm′ F-compEq PE.refl [F]₂ [F]₁ [a≡b]
        in  irrelevanceEqTerm″ (PE.cong (λ x → x ∘ _) (PE.sym (wk-comp ρ₁ ρ _)))
                                (PE.cong (λ x → x ∘ _) (PE.sym (wk-comp ρ₁ ρ _)))
                                G-compEq
                                [G]₁ [G]₂
                                ([f] ([ρ₁] •ₜ [ρ]) ⊢Δ₁ [a]′ [b]′ [a≡b]′))
     (λ {ρ₁} [ρ₁] ⊢Δ₁ [a] →
        let [F]₁ = [F] ([ρ₁] •ₜ [ρ]) ⊢Δ₁
            [F]₂ = irrelevance′ (PE.sym (wk-comp ρ₁ ρ F)) [F]₁
            [a]′ = irrelevanceTerm′ (wk-comp ρ₁ ρ F) PE.refl [F]₂ [F]₁ [a]
            [G]₁ = [G] ([ρ₁] •ₜ [ρ]) ⊢Δ₁ [a]′
            [G]₂ = irrelevance′ (wk-comp-subst ρ₁ ρ G) [G]₁
        in  irrelevanceTerm″ (wk-comp-subst ρ₁ ρ G)
                              (PE.cong (λ x → x ∘ _) (PE.sym (wk-comp ρ₁ ρ _)))
                              [G]₁ [G]₂ ([f]₁ ([ρ₁] •ₜ [ρ]) ⊢Δ₁ [a]′))
wkTerm ρ ⊢Δ (emb 0<1 x) t = wkTerm ρ ⊢Δ x t

wkEqTerm : ∀ {ρ Γ Δ A t u r l} ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
           ([A] : Γ ⊩⟨ l ⟩ A ^ r)
         → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ r / [A]
         → Δ ⊩⟨ l ⟩ U.wk ρ t ≡ U.wk ρ u ∷ U.wk ρ A ^ r / wk [ρ] ⊢Δ [A]
wkEqTerm {ρ} [ρ] ⊢Δ (Uᵣ′ _ .⁰ 0<1 ⊢Γ) (Uₜ₌ A B d d′ typeA typeB A≡B [t] [u] [t≡u]) =
  Uₜ₌ (U.wk ρ A) (U.wk ρ B) (wkRed:*:Term [ρ] ⊢Δ d) (wkRed:*:Term [ρ] ⊢Δ d′)
      (wkType ρ typeA) (wkType ρ typeB) (≅ₜ-wk [ρ] ⊢Δ A≡B)
      (wk [ρ] ⊢Δ [t]) (wk [ρ] ⊢Δ [u]) (wkEq [ρ] ⊢Δ [t] [t≡u])
wkEqTerm ρ ⊢Δ (ℕᵣ D) [t≡u] = wkEqTermℕ ρ ⊢Δ [t≡u]
wkEqTerm ρ ⊢Δ (Emptyᵣ D) [t≡u] = wkEqTermEmpty ρ ⊢Δ [t≡u]
wkEqTerm {ρ} [ρ] ⊢Δ (ne′ K D neK K≡K) (neₜ₌ k m d d′ nf) =
  neₜ₌ (U.wk ρ k) (U.wk ρ m)
       (wkRed:*:Term [ρ] ⊢Δ d) (wkRed:*:Term [ρ] ⊢Δ d′)
       (wkEqTermNe [ρ] ⊢Δ nf)
wkEqTerm {ρ} [ρ] ⊢Δ (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                    (Πₜ₌ f g d d′ funcF funcG f≡g [t] [u] [f≡g]) =
  let [A] = Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext
  in  Πₜ₌ (U.wk ρ f) (U.wk ρ g) (wkRed:*:Term [ρ] ⊢Δ d) (wkRed:*:Term [ρ] ⊢Δ d′)
          (wkFunction ρ funcF) (wkFunction ρ funcG)
          (≅ₜ-wk [ρ] ⊢Δ f≡g) (wkTerm [ρ] ⊢Δ [A] [t]) (wkTerm [ρ] ⊢Δ [A] [u])
          (λ {ρ₁} [ρ₁] ⊢Δ₁ [a] →
             let [F]₁ = [F] ([ρ₁] •ₜ [ρ]) ⊢Δ₁
                 [F]₂ = irrelevance′ (PE.sym (wk-comp ρ₁ ρ F)) [F]₁
                 [a]′ = irrelevanceTerm′ (wk-comp ρ₁ ρ F) PE.refl [F]₂ [F]₁ [a]
                 [G]₁ = [G] ([ρ₁] •ₜ [ρ]) ⊢Δ₁ [a]′
                 [G]₂ = irrelevance′ (wk-comp-subst ρ₁ ρ G) [G]₁
             in  irrelevanceEqTerm″ (PE.cong (λ y → y ∘ _) (PE.sym (wk-comp ρ₁ ρ _)))
                                     (PE.cong (λ y → y ∘ _) (PE.sym (wk-comp ρ₁ ρ _)))
                                     (wk-comp-subst ρ₁ ρ G)
                                     [G]₁ [G]₂
                                     ([f≡g] ([ρ₁] •ₜ [ρ]) ⊢Δ₁ [a]′))
wkEqTerm ρ ⊢Δ (emb 0<1 x) t≡u = wkEqTerm ρ ⊢Δ x t≡u
