{-# OPTIONS --without-K  #-}

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

wkTermNe : ∀ {ρ Γ Δ k A sA} → ρ ∷ Δ ⊆ Γ → (⊢Δ : ⊢ Δ)
         → Γ ⊩neNf k ∷ A ⦂ sA → Δ ⊩neNf U.wk ρ k ∷ U.wk ρ A ⦂ sA
wkTermNe {ρ} [ρ] ⊢Δ (neNfₜ neK ⊢k k≡k) =
  neNfₜ (wkNeutral ρ neK) (T.wkTerm [ρ] ⊢Δ ⊢k) (~-wk [ρ] ⊢Δ k≡k)

wkEqTermNe : ∀ {ρ Γ Δ k k′ A sA} → ρ ∷ Δ ⊆ Γ → (⊢Δ : ⊢ Δ)
           → Γ ⊩neNf k ≡ k′ ∷ A ⦂ sA → Δ ⊩neNf U.wk ρ k ≡ U.wk ρ k′ ∷ U.wk ρ A ⦂ sA
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
wkTermEmpty {ρ} [ρ] ⊢Δ (Emptyₜ n d n≡n (ne prop)) =
  Emptyₜ (U.wk ρ n) (wkRed:*:Term [ρ] ⊢Δ d)
     (≅ₜ-wk [ρ] ⊢Δ n≡n)
     (ne (wkTermNe [ρ] ⊢Δ prop))

wk[Empty]-prop : ∀ {ρ Γ Δ n n′} → ρ ∷ Δ ⊆ Γ → (⊢Δ : ⊢ Δ)
  → [Empty]-prop Γ n n′
  → [Empty]-prop Δ (U.wk ρ n) (U.wk ρ n′)
wk[Empty]-prop ρ ⊢Δ (ne x) = ne (wkEqTermNe ρ ⊢Δ x)

wkEqTermEmpty : ∀ {ρ Γ Δ t u} → ρ ∷ Δ ⊆ Γ → (⊢Δ : ⊢ Δ)
  → Γ ⊩Empty t ≡ u ∷Empty
  → Δ ⊩Empty U.wk ρ t ≡ U.wk ρ u ∷Empty
wkEqTermEmpty {ρ} [ρ] ⊢Δ (Emptyₜ₌ k k′ d d′ t≡u prop) =
  Emptyₜ₌ (U.wk ρ k) (U.wk ρ k′) (wkRed:*:Term [ρ] ⊢Δ d)
      (wkRed:*:Term [ρ] ⊢Δ d′) (≅ₜ-wk [ρ] ⊢Δ t≡u)
      (wk[Empty]-prop [ρ] ⊢Δ prop)


module wkCstr {K : constructors}
              {Pi Qi : ∀ ki → [ K ]-cstr (cstr-cod ki) → Term → Set}
              {ρ Γ Δ}
              ([ρ] : ρ ∷ Δ ⊆ Γ)
              (⊢Δ : ⊢ Δ)
              (PQ : ∀ ki kiK t → Pi ki kiK t → Qi ki kiK (U.wk ρ t))
              where
  module C = Cstr K Pi
  module C' = Cstr K Qi

  wkcstr : ∀ {a s k} → Γ C.⊩cstr k ∷K a ⦂ s → Δ C'.⊩cstr U.wk ρ k ∷K U.wk ρ a ⦂ s
  wk-prop : ∀ {a s k} → C.Cstr-prop Γ a s k → C'.Cstr-prop Δ (U.wk ρ a) s (U.wk ρ k)

  wkcstr (Cstr.cstrₜ k D k≡k [k]) = Cstr.cstrₜ (U.wk ρ k) (wkRed:*:Term [ρ] ⊢Δ D) (≅ₜ-wk [ρ] ⊢Δ k≡k) (wk-prop [k])

  wk-prop (Cstr.cstrᵣ kK x) = C'.cstrᵣ kK (PQ _ kK _ x)
  wk-prop (Cstr.cstr-recᵣ kK kdomK x ⊢Kx [x]) =
    C'.cstr-recᵣ kK kdomK
                 (PE.subst (Qi _ kK) (wk-wkAll [ρ]) (PQ _ kK _ x))
                 (PE.subst (λ t → Δ ⊢ cstr K t ⦂ _) (wk-wkAll [ρ]) (T.wk [ρ] ⊢Δ ⊢Kx))
                 (PE.subst (λ t → Δ C'.⊩cstr U.wk ρ _ ∷K t ⦂ _) (wk-wkAll [ρ]) (wkcstr [x]))
  wk-prop (Cstr.ne x) = C'.ne (wkTermNe [ρ] ⊢Δ x)

module wk[Cstr] {K : constructors}
                {Pi Qi : ∀ ki → [ K ]-cstr (cstr-cod ki) → Term → Term → Set}
                {ρ Γ Δ}
                ([ρ] : ρ ∷ Δ ⊆ Γ)
                (⊢Δ : ⊢ Δ)
                (PQ : ∀ ki kiK t t' → Pi ki kiK t t' → Qi ki kiK (U.wk ρ t) (U.wk ρ t'))
                where
  module C = [Cstr] K Pi
  module C' = [Cstr] K Qi

  wkcstr : ∀ {a s k k'} → Γ C.⊩cstr k ≡ k' ∷K a ⦂ s → Δ C'.⊩cstr U.wk ρ k ≡ U.wk ρ k' ∷K U.wk ρ a ⦂ s
  wk-prop : ∀ {a s k k'} → C.[Cstr]-prop Γ a s k k' → C'.[Cstr]-prop Δ (U.wk ρ a) s (U.wk ρ k) (U.wk ρ k')

  wkcstr ([Cstr].cstrₜ k k' D D' k≡k' [k≡k']) =
    [Cstr].cstrₜ (U.wk ρ k) (U.wk ρ k') (wkRed:*:Term [ρ] ⊢Δ D) (wkRed:*:Term [ρ] ⊢Δ D') (≅ₜ-wk [ρ] ⊢Δ k≡k') (wk-prop [k≡k'])

  wk-prop ([Cstr].cstrᵣ kK x) = C'.cstrᵣ kK (PQ _ kK _ _ x)
  wk-prop ([Cstr].cstr-recᵣ kK kdomK x ⊢Kx [x]) =
    C'.cstr-recᵣ kK kdomK
                 (PE.subst₂ (Qi _ kK) (wk-wkAll [ρ]) (wk-wkAll [ρ]) (PQ _ kK _ _ x))
                 (PE.subst (λ t → Δ ⊢ cstr K t ⦂ _) (wk-wkAll [ρ]) (T.wk [ρ] ⊢Δ ⊢Kx))
                 (PE.subst (λ t → Δ C'.⊩cstr U.wk ρ _ ≡ U.wk ρ _ ∷K t ⦂ _) (wk-wkAll [ρ]) (wkcstr [x]))
  wk-prop ([Cstr].ne x) = C'.ne (wkEqTermNe [ρ] ⊢Δ x)


wkBox-prop : ∀ {ρ P Q Γ Δ F sF b} →
               ([ρ] : ρ ∷ Δ ⊆ Γ)
               (⊢Δ : ⊢ Δ)
               (PQ : ∀ b → P b → Q (U.wk ρ b))
               (d : Box-prop P Γ F sF b)
               → Box-prop Q Δ (U.wk ρ F) sF (U.wk ρ b)
wkBox-prop [ρ] ⊢Δ PQ (boxᵣ x) = boxᵣ (PQ _ x)
wkBox-prop [ρ] ⊢Δ PQ (ne x) = ne (wkTermNe [ρ] ⊢Δ x)

wk[Box]-prop : ∀ {ρ P Q Γ Δ F sF b b'} →
               ([ρ] : ρ ∷ Δ ⊆ Γ)
               (⊢Δ : ⊢ Δ)
               (PQ : ∀ b b' → P b b' → Q (U.wk ρ b) (U.wk ρ b'))
               (d : [Box]-prop P Γ F sF b b')
               → [Box]-prop Q Δ (U.wk ρ F) sF (U.wk ρ b) (U.wk ρ b')
wk[Box]-prop [ρ] ⊢Δ PQ (boxᵣ x) = boxᵣ (PQ _ _ x)
wk[Box]-prop [ρ] ⊢Δ PQ (ne x) = ne (wkEqTermNe [ρ] ⊢Δ x)


mutual
  -- Weakening of the logical relation

  {-# TERMINATING #-}
  wk : ∀ {ρ Γ Δ A sA l}
    → ρ ∷ Δ ⊆ Γ
    → ⊢ Δ → Γ ⊩⟨ l ⟩ A ⦂ sA
    → Δ ⊩⟨ l ⟩ U.wk ρ A ⦂ sA
  wk ρ ⊢Δ (Uᵣ′ s l′ l< ⊢Γ) = Uᵣ′ s l′ l< ⊢Δ
  wk ρ ⊢Δ (ℕᵣ D) = ℕᵣ (wkRed:*: ρ ⊢Δ D)
  wk ρ ⊢Δ (Emptyᵣ D) = Emptyᵣ (wkRed:*: ρ ⊢Δ D)
  wk {ρ} {Γ} {Δ = Δ} {l = l} [ρ] ⊢Δ (cstrᵣ′ K KcodU a D ⊢a A≡A [domK] [a] [Yi]) =
    let ρ[domK]  = wk [ρ] ⊢Δ [domK]
        ρ[domK]' = PE.subst (λ x → _ ⊩⟨ _ ⟩ x ⦂ _) (T.wk-wkAll [ρ]) ρ[domK]
    in
    cstrᵣ′ K KcodU (U.wk ρ a) (wkRed:*: [ρ] ⊢Δ D)
          (PE.subst (λ x → _ ⊢ U.wk ρ a ∷ x ⦂ _)
                    (T.wk-wkAll [ρ])
                    (T.wkTerm [ρ] ⊢Δ ⊢a))
          (PE.subst (λ x → _ ⊢ U.wk ρ a ≅ U.wk ρ a ∷ x ⦂ _)
                    (T.wk-wkAll [ρ])
                    (≅ₜ-wk [ρ] ⊢Δ A≡A))
          ρ[domK]'
          (irrelevanceTerm′ (T.wk-wkAll [ρ]) PE.refl ρ[domK] ρ[domK]' (wkTerm [ρ] ⊢Δ [domK] [a]))
          (wk[domi] [ρ] ⊢Δ [Yi])
  wk {ρ} [ρ] ⊢Δ (Boxᵣ′ F sF D ⊢F A≡A [F]) =
    Boxᵣ′ (U.wk ρ F) sF (wkRed:*: [ρ] ⊢Δ D) (T.wk [ρ] ⊢Δ ⊢F) (≅-wk [ρ] ⊢Δ A≡A) (wk [ρ] ⊢Δ [F])
  wk {ρ} [ρ] ⊢Δ (ne′ K D neK K≡K) =
    ne′ (U.wk ρ K) (wkRed:*: [ρ] ⊢Δ D) (wkNeutral ρ neK) (~-wk [ρ] ⊢Δ K≡K)
  wk {ρ} {Γ} {Δ} {A} {sA} {l} [ρ] ⊢Δ (Πᵣ′ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext) =
    let ⊢ρF = T.wk [ρ] ⊢Δ ⊢F
        [F]′ : ∀ {ρ ρ′ E} ([ρ] : ρ ∷ E ⊆ Δ) ([ρ′] : ρ′ ∷ Δ ⊆ Γ) (⊢E : ⊢ E)
            → E ⊩⟨ l ⟩ U.wk ρ (U.wk ρ′ F) ⦂ sF
        [F]′ {ρ} {ρ′} [ρ] [ρ′] ⊢E = irrelevance′
                                (PE.sym (wk-comp ρ ρ′ F))
                                ([F] ([ρ] •ₜ [ρ′]) ⊢E)
        [a]′ : ∀ {ρ ρ′ E a} ([ρ] : ρ ∷ E ⊆ Δ) ([ρ′] : ρ′ ∷ Δ ⊆ Γ) (⊢E : ⊢ E)
              ([a] : E ⊩⟨ l ⟩ a ∷ U.wk ρ (U.wk ρ′ F) ⦂ sF / [F]′ [ρ] [ρ′] ⊢E)
            → E ⊩⟨ l ⟩ a ∷ U.wk (ρ • ρ′) F ⦂ sF / [F] ([ρ] •ₜ [ρ′]) ⊢E
        [a]′ {ρ} {ρ′} [ρ] [ρ′] ⊢E [a] = irrelevanceTerm′ (wk-comp ρ ρ′ F) PE.refl
                                            ([F]′ [ρ] [ρ′] ⊢E) ([F] ([ρ] •ₜ [ρ′]) ⊢E) [a]
        [G]′ : ∀ {ρ ρ′ E a} ([ρ] : ρ ∷ E ⊆ Δ) ([ρ′] : ρ′ ∷ Δ ⊆ Γ) (⊢E : ⊢ E)
              ([a] : E ⊩⟨ l ⟩ a ∷ U.wk ρ (U.wk ρ′ F) ⦂ sF / [F]′ [ρ] [ρ′] ⊢E)
            → E ⊩⟨ l ⟩ U.wk (lift (ρ • ρ′)) G [ a ] ⦂ sA
        [G]′ η η′ ⊢E [a] = [G] (η •ₜ η′) ⊢E ([a]′ η η′ ⊢E [a])
    in  Πᵣ′ sF (U.wk ρ F) (U.wk (lift ρ) G) (T.wkRed:*: [ρ] ⊢Δ D) ⊢ρF
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

  wk[domi] : ∀ {ρ K Γ Δ l} ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ) → LogRel.type[domi] l (logRelRec l) Γ K → LogRel.type[domi] l (logRelRec l) Δ K
  wk[domi] {K = K} [ρ] ⊢Δ  [domi] ki kiK with [domi] ki kiK
  ... | (LogRel.cstᵣ n x) = LogRel.cstᵣ (λ x → n (wk-[]-cstr (wk-[]-cstr-rev x))) (PE.subst (λ x → _ ⊩⟨ _ ⟩ x ⦂ _) (T.wk-wkAll [ρ]) (wk [ρ] ⊢Δ x))
  ... | (LogRel.monᵣ d x) = LogRel.monᵣ (PE.subst ([ K ]-cstr) (wk-wkAll [ρ]) (wk-[]-cstr d)) x

  wkEq : ∀ {ρ Γ Δ A B s l} → ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
        ([A] : Γ ⊩⟨ l ⟩ A ⦂ s)
      → Γ ⊩⟨ l ⟩ A ≡ B ⦂ s / [A]
      → Δ ⊩⟨ l ⟩ U.wk ρ A ≡ U.wk ρ B ⦂ s / wk [ρ] ⊢Δ [A]
  wkEq ρ ⊢Δ (Uᵣ′ _ _ _ _) PE.refl = PE.refl
  wkEq ρ ⊢Δ (ℕᵣ D) A≡B = wkRed* ρ ⊢Δ A≡B
  wkEq ρ ⊢Δ (Emptyᵣ D) A≡B = wkRed* ρ ⊢Δ A≡B
  wkEq {ρ} [ρ] ⊢Δ (ne′ _ _ _ _) (ne₌ M D′ neM K≡M) =
    ne₌ (U.wk ρ M) (wkRed:*: [ρ] ⊢Δ D′)
        (wkNeutral ρ neM) (~-wk [ρ] ⊢Δ K≡M)
  wkEq {ρ} [ρ] ⊢Δ
       (cstrᵣ′ K KcodU a D ⊢a A≡A [domK] [a] [Yi])
       (cstr₌ a' D' A≡B [a≡a']) =
    let ρ[domK]  = wk [ρ] ⊢Δ [domK]
        ρ[domK]' = PE.subst (λ x → _ ⊩⟨ _ ⟩ x ⦂ _) (T.wk-wkAll [ρ]) ρ[domK]
    in cstr₌ (U.wk ρ a') (wkRed:*: [ρ] ⊢Δ D')
             (PE.subst (λ x → _ ⊢ U.wk ρ a ≅ U.wk ρ a' ∷ x ⦂ _)
                       (T.wk-wkAll [ρ])
                       (≅ₜ-wk [ρ] ⊢Δ A≡B))
             (irrelevanceEqTerm′ (T.wk-wkAll [ρ]) PE.refl ρ[domK] ρ[domK]'
                                 (wkEqTerm [ρ] ⊢Δ [domK] [a≡a']) )
  wkEq {ρ} [ρ] ⊢Δ (Boxᵣ′ F sF D ⊢F A≡A [F]) (Box₌ F' D' A≡B [F≡F']) =
    Box₌ (U.wk ρ F') (wkRed:*: [ρ] ⊢Δ D') (≅-wk [ρ] ⊢Δ A≡B) (wkEq [ρ] ⊢Δ [F] [F≡F'])
  wkEq {ρ} [ρ] ⊢Δ (Πᵣ′ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
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

  wkTerm : ∀ {ρ Γ Δ A t s l} ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
          ([A] : Γ ⊩⟨ l ⟩ A ⦂ s)
        → Γ ⊩⟨ l ⟩ t ∷ A ⦂ s / [A]
        → Δ ⊩⟨ l ⟩ U.wk ρ t ∷ U.wk ρ A ⦂ s / wk [ρ] ⊢Δ [A]
  wkTerm {ρ} [ρ] ⊢Δ (Uᵣ′ ru .⁰ 0<1 ⊢Γ) (Uₜ A d typeA A≡A [t]) =
    Uₜ (U.wk ρ A) (wkRed:*:Term [ρ] ⊢Δ d)
      (wkType ρ typeA) (≅ₜ-wk [ρ] ⊢Δ A≡A) (wk [ρ] ⊢Δ [t])
  wkTerm ρ ⊢Δ (ℕᵣ D) [t] = wkTermℕ ρ ⊢Δ [t]
  wkTerm ρ ⊢Δ (Emptyᵣ D) [t] = wkTermEmpty ρ ⊢Δ [t]
  wkTerm {ρ} [ρ] ⊢Δ (ne′ K D neK K≡K) (neₜ k d nf) =
    neₜ (U.wk ρ k) (wkRed:*:Term [ρ] ⊢Δ d) (wkTermNe [ρ] ⊢Δ nf)
  wkTerm {ρ} {Γ} {Δ} {t} {s = s} {l = l} [ρ] ⊢Δ
      (cstrᵣ′ K KcodU a D ⊢a A≡A [domK] [a] [Yi])
      d =
    wkCstr.wkcstr [ρ] ⊢Δ wk-aux d
    where
      [domK]' = PE.subst (λ x → Δ ⊩⟨ l ⟩ x ⦂ cstr-dom-sort K) (wk-wkAll [ρ]) (wk [ρ] ⊢Δ [domK])
      wk-aux : (ki : constructors) (kiK : [ K ]-cstr (cstr-cod ki)) (t : Term) →
               LogRel.cstr-arg-dispatch l (logRelRec l) Γ s K [domK] [Yi] ki kiK t →
               LogRel.cstr-arg-dispatch l (logRelRec l) Δ s K [domK]' (wk[domi] [ρ] ⊢Δ [Yi]) ki kiK (U.wk ρ t)
      wk-aux ki kiK t d with [Yi] ki kiK
      ... | LogRel.cstᵣ n [A] =
            let ρ[A]  = wk [ρ] ⊢Δ [A]
                ρ[A]' = PE.subst (λ x → _ ⊩⟨ _ ⟩ x ⦂ _) (T.wk-wkAll [ρ]) ρ[A]
            in irrelevanceTerm′ (T.wk-wkAll [ρ]) PE.refl ρ[A] ρ[A]' (wkTerm [ρ] ⊢Δ [A] d)
      ... | LogRel.monᵣ kidomK x =
          let kidomK' = wk-[]-cstr kidomK
              kidomK'' = PE.subst [ K ]-cstr (wk-wkAll [ρ]) kidomK'
          in
          PE.subst (λ t → Δ ⊩⟨ l ⟩ t ∷ cstr-dom-ctx Δ K ⦂ cstr-dom-sort K / [domK]')
                   (wk-[]-cstr-params' kidomK kidomK'' (wk-wkAll [ρ]))
                   (irrelevanceTerm′ (wk-wkAll [ρ]) PE.refl (wk [ρ] ⊢Δ [domK]) [domK]' (wkTerm [ρ] ⊢Δ [domK] d))
  wkTerm {ρ} [ρ] ⊢Δ (Boxᵣ′ F sF D ⊢F A≡A [F]) (boxₜ b d b≡b [b]) =
    boxₜ (U.wk ρ b) (wkRed:*:Term [ρ] ⊢Δ d) (≅ₜ-wk [ρ] ⊢Δ b≡b) (wkBox-prop [ρ] ⊢Δ (λ b d → wkTerm [ρ] ⊢Δ [F] d) [b])
  wkTerm {ρ} [ρ] ⊢Δ (Πᵣ′ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext) (Πₜ f d funcF f≡f [f] [f]₁) =
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

  wkEqTerm : ∀ {ρ Γ Δ A t u s l} ([ρ] : ρ ∷ Δ ⊆ Γ) (⊢Δ : ⊢ Δ)
            ([A] : Γ ⊩⟨ l ⟩ A ⦂ s)
          → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ⦂ s / [A]
          → Δ ⊩⟨ l ⟩ U.wk ρ t ≡ U.wk ρ u ∷ U.wk ρ A ⦂ s / wk [ρ] ⊢Δ [A]
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
  wkEqTerm {ρ} {Γ} {Δ} {s = s} {l} [ρ] ⊢Δ
          (cstrᵣ′ K KcodU a D ⊢a A≡A [domK] [a] [Yi])
          (cstrₜ₌ [k] [k'] d) =
    let cstrA = cstrᵣ′ K KcodU a D ⊢a A≡A [domK] [a] [Yi]
    in cstrₜ₌ (wkTerm [ρ] ⊢Δ cstrA [k]) (wkTerm [ρ] ⊢Δ cstrA [k'])
              (wk[Cstr].wkcstr [ρ] ⊢Δ wk-aux d)
    where
      [domK]' = PE.subst (λ x → Δ ⊩⟨ l ⟩ x ⦂ cstr-dom-sort K) (wk-wkAll [ρ]) (wk [ρ] ⊢Δ [domK])
      wk-aux : (ki : constructors) (kiK : [ K ]-cstr (cstr-cod ki)) (t t' : Term) →
               LogRel.cstr≡-arg-dispatch l (logRelRec l) Γ s K [domK] [Yi] ki kiK t t' →
               LogRel.cstr≡-arg-dispatch l (logRelRec l) Δ s K [domK]' (wk[domi] [ρ] ⊢Δ [Yi]) ki kiK (U.wk ρ t) (U.wk ρ t')
      wk-aux ki kiK t t' d with [Yi] ki kiK
      ... | LogRel.cstᵣ n [A] =
            let ρ[A]  = wk [ρ] ⊢Δ [A]
                ρ[A]' = PE.subst (λ x → _ ⊩⟨ _ ⟩ x ⦂ _) (T.wk-wkAll [ρ]) ρ[A]
            in irrelevanceEqTerm′ (T.wk-wkAll [ρ]) PE.refl ρ[A] ρ[A]' (wkEqTerm [ρ] ⊢Δ [A] d)
      ... | LogRel.monᵣ kidomK x =
          let kidomK' = wk-[]-cstr kidomK
              kidomK'' = PE.subst [ K ]-cstr (wk-wkAll [ρ]) kidomK'
          in
          PE.subst (λ t → Δ ⊩⟨ l ⟩ t ∷ cstr-dom-ctx Δ K ⦂ cstr-dom-sort K / [domK]')
                   (wk-[]-cstr-params' kidomK kidomK'' (wk-wkAll [ρ]))
                   (irrelevanceTerm′ (wk-wkAll [ρ]) PE.refl (wk [ρ] ⊢Δ [domK]) [domK]' (wkTerm [ρ] ⊢Δ [domK] d))

          -- (cstrₜ₌ k k' d d' k≡k' [k] [k'] [k≡k']) =
    -- let ρ[domK]  = wk [ρ] ⊢Δ [domK]
    --     ρ[domK]' = PE.subst (λ x → _ ⊩⟨ _ ⟩ x ⦂ _) (T.wk-wkAll [ρ]) ρ[domK]
    --     cstrA    = cstrᵣ′ K KcodU a D ⊢a A≡A [domK] [a] [Yi]
    -- in cstrₜ₌ (U.wk ρ k) (U.wk ρ k')
    --           (wkRed:*:Term [ρ] ⊢Δ d) (wkRed:*:Term [ρ] ⊢Δ d')
    --           (≅ₜ-wk [ρ] ⊢Δ k≡k')
    --           (wkTerm [ρ] ⊢Δ cstrA [k]) (wkTerm [ρ] ⊢Δ cstrA [k'])
    --           (wk[Cstr]-prop [ρ] ⊢Δ
    --                          (λ ki kiK t t' x →
    --                             let Yi   = [Yi] ki kiK
    --                                 ρYi  = wk [ρ] ⊢Δ Yi
    --                                 ρYi' = PE.subst (λ x → _ ⊩⟨ _ ⟩ x ⦂ _) (T.wk-wkAll [ρ]) ρYi
    --                             in irrelevanceEqTerm′ (T.wk-wkAll [ρ]) PE.refl ρYi ρYi' (wkEqTerm [ρ] ⊢Δ Yi x))
    --                          [k≡k'])
  wkEqTerm {ρ} [ρ] ⊢Δ (Boxᵣ′ F sF D ⊢F A≡A [F]) (boxₜ₌ b b' d d' b≡b' [b] [b'] [b≡b']) =
    let BoxA = Boxᵣ′ F sF D ⊢F A≡A [F]
    in boxₜ₌ (U.wk ρ b) (U.wk ρ b')
             (wkRed:*:Term [ρ] ⊢Δ d)
             (wkRed:*:Term [ρ] ⊢Δ d')
             (≅ₜ-wk [ρ] ⊢Δ b≡b')
             (wkTerm [ρ] ⊢Δ BoxA [b])
             (wkTerm [ρ] ⊢Δ BoxA [b'])
             (wk[Box]-prop [ρ] ⊢Δ (λ _ _ d → wkEqTerm [ρ] ⊢Δ [F] d) [b≡b'])
  wkEqTerm {ρ} [ρ] ⊢Δ (Πᵣ′ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
                      (Πₜ₌ f g d d′ funcF funcG f≡g [t] [u] [f≡g]) =
    let [A] = Πᵣ′ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext
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
