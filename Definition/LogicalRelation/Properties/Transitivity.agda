{-# OPTIONS --without-K  #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Properties.Transitivity {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties.Conversion

open import Tools.Product
import Tools.PropositionalEquality as PE

transEqTermNe : ∀ {Γ n n′ n″ A s}
              → Γ ⊩neNf n  ≡ n′  ∷ A ⦂ s
              → Γ ⊩neNf n′ ≡ n″ ∷ A ⦂ s
              → Γ ⊩neNf n  ≡ n″ ∷ A ⦂ s
transEqTermNe (neNfₜ₌ neK neM k≡m) (neNfₜ₌ neK₁ neM₁ k≡m₁) =
  neNfₜ₌ neK neM₁ (~-trans k≡m k≡m₁)

mutual
  transEqTermℕ : ∀ {Γ n n′ n″}
               → Γ ⊩ℕ n  ≡ n′  ∷ℕ
               → Γ ⊩ℕ n′ ≡ n″ ∷ℕ
               → Γ ⊩ℕ n  ≡ n″ ∷ℕ
  transEqTermℕ (ℕₜ₌ k k′ d d′ t≡u prop)
               (ℕₜ₌ k₁ k″ d₁ d″ t≡u₁ prop₁) =
    let k₁Whnf = naturalWhnf (proj₁ (split prop₁))
        k′Whnf = naturalWhnf (proj₂ (split prop))
        k₁≡k′ = whrDet*Term (redₜ d₁ , k₁Whnf) (redₜ d′ , k′Whnf)
        prop′ = PE.subst (λ x → [Natural]-prop _ x _) k₁≡k′ prop₁
    in  ℕₜ₌ k k″ d d″ (≅ₜ-trans t≡u (PE.subst (λ x → _ ⊢ x ≅ _ ∷ _ ⦂ _) k₁≡k′ t≡u₁))
            (transNatural-prop prop prop′)

  transNatural-prop : ∀ {Γ k k′ k″}
                    → [Natural]-prop Γ k k′
                    → [Natural]-prop Γ k′ k″
                    → [Natural]-prop Γ k k″
  transNatural-prop (sucᵣ x) (sucᵣ x₁) = sucᵣ (transEqTermℕ x x₁)
  transNatural-prop (sucᵣ x) (ne (neNfₜ₌ () neM k≡m))
  transNatural-prop zeroᵣ prop₁ = prop₁
  transNatural-prop prop zeroᵣ = prop
  transNatural-prop (ne (neNfₜ₌ neK () k≡m)) (sucᵣ x₃)
  transNatural-prop (ne [k≡k′]) (ne [k′≡k″]) =
    ne (transEqTermNe [k≡k′] [k′≡k″])

-- Empty
transEmpty-prop : ∀ {Γ k k′ k″}
  → [Empty]-prop Γ k k′
  → [Empty]-prop Γ k′ k″
  → [Empty]-prop Γ k k″
transEmpty-prop (ne [k≡k′]) (ne [k′≡k″]) =
  ne (transEqTermNe [k≡k′] [k′≡k″])

transEqTermEmpty : ∀ {Γ n n′ n″}
  → Γ ⊩Empty n  ≡ n′  ∷Empty
  → Γ ⊩Empty n′ ≡ n″ ∷Empty
  → Γ ⊩Empty n  ≡ n″ ∷Empty
transEqTermEmpty (Emptyₜ₌ k k′ d d′ t≡u prop)
             (Emptyₜ₌ k₁ k″ d₁ d″ t≡u₁ prop₁) =
  let k₁Whnf = ne (proj₁ (esplit prop₁))
      k′Whnf = ne (proj₂ (esplit prop))
      k₁≡k′ = whrDet*Term (redₜ d₁ , k₁Whnf) (redₜ d′ , k′Whnf)
      prop′ = PE.subst (λ x → [Empty]-prop _ x _) k₁≡k′ prop₁
    in  Emptyₜ₌ k k″ d d″ (≅ₜ-trans t≡u (PE.subst (λ x → _ ⊢ x ≅ _ ∷ _ ⦂ _) k₁≡k′ t≡u₁))
      (transEmpty-prop prop prop′)


trans[Cstr]-prop : ∀ {K Γ Pi Pi' Pi'' t t' t'' a s}
                     (Pi-trans : ∀ ki kiK kiK' kiK'' t t' t'' → Pi ki kiK t t' → Pi' ki kiK' t' t'' → Pi'' ki kiK'' t t'')
                     (d : [Cstr]-prop K Γ Pi a s t t')
                     (d' : [Cstr]-prop K Γ Pi' a s t' t'')
                   → [Cstr]-prop K Γ Pi'' a s t t''
trans[Cstr]-prop Pi-trans (cstrᵣ kK x) (cstrᵣ kK₁ x₁) = cstrᵣ kK (Pi-trans _ kK kK₁ kK _ _ _ x x₁)
trans[Cstr]-prop Pi-trans (cstrᵣ kK x) (ne (neNfₜ₌ (∘ₙ ()) neM k≡m))
trans[Cstr]-prop Pi-trans (ne (neNfₜ₌ _ (∘ₙ ()) k≡m)) (cstrᵣ kK x₁)
trans[Cstr]-prop Pi-trans (ne x) (ne x₁) = ne (transEqTermNe x x₁)

trans[Box]-prop : ∀ {P P' P'' Γ sF sF' F F' b b' b''}
                    (P-trans : ∀ b b' b'' → P b b' → P' b' b'' → P'' b b'')
                    (d : [Box]-prop P Γ sF F b b')
                    (d' : [Box]-prop P' Γ sF' F' b' b'')
                    (sF≡sF' : sF PE.≡ sF')
                    (F≡F' : F PE.≡ F')
                  → [Box]-prop P'' Γ sF F b b''
trans[Box]-prop P-trans (boxᵣ x) (boxᵣ x₁) PE.refl F≡F' = boxᵣ (P-trans _ _ _ x x₁)
trans[Box]-prop P-trans (ne x) (ne x₁) PE.refl PE.refl = ne (transEqTermNe x x₁)

mutual
  -- Helper function for transitivity of type equality using shape views.
  {-# TERMINATING #-}
  transEqT : ∀ {Γ A B C s l l′ l″}
             {[A] : Γ ⊩⟨ l ⟩ A ⦂ s} {[B] : Γ ⊩⟨ l′ ⟩ B ⦂ s} {[C] : Γ ⊩⟨ l″ ⟩ C ⦂ s}
           → ShapeView₃ Γ l l′ l″ A B C s s s [A] [B] [C]
           → Γ ⊩⟨ l ⟩  A ≡ B ⦂ s / [A]
           → Γ ⊩⟨ l′ ⟩ B ≡ C ⦂ s / [B]
           → Γ ⊩⟨ l ⟩  A ≡ C ⦂ s / [A]
  transEqT (ℕᵥ D D′ D″) A≡B B≡C = B≡C
  transEqT (Emptyᵥ D D′ D″) A≡B B≡C = B≡C
  transEqT (ne (ne K [ ⊢A , ⊢B , D ] neK K≡K) (ne K₁ D₁ neK₁ _)
               (ne K₂ D₂ neK₂ _))
           (ne₌ M D′ neM K≡M) (ne₌ M₁ D″ neM₁ K≡M₁)
           rewrite whrDet* (red D₁ , ne neK₁) (red D′ , ne neM)
                 | whrDet* (red D₂ , ne neK₂) (red D″ , ne neM₁) =
    ne₌ M₁ D″ neM₁
        (~-trans K≡M K≡M₁)
  transEqT {Γ}  {s = s} {l = l} {l′ = l′} {l″ = l″}
           (Πᵥ (Πᵣ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
               (Πᵣ sF₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
               (Πᵣ sF₂ F₂ G₂ D₂ ⊢F₂ ⊢G₂ A≡A₂ [F]₂ [G]₂ G-ext₂))
           (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
           (Π₌ F″ G″ D″ A≡B₁ [F≡F′]₁ [G≡G′]₁) =
    let ΠF₁G₁≡ΠF′G′    = whrDet* (red D₁ , Πₙ) (D′  , Πₙ)
        F₁≡F′ , sF₁≡sF′ , G₁≡G′ = Π-PE-injectivity ΠF₁G₁≡ΠF′G′
        F₂≡F″ , sF₂≡sF′ , G₂≡G″  = Π-PE-injectivity (whrDet* (red D₂ , Πₙ) (D″ , Πₙ))
        substLift {Δ} {l} {a} {s} ρ x = Δ ⊩⟨ l ⟩ wk (lift ρ) x [ a ] ⦂ s
        [F′] : ∀ {ρ Δ} [ρ] ⊢Δ → Δ ⊩⟨ l′ ⟩ wk ρ F′ ⦂ sF₁
        [F′] {ρ} [ρ] ⊢Δ = PE.subst (λ x → _ ⊩⟨ _ ⟩ wk ρ x ⦂ _) F₁≡F′ ([F]₁ [ρ] ⊢Δ)
        [F″] : ∀ {ρ} {Δ} [ρ] ⊢Δ → Δ ⊩⟨ l″ ⟩ wk ρ F″ ⦂ sF₂
        [F″] {ρ} [ρ] ⊢Δ = PE.subst (λ x → _ ⊩⟨ _ ⟩ wk ρ x ⦂ _) F₂≡F″ ([F]₂ [ρ] ⊢Δ)
        [F′≡F″] : ∀ {ρ} {Δ} [ρ] ⊢Δ → Δ ⊩⟨ l′ ⟩ wk ρ F′ ≡ wk ρ F″ ⦂ sF₁ / [F′] [ρ] ⊢Δ
        [F′≡F″] {ρ} [ρ] ⊢Δ = irrelevanceEq′ (PE.cong (wk ρ) F₁≡F′) PE.refl
                                      ([F]₁ [ρ] ⊢Δ) ([F′] [ρ] ⊢Δ) ([F≡F′]₁ [ρ] ⊢Δ)
        [G′] : ∀ {ρ Δ a} [ρ] ⊢Δ
             → Δ ⊩⟨ l′ ⟩ a ∷ wk ρ F′ ⦂ sF₁ / [F′] [ρ] ⊢Δ
             → Δ ⊩⟨ l′ ⟩ wk (lift ρ) G′ [ a ] ⦂ s
        [G′] {ρ} [ρ] ⊢Δ [a] =
          let [a′] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F₁≡F′)) PE.refl
                                      ([F′] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [a]
          in  PE.subst (substLift ρ) G₁≡G′ ([G]₁ [ρ] ⊢Δ [a′])
        [G″] : ∀ {ρ Δ a} [ρ] ⊢Δ
             → Δ ⊩⟨ l″ ⟩ a ∷ wk ρ F″ ⦂ sF₂ / [F″] [ρ] ⊢Δ
             → Δ ⊩⟨ l″ ⟩ wk (lift ρ) G″ [ a ] ⦂ s
        [G″] {ρ} [ρ] ⊢Δ [a] =
          let [a″] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F₂≡F″)) PE.refl
                                      ([F″] [ρ] ⊢Δ) ([F]₂ [ρ] ⊢Δ) [a]
          in  PE.subst (substLift ρ) G₂≡G″ ([G]₂ [ρ] ⊢Δ [a″])
        [G′≡G″] : ∀ {ρ Δ a} [ρ] ⊢Δ
                  ([a] : Δ ⊩⟨ l′ ⟩ a ∷ wk ρ F′ ⦂ sF₁ / [F′] [ρ] ⊢Δ)
                → Δ ⊩⟨ l′ ⟩ wk (lift ρ) G′  [ a ]
                          ≡ wk (lift ρ) G″ [ a ] ⦂ s / [G′] [ρ] ⊢Δ [a]
        [G′≡G″] {ρ} [ρ] ⊢Δ [a′] =
          let [a]₁ = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F₁≡F′)) PE.refl
                                      ([F′] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [a′]
          in  irrelevanceEq′ (PE.cong (λ x → wk (lift ρ) x [ _ ]) G₁≡G′) PE.refl
                             ([G]₁ [ρ] ⊢Δ [a]₁) ([G′] [ρ] ⊢Δ [a′])
                             ([G≡G′]₁ [ρ] ⊢Δ [a]₁)
                             -- Γ ⊢ .C ⇒* Π F″ ⦂ sF ▹ G″ ⦂ s
    in  Π₌ F″ G″ (PE.subst (λ sx → Γ ⊢ _ ⇒* Π F″ ⦂ sx ▹ G″ ⦂ s) sF₁≡sF′ D″) (PE.subst _ sF₁≡sF′ (≅-trans A≡B (PE.subst (λ x → Γ ⊢ x ≅ Π F″ ⦂ sF₁ ▹ G″ ⦂ s) ΠF₁G₁≡ΠF′G′ A≡B₁)))
           (λ ρ ⊢Δ → transEq′ PE.refl PE.refl (PE.sym sF₁≡sF′) (PE.sym (PE.trans sF₂≡sF′ sF₁≡sF′))
           ([F] ρ ⊢Δ) ([F′] ρ ⊢Δ) ([F″] ρ ⊢Δ)
           ([F≡F′] ρ ⊢Δ) ([F′≡F″] ρ ⊢Δ))
           (λ ρ ⊢Δ [a] →
              let [a′] = convTerm₁′ (PE.sym sF₁≡sF′) ([F] ρ ⊢Δ) ([F′] ρ ⊢Δ) ([F≡F′] ρ ⊢Δ) [a]
                  [a″] = convTerm₁′ (PE.sym sF₂≡sF′) ([F′] ρ ⊢Δ) ([F″] ρ ⊢Δ) ([F′≡F″] ρ ⊢Δ) [a′]
              in  transEq ([G] ρ ⊢Δ [a]) ([G′] ρ ⊢Δ [a′]) ([G″] ρ ⊢Δ [a″])
                          ([G≡G′] ρ ⊢Δ [a]) ([G′≡G″] ρ ⊢Δ [a′]))
  transEqT (Uᵥ ⊢Γ ⊢Γ₁ _) A≡B B≡C rewrite Univ-PE-injectivity B≡C = A≡B
  transEqT {Γ = Γ} {C = C} {s = s}
           (cstrᵥ (cstrᵣ K KcodU a D ⊢a A≡A [domK] [a] [Yi])
                  (cstrᵣ K₁ KcodU₁ a₁ D₁ ⊢a₁ A≡A₁ [domK]₁ [a]₁ [Yi]₁)
                  (cstrᵣ K₂ KcodU₂ a₂ D₂ ⊢a₂ A≡A₂ [domK]₂ [a]₂ [Yi]₂))
           (cstr₌ a₀₁ D₀₁ A≡B₀₁ [a≡a']₀₁)
           (cstr₌ a₁₂ D₁₂ A≡B₁₂ [a≡a']₁₂) =
    let K₁a₁≡Ka₀₁    = whrDet* (red D₁ , cstrₙ) (red D₀₁  , cstrₙ)
        K₁≡K         = cstr-app-PE-injectivity K₁a₁≡Ka₀₁
        a₁≡a₀₁       = cstr-app-PE-arg-injectivity K₁a₁≡Ka₀₁
        -- K₂a₂≡K₁a₁₂   = whrDet* (red D₂ , cstrₙ) (red D₁₂  , cstrₙ)
    in cstr₌ a₁₂ (PE.subst (λ k → Γ ⊢ C :⇒*: cstr k ∘ a₁₂ ⦂ s) K₁≡K D₁₂)
                 (≅ₜ-trans A≡B₀₁ (PE.subst₂ (λ a' k → Γ ⊢ a' ≅ a₁₂ ∷ wkAll Γ (cstr-dom k) ⦂ cstr-dom-sort k) a₁≡a₀₁ K₁≡K A≡B₁₂))
                 (transEqTerm [domK] [a≡a']₀₁
                              (PE.subst (λ a₃ → Γ ⊩⟨ _ ⟩ a₃ ≡ a₁₂ ∷ _ ⦂ _ / [domK])
                                        a₁≡a₀₁
                                        (irrelevanceEqTerm′ (PE.cong (λ k → wkAll Γ (cstr-dom k)) K₁≡K)
                                                            (PE.cong cstr-dom-sort K₁≡K)
                                                            [domK]₁ [domK] [a≡a']₁₂)))
  transEqT {Γ = Γ} {C = C} {s = s}
         (Boxᵥ (Boxᵣ Fx sFx Dx ⊢Fx A≡Ax [Fx])
               (Boxᵣ Fy sFy Dy ⊢Fy A≡Ay [Fy])
               (Boxᵣ Fz sFz Dz ⊢Fz A≡Az [Fz]))
         (Box₌ Fxy Dxy A≡Bxy [F≡Fxy])
         (Box₌ Fyz Dyz A≡Byz [F≡Fyz]) =
    let BFy≡BFxy = whrDet* (red Dy , Boxₙ) (red Dxy , Boxₙ)
        sFy≡sFx  = Box-sort-inj BFy≡BFxy
        Fy≡Fxy   = Box-inj BFy≡BFxy
        BFz≡BFyz = whrDet* (red Dz , Boxₙ) (red Dyz , Boxₙ)
        sFz≡sFy  = Box-sort-inj BFz≡BFyz
        Fz≡Fyz   = Box-inj BFz≡BFyz
    in Box₌ Fyz
            (PE.subst (λ s → Γ ⊢ C :⇒*: Box s Fyz ⦂ 𝕥y) sFy≡sFx Dyz)
            (≅-trans A≡Bxy (PE.subst₂ (λ s F → Γ ⊢ Box s F ≅ Box s Fyz ⦂ 𝕥y) sFy≡sFx Fy≡Fxy A≡Byz))
            (PE.subst (λ F → Γ ⊩⟨ _ ⟩ Fx ≡ F ⦂ _ / [Fx])
                      Fz≡Fyz
                      (transEq′ Fy≡Fxy Fz≡Fyz
                                (PE.cong ‼ (PE.sym sFy≡sFx))
                                (PE.cong ‼ (PE.sym (PE.trans sFz≡sFy sFy≡sFx)))
                                [Fx] [Fy] [Fz] [F≡Fxy] [F≡Fyz]))
            -- (transEq′ Fy≡Fxy {!!} {!!} {!!} [Fx] [Fy] {![Fz]!} [F≡Fxy] [F≡Fyz])
  transEqT (emb⁰¹¹ AB) A≡B B≡C = transEqT AB A≡B B≡C
  transEqT (emb¹⁰¹ AB) A≡B B≡C = transEqT AB A≡B B≡C
  transEqT (emb¹¹⁰ AB) A≡B B≡C = transEqT AB A≡B B≡C

  -- Transitivty of type equality.
  transEq : ∀ {Γ A B C s l l′ l″}
            ([A] : Γ ⊩⟨ l ⟩ A ⦂ s) ([B] : Γ ⊩⟨ l′ ⟩ B ⦂ s) ([C] : Γ ⊩⟨ l″ ⟩ C ⦂ s)
          → Γ ⊩⟨ l ⟩  A ≡ B ⦂ s / [A]
          → Γ ⊩⟨ l′ ⟩ B ≡ C ⦂ s / [B]
          → Γ ⊩⟨ l ⟩  A ≡ C ⦂ s / [A]
  transEq [A] [B] [C] A≡B B≡C =
    transEqT (combine (goodCases [A] [B] A≡B) (goodCases [B] [C] B≡C)) A≡B B≡C

  -- Transitivity of type equality with some propositonally equal types.
  transEq′ : ∀ {Γ A B B′ C C′ s s' s''  l l′ l″} → B PE.≡ B′ → C PE.≡ C′ → s PE.≡ s' → s PE.≡ s''
           → ([A] : Γ ⊩⟨ l ⟩ A ⦂ s) ([B] : Γ ⊩⟨ l′ ⟩ B ⦂ s') ([C] : Γ ⊩⟨ l″ ⟩ C ⦂ s'')
           → Γ ⊩⟨ l ⟩  A ≡ B′ ⦂ s / [A]
           → Γ ⊩⟨ l′ ⟩ B ≡ C′ ⦂ s' / [B]
           → Γ ⊩⟨ l ⟩  A ≡ C  ⦂ s / [A]
  transEq′ PE.refl PE.refl PE.refl PE.refl [A] [B] [C] A≡B B≡C = transEq [A] [B] [C] A≡B B≡C




  -- Transitivty of term equality.
  transEqTerm : ∀ {l Γ A t u v s}
                ([A] : Γ ⊩⟨ l ⟩ A ⦂ s)
              → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ⦂ s / [A]
              → Γ ⊩⟨ l ⟩ u ≡ v ∷ A ⦂ s / [A]
              → Γ ⊩⟨ l ⟩ t ≡ v ∷ A ⦂ s / [A]
  transEqTerm (Uᵣ′ sU .⁰ 0<1 ⊢Γ)
              (Uₜ₌ A B d d′ typeA typeB t≡u [t] [u] [t≡u])
              (Uₜ₌ A₁ B₁ d₁ d₁′ typeA₁ typeB₁ t≡u₁ [t]₁ [u]₁ [t≡u]₁)
              rewrite whrDet*Term (redₜ d′ , typeWhnf typeB) (redₜ d₁ , typeWhnf typeA₁) =
    Uₜ₌ A B₁ d d₁′ typeA typeB₁ (≅ₜ-trans t≡u t≡u₁) [t] [u]₁
        (transEq [t] [u] [u]₁ [t≡u] (irrelevanceEq [t]₁ [u] [t≡u]₁))
  transEqTerm (ℕᵣ D) [t≡u] [u≡v] = transEqTermℕ [t≡u] [u≡v]
  transEqTerm (Emptyᵣ D) [t≡u] [u≡v] = transEqTermEmpty [t≡u] [u≡v]
  transEqTerm (ne′ K D neK K≡K) (neₜ₌ k m d d′ (neNfₜ₌ neK₁ neM k≡m))
                                (neₜ₌ k₁ m₁ d₁ d″ (neNfₜ₌ neK₂ neM₁ k≡m₁)) =
    let k₁≡m = whrDet*Term (redₜ d₁ , ne neK₂) (redₜ d′ , ne neM)
    in  neₜ₌ k m₁ d d″
            (neNfₜ₌ neK₁ neM₁
                    (~-trans k≡m (PE.subst (λ x → _ ⊢ x ~ _ ∷ _ ⦂ _) k₁≡m k≡m₁)))
  transEqTerm (Πᵣ′ sF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
              (Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g])
              (Πₜ₌ f₁ g₁ d₁ d₁′ funcF₁ funcG₁ f≡g₁ [f]₁ [g]₁ [f≡g]₁)
              rewrite whrDet*Term (redₜ d′ , functionWhnf funcG)
                              (redₜ d₁ , functionWhnf funcF₁) =
    Πₜ₌ f g₁ d d₁′ funcF funcG₁ (≅ₜ-trans f≡g f≡g₁) [f] [g]₁
        (λ ρ ⊢Δ [a] → transEqTerm ([G] ρ ⊢Δ [a])
                                  ([f≡g] ρ ⊢Δ [a])
                                  ([f≡g]₁ ρ ⊢Δ [a]))
  transEqTerm (cstrᵣ′ K KcodU a D ⊢a A≡A [domK] [a] [Yi])
              (cstrₜ₌ k k' d d' k≡k' [k] [k'] [k≡k'])
              (cstrₜ₌ k₁ k₁' d₁ d₁' k₁≡k₁' [k₁] [k₁'] [k₁≡k₁']) =
    let k₁≡k' = PE.sym (whrDet*Term (redₜ d' , [Cstr]-prop-right-Whnf [k≡k']) (redₜ d₁ , [Cstr]-prop-left-Whnf [k₁≡k₁']))
    in cstrₜ₌ k k₁' d d₁'
            (≅ₜ-trans k≡k' ( PE.subst (λ k → _ ⊢ k ≅ k₁' ∷ cstr K ∘ a ⦂ _) k₁≡k' k₁≡k₁' )) [k] [k₁']
            (trans[Cstr]-prop (λ ki kiK kiK' kiK'' t t' t'' x x₁ → transEqTerm ([Yi] ki kiK'')
                                                                                (irrelevanceEqTerm ([Yi] ki kiK) ([Yi] ki kiK'') x)
                                                                                (irrelevanceEqTerm ([Yi] ki kiK') ([Yi] ki kiK'') x₁))
                              [k≡k']
                              (PE.subst (λ k → [Cstr]-prop K _ _ a _ k k₁') k₁≡k' [k₁≡k₁'] ))
  transEqTerm (Boxᵣ′ F sF D ⊢F A≡A [F])
              (boxₜ₌ b b' d d' b≡b' [b] [b'] [b≡b'])
              (boxₜ₌ b₁ b₁' d₁ d₁' b₁≡b₁' [b₁] [b₁'] [b₁≡b₁']) with [Box]-prop-Whnf [b≡b'] with [Box]-prop-Whnf [b₁≡b₁']
  ... | _ , whnb' | whnb₁ , _ =
    let b₁≡b' = whrDet*Term (redₜ d₁ , whnb₁) (redₜ d' , whnb')
    in boxₜ₌ b b₁' d d₁'
             (≅ₜ-trans b≡b' (PE.subst (λ b → _ ⊢ b ≅ b₁' ∷ Box sF F ⦂ 𝕥y) b₁≡b' b₁≡b₁'))
             [b] [b₁']
             (trans[Box]-prop (λ _ _ _ d d' → transEqTerm [F] d d')
                              [b≡b']
                              (PE.subst (λ b → [Box]-prop _ _ F sF b b₁') b₁≡b' [b₁≡b₁'])
                              PE.refl PE.refl)
  transEqTerm (emb 0<1 x) t≡u u≡v = transEqTerm x t≡u u≡v
