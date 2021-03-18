{-# OPTIONS --safe #-}

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

mutual
  -- Helper function for transitivity of type equality using shape views.
  transEqT : ∀ {Γ A B C r l l′ l″}
             {[A] : Γ ⊩⟨ l ⟩ A ^ r} {[B] : Γ ⊩⟨ l′ ⟩ B ^ r} {[C] : Γ ⊩⟨ l″ ⟩ C ^ r}
           → ShapeView₃ Γ l l′ l″ A B C r r r [A] [B] [C]
           → Γ ⊩⟨ l ⟩  A ≡ B ^ r / [A]
           → Γ ⊩⟨ l′ ⟩ B ≡ C ^ r / [B]
           → Γ ⊩⟨ l ⟩  A ≡ C ^ r / [A]
  transEqT (Uᵥ UA UB UC) A≡B B≡C =
    let
      U≡U : Univ (LogRel._⊩¹U_^_.r UA) (LogRel._⊩¹U_^_.l′ UA) PE.≡ Univ (LogRel._⊩¹U_^_.r UB) (LogRel._⊩¹U_^_.l′ UB)
      U≡U = whrDet* (A≡B , Uₙ) ((_⊢_:⇒*:_^_.D (LogRel._⊩¹U_^_.d UB)) , Uₙ)
      r≡r , l≡l = Univ-PE-injectivity U≡U
    in
    PE.subst₂ (λ X Y → _ ⊢ _ ⇒* Univ X Y ^ [ ! , _ ]) (PE.sym r≡r) (PE.sym l≡l) B≡C
  transEqT (ℕᵥ D D′ D″) A≡B B≡C = B≡C
  transEqT (Emptyᵥ D D′ D″) A≡B B≡C = B≡C
  transEqT (ne (ne K [[ ⊢A , ⊢B , D ]] neK K≡K) (ne K₁ D₁ neK₁ _)
               (ne K₂ D₂ neK₂ _))
           (ne₌ M D′ neM K≡M) (ne₌ M₁ D″ neM₁ K≡M₁)
           rewrite whrDet* (red D₁ , ne neK₁) (red D′ , ne neM)
                 | whrDet* (red D₂ , ne neK₂) (red D″ , ne neM₁) =
    ne₌ M₁ D″ neM₁
        (~-trans K≡M K≡M₁)
  transEqT {Γ}  {r = r} {l = l} {l′ = l′} {l″ = l″}
           (Πᵥ (Πᵣ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
               (Πᵣ rF₁ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
               (Πᵣ rF₂ F₂ G₂ D₂ ⊢F₂ ⊢G₂ A≡A₂ [F]₂ [G]₂ G-ext₂))
           (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
           (Π₌ F″ G″ D″ A≡B₁ [F≡F′]₁ [G≡G′]₁) =
    let ΠF₁G₁≡ΠF′G′    = whrDet* (red D₁ , Πₙ) (D′  , Πₙ)
        F₁≡F′ , rF₁≡rF′ , G₁≡G′ = Π-PE-injectivity ΠF₁G₁≡ΠF′G′
        F₂≡F″ , rF₂≡rF′ , G₂≡G″  = Π-PE-injectivity (whrDet* (red D₂ , Πₙ) (D″ , Πₙ))
        substLift {Δ} {l} {a} {r} ρ x = Δ ⊩⟨ l ⟩ wk (lift ρ) x [ a ] ^ r
        lr = TypeInfo.l r
        [F′] : ∀ {ρ Δ} [ρ] ⊢Δ → Δ ⊩⟨ l′ ⟩ wk ρ F′ ^ [ rF₁ , lr ]
        [F′] {ρ} [ρ] ⊢Δ = PE.subst (λ x → _ ⊩⟨ _ ⟩ wk ρ x ^ _) F₁≡F′ ([F]₁ [ρ] ⊢Δ)
        [F″] : ∀ {ρ} {Δ} [ρ] ⊢Δ → Δ ⊩⟨ l″ ⟩ wk ρ F″ ^ [ rF₂ , lr ]
        [F″] {ρ} [ρ] ⊢Δ = PE.subst (λ x → _ ⊩⟨ _ ⟩ wk ρ x ^ _) F₂≡F″ ([F]₂ [ρ] ⊢Δ)
        [F′≡F″] : ∀ {ρ} {Δ} [ρ] ⊢Δ → Δ ⊩⟨ l′ ⟩ wk ρ F′ ≡ wk ρ F″ ^ [ rF₁ , lr ] / [F′] [ρ] ⊢Δ
        [F′≡F″] {ρ} [ρ] ⊢Δ = irrelevanceEq′ (PE.cong (wk ρ) F₁≡F′) PE.refl
                                      ([F]₁ [ρ] ⊢Δ) ([F′] [ρ] ⊢Δ) ([F≡F′]₁ [ρ] ⊢Δ)
        [G′] : ∀ {ρ Δ a} [ρ] ⊢Δ
             → Δ ⊩⟨ l′ ⟩ a ∷ wk ρ F′ ^ [ rF₁ , lr ] / [F′] [ρ] ⊢Δ
             → Δ ⊩⟨ l′ ⟩ wk (lift ρ) G′ [ a ] ^ r
        [G′] {ρ} [ρ] ⊢Δ [a] =
          let [a′] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F₁≡F′)) PE.refl
                                      ([F′] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [a]
          in  PE.subst (substLift ρ) G₁≡G′ ([G]₁ [ρ] ⊢Δ [a′])
        [G″] : ∀ {ρ Δ a} [ρ] ⊢Δ
             → Δ ⊩⟨ l″ ⟩ a ∷ wk ρ F″ ^ [ rF₂ , lr ] / [F″] [ρ] ⊢Δ
             → Δ ⊩⟨ l″ ⟩ wk (lift ρ) G″ [ a ] ^ r
        [G″] {ρ} [ρ] ⊢Δ [a] =
          let [a″] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F₂≡F″)) PE.refl
                                      ([F″] [ρ] ⊢Δ) ([F]₂ [ρ] ⊢Δ) [a]
          in  PE.subst (substLift ρ) G₂≡G″ ([G]₂ [ρ] ⊢Δ [a″])
        [G′≡G″] : ∀ {ρ Δ a} [ρ] ⊢Δ
                  ([a] : Δ ⊩⟨ l′ ⟩ a ∷ wk ρ F′ ^ [ rF₁ , lr ] / [F′] [ρ] ⊢Δ)
                → Δ ⊩⟨ l′ ⟩ wk (lift ρ) G′  [ a ]
                          ≡ wk (lift ρ) G″ [ a ] ^ r / [G′] [ρ] ⊢Δ [a]
        [G′≡G″] {ρ} [ρ] ⊢Δ [a′] =
          let [a]₁ = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F₁≡F′)) PE.refl
                                      ([F′] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [a′]
          in  irrelevanceEq′ (PE.cong (λ x → wk (lift ρ) x [ _ ]) G₁≡G′) PE.refl
                             ([G]₁ [ρ] ⊢Δ [a]₁) ([G′] [ρ] ⊢Δ [a′])
                             ([G≡G′]₁ [ρ] ⊢Δ [a]₁)
                             -- Γ ⊢ .C ⇒* Π F″ ^ rF ▹ G″ ^ r
    in  Π₌ F″ G″ (PE.subst (λ rx → Γ ⊢ _ ⇒* Π F″ ^ rx ▹ G″ ^ r) rF₁≡rF′ D″) (PE.subst _ rF₁≡rF′ (≅-trans A≡B (PE.subst (λ x → Γ ⊢ x ≅ Π F″ ^ rF₁ ▹ G″ ^ r) ΠF₁G₁≡ΠF′G′ A≡B₁)))
           (λ ρ ⊢Δ → transEq′ PE.refl PE.refl (PE.subst (λ X → [ X , lr ] PE.≡ [ rF₁ , lr ]) rF₁≡rF′ PE.refl) (PE.subst (λ X → [ X , lr ] PE.≡ [ rF₂ , lr ]) (PE.trans rF₂≡rF′ rF₁≡rF′) PE.refl)
           ([F] ρ ⊢Δ) ([F′] ρ ⊢Δ) ([F″] ρ ⊢Δ)
           ([F≡F′] ρ ⊢Δ) ([F′≡F″] ρ ⊢Δ))
           (λ ρ ⊢Δ [a] →
              let [a′] = convTerm₁′ (PE.sym rF₁≡rF′) ([F] ρ ⊢Δ) ([F′] ρ ⊢Δ) ([F≡F′] ρ ⊢Δ) [a]
                  [a″] = convTerm₁′ (PE.sym rF₂≡rF′) ([F′] ρ ⊢Δ) ([F″] ρ ⊢Δ) ([F′≡F″] ρ ⊢Δ) [a′]
              in  transEq ([G] ρ ⊢Δ [a]) ([G′] ρ ⊢Δ [a′]) ([G″] ρ ⊢Δ [a″])
                          ([G≡G′] ρ ⊢Δ [a]) ([G′≡G″] ρ ⊢Δ [a′]))
  transEqT {Γ}  {r = r} {l = l} {l′ = l′} {l″ = l″}
           (∃ᵥ (∃ᵣ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
               (∃ᵣ F₁ G₁ D₁ ⊢F₁ ⊢G₁ A≡A₁ [F]₁ [G]₁ G-ext₁)
               (∃ᵣ F₂ G₂ D₂ ⊢F₂ ⊢G₂ A≡A₂ [F]₂ [G]₂ G-ext₂))
           (∃₌ F′ G′ D′ A≡B [F≡F′] [G≡G′])
           (∃₌ F″ G″ D″ A≡B₁ [F≡F′]₁ [G≡G′]₁) =
    let ∃F₁G₁≡∃F′G′    = whrDet* (red D₁ , ∃ₙ) (D′  , ∃ₙ)
        F₁≡F′ ,  G₁≡G′ = ∃-PE-injectivity ∃F₁G₁≡∃F′G′
        F₂≡F″ ,  G₂≡G″  = ∃-PE-injectivity (whrDet* (red D₂ , ∃ₙ) (D″ , ∃ₙ))
        substLift {Δ} {l} {a} {r} ρ x = Δ ⊩⟨ l ⟩ wk (lift ρ) x [ a ] ^ r
        lr = TypeInfo.l r
        [F′] : ∀ {ρ Δ} [ρ] ⊢Δ → Δ ⊩⟨ l′ ⟩ wk ρ F′ ^ [ % , lr ]
        [F′] {ρ} [ρ] ⊢Δ = PE.subst (λ x → _ ⊩⟨ _ ⟩ wk ρ x ^ _) F₁≡F′ ([F]₁ [ρ] ⊢Δ)
        [F″] : ∀ {ρ} {Δ} [ρ] ⊢Δ → Δ ⊩⟨ l″ ⟩ wk ρ F″ ^ [ % , lr ]
        [F″] {ρ} [ρ] ⊢Δ = PE.subst (λ x → _ ⊩⟨ _ ⟩ wk ρ x ^ _) F₂≡F″ ([F]₂ [ρ] ⊢Δ)
        [F′≡F″] : ∀ {ρ} {Δ} [ρ] ⊢Δ → Δ ⊩⟨ l′ ⟩ wk ρ F′ ≡ wk ρ F″ ^ [ % , lr ] / [F′] [ρ] ⊢Δ
        [F′≡F″] {ρ} [ρ] ⊢Δ = irrelevanceEq′ (PE.cong (wk ρ) F₁≡F′) PE.refl
                                      ([F]₁ [ρ] ⊢Δ) ([F′] [ρ] ⊢Δ) ([F≡F′]₁ [ρ] ⊢Δ)
        [G′] : ∀ {ρ Δ a} [ρ] ⊢Δ
             → Δ ⊩⟨ l′ ⟩ a ∷ wk ρ F′ ^ [ % , lr ] / [F′] [ρ] ⊢Δ
             → Δ ⊩⟨ l′ ⟩ wk (lift ρ) G′ [ a ] ^ r
        [G′] {ρ} [ρ] ⊢Δ [a] =
          let [a′] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F₁≡F′)) PE.refl
                                      ([F′] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [a]
          in  PE.subst (substLift ρ) G₁≡G′ ([G]₁ [ρ] ⊢Δ [a′])
        [G″] : ∀ {ρ Δ a} [ρ] ⊢Δ
             → Δ ⊩⟨ l″ ⟩ a ∷ wk ρ F″ ^ [ % , lr ] / [F″] [ρ] ⊢Δ
             → Δ ⊩⟨ l″ ⟩ wk (lift ρ) G″ [ a ] ^ r
        [G″] {ρ} [ρ] ⊢Δ [a] =
          let [a″] = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F₂≡F″)) PE.refl
                                      ([F″] [ρ] ⊢Δ) ([F]₂ [ρ] ⊢Δ) [a]
          in  PE.subst (substLift ρ) G₂≡G″ ([G]₂ [ρ] ⊢Δ [a″])
        [G′≡G″] : ∀ {ρ Δ a} [ρ] ⊢Δ
                  ([a] : Δ ⊩⟨ l′ ⟩ a ∷ wk ρ F′ ^ [ % , lr ] / [F′] [ρ] ⊢Δ)
                → Δ ⊩⟨ l′ ⟩ wk (lift ρ) G′  [ a ]
                          ≡ wk (lift ρ) G″ [ a ] ^ r / [G′] [ρ] ⊢Δ [a]
        [G′≡G″] {ρ} [ρ] ⊢Δ [a′] =
          let [a]₁ = irrelevanceTerm′ (PE.cong (wk ρ) (PE.sym F₁≡F′)) PE.refl
                                      ([F′] [ρ] ⊢Δ) ([F]₁ [ρ] ⊢Δ) [a′]
          in  irrelevanceEq′ (PE.cong (λ x → wk (lift ρ) x [ _ ]) G₁≡G′) PE.refl
                             ([G]₁ [ρ] ⊢Δ [a]₁) ([G′] [ρ] ⊢Δ [a′])
                             ([G≡G′]₁ [ρ] ⊢Δ [a]₁)
                             -- Γ ⊢ .C ⇒* ∃ F″ ^ rF ▹ G″ ^ r
    in  ∃₌ F″ G″ D″ (≅-trans A≡B (PE.subst (λ x → Γ ⊢ x ≅ ∃ F″ ▹ G″ ^ [ % , lr ]) ∃F₁G₁≡∃F′G′ A≡B₁))
           (λ ρ ⊢Δ → transEq′ PE.refl PE.refl PE.refl PE.refl
           ([F] ρ ⊢Δ) ([F′] ρ ⊢Δ) ([F″] ρ ⊢Δ)
           ([F≡F′] ρ ⊢Δ) ([F′≡F″] ρ ⊢Δ))
           (λ ρ ⊢Δ [a] →
              let [a′] = convTerm₁′ PE.refl ([F] ρ ⊢Δ) ([F′] ρ ⊢Δ) ([F≡F′] ρ ⊢Δ) [a]
                  [a″] = convTerm₁′ PE.refl ([F′] ρ ⊢Δ) ([F″] ρ ⊢Δ) ([F′≡F″] ρ ⊢Δ) [a′]
              in  transEq ([G] ρ ⊢Δ [a]) ([G′] ρ ⊢Δ [a′]) ([G″] ρ ⊢Δ [a″])
                          ([G≡G′] ρ ⊢Δ [a]) ([G′≡G″] ρ ⊢Δ [a′]))
  transEqT (emb⁰¹¹ S) A≡B B≡C = transEqT S A≡B B≡C
  transEqT (emb¹⁰¹ S) A≡B B≡C = transEqT S A≡B B≡C
  transEqT (emb¹¹⁰ S) A≡B B≡C = transEqT S A≡B B≡C
  transEqT (emb⁰∞∞ S) A≡B B≡C = transEqT S A≡B B≡C
  transEqT (emb∞⁰∞ S) A≡B B≡C = transEqT S A≡B B≡C
  transEqT (emb∞∞⁰ S) A≡B B≡C = transEqT S A≡B B≡C
  transEqT (emb¹∞∞ S) A≡B B≡C = transEqT S A≡B B≡C
  transEqT (emb∞¹∞ S) A≡B B≡C = transEqT S A≡B B≡C
  transEqT (emb∞∞¹ S) A≡B B≡C = transEqT S A≡B B≡C

  -- Transitivty of type equality.
  transEq : ∀ {Γ A B C r l l′ l″}
            ([A] : Γ ⊩⟨ l ⟩ A ^ r) ([B] : Γ ⊩⟨ l′ ⟩ B ^ r) ([C] : Γ ⊩⟨ l″ ⟩ C ^ r)
          → Γ ⊩⟨ l ⟩  A ≡ B ^ r / [A]
          → Γ ⊩⟨ l′ ⟩ B ≡ C ^ r / [B]
          → Γ ⊩⟨ l ⟩  A ≡ C ^ r / [A]
  transEq [A] [B] [C] A≡B B≡C =
    transEqT (combine (goodCases [A] [B] A≡B) (goodCases [B] [C] B≡C)) A≡B B≡C

  -- Transitivity of type equality with some propositonally equal types.
  transEq′ : ∀ {Γ A B B′ C C′ r r' r''  l l′ l″} → B PE.≡ B′ → C PE.≡ C′ → r PE.≡ r' → r PE.≡ r''
           → ([A] : Γ ⊩⟨ l ⟩ A ^ r) ([B] : Γ ⊩⟨ l′ ⟩ B ^ r') ([C] : Γ ⊩⟨ l″ ⟩ C ^ r'')
           → Γ ⊩⟨ l ⟩  A ≡ B′ ^ r / [A]
           → Γ ⊩⟨ l′ ⟩ B ≡ C′ ^ r' / [B]
           → Γ ⊩⟨ l ⟩  A ≡ C  ^ r / [A]
  transEq′ PE.refl PE.refl PE.refl PE.refl [A] [B] [C] A≡B B≡C = transEq [A] [B] [C] A≡B B≡C


transEqTermNe : ∀ {Γ n n′ n″ A r}
              → Γ ⊩neNf n  ≡ n′  ∷ A ^ r
              → Γ ⊩neNf n′ ≡ n″ ∷ A ^ r
              → Γ ⊩neNf n  ≡ n″ ∷ A ^ r
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
    in  ℕₜ₌ k k″ d d″ (≅ₜ-trans t≡u (PE.subst (λ x → _ ⊢ x ≅ _ ∷ _ ^ _) k₁≡k′ t≡u₁))
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
transEmpty-prop (ne a b) (ne c d) = ne a d

transEqTermEmpty : ∀ {Γ n n′ n″}
  → Γ ⊩Empty n  ≡ n′  ∷Empty
  → Γ ⊩Empty n′ ≡ n″ ∷Empty
  → Γ ⊩Empty n  ≡ n″ ∷Empty
transEqTermEmpty (Emptyₜ₌ (ne a b)) (Emptyₜ₌ (ne c d)) = Emptyₜ₌ (ne a d)


-- Transitivty of term equality.
transEqTerm : ∀ {l Γ A t u v r}
              ([A] : Γ ⊩⟨ l ⟩ A ^ r)
            → Γ ⊩⟨ l ⟩ t ≡ u ∷ A ^ r / [A]
            → Γ ⊩⟨ l ⟩ u ≡ v ∷ A ^ r / [A]
            → Γ ⊩⟨ l ⟩ t ≡ v ∷ A ^ r / [A]
transEqTerm = {!!}
-- transEqTerm (Uᵣ′ rU .⁰ 0<1 ⊢Γ)
--             (Uₜ₌ A B d d′ typeA typeB t≡u [t] [u] [t≡u])
--             (Uₜ₌ A₁ B₁ d₁ d₁′ typeA₁ typeB₁ t≡u₁ [t]₁ [u]₁ [t≡u]₁)
--             rewrite whrDet*Term (redₜ d′ , typeWhnf typeB) (redₜ d₁ , typeWhnf typeA₁) =
--   Uₜ₌ A B₁ d d₁′ typeA typeB₁ (≅ₜ-trans t≡u t≡u₁) [t] [u]₁
--       (transEq [t] [u] [u]₁ [t≡u] (irrelevanceEq [t]₁ [u] [t≡u]₁))
-- transEqTerm (ℕᵣ D) [t≡u] [u≡v] = transEqTermℕ [t≡u] [u≡v]
-- transEqTerm (Emptyᵣ D) [t≡u] [u≡v] = transEqTermEmpty [t≡u] [u≡v]
-- transEqTerm {r = !} (ne′ K D neK K≡K) (neₜ₌ k m d d′ (neNfₜ₌ neK₁ neM k≡m))
--                               (neₜ₌ k₁ m₁ d₁ d″ (neNfₜ₌ neK₂ neM₁ k≡m₁)) =
--   let k₁≡m = whrDet*Term (redₜ d₁ , ne neK₂) (redₜ d′ , ne neM)
--   in  neₜ₌ k m₁ d d″
--            (neNfₜ₌ neK₁ neM₁
--                    (~-trans k≡m (PE.subst (λ x → _ ⊢ x ~ _ ∷ _ ^ _) k₁≡m k≡m₁)))
-- transEqTerm {r = %} (ne′ K D neK K≡K) (neₜ₌ d d′)
--                               (neₜ₌ d₁ d″) = neₜ₌ d d″
-- transEqTerm {r = !} (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
--             (Πₜ₌ f g d d′ funcF funcG f≡g [f] [g] [f≡g])
--             (Πₜ₌ f₁ g₁ d₁ d₁′ funcF₁ funcG₁ f≡g₁ [f]₁ [g]₁ [f≡g]₁)
--             rewrite whrDet*Term (redₜ d′ , functionWhnf funcG)
--                             (redₜ d₁ , functionWhnf funcF₁) =
--   Πₜ₌ f g₁ d d₁′ funcF funcG₁ (≅ₜ-trans f≡g f≡g₁) [f] [g]₁
--       (λ ρ ⊢Δ [a] → transEqTerm ([G] ρ ⊢Δ [a])
--                                 ([f≡g] ρ ⊢Δ [a])
--                                 ([f≡g]₁ ρ ⊢Δ [a]))
-- transEqTerm {r = %} (Πᵣ′ rF F G D ⊢F ⊢G A≡A [F] [G] G-ext)
--             (d , d′)
--             (d₁ , d₁′) = d , d₁′
-- transEqTerm {r = %} (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext)
--             (d , d′)
--             (d₁ , d₁′) = d , d₁′
-- transEqTerm (emb 0<1 x) t≡u u≡v = transEqTerm x t≡u u≡v
