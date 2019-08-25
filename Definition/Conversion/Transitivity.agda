{-# OPTIONS --without-K --safe #-}

module Definition.Conversion.Transitivity where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.RedSteps
open import Definition.Conversion
open import Definition.Conversion.Soundness
open import Definition.Conversion.Stability
open import Definition.Conversion.Whnf
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Injectivity
import Definition.Typed.Consequences.Inequality as WF
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution
open import Definition.Typed.Consequences.NeTypeEq
open import Definition.Typed.Consequences.SucCong

open import Tools.Nat
open import Tools.Product
open import Tools.Empty
import Tools.PropositionalEquality as PE


mutual
  -- Transitivity of algorithmic equality of neutrals.
  trans~↑! : ∀ {t u v A B Γ Δ}
         → ⊢ Γ ≡ Δ
         → Γ ⊢ t ~ u ↑! A
         → Δ ⊢ u ~ v ↑! B
         → Γ ⊢ t ~ v ↑! A
         × Γ ⊢ A ≡ B ^ !
  trans~↑! Γ≡Δ (var-refl x₁ x≡y) (var-refl x₂ x≡y₁) =
    var-refl x₁ (PE.trans x≡y x≡y₁)
    , neTypeEq (var _) x₁
               (PE.subst (λ x → _ ⊢ var x ∷ _ ^ _) (PE.sym x≡y)
                         (stabilityTerm (symConEq Γ≡Δ) x₂))
  trans~↑! Γ≡Δ (app-cong t~u a<>b) (app-cong u~v b<>c) =
    let t~v , ΠFG≡ΠF′G′ = trans~↓ Γ≡Δ t~u u~v
        F≡F₁ , rF≡rF₁ , G≡G₁ = injectivity ΠFG≡ΠF′G′
        a<>c = transConv↑Term Γ≡Δ F≡F₁ a<>b (PE.subst _ (PE.sym rF≡rF₁) b<>c)
    in  app-cong t~v a<>c , substTypeEq G≡G₁ (soundnessConv↑Term a<>b)
  trans~↑! Γ≡Δ (natrec-cong A<>B a₀<>b₀ aₛ<>bₛ t~u) (natrec-cong B<>C b₀<>c₀ bₛ<>cₛ u~v) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        A≡B = soundnessConv↑ A<>B
        F[0]≡F₁[0] = substTypeEq A≡B (refl (zeroⱼ ⊢Γ))
        ΠℕFs≡ΠℕF₁s = sucCong A≡B
        A<>C = transConv↑ (Γ≡Δ ∙ (refl (ℕⱼ ⊢Γ))) A<>B B<>C
        a₀<>c₀ = transConv↑Term Γ≡Δ F[0]≡F₁[0] a₀<>b₀ b₀<>c₀
        aₛ<>cₛ = transConv↑Term Γ≡Δ ΠℕFs≡ΠℕF₁s aₛ<>bₛ bₛ<>cₛ
        t~v , _ = trans~↓ Γ≡Δ t~u u~v
    in  natrec-cong A<>C a₀<>c₀ aₛ<>cₛ t~v
    ,   substTypeEq A≡B (soundness~↓ t~u)
  trans~↑! Γ≡Δ (Emptyrec-cong A<>B t~u) (Emptyrec-cong B<>C u~v) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
        A≡B = soundnessConv↑ A<>B
        A<>C = transConv↑ Γ≡Δ A<>B B<>C
        t~v , _ = trans~↓ Γ≡Δ t~u u~v
    in  Emptyrec-cong A<>C t~v , A≡B

  trans~↑ : ∀ {t u v A B r Γ Δ}
         → ⊢ Γ ≡ Δ
         → Γ ⊢ t ~ u ↑ A ^ r
         → Δ ⊢ u ~ v ↑ B ^ r
         → Γ ⊢ t ~ v ↑ A ^ r
         × Γ ⊢ A ≡ B ^ r
  trans~↑ Γ≡Δ (relevant-neutrals t~u) (relevant-neutrals u~v) =
    let t~v , A≡B = trans~↑! Γ≡Δ t~u u~v
    in relevant-neutrals t~v , A≡B
  trans~↑ Γ≡Δ (irrelevant-neutrals ac bc t u) (irrelevant-neutrals ac′ bc′ u′ v) =
    let ⊢t = soundness~↑% t
        ⊢u = soundness~↑% u
        ⊢u′ = soundness~↑% u′
        ⊢v = soundness~↑% v
        neU = ne~↑% u
        A≡B = neTypeEq neU ⊢u (stabilityTerm (symConEq Γ≡Δ) ⊢u′)
        -- ac″ = stabilityConv↑ (symConEq Γ≡Δ) ac′
        -- bc″ = stabilityConv↑ (symConEq Γ≡Δ) bc′
        -- A≡B′ = trans (sym bc) (trans A≡B ac″)
    in irrelevant-neutrals {!!} {!!} t {!!} , {!!}

  -- Transitivity of algorithmic equality of neutrals with types in WHNF.
  trans~↓ : ∀ {t u v A B r Γ Δ}
          → ⊢ Γ ≡ Δ
          → Γ ⊢ t ~ u ↓ A ^ r
          → Δ ⊢ u ~ v ↓ B ^ r
          → Γ ⊢ t ~ v ↓ A ^ r
          × Γ ⊢ A ≡ B ^ r
  trans~↓ Γ≡Δ ([~] A₁ D whnfA k~l) ([~] A₂ D₁ whnfA₁ k~l₁) =
    let t~v , A≡B = trans~↑ Γ≡Δ k~l k~l₁
    in  [~] A₁ D whnfA t~v
    ,   trans (sym (subset* D))
              (trans A≡B
                     (subset* (stabilityRed* (symConEq Γ≡Δ) D₁)))

  -- Transitivity of algorithmic equality of types.
  transConv↑ : ∀ {A B C r Γ Δ}
            → ⊢ Γ ≡ Δ
            → Γ ⊢ A [conv↑] B ^ r
            → Δ ⊢ B [conv↑] C ^ r
            → Γ ⊢ A [conv↑] C ^ r
  transConv↑ {r = r} Γ≡Δ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′)
             ([↑] A″ B″ D₁ D″ whnfA″ whnfB″ A′<>B″) =
    [↑] A′ B″ D (stabilityRed* (symConEq Γ≡Δ) D″) whnfA′ whnfB″
        (transConv↓ Γ≡Δ A′<>B′
                    (PE.subst (λ x → _ ⊢ x [conv↓] B″ ^ r)
                              (whrDet* (D₁ , whnfA″)
                                        (stabilityRed* Γ≡Δ D′ , whnfB′))
                              A′<>B″))

  -- Transitivity of algorithmic equality of types in WHNF.
  transConv↓ : ∀ {A B C r Γ Δ}
            → ⊢ Γ ≡ Δ
            → Γ ⊢ A [conv↓] B ^ r
            → Δ ⊢ B [conv↓] C ^ r
            → Γ ⊢ A [conv↓] C ^ r
  transConv↓ Γ≡Δ (U-refl e x) (U-refl e₁ x₁) = U-refl (PE.trans e e₁) x
  transConv↓ Γ≡Δ (ℕ-refl x) (ℕ-refl x₁) = ℕ-refl x
  transConv↓ Γ≡Δ (Empty-refl x) (Empty-refl x₁) = Empty-refl x
  transConv↓ Γ≡Δ (ne x) (ne x₁) =
    let A~C , U≡U = trans~↓ Γ≡Δ x x₁
    in  ne A~C
  transConv↓ Γ≡Δ (Π-cong e x x₁ x₂) (Π-cong e₁ x₃ x₄ x₅) =
    Π-cong (PE.trans e e₁) x (transConv↑ Γ≡Δ x₁ (PE.subst _ (PE.sym e) x₄))
           (transConv↑ (Γ≡Δ ∙ soundnessConv↑ x₁) x₂ (PE.subst (λ rx → _ ∙ _ ^ rx ⊢ _ [conv↑] _ ^ _) (PE.sym e) x₅))
  -- Refutable cases
  transConv↓ Γ≡Δ (U-refl e x) (ne ([~] A D whnfB (relevant-neutrals ())))
  transConv↓ Γ≡Δ (ℕ-refl x) (ne ([~] A D whnfB (relevant-neutrals ())))
  transConv↓ Γ≡Δ (Empty-refl x) (ne ([~] A D whnfB (relevant-neutrals ())))
  transConv↓ Γ≡Δ (Π-cong e x x₁ x₂) (ne ([~] A D whnfB (relevant-neutrals ())))
  transConv↓ Γ≡Δ (ne ([~] A₁ D whnfB (relevant-neutrals ()))) (U-refl e x₁)
  transConv↓ Γ≡Δ (ne ([~] A₁ D whnfB (relevant-neutrals ()))) (ℕ-refl x₁)
  transConv↓ Γ≡Δ (ne ([~] A₁ D whnfB (relevant-neutrals ()))) (Empty-refl x₁)
  transConv↓ Γ≡Δ (ne ([~] A₁ D whnfB (relevant-neutrals ()))) (Π-cong e x₁ x₂ x₃)

  -- Transitivity of algorithmic equality of terms.
  transConv↑Term : ∀ {t u v A B r Γ Δ}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B ^ r
                → Γ ⊢ t [conv↑] u ∷ A ^ r
                → Δ ⊢ u [conv↑] v ∷ B ^ r
                → Γ ⊢ t [conv↑] v ∷ A ^ r
  transConv↑Term {r = r} Γ≡Δ A≡B ([↑]ₜ B₁ t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u)
                 ([↑]ₜ B₂ t″ u″ D₁ d₁ d″ whnfB₁ whnft″ whnfu″ t<>u₁) =
    let B₁≡B₂ = trans (sym (subset* D))
                      (trans A≡B
                             (subset* (stabilityRed* (symConEq Γ≡Δ) D₁)))
        d₁″ = conv* (stabilityRed*Term (symConEq Γ≡Δ) d″) (sym B₁≡B₂)
        d₁′  = stabilityRed*Term Γ≡Δ (conv* d′ B₁≡B₂)
    in  [↑]ₜ B₁ t′ u″ D d d₁″ whnfB whnft′ whnfu″
             (transConv↓Term Γ≡Δ B₁≡B₂ t<>u
                             (PE.subst (λ x → _ ⊢ x [conv↓] u″ ∷ B₂ ^ r)
                                       (whrDet*Term (d₁ , whnft″)
                                                (d₁′ , whnfu′))
                                       t<>u₁))

  -- Transitivity of algorithmic equality of terms in WHNF.
  transConv↓Term : ∀ {t u v A B r Γ Δ}
                → ⊢ Γ ≡ Δ
                → Γ ⊢ A ≡ B ^ r
                → Γ ⊢ t [conv↓] u ∷ A ^ r
                → Δ ⊢ u [conv↓] v ∷ B ^ r
                → Γ ⊢ t [conv↓] v ∷ A ^ r
  transConv↓Term Γ≡Δ A≡B (ℕ-ins x) (ℕ-ins x₁) =
    ℕ-ins (proj₁ (trans~↓ Γ≡Δ x x₁))
  transConv↓Term Γ≡Δ A≡B (Empty-ins x) (Empty-ins x₁) =
    Empty-ins (proj₁ (trans~↓ Γ≡Δ x x₁))
  transConv↓Term Γ≡Δ A≡B (ne-ins t u x x₁) (ne-ins t′ u′ x₂ x₃) =
    ne-ins t (conv (stabilityTerm (symConEq Γ≡Δ) u′) (sym A≡B)) x
           (proj₁ (trans~↓ Γ≡Δ x₁ x₃))
  transConv↓Term Γ≡Δ A≡B (univ x x₁ x₂) (univ x₃ x₄ x₅) =
    let r₁≡r = Uinjectivity A≡B
    in univ x (stabilityTerm (symConEq Γ≡Δ) (PE.subst _ (PE.sym r₁≡r) x₄))
                             (transConv↓ Γ≡Δ x₂ (PE.subst _ (PE.sym r₁≡r) x₅))
  transConv↓Term Γ≡Δ A≡B (zero-refl x) (zero-refl x₁) =
    zero-refl x
  transConv↓Term Γ≡Δ A≡B (suc-cong x) (suc-cong x₁) =
    suc-cong (transConv↑Term Γ≡Δ A≡B x x₁)
  transConv↓Term Γ≡Δ A≡B (η-eq x x₁ x₂ y y₁ x₃) (η-eq x₄ x₅ x₆ y₂ y₃ x₇) =
    -- G₁≡G x₇
    let F₁≡F , rF₁≡rF , G₁≡G = injectivity A≡B
    in  η-eq x x₁ (conv (stabilityTerm (symConEq Γ≡Δ) x₆) (sym A≡B))
             y y₃ (transConv↑Term (Γ≡Δ ∙ F₁≡F) G₁≡G x₃
                                  (PE.subst (λ rx → _ ∙ _ ^ rx ⊢ _ [conv↑] _ ∷ _ ^ _) (PE.sym rF₁≡rF) x₇))
  -- Refutable cases
  transConv↓Term Γ≡Δ A≡B (ℕ-ins x) (ne-ins t u x₂ x₃) = ⊥-elim (WF.ℕ≢ne x₂ A≡B)
  transConv↓Term Γ≡Δ A≡B (ℕ-ins x) (univ x₂ x₃ x₄) = ⊥-elim (WF.U≢ℕ (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (ℕ-ins ([~] A D whnfB (relevant-neutrals ()))) (zero-refl x₂)
  transConv↓Term Γ≡Δ A≡B (ℕ-ins ([~] A D whnfB (relevant-neutrals ()))) (suc-cong x₂)
  transConv↓Term Γ≡Δ A≡B (ℕ-ins x) (η-eq x₂ x₃ x₄ y y₁ x₅) = ⊥-elim (WF.ℕ≢Π A≡B)
  transConv↓Term Γ≡Δ A≡B (Empty-ins x) (ne-ins t u x₂ x₃) = ⊥-elim (WF.Empty≢ne x₂ A≡B)
  transConv↓Term Γ≡Δ A≡B (Empty-ins x) (η-eq x₂ x₃ x₄ y y₁ x₅) = ⊥-elim (WF.Empty≢Π A≡B)
  transConv↓Term Γ≡Δ A≡B (ne-ins t u x x₁) (ℕ-ins x₂) = ⊥-elim (WF.ℕ≢ne x (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (ne-ins t u x x₁) (Empty-ins x₂) = ⊥-elim (WF.Empty≢ne x (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (ne-ins t u x x₁) (univ x₃ x₄ x₅) = ⊥-elim (WF.U≢ne x (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (ne-ins t u x ([~] A D whnfB (relevant-neutrals ()))) (zero-refl x₃)
  transConv↓Term Γ≡Δ A≡B (ne-ins t u x ([~] A D whnfB (relevant-neutrals ()))) (suc-cong x₃)
  transConv↓Term Γ≡Δ A≡B (ne-ins t u x x₁) (η-eq x₃ x₄ x₅ y y₁ x₆) = ⊥-elim (WF.Π≢ne x (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (univ x x₁ x₂) (ℕ-ins x₃) = ⊥-elim (WF.U≢ℕ A≡B)
  transConv↓Term Γ≡Δ A≡B (univ x x₁ x₂) (ne-ins t u x₃ x₄) = ⊥-elim (WF.U≢ne x₃ A≡B)
  transConv↓Term Γ≡Δ A≡B (univ x x₁ x₂) (zero-refl x₃) = ⊥-elim (WF.U≢ℕ A≡B)
  transConv↓Term Γ≡Δ A≡B (univ x x₁ x₂) (suc-cong x₃) = ⊥-elim (WF.U≢ℕ A≡B)
  transConv↓Term Γ≡Δ A≡B (univ x x₁ x₂) (η-eq x₃ x₄ x₅ y y₁ x₆) = ⊥-elim (WF.U≢Π A≡B)
  transConv↓Term Γ≡Δ A≡B (zero-refl x) (ℕ-ins ([~] A D whnfB (relevant-neutrals ())))
  transConv↓Term Γ≡Δ A≡B (zero-refl x) (ne-ins t u x₁ ([~] A D whnfB (relevant-neutrals ())))
  transConv↓Term Γ≡Δ A≡B (zero-refl x) (univ x₁ x₂ x₃) = ⊥-elim (WF.U≢ℕ (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (zero-refl x) (η-eq x₁ x₂ x₃ y y₁ x₄) = ⊥-elim (WF.ℕ≢Π A≡B)
  transConv↓Term Γ≡Δ A≡B (suc-cong x) (ℕ-ins ([~] A D whnfB (relevant-neutrals ())))
  transConv↓Term Γ≡Δ A≡B (suc-cong x) (ne-ins t u x₁ ([~] A D whnfB (relevant-neutrals ())))
  transConv↓Term Γ≡Δ A≡B (suc-cong x) (univ x₁ x₂ x₃) = ⊥-elim (WF.U≢ℕ (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (suc-cong x) (η-eq x₁ x₂ x₃ y y₁ x₄) = ⊥-elim (WF.ℕ≢Π A≡B)
  transConv↓Term Γ≡Δ A≡B (η-eq x x₁ x₂ y y₁ x₃) (ℕ-ins x₄) = ⊥-elim (WF.ℕ≢Π (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (η-eq x x₁ x₂ y y₁ x₃) (Empty-ins x₄) = ⊥-elim (WF.Empty≢Π (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (η-eq x x₁ x₂ y y₁ x₃) (ne-ins t u x₄ x₅) = ⊥-elim (WF.Π≢ne x₄ A≡B)
  transConv↓Term Γ≡Δ A≡B (η-eq x x₁ x₂ y y₁ x₃) (univ x₄ x₅ x₆) = ⊥-elim (WF.U≢Π (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (η-eq x x₁ x₂ y y₁ x₃) (zero-refl x₄) = ⊥-elim (WF.ℕ≢Π (sym A≡B))
  transConv↓Term Γ≡Δ A≡B (η-eq x x₁ x₂ y y₁ x₃) (suc-cong x₄) = ⊥-elim (WF.ℕ≢Π (sym A≡B))
-- free from clashing relevances
--  transConv↓Term Γ≡Δ A≡B (ℕ-ins x) (Empty-ins x₁) = ⊥-elim (WF.ℕ≢Empty A≡B)
--  transConv↓Term Γ≡Δ A≡B (Empty-ins x) (univ x₂ x₃ x₄) = ⊥-elim (WF.U≢Empty (sym A≡B))
--  transConv↓Term Γ≡Δ A≡B (Empty-ins x₁) (ℕ-ins x) = ⊥-elim (WF.ℕ≢Empty (sym A≡B))
--  transConv↓Term Γ≡Δ A≡B (Empty-ins ([~] A D whnfB ())) (zero-refl x₂)
--  transConv↓Term Γ≡Δ A≡B (Empty-ins ([~] A D whnfB ())) (suc-cong x₂)
--  transConv↓Term Γ≡Δ A≡B (univ x x₁ x₂) (Empty-ins x₃) = ⊥-elim (WF.U≢Empty A≡B)
--  transConv↓Term Γ≡Δ A≡B (zero-refl x) (Empty-ins ([~] A D whnfB ()))
--  transConv↓Term Γ≡Δ A≡B (suc-cong x) (Empty-ins ([~] A D whnfB ()))

-- Transitivity of algorithmic equality of types of the same context.
transConv : ∀ {A B C r Γ}
          → Γ ⊢ A [conv↑] B ^ r
          → Γ ⊢ B [conv↑] C ^ r
          → Γ ⊢ A [conv↑] C ^ r
transConv A<>B B<>C =
  let Γ≡Γ = reflConEq (wfEq (soundnessConv↑ A<>B))
  in  transConv↑ Γ≡Γ A<>B B<>C

-- Transitivity of algorithmic equality of terms of the same context.
transConvTerm : ∀ {t u v A r Γ}
              → Γ ⊢ t [conv↑] u ∷ A ^ r
              → Γ ⊢ u [conv↑] v ∷ A ^ r
              → Γ ⊢ t [conv↑] v ∷ A ^ r
transConvTerm t<>u u<>v =
  let t≡u = soundnessConv↑Term t<>u
      Γ≡Γ = reflConEq (wfEqTerm t≡u)
      ⊢A , _ , _ = syntacticEqTerm t≡u
  in  transConv↑Term Γ≡Γ (refl ⊢A) t<>u u<>v
