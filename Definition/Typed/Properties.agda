{-# OPTIONS --without-K  #-}

module Definition.Typed.Properties where

open import Definition.Untyped
open import Definition.Typed

open import Tools.Empty using (⊥; ⊥-elim)
open import Tools.Product
import Tools.PropositionalEquality as PE


-- Escape context extraction

wfTerm : ∀ {Γ A t s} → Γ ⊢ t ∷ A ⦂ s → ⊢ Γ
wfTerm (ℕⱼ ⊢Γ) = ⊢Γ
wfTerm (Emptyⱼ ⊢Γ) = ⊢Γ
wfTerm (Πⱼ F ▹ G) = wfTerm F
wfTerm (var ⊢Γ x₁) = ⊢Γ
wfTerm (lamⱼ F t) with wfTerm t
wfTerm (lamⱼ F t) | ⊢Γ ∙ F′ = ⊢Γ
wfTerm (g ∘ⱼ a) = wfTerm a
wfTerm (zeroⱼ ⊢Γ) = ⊢Γ
wfTerm (sucⱼ n) = wfTerm n
wfTerm (natrecⱼ F z s n) = wfTerm z
wfTerm (Emptyrecⱼ A e) = wfTerm e
wfTerm (conv t A≡B) = wfTerm t
wfTerm (Boxⱼ d) = wfTerm d
wfTerm (boxⱼ d) = wfTerm d
wfTerm (cstrⱼ _ _ _ ⊢a) = wfTerm ⊢a
wfTerm (dstrⱼ _ _ _ ⊢p _ _) = wfTerm ⊢p
wfTerm (Boxrecⱼ _ x d d₁) = wfTerm d

wf : ∀ {Γ A s} → Γ ⊢ A ⦂ s → ⊢ Γ
wf (ℕⱼ ⊢Γ) = ⊢Γ
wf (Emptyⱼ ⊢Γ) = ⊢Γ
wf (Uⱼ ⊢Γ) = ⊢Γ
wf (Πⱼ F ▹ G) = wf F
wf (univ A) = wfTerm A
wf (Boxⱼ d) = wf d

wfEqTerm : ∀ {Γ A t u s} → Γ ⊢ t ≡ u ∷ A ⦂ s → ⊢ Γ
wfEqTerm (refl t) = wfTerm t
wfEqTerm (sym t≡u) = wfEqTerm t≡u
wfEqTerm (trans t≡u u≡s) = wfEqTerm t≡u
wfEqTerm (conv t≡u A≡B) = wfEqTerm t≡u
wfEqTerm (Π-cong F F≡H G≡E) = wfEqTerm F≡H
wfEqTerm (app-cong f≡g a≡b) = wfEqTerm f≡g
wfEqTerm (β-red F t a) = wfTerm a
wfEqTerm (η-eq F f g f0≡g0) = wfTerm f
wfEqTerm (suc-cong n) = wfEqTerm n
wfEqTerm (natrec-cong F≡F′ z≡z′ s≡s′ n≡n′) = wfEqTerm z≡z′
wfEqTerm (natrec-zero F z s) = wfTerm z
wfEqTerm (natrec-suc n F z s) = wfTerm n
wfEqTerm (Emptyrec-cong A≡A' e≡e') = wfEqTerm e≡e'
wfEqTerm (Box-cong x d) = wfTerm x
wfEqTerm (box-cong _ _ _ d) = wfEqTerm d
wfEqTerm (Boxrec-cong _ _ x d₁ d) = wfEqTerm d
wfEqTerm (Boxrec-box _ x x₁ x₂) = wfTerm x₁
wfEqTerm (rew _ _ ⊢ka) = wfTerm ⊢ka
wfEqTerm (cstr-cong d) = wfEqTerm d
wfEqTerm (dstr-cong d d₁) = wfEqTerm d

wfEq : ∀ {Γ A B s} → Γ ⊢ A ≡ B ⦂ s → ⊢ Γ
wfEq (univ A≡B) = wfEqTerm A≡B
wfEq (refl A) = wf A
wfEq (sym A≡B) = wfEq A≡B
wfEq (trans A≡B B≡C) = wfEq A≡B
wfEq (Π-cong F F≡H G≡E) = wfEq F≡H
wfEq (Box-cong x d) = wf x

-- Reduction is a subset of conversion

subsetTerm : ∀ {Γ A t u s} → Γ ⊢ t ⇒ u ∷ A ⦂ s → Γ ⊢ t ≡ u ∷ A ⦂ s
subsetTerm (natrec-subst F z s n⇒n′) =
  natrec-cong (refl F) (refl z) (refl s) (subsetTerm n⇒n′)
subsetTerm (natrec-zero F z s) = natrec-zero F z s
subsetTerm (natrec-suc n F z s) = natrec-suc n F z s
subsetTerm (Emptyrec-subst A n⇒n′) =
  Emptyrec-cong (refl A) (subsetTerm n⇒n′)
subsetTerm (app-subst t⇒u a) = app-cong (subsetTerm t⇒u) (refl a)
subsetTerm (β-red A t a) = β-red A t a
subsetTerm (conv t⇒u A≡B) = conv (subsetTerm t⇒u) A≡B
subsetTerm (Boxrec-subst F E u t⇒t') = Boxrec-cong F (refl F) (refl E) (refl u) (subsetTerm t⇒t')
subsetTerm (Boxrec-box F E a u) = Boxrec-box F E a u
subsetTerm (rew r ka⇒t ⊢ka PE.refl PE.refl) = rew r ka⇒t ⊢ka

subset : ∀ {Γ A B s} → Γ ⊢ A ⇒ B ⦂ s → Γ ⊢ A ≡ B ⦂ s
subset (univ A⇒B) = univ (subsetTerm A⇒B)

subset*Term : ∀ {Γ A t u s} → Γ ⊢ t ⇒* u ∷ A ⦂ s → Γ ⊢ t ≡ u ∷ A ⦂ s
subset*Term (id t) = refl t
subset*Term (t⇒t′ ⇨ t⇒*u) = trans (subsetTerm t⇒t′) (subset*Term t⇒*u)

subset* : ∀ {Γ A B s} → Γ ⊢ A ⇒* B ⦂ s → Γ ⊢ A ≡ B ⦂ s
subset* (id A) = refl A
subset* (A⇒A′ ⇨ A′⇒*B) = trans (subset A⇒A′) (subset* A′⇒*B)


-- Can extract left-part of a reduction

redFirstTerm : ∀ {Γ t u A s} → Γ ⊢ t ⇒ u ∷ A ⦂ s → Γ ⊢ t ∷ A ⦂ s
redFirstTerm (conv t⇒u A≡B) = conv (redFirstTerm t⇒u) A≡B
redFirstTerm (app-subst t⇒u a) = (redFirstTerm t⇒u) ∘ⱼ a
redFirstTerm (β-red A t a) = (lamⱼ A t) ∘ⱼ a
redFirstTerm (natrec-subst F z s n⇒n′) = natrecⱼ F z s (redFirstTerm n⇒n′)
redFirstTerm (natrec-zero F z s) = natrecⱼ F z s (zeroⱼ (wfTerm z))
redFirstTerm (natrec-suc n F z s) = natrecⱼ F z s (sucⱼ n)
redFirstTerm (Emptyrec-subst A n⇒n′) = Emptyrecⱼ A (redFirstTerm n⇒n′)
redFirstTerm (Boxrec-subst F E u t⇒t') = Boxrecⱼ F E u (redFirstTerm t⇒t')
redFirstTerm (Boxrec-box F E u a) = Boxrecⱼ F E u (boxⱼ a)
redFirstTerm (rew _ ka⇒t ⊢ka eqrhs PE.refl) = ⊢ka

redFirst : ∀ {Γ A B s} → Γ ⊢ A ⇒ B ⦂ s → Γ ⊢ A ⦂ s
redFirst (univ A⇒B) = univ (redFirstTerm A⇒B)

redFirst*Term : ∀ {Γ t u A s} → Γ ⊢ t ⇒* u ∷ A ⦂ s → Γ ⊢ t ∷ A ⦂ s
redFirst*Term (id t) = t
redFirst*Term (t⇒t′ ⇨ t′⇒*u) = redFirstTerm t⇒t′

redFirst* : ∀ {Γ A B s} → Γ ⊢ A ⇒* B ⦂ s → Γ ⊢ A ⦂ s
redFirst* (id A) = A
redFirst* (A⇒A′ ⇨ A′⇒*B) = redFirst A⇒A′


-- No neutral terms are well-formed in an empty context

mutual
  noNe : ∀ {t A s} → ε ⊢ t ∷ A ⦂ s → Neutral t → ⊥
  noNe (var x₁ ()) (var x)
  noNe (conv ⊢t x) neT = noNe ⊢t neT
  noNe (⊢t ∘ⱼ ⊢t₁) (∘ₙ neT) = noNe ⊢t neT
  noNe (natrecⱼ x ⊢t ⊢t₁ ⊢t₂) (natrecₙ neT) = noNe ⊢t₂ neT
  noNe (Emptyrecⱼ A ⊢e) (Emptyrecₙ neT) = noNe ⊢e neT
  noNe (Boxrecⱼ _ ⊢C  ⊢u ⊢t) (Boxrecₙ net) = noNe ⊢t net
  noNe (dstrⱼ x x₁ d ⊢p ⊢a _) (destrₙ n) = noNe ⊢a n

-- Neutrals do not weak head reduce

-- noRed-cstr : ∀ {Γ k u A s} (c : Γ ⊢ cstr k ⇒ u ∷ A ⦂ s) → ⊥
-- noRed-cstr (conv c x) = noRed-cstr c

-- noRed-dstr : ∀ {Γ d u A s} → Γ ⊢ dstr d ⇒ u ∷ A ⦂ s → ⊥
-- noRed-dstr (conv d x) = noRed-dstr d

-- noRed-dstr-app : ∀ {Γ d t u A s} (d : Γ ⊢ dstr d ∘ t ⇒ u ∷ A ⦂ s) → ⊥
-- noRed-dstr-app (conv d x) = noRed-dstr-app d
-- noRed-dstr-app (app-subst d x) = noRed-dstr d

open import Tools.List renaming (_∷_ to _⦂⦂_)

neWk : ∀ {t t' ρ} → wk ρ t PE.≡ t' → Neutral t' → Neutral t
neWk {var x} e _ = var x
neWk {gen Appkind (⟦ 0 , k ⟧ ⦂⦂ ⟦ 0 , _ ⟧ ⦂⦂ [])} e (∘ₙ n) = ∘ₙ (neWk (∘-inj-head e) n)
neWk {gen Natreckind (⟦ 1 , _ ⟧ ⦂⦂ ⟦ 0 , _ ⟧ ⦂⦂ ⟦ 0 , _ ⟧ ⦂⦂ ⟦ 0 , k ⟧ ⦂⦂ [])} e (natrecₙ n) = natrecₙ (neWk (natrec-inj-head e) n)
neWk {gen Emptyreckind (⟦ 0 , _ ⟧ ⦂⦂ ⟦ 0 , t ⟧ ⦂⦂ [])} e (Emptyrecₙ n) = Emptyrecₙ (neWk (Emptyrec-inj-head e) n)
neWk {gen (Boxreckind _) (⟦ 0 , _ ⟧ ⦂⦂ ⟦ 1 , _ ⟧ ⦂⦂ ⟦ 0 , _ ⟧ ⦂⦂ ⟦ 0 , t ⟧  ⦂⦂ [])} e (Boxrecₙ n) = Boxrecₙ (neWk (Boxrec-inj-head e) n)
neWk {gen (Destructorkind _) (⟦ 0 , _ ⟧ ⦂⦂ ⟦ 0 , a ⟧ ⦂⦂ [])} e (destrₙ n) = destrₙ (neWk (dstr-inj-head e) n)

neSubst : ∀ {t t' u} → t [ u ] PE.≡ t' → Neutral t' → Neutral t
neSubst {var x} e _ = var x
neSubst {gen Appkind (⟦ 0 , k ⟧ ⦂⦂ ⟦ 0 , _ ⟧ ⦂⦂ [])} e (∘ₙ n) = ∘ₙ (neSubst (∘-inj-head e) n)
neSubst {gen Natreckind (⟦ 1 , _ ⟧ ⦂⦂ ⟦ 0 , _ ⟧ ⦂⦂ ⟦ 0 , _ ⟧ ⦂⦂ ⟦ 0 , k ⟧ ⦂⦂ [])} e (natrecₙ n) = natrecₙ (neSubst (natrec-inj-head e) n)
neSubst {gen Emptyreckind (⟦ 0 , _ ⟧ ⦂⦂ ⟦ 0 , t ⟧ ⦂⦂ [])} e (Emptyrecₙ n) = Emptyrecₙ (neSubst (Emptyrec-inj-head e) n)
neSubst {gen (Boxreckind _) (⟦ 0 , _ ⟧ ⦂⦂ ⟦ 1 , _ ⟧ ⦂⦂ ⟦ 0 , _ ⟧ ⦂⦂ ⟦ 0 , t ⟧  ⦂⦂ [])} e (Boxrecₙ n) = Boxrecₙ (neSubst (Boxrec-inj-head e) n)
neSubst {gen (Destructorkind _) (⟦ 0 , _ ⟧ ⦂⦂ ⟦ 0 , a ⟧ ⦂⦂ [])} e (destrₙ n) = destrₙ (neSubst (dstr-inj-head e) n)

-- KM: would it be possible to only assume something on Rew⊢_⊚_⇒_ ?
postulate neRedRew : ∀ {k l r} (d : Rew⊢ k ⊚ l ⇒ r) (n : Neutral l) → ⊥

neRedTerm : ∀ {Γ t u A s} (d : Γ ⊢ t ⇒ u ∷ A ⦂ s) (n : Neutral t) → ⊥
neRedTerm (conv d x) n = neRedTerm d n
neRedTerm (app-subst d x) (∘ₙ n) = neRedTerm d n
neRedTerm (β-red x x₁ x₂) (∘ₙ ())
neRedTerm (natrec-subst x x₁ x₂ d) (natrecₙ n₁) = neRedTerm d n₁
neRedTerm (natrec-zero x x₁ x₂) (natrecₙ ())
neRedTerm (natrec-suc x x₁ x₂ x₃) (natrecₙ ())
neRedTerm (Emptyrec-subst x d) (Emptyrecₙ n₁) = neRedTerm d n₁
neRedTerm (Boxrec-subst x x₁ x₂ d) (Boxrecₙ n) = neRedTerm d n
neRedTerm (Boxrec-box x x₁ x₂ x₃) (Boxrecₙ ())
neRedTerm (rew ka⇒t _ ⊢ka _ eqlhs) (destrₙ n) = neRedRew ka⇒t (neWk PE.refl (neSubst (PE.sym eqlhs) n))

neRed : ∀ {Γ A B s} (d : Γ ⊢ A ⇒ B ⦂ s) (N : Neutral A) → ⊥
neRed (univ x) N = neRedTerm x N

-- Whnfs do not weak head reduce

whnfRedTerm : ∀ {Γ t u A s} (d : Γ ⊢ t ⇒ u ∷ A ⦂ s) (w : Whnf t) → ⊥
whnfRedTerm (conv d x) w = whnfRedTerm d w
whnfRedTerm (app-subst d x) (ne (∘ₙ x₁)) = neRedTerm d x₁
whnfRedTerm (β-red x x₁ x₂) (ne (∘ₙ ()))
whnfRedTerm (natrec-subst x x₁ x₂ d) (ne (natrecₙ x₃)) = neRedTerm d x₃
whnfRedTerm (natrec-zero x x₁ x₂) (ne (natrecₙ ()))
whnfRedTerm (natrec-suc x x₁ x₂ x₃) (ne (natrecₙ ()))
whnfRedTerm (Emptyrec-subst x d) (ne (Emptyrecₙ x₂)) = neRedTerm d x₂
whnfRedTerm (Boxrec-subst x x₁ x₂ d) (ne (Boxrecₙ x₃)) = neRedTerm d x₃
whnfRedTerm (Boxrec-box x x₁ x₂ x₃) (ne n) = neRedTerm (Boxrec-box x x₁ x₂ x₃) n
whnfRedTerm (rew ka⇒t _ _ _ eqlhs) (ne (destrₙ n)) = neRedRew ka⇒t (neWk PE.refl (neSubst (PE.sym eqlhs) n))

whnfRed : ∀ {Γ A B s} (d : Γ ⊢ A ⇒ B ⦂ s) (w : Whnf A) → ⊥
whnfRed (univ x) w = whnfRedTerm x w

whnfRed*Term : ∀ {Γ t u A s} (d : Γ ⊢ t ⇒* u ∷ A ⦂ s) (w : Whnf t) → t PE.≡ u
whnfRed*Term (id x) Uₙ = PE.refl
whnfRed*Term (id x) Πₙ = PE.refl
whnfRed*Term (id x) ℕₙ = PE.refl
whnfRed*Term (id x) Emptyₙ = PE.refl
whnfRed*Term (id x) lamₙ = PE.refl
whnfRed*Term (id x) zeroₙ = PE.refl
whnfRed*Term (id x) sucₙ = PE.refl
whnfRed*Term (id x) Boxₙ = PE.refl
whnfRed*Term (id x) boxₙ = PE.refl
whnfRed*Term (id x) cstrₙ = PE.refl
whnfRed*Term (id x) (ne x₁) = PE.refl
whnfRed*Term (x ⇨ d) w = ⊥-elim (whnfRedTerm x w)

whnfRed* : ∀ {Γ A B s} (d : Γ ⊢ A ⇒* B ⦂ s) (w : Whnf A) → A PE.≡ B
whnfRed* (id x) w = PE.refl
whnfRed* (x ⇨ d) w = ⊥-elim (whnfRed x w)

-- Whr is deterministic

-- KM: I am doing something a bit fishy with the substitutions:
-- Morally, the rhs of a rewrite rule should only depend on the free variables of the pattern on the lhs
-- and whenever a [ ρ ] ≡ a' [ ρ' ] then ρ and ρ' agree on these free variables
-- It should be enough to restrict the substitution to the domain of l/r
postulate redRewDet : ∀ {Γ k p u u' l l' r r'} (d : Rew⊢ k ⊚ l ⇒ r) (d' : Rew⊢ k ⊚ l' ⇒ r') → Rew.lhs-ctx d Γ p u PE.≡ Rew.lhs-ctx d' Γ p u' → Rew.rhs-ctx d Γ p u PE.≡ Rew.rhs-ctx d' Γ p u'
-- l [ u ] PE.≡ l' [ u' ] →
-- subst ρ l PE.≡ subst ρ' l' → subst ρ r PE.≡ subst ρ' r'

-- red𝕊Det : ∀ {Δ k a p u u' s s'} (d : Δ 𝕊⊢ k ⊚ a ⊚ p ⇒ u ⦂ s) (d' : Δ 𝕊⊢ k ⊚ a ⊚ p ⇒ u' ⦂ s') → u PE.≡ u'
-- red𝕊Det d d' = red𝕊Det-aux d d' PE.refl PE.refl PE.refl
--   where
--     red𝕊Det-aux : ∀ {Δ Δ' k a a' p p' u u' s s'} (d : Δ 𝕊⊢ k ⊚ a ⊚ p ⇒ u ⦂ s) (d' : Δ' 𝕊⊢ k ⊚ a' ⊚ p' ⇒ u' ⦂ s') → Δ PE.≡ Δ' → a PE.≡ a' → p PE.≡ p' → u PE.≡ u'
--     red𝕊Det-aux (rew _ d) (rew _ d') Δ≡Δ' a≡a' = redRewDet d d' a≡a'

whrDetTerm : ∀{Γ t u A u′ A′ s s'} (d : Γ ⊢ t ⇒ u ∷ A ⦂ s) (d′ : Γ ⊢ t ⇒ u′ ∷ A′ ⦂ s') → u PE.≡ u′
whrDetTerm (conv d x) d′ = whrDetTerm d d′
whrDetTerm d (conv d′ x₁) = whrDetTerm d d′
whrDetTerm (app-subst d x) (app-subst d′ x₁) rewrite whrDetTerm d d′ = PE.refl
whrDetTerm (app-subst d x) (β-red x₁ x₂ x₃) = ⊥-elim (whnfRedTerm d lamₙ)
whrDetTerm (β-red x x₁ x₂) (app-subst d x₃) = ⊥-elim (whnfRedTerm d lamₙ)
whrDetTerm (β-red x x₁ x₂) (β-red x₃ x₄ x₅) = PE.refl
whrDetTerm (natrec-subst x x₁ x₂ d) (natrec-subst x₃ x₄ x₅ d′) rewrite whrDetTerm d d′ = PE.refl
whrDetTerm (natrec-subst x x₁ x₂ d) (natrec-zero x₃ x₄ x₅) = ⊥-elim (whnfRedTerm d zeroₙ)
whrDetTerm (natrec-subst x x₁ x₂ d) (natrec-suc x₃ x₄ x₅ x₆) = ⊥-elim (whnfRedTerm d sucₙ)
whrDetTerm (natrec-zero x x₁ x₂) (natrec-subst x₃ x₄ x₅ d′) = ⊥-elim (whnfRedTerm d′ zeroₙ)
whrDetTerm (natrec-zero x x₁ x₂) (natrec-zero x₃ x₄ x₅) = PE.refl
whrDetTerm (natrec-suc x x₁ x₂ x₃) (natrec-subst x₄ x₅ x₆ d′) = ⊥-elim (whnfRedTerm d′ sucₙ)
whrDetTerm (natrec-suc x x₁ x₂ x₃) (natrec-suc x₄ x₅ x₆ x₇) = PE.refl
whrDetTerm (Emptyrec-subst x d) (Emptyrec-subst x₂ d′) rewrite whrDetTerm d d′ = PE.refl
whrDetTerm (Boxrec-subst x x₁ x₂ d) (Boxrec-subst x₃ x₄ x₅ d') rewrite whrDetTerm d d' = PE.refl
whrDetTerm (Boxrec-subst x x₁ x₂ d) (Boxrec-box x₃ x₄ x₅ x₆) = ⊥-elim (whnfRedTerm d boxₙ)
whrDetTerm (Boxrec-box x x₁ x₂ x₃) (Boxrec-subst x₄ x₅ x₆ d') = ⊥-elim (whnfRedTerm d' boxₙ)
whrDetTerm (Boxrec-box x x₁ x₂ x₃) (Boxrec-box x₄ x₅ x₆ x₇) = PE.refl
-- whrDetTerm (app-subst d x) (rew _ ka⇒t ⊢ka) = ⊥-elim (noRed-dstr-app d)
-- whrDetTerm (rew _ ka⇒t ⊢ka) (app-subst d x) = ⊥-elim (noRed-dstr-app d)
whrDetTerm (rew {d = d} {p = p} ka⇒t _ ⊢ka PE.refl eqlhs) (rew ka⇒t' _ ⊢ka' PE.refl eqlhs') =
  redRewDet ka⇒t ka⇒t' (PE.cong (dstr d p) (PE.trans (PE.sym eqlhs) eqlhs'))

whrDet : ∀{Γ A B B′ s s'} (d : Γ ⊢ A ⇒ B ⦂ s) (d′ : Γ ⊢ A ⇒ B′ ⦂ s') → B PE.≡ B′
whrDet (univ x) (univ x₁) = whrDetTerm x x₁

whrDet↘Term : ∀{Γ t u A u′ s s'} (d : Γ ⊢ t ↘ u ∷ A ⦂ s) (d′ : Γ ⊢ t ⇒* u′ ∷ A ⦂ s')
  → Γ ⊢ u′ ⇒* u ∷ A ⦂ s
whrDet↘Term (proj₁ , proj₂) (id x) = proj₁
whrDet↘Term (id x , proj₂) (x₁ ⇨ d′) = ⊥-elim (whnfRedTerm x₁ proj₂)
whrDet↘Term (x ⇨ proj₁ , proj₂) (x₁ ⇨ d′) =
  whrDet↘Term (PE.subst (λ x₂ → _ ⊢ x₂ ↘ _ ∷ _ ⦂ _) (whrDetTerm x x₁) (proj₁ , proj₂)) d′

whrDet*Term : ∀{Γ t u A A' u′ s s'} (d : Γ ⊢ t ↘ u ∷ A ⦂ s) (d′ : Γ ⊢ t ↘ u′ ∷ A' ⦂ s') → u PE.≡ u′
whrDet*Term (id x , proj₂) (id x₁ , proj₄) = PE.refl
whrDet*Term (id x , proj₂) (x₁ ⇨ proj₃ , proj₄) = ⊥-elim (whnfRedTerm x₁ proj₂)
whrDet*Term (x ⇨ proj₁ , proj₂) (id x₁ , proj₄) = ⊥-elim (whnfRedTerm x proj₄)
whrDet*Term (x ⇨ proj₁ , proj₂) (x₁ ⇨ proj₃ , proj₄) =
  whrDet*Term (proj₁ , proj₂) (PE.subst (λ x₂ → _ ⊢ x₂ ↘ _ ∷ _ ⦂ _)
                                    (whrDetTerm x₁ x) (proj₃ , proj₄))

whrDet* : ∀{Γ A B B′ s s'} (d : Γ ⊢ A ↘ B ⦂ s) (d′ : Γ ⊢ A ↘ B′ ⦂ s') → B PE.≡ B′
whrDet* (id x , proj₂) (id x₁ , proj₄) = PE.refl
whrDet* (id x , proj₂) (x₁ ⇨ proj₃ , proj₄) = ⊥-elim (whnfRed x₁ proj₂)
whrDet* (x ⇨ proj₁ , proj₂) (id x₁ , proj₄) = ⊥-elim (whnfRed x proj₄)
whrDet* (A⇒A′ ⇨ A′⇒*B , whnfB) (A⇒A″ ⇨ A″⇒*B′ , whnfB′) =
  whrDet* (A′⇒*B , whnfB) (PE.subst (λ x → _ ⊢ x ↘ _ ⦂ _)
                                     (whrDet A⇒A″ A⇒A′)
                                     (A″⇒*B′ , whnfB′))

-- Identity of syntactic reduction

idRed:*: : ∀ {Γ A s} → Γ ⊢ A ⦂ s → Γ ⊢ A :⇒*: A ⦂ s
idRed:*: A = [ A , A , id A ]

idRedTerm:*: : ∀ {Γ A t s} → Γ ⊢ t ∷ A ⦂ s → Γ ⊢ t :⇒*: t ∷ A ⦂ s
idRedTerm:*: t = [ t , t , id t ]

-- U cannot be a term

UnotInA : ∀ {A Γ s s'} → Γ ⊢ (Univ s) ∷ A ⦂ s' → ⊥
UnotInA (conv U∷U x) = UnotInA U∷U

UnotInA[t] : ∀ {A B t a Γ s s' s'' s'''}
         → t [ a ] PE.≡ (Univ s)
         → Γ ⊢ a ∷ A ⦂ s'
         → Γ ∙ A ⦂ s'' ⊢ t ∷ B ⦂ s'''
         → ⊥
UnotInA[t] () x₁ (ℕⱼ x₂)
UnotInA[t] () x₁ (Emptyⱼ x₂)
UnotInA[t] () x₁ (Πⱼ x₂ ▹ x₃)
UnotInA[t] x₁ x₂ (var x₃ here) rewrite x₁ = UnotInA x₂
UnotInA[t] () x₂ (var x₃ (there x₄))
UnotInA[t] () x₁ (lamⱼ x₂ x₃)
UnotInA[t] () x₁ (x₂ ∘ⱼ x₃)
UnotInA[t] () x₁ (zeroⱼ x₂)
UnotInA[t] () x₁ (sucⱼ x₂)
UnotInA[t] () x₁ (natrecⱼ x₂ x₃ x₄ x₅)
UnotInA[t] () x₁ (Emptyrecⱼ x₂ x₃)
UnotInA[t] x x₁ (conv x₂ x₃) = UnotInA[t] x x₁ x₂

postulate RewSR : ∀ {Γ A s k l r p u} → (d : Rew⊢ k ⊚ l ⇒ r) → Γ ⊢ Rew.lhs-ctx d Γ p u ∷ A ⦂ s → Γ ⊢ Rew.rhs-ctx d Γ p u ∷ A ⦂ s

redU*Term′ : ∀ {A B U′ Γ s s'} → U′ PE.≡ (Univ s) → Γ ⊢ A ⇒ U′ ∷ B ⦂ s' → ⊥
redU*Term′ U′≡U (conv A⇒U x) = redU*Term′ U′≡U A⇒U
redU*Term′ () (app-subst A⇒U x)
redU*Term′ U′≡U (β-red x x₁ x₂) = UnotInA[t] U′≡U x₂ x₁
redU*Term′ () (natrec-subst x x₁ x₂ A⇒U)
redU*Term′ U′≡U (natrec-zero x x₁ x₂) rewrite U′≡U = UnotInA x₁
redU*Term′ () (natrec-suc x x₁ x₂ x₃)
redU*Term′ () (Emptyrec-subst x A⇒U)
redU*Term′ U′≡U (rew ka⇒t _ ⊢ka eqrhs eqlhs) rewrite U′≡U =
  UnotInA (PE.subst (λ t → _ ⊢ t ∷ _ ⦂ _) (PE.sym eqrhs) (RewSR ka⇒t ⊢ka))

redU*Term : ∀ {A B Γ s s'} → Γ ⊢ A ⇒* (Univ s) ∷ B ⦂ s' → ⊥
redU*Term (id x) = UnotInA x
redU*Term (x ⇨ A⇒*U) = redU*Term A⇒*U

-- Nothing reduces to U

redU : ∀ {A Γ s s'} → Γ ⊢ A ⇒ (Univ s) ⦂ s' → ⊥
redU (univ x) = redU*Term′ PE.refl x

redU* : ∀ {A Γ s s'} → Γ ⊢ A ⇒* (Univ s) ⦂ s' → A PE.≡ (Univ s)
redU* (id x) = PE.refl
redU* (x ⇨ A⇒*U) rewrite redU* A⇒*U = ⊥-elim (redU x)


Univ-sort : ∀ {Γ s s'} → Γ ⊢ Univ s ⦂ s' → s' PE.≡ 𝕥y
Univ-sort (Uⱼ x) = PE.refl
Univ-sort (univ x) = ⊥-elim (UnotInA x)

cstr-cod-Univ-sort : ∀ {k s} → cstr-cod k PE.≡ Univ s → cstr-𝕊 k PE.≡ 𝕥y
cstr-cod-Univ-sort {k} kdomU =
  Univ-sort (PE.subst (λ x → ε ∙ cstr-dom k ⦂ cstr-dom-sort k ⊢ x ⦂ cstr-𝕊 k)
                      kdomU
                      (cstr-cod-wty k))
