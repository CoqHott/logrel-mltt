{-# OPTIONS --without-K --safe #-}

module Definition.Typed.Properties where

open import Definition.Untyped
open import Definition.Typed

open import Tools.Empty using (⊥; ⊥-elim)
open import Tools.Product
import Tools.PropositionalEquality as PE


-- Escape context extraction

wfTerm : ∀ {Γ A t r} → Γ ⊢ t ∷ A ^ r → ⊢ Γ
wfTerm (ℕⱼ ⊢Γ) = ⊢Γ
wfTerm (Emptyⱼ ⊢Γ) = ⊢Γ
wfTerm (Πⱼ F ▹ G) = wfTerm F
wfTerm (Σⱼ F ▹ G) = wfTerm F
wfTerm (var ⊢Γ x₁) = ⊢Γ
wfTerm (lamⱼ F t) with wfTerm t
wfTerm (lamⱼ F t) | ⊢Γ ∙ F′ = ⊢Γ
wfTerm (g ∘ⱼ a) = wfTerm a
wfTerm (⦅ t , u ⦆ⱼ) = wfTerm t
wfTerm (sigmarecⱼ A t u) = wfTerm u
wfTerm (zeroⱼ ⊢Γ) = ⊢Γ
wfTerm (sucⱼ n) = wfTerm n
wfTerm (natrecⱼ F z s n) = wfTerm z
wfTerm (Emptyrecⱼ A e) = wfTerm e
wfTerm (Idⱼ A t u) = wfTerm t
wfTerm (Idreflⱼ t) = wfTerm t
wfTerm (transpⱼ P t s u e) = wfTerm t
wfTerm (castⱼ A B e t) = wfTerm t
wfTerm (cast_reflⱼ A t) = wfTerm t
wfTerm (conv t A≡B) = wfTerm t

wf : ∀ {Γ A r} → Γ ⊢ A ^ r → ⊢ Γ
wf (ℕⱼ ⊢Γ) = ⊢Γ
wf (Emptyⱼ ⊢Γ) = ⊢Γ
wf (Uⱼ ⊢Γ) = ⊢Γ
wf (Πⱼ F ▹ G) = wf F
wf (Σⱼ F ▹ G) = wf F
wf (univ A) = wfTerm A
wf (Idⱼ A t u) = wfTerm t

wfEqTerm : ∀ {Γ A t u r} → Γ ⊢ t ≡ u ∷ A ^ r → ⊢ Γ
wfEqTerm (refl t) = wfTerm t
wfEqTerm (sym t≡u) = wfEqTerm t≡u
wfEqTerm (trans t≡u u≡r) = wfEqTerm t≡u
wfEqTerm (conv t≡u A≡B) = wfEqTerm t≡u
wfEqTerm (Π-cong F F≡H G≡E) = wfEqTerm F≡H
wfEqTerm (Σ-cong F F≡H G≡E) = wfEqTerm F≡H
wfEqTerm (app-cong f≡g a≡b) = wfEqTerm f≡g
wfEqTerm (β-red F t a) = wfTerm a
wfEqTerm (η-eq F f g f0≡g0) = wfTerm f
wfEqTerm (suc-cong n) = wfEqTerm n
wfEqTerm (natrec-cong F≡F′ z≡z′ s≡s′ n≡n′) = wfEqTerm z≡z′
wfEqTerm (natrec-zero F z s) = wfTerm z
wfEqTerm (natrec-suc n F z s) = wfTerm n
wfEqTerm (sigmarec-cong A t u) = wfEqTerm u
wfEqTerm (sigmarec-pair A t u v) = wfTerm u
wfEqTerm (Emptyrec-cong A≡A' e≡e') = wfEqTerm e≡e'
wfEqTerm (proof-irrelevance t u) = wfTerm t
wfEqTerm (Id-cong A t u) = wfEqTerm u
wfEqTerm (Id-Π A B t u) = wfTerm t
wfEqTerm (Id-ℕ-00 ⊢Γ) = ⊢Γ
wfEqTerm (Id-ℕ-SS m n) = wfTerm n
wfEqTerm (Id-U-ΠΠ A B A' B') = wfTerm A
wfEqTerm (Id-U-ℕℕ ⊢Γ) = ⊢Γ
wfEqTerm (Id-SProp A B) = wfTerm A
wfEqTerm (cast-cong A B e t) = wfEqTerm t
wfEqTerm (cast-Π A B A' B' e f) = wfTerm f
wfEqTerm (cast-ℕ-0 e) = wfTerm e
wfEqTerm (cast-ℕ-S e n) = wfTerm n

wfEq : ∀ {Γ A B r} → Γ ⊢ A ≡ B ^ r → ⊢ Γ
wfEq (univ A≡B) = wfEqTerm A≡B
wfEq (refl A) = wf A
wfEq (sym A≡B) = wfEq A≡B
wfEq (trans A≡B B≡C) = wfEq A≡B
wfEq (Π-cong F F≡H G≡E) = wfEq F≡H


-- Reduction is a subset of conversion

subsetTerm : ∀ {Γ A t u r} → Γ ⊢ t ⇒ u ∷ A ^ r → Γ ⊢ t ≡ u ∷ A ^ r
subsetTerm (natrec-subst F z s n⇒n′) =
  natrec-cong (refl F) (refl z) (refl s) (subsetTerm n⇒n′)
subsetTerm (natrec-zero F z s) = natrec-zero F z s
subsetTerm (natrec-suc n F z s) = natrec-suc n F z s
subsetTerm (sigmarec-subst A t u) = sigmarec-cong (refl A) (refl t) (subsetTerm u)
subsetTerm (sigmarec-pair A t u v) = sigmarec-pair A t u v
subsetTerm (Emptyrec-subst A n⇒n′) =
  Emptyrec-cong (refl A) (subsetTerm n⇒n′)
subsetTerm (app-subst t⇒u a) = app-cong (subsetTerm t⇒u) (refl a)
subsetTerm (β-red A t a) = β-red A t a
subsetTerm (conv t⇒u A≡B) = conv (subsetTerm t⇒u) A≡B
subsetTerm (Id-subst A t u) = Id-cong (univ (subsetTerm A)) (refl t) (refl u)
subsetTerm (Id-ℕ-subst m n) = Id-cong (refl (ℕⱼ (wfTerm n))) (subsetTerm m) (refl n)
subsetTerm (Id-ℕ-0-subst n) = let ⊢Γ = wfEqTerm (subsetTerm n) in Id-cong (refl (ℕⱼ ⊢Γ)) (refl (zeroⱼ ⊢Γ)) (subsetTerm n)
subsetTerm (Id-ℕ-S-subst m n) = Id-cong (refl (ℕⱼ (wfTerm m))) (refl (sucⱼ m)) (subsetTerm n)
subsetTerm (Id-U-subst A B) = Id-cong (refl (Uⱼ (wfTerm B))) (subsetTerm A) (refl B)
subsetTerm (Id-U-ℕ-subst B) = let ⊢Γ = wfEqTerm (subsetTerm B) in Id-cong (refl (Uⱼ ⊢Γ)) (refl (ℕⱼ ⊢Γ)) (subsetTerm B)
subsetTerm (Id-U-Π-subst A P B) = Id-cong (refl (Uⱼ (wfTerm A))) (refl (Πⱼ A ▹ P)) (subsetTerm B)
subsetTerm (Id-Π A B t u) = Id-Π A B t u
subsetTerm (Id-ℕ-00 ⊢Γ) = Id-ℕ-00 ⊢Γ
subsetTerm (Id-ℕ-SS m n) = Id-ℕ-SS m n
subsetTerm (Id-U-ΠΠ A B A' B') = Id-U-ΠΠ A B A' B'
subsetTerm (Id-U-ℕℕ ⊢Γ) = Id-U-ℕℕ ⊢Γ
subsetTerm (Id-SProp A B) = Id-SProp A B
subsetTerm (cast-subst A B e t) = cast-cong (subsetTerm A) (refl B) (refl e) (refl t)
subsetTerm (cast-ℕ-subst B e t) = cast-cong (refl (ℕⱼ (wfTerm t))) (subsetTerm B) (refl e) (refl t)
subsetTerm (cast-Π-subst A P B e t) = cast-cong (refl (Πⱼ A ▹ P)) (subsetTerm B) (refl e) (refl t)
subsetTerm (cast-Π A B A' B' e f) = cast-Π A B A' B' e f
subsetTerm (cast-ℕ-0 e) = cast-ℕ-0 e
subsetTerm (cast-ℕ-S e n) = cast-ℕ-S e n

subset : ∀ {Γ A B r} → Γ ⊢ A ⇒ B ^ r → Γ ⊢ A ≡ B ^ r
subset (univ A⇒B) = univ (subsetTerm A⇒B)

subset*Term : ∀ {Γ A t u r} → Γ ⊢ t ⇒* u ∷ A ^ r → Γ ⊢ t ≡ u ∷ A ^ r
subset*Term (id t) = refl t
subset*Term (t⇒t′ ⇨ t⇒*u) = trans (subsetTerm t⇒t′) (subset*Term t⇒*u)

subset* : ∀ {Γ A B r} → Γ ⊢ A ⇒* B ^ r → Γ ⊢ A ≡ B ^ r
subset* (id A) = refl A
subset* (A⇒A′ ⇨ A′⇒*B) = trans (subset A⇒A′) (subset* A′⇒*B)


-- Can extract left-part of a reduction

redFirstTerm : ∀ {Γ t u A r} → Γ ⊢ t ⇒ u ∷ A ^ r → Γ ⊢ t ∷ A ^ r
redFirstTerm (conv t⇒u A≡B) = conv (redFirstTerm t⇒u) A≡B
redFirstTerm (app-subst t⇒u a) = (redFirstTerm t⇒u) ∘ⱼ a
redFirstTerm (β-red A t a) = (lamⱼ A t) ∘ⱼ a
redFirstTerm (natrec-subst F z s n⇒n′) = natrecⱼ F z s (redFirstTerm n⇒n′)
redFirstTerm (natrec-zero F z s) = natrecⱼ F z s (zeroⱼ (wfTerm z))
redFirstTerm (natrec-suc n F z s) = natrecⱼ F z s (sucⱼ n)
redFirstTerm (sigmarec-subst A t u) = sigmarecⱼ A t (redFirstTerm u)
redFirstTerm (sigmarec-pair A t u v) = sigmarecⱼ A t ⦅ u , v ⦆ⱼ
redFirstTerm (Emptyrec-subst A n⇒n′) = Emptyrecⱼ A (redFirstTerm n⇒n′)
redFirstTerm (Id-subst A t u) = Idⱼ (univ (redFirstTerm A)) t u
redFirstTerm (Id-ℕ-subst m n) = Idⱼ (ℕⱼ (wfTerm n)) (redFirstTerm m) n
redFirstTerm (Id-ℕ-0-subst n) = Idⱼ (ℕⱼ (wfEqTerm (subsetTerm n))) (zeroⱼ (wfEqTerm (subsetTerm n))) (redFirstTerm n)
redFirstTerm (Id-ℕ-S-subst m n) = Idⱼ (ℕⱼ (wfTerm m)) (sucⱼ m) (redFirstTerm n)
redFirstTerm (Id-U-subst A B) = Idⱼ (Uⱼ (wfTerm B)) (redFirstTerm A) B
redFirstTerm (Id-U-ℕ-subst B) = let ⊢Γ = (wfEqTerm (subsetTerm B)) in Idⱼ (Uⱼ ⊢Γ) (ℕⱼ ⊢Γ) (redFirstTerm B)
redFirstTerm (Id-U-Π-subst A P B) = Idⱼ (Uⱼ (wfTerm A)) (Πⱼ A ▹ P) (redFirstTerm B)
redFirstTerm (Id-Π {rA = rA} A B t u) = Idⱼ (Πⱼ (univ A) ▹ B) t u
redFirstTerm (Id-ℕ-00 ⊢Γ) = Idⱼ (ℕⱼ ⊢Γ) (zeroⱼ ⊢Γ) (zeroⱼ ⊢Γ)
redFirstTerm (Id-ℕ-SS m n) = Idⱼ (ℕⱼ (wfTerm m)) (sucⱼ m) (sucⱼ n)
redFirstTerm (Id-U-ΠΠ A B A' B') = Idⱼ (Uⱼ (wfTerm A)) (Πⱼ A ▹ B) (Πⱼ A' ▹ B')
redFirstTerm (Id-U-ℕℕ ⊢Γ) = Idⱼ (Uⱼ ⊢Γ) (ℕⱼ ⊢Γ) (ℕⱼ ⊢Γ)
redFirstTerm (Id-SProp A B) = Idⱼ (Uⱼ (wfTerm A)) A B
redFirstTerm (cast-subst A B e t) = castⱼ (redFirstTerm A) B e t
redFirstTerm (cast-ℕ-subst B e t) = castⱼ (ℕⱼ (wfTerm t)) (redFirstTerm B) e t
redFirstTerm (cast-Π-subst A P B e t) = castⱼ (Πⱼ A ▹ P) (redFirstTerm B) e t
redFirstTerm (cast-Π A B A' B' e f) = castⱼ (Πⱼ A ▹ B) (Πⱼ A' ▹ B') e f
redFirstTerm (cast-ℕ-0 e) = castⱼ (ℕⱼ (wfTerm e)) (ℕⱼ (wfTerm e)) e (zeroⱼ (wfTerm e))
redFirstTerm (cast-ℕ-S e n) = castⱼ (ℕⱼ (wfTerm e)) (ℕⱼ (wfTerm e)) e (sucⱼ n)

redFirst : ∀ {Γ A B r} → Γ ⊢ A ⇒ B ^ r → Γ ⊢ A ^ r
redFirst (univ A⇒B) = univ (redFirstTerm A⇒B)

redFirst*Term : ∀ {Γ t u A r} → Γ ⊢ t ⇒* u ∷ A ^ r → Γ ⊢ t ∷ A ^ r
redFirst*Term (id t) = t
redFirst*Term (t⇒t′ ⇨ t′⇒*u) = redFirstTerm t⇒t′

redFirst* : ∀ {Γ A B r} → Γ ⊢ A ⇒* B ^ r → Γ ⊢ A ^ r
redFirst* (id A) = A
redFirst* (A⇒A′ ⇨ A′⇒*B) = redFirst A⇒A′

-- Neutral types are always small

tyNe : ∀ {Γ t r} → Γ ⊢ t ^ r → Neutral t → Γ ⊢ t ∷ (Univ r) ^ !
tyNe (univ x) tn = x
tyNe (Idⱼ A x y) tn = Idⱼ A x y

-- No neutral terms are well-formed in an empty context

noNe : ∀ {t A r} → ε ⊢ t ∷ A ^ r → Neutral t → ⊥
noNe (tj ∘ⱼ tj₁) (∘ₙ tn) = noNe tj tn
noNe (natrecⱼ x tj tj₁ tj₂) (natrecₙ tn) = noNe tj₂ tn
noNe (Emptyrecⱼ x tj) (Emptyrecₙ tn) = noNe tj tn
noNe (Idⱼ A x y) (Idₙ An) = noNe (tyNe A An) An
noNe (Idⱼ A x y) (Idℕₙ xn) = noNe x xn
noNe (Idⱼ A x y) (Idℕ0ₙ yn) = noNe y yn
noNe (Idⱼ A x y) (IdℕSₙ yn) = noNe y yn
noNe (Idⱼ A x y) (IdUₙ xn) = noNe x xn
noNe (Idⱼ A x y) (IdUℕₙ yn) = noNe y yn
noNe (Idⱼ A x y) (IdUΠₙ yn) = noNe y yn
noNe (castⱼ A B e x) (castₙ An) = noNe A An
noNe (castⱼ A B e x) (castℕₙ Bn) = noNe B Bn
noNe (castⱼ A B e x) (castΠₙ Bn) = noNe B Bn
noNe (castⱼ A B e x) (castℕℕₙ xn) = noNe x xn
noNe (conv tj x) tn = noNe tj tn


-- -- Neutrals and Whnfs do not weak head reduce

neRedTerm : ∀ {Γ t u A r} (d : Γ ⊢ t ⇒ u ∷ A ^ r) (n : Neutral t) → ⊥
neRed : ∀ {Γ A B r} (d : Γ ⊢ A ⇒ B ^ r) (N : Neutral A) → ⊥
whnfRedTerm : ∀ {Γ t u A r} (d : Γ ⊢ t ⇒ u ∷ A ^ r) (w : Whnf t) → ⊥

neRedTerm (conv tr x) tn = neRedTerm tr tn
neRedTerm (app-subst tr x) (∘ₙ tn) = neRedTerm tr tn
neRedTerm (β-red x x₁ x₂) (∘ₙ ())
neRedTerm (natrec-zero x x₁ x₂) (natrecₙ ())
neRedTerm (natrec-suc x x₁ x₂ x₃) (natrecₙ ())
neRedTerm (natrec-subst x x₁ x₂ tr) (natrecₙ tn) = neRedTerm tr tn
neRedTerm (sigmarec-subst x x₁ tr) ()
neRedTerm (sigmarec-pair x x₁ x₂ x₃) ()
neRedTerm (Emptyrec-subst x tr) (Emptyrecₙ tn) = neRedTerm tr tn
neRedTerm (Id-subst tr x y) (Idₙ tn) = neRedTerm tr tn
neRedTerm (Id-ℕ-subst tr x) (Idℕₙ tn) = neRedTerm tr tn
neRedTerm (Id-ℕ-0-subst tr) (Idℕ0ₙ tn) = neRedTerm tr tn
neRedTerm (Id-ℕ-S-subst x tr) (IdℕSₙ tn) = neRedTerm tr tn
neRedTerm (Id-U-subst tr x) (IdUₙ tn) = neRedTerm tr tn
neRedTerm (Id-U-ℕ-subst tr) (IdUℕₙ tn) = neRedTerm tr tn
neRedTerm (Id-U-Π-subst A B tr) (IdUΠₙ tn) = neRedTerm tr tn
neRedTerm (Id-subst tr x y) (Idℕₙ tn) = whnfRedTerm tr ℕₙ
neRedTerm (Id-subst tr x y) (Idℕ0ₙ tn) = whnfRedTerm tr ℕₙ
neRedTerm (Id-subst tr x y) (IdℕSₙ tn) = whnfRedTerm tr ℕₙ
neRedTerm (Id-subst tr x y) (IdUₙ tn) = whnfRedTerm tr Uₙ
neRedTerm (Id-subst tr x y) (IdUℕₙ tn) = whnfRedTerm tr Uₙ
neRedTerm (Id-subst tr x y) (IdUΠₙ tn) = whnfRedTerm tr Uₙ
neRedTerm (Id-ℕ-subst tr x) (Idℕ0ₙ tn) = whnfRedTerm tr zeroₙ
neRedTerm (Id-ℕ-subst tr x) (IdℕSₙ tn) = whnfRedTerm tr sucₙ
neRedTerm (Id-U-subst tr x) (IdUℕₙ tn) = whnfRedTerm tr ℕₙ
neRedTerm (Id-U-subst tr x) (IdUΠₙ tn) = whnfRedTerm tr Πₙ
neRedTerm (Id-Π A B t u) (Idₙ ())
neRedTerm (Id-ℕ-00 tr) (Idₙ ())
neRedTerm (Id-ℕ-00 tr) (Idℕₙ ())
neRedTerm (Id-ℕ-00 tr) (Idℕ0ₙ ())
neRedTerm (Id-ℕ-SS x tr) (Idₙ ())
neRedTerm (Id-ℕ-SS x tr) (Idℕₙ ())
neRedTerm (Id-U-ΠΠ A B A' B') (Idₙ ())
neRedTerm (Id-U-ΠΠ A B A' B') (IdUₙ ())
neRedTerm (Id-U-ΠΠ A B A' B') (IdUΠₙ ())
neRedTerm (Id-U-ℕℕ x) (Idₙ ())
neRedTerm (Id-U-ℕℕ x) (IdUₙ ())
neRedTerm (Id-U-ℕℕ x) (IdUℕₙ ())
neRedTerm (Id-SProp A B) (Idₙ ())
neRedTerm (cast-subst tr B e x) (castₙ tn) = neRedTerm tr tn
neRedTerm (cast-ℕ-subst tr e x) (castℕₙ tn) = neRedTerm tr tn
neRedTerm (cast-Π-subst A B tr e x) (castΠₙ tn) = neRedTerm tr tn
neRedTerm (cast-subst tr x x₁ x₂) (castℕₙ tn) = whnfRedTerm tr ℕₙ
neRedTerm (cast-subst tr x x₁ x₂) (castΠₙ tn) = whnfRedTerm tr Πₙ
neRedTerm (cast-subst tr x x₁ x₂) (castℕℕₙ tn) = whnfRedTerm tr ℕₙ
neRedTerm (cast-ℕ-subst tr x x₁) (castℕℕₙ tn) = whnfRedTerm tr ℕₙ
neRedTerm (cast-Π A B A' B' e f) (castₙ ())
neRedTerm (cast-Π A B A' B' e f) (castΠₙ ())
neRedTerm (cast-ℕ-0 x) (castₙ ())
neRedTerm (cast-ℕ-0 x) (castℕₙ ())
neRedTerm (cast-ℕ-0 x) (castℕℕₙ ())
neRedTerm (cast-ℕ-S x x₁) (castₙ ())
neRedTerm (cast-ℕ-S x x₁) (castℕₙ ())
neRedTerm (cast-ℕ-S x x₁) (castℕℕₙ ())

neRed (univ x) N = neRedTerm x N

whnfRedTerm (conv d x) w = whnfRedTerm d w
whnfRedTerm (app-subst d x) (ne (∘ₙ x₁)) = neRedTerm d x₁
whnfRedTerm (β-red x x₁ x₂) (ne (∘ₙ ()))
whnfRedTerm (natrec-subst x x₁ x₂ d) (ne (natrecₙ x₃)) = neRedTerm d x₃
whnfRedTerm (natrec-zero x x₁ x₂) (ne (natrecₙ ()))
whnfRedTerm (natrec-suc x x₁ x₂ x₃) (ne (natrecₙ ()))
whnfRedTerm (Emptyrec-subst x d) (ne (Emptyrecₙ x₂)) = neRedTerm d x₂
whnfRedTerm (sigmarec-subst x x₁ d) (ne ())
whnfRedTerm (sigmarec-pair x x₁ x₂ d) (ne ())
whnfRedTerm (Id-subst d x x₁) (ne (Idₙ x₂)) = neRedTerm d x₂
whnfRedTerm (Id-subst d x x₁) (ne (Idℕₙ x₂)) = whnfRedTerm d ℕₙ
whnfRedTerm (Id-subst d x x₁) (ne (Idℕ0ₙ x₂)) = whnfRedTerm d ℕₙ
whnfRedTerm (Id-subst d x x₁) (ne (IdℕSₙ x₂)) = whnfRedTerm d ℕₙ
whnfRedTerm (Id-subst d x x₁) (ne (IdUₙ x₂)) = whnfRedTerm d Uₙ
whnfRedTerm (Id-subst d x x₁) (ne (IdUℕₙ x₂)) = whnfRedTerm d Uₙ
whnfRedTerm (Id-subst d x x₁) (ne (IdUΠₙ x₂)) = whnfRedTerm d Uₙ
whnfRedTerm (Id-ℕ-subst d x) (ne (Idℕₙ x₁)) = neRedTerm d x₁
whnfRedTerm (Id-ℕ-subst d x) (ne (Idℕ0ₙ x₁)) = whnfRedTerm d zeroₙ
whnfRedTerm (Id-ℕ-subst d x) (ne (IdℕSₙ x₁)) = whnfRedTerm d sucₙ
whnfRedTerm (Id-ℕ-0-subst d) (ne (Idℕ0ₙ x)) = neRedTerm d x
whnfRedTerm (Id-ℕ-S-subst x d) (ne (IdℕSₙ x₁)) = neRedTerm d x₁
whnfRedTerm (Id-U-subst d x) (ne (IdUₙ x₁)) = neRedTerm d x₁
whnfRedTerm (Id-U-subst d x) (ne (IdUℕₙ x₁)) = whnfRedTerm d ℕₙ
whnfRedTerm (Id-U-subst d x) (ne (IdUΠₙ x₁)) = whnfRedTerm d Πₙ
whnfRedTerm (Id-U-ℕ-subst d) (ne (IdUℕₙ x)) = neRedTerm d x
whnfRedTerm (Id-U-Π-subst x x₁ d) (ne (IdUΠₙ x₂)) = neRedTerm d x₂
whnfRedTerm (Id-Π x x₁ x₂ x₃) (ne (Idₙ ()))
whnfRedTerm (Id-ℕ-00 x) (ne (Idₙ ()))
whnfRedTerm (Id-ℕ-00 x) (ne (Idℕₙ ()))
whnfRedTerm (Id-ℕ-00 x) (ne (Idℕ0ₙ ()))
whnfRedTerm (Id-ℕ-SS x x₁) (ne (Idₙ ()))
whnfRedTerm (Id-ℕ-SS x x₁) (ne (Idℕₙ ()))
whnfRedTerm (Id-ℕ-SS x x₁) (ne (IdℕSₙ ()))
whnfRedTerm (Id-U-ΠΠ x x₁ x₂ x₃) (ne (Idₙ ()))
whnfRedTerm (Id-U-ΠΠ x x₁ x₂ x₃) (ne (IdUₙ ()))
whnfRedTerm (Id-U-ΠΠ x x₁ x₂ x₃) (ne (IdUΠₙ ()))
whnfRedTerm (Id-U-ℕℕ x) (ne (Idₙ ()))
whnfRedTerm (Id-U-ℕℕ x) (ne (IdUₙ ()))
whnfRedTerm (Id-U-ℕℕ x) (ne (IdUℕₙ ()))
whnfRedTerm (Id-SProp x x₁) (ne (Idₙ ()))
whnfRedTerm (cast-subst d x x₁ x₂) (ne (castₙ x₃)) = neRedTerm d x₃
whnfRedTerm (cast-subst d x x₁ x₂) (ne (castℕₙ x₃)) = whnfRedTerm d ℕₙ
whnfRedTerm (cast-subst d x x₁ x₂) (ne (castΠₙ x₃)) = whnfRedTerm d Πₙ
whnfRedTerm (cast-subst d x x₁ x₂) (ne (castℕℕₙ x₃)) = whnfRedTerm d ℕₙ
whnfRedTerm (cast-ℕ-subst d x x₁) (ne (castℕₙ x₂)) = neRedTerm d x₂
whnfRedTerm (cast-ℕ-subst d x x₁) (ne (castℕℕₙ x₂)) = whnfRedTerm d ℕₙ
whnfRedTerm (cast-Π-subst x x₁ d x₂ x₃) (ne (castΠₙ x₄)) = neRedTerm d x₄
whnfRedTerm (cast-Π x x₁ x₂ x₃ x₄ x₅) (ne (castₙ ()))
whnfRedTerm (cast-Π x x₁ x₂ x₃ x₄ x₅) (ne (castΠₙ ()))
whnfRedTerm (cast-ℕ-0 x) (ne (castₙ ()))
whnfRedTerm (cast-ℕ-0 x) (ne (castℕₙ ()))
whnfRedTerm (cast-ℕ-0 x) (ne (castℕℕₙ ()))
whnfRedTerm (cast-ℕ-S x x₁) (ne (castₙ ()))
whnfRedTerm (cast-ℕ-S x x₁) (ne (castℕₙ ()))
whnfRedTerm (cast-ℕ-S x x₁) (ne (castℕℕₙ ()))

whnfRed : ∀ {Γ A B r} (d : Γ ⊢ A ⇒ B ^ r) (w : Whnf A) → ⊥
whnfRed (univ x) w = whnfRedTerm x w

whnfRed*Term : ∀ {Γ t u A r} (d : Γ ⊢ t ⇒* u ∷ A ^ r) (w : Whnf t) → t PE.≡ u
whnfRed*Term (id x) Uₙ = PE.refl
whnfRed*Term (id x) Πₙ = PE.refl
whnfRed*Term (id x) Σₙ = PE.refl
whnfRed*Term (id x) ℕₙ = PE.refl
whnfRed*Term (id x) Emptyₙ = PE.refl
whnfRed*Term (id x) lamₙ = PE.refl
whnfRed*Term (id x) zeroₙ = PE.refl
whnfRed*Term (id x) sucₙ = PE.refl
whnfRed*Term (id x) (ne x₁) = PE.refl
whnfRed*Term (conv x x₁ ⇨ d) w = ⊥-elim (whnfRedTerm x w)
whnfRed*Term (x ⇨ d) (ne x₁) = ⊥-elim (neRedTerm x x₁)

whnfRed* : ∀ {Γ A B r} (d : Γ ⊢ A ⇒* B ^ r) (w : Whnf A) → A PE.≡ B
whnfRed* (id x) w = PE.refl
whnfRed* (x ⇨ d) w = ⊥-elim (whnfRed x w)

-- -- Whr is deterministic
-- -- this is straight up false with our subst rules for Idℕ, IdU and cast
-- -- Of course, we can reduce the second iff the first is a Whnf
-- whrDetTerm : ∀{Γ t u A u′ A′ r r'} (d : Γ ⊢ t ⇒ u ∷ A ^ r) (d′ : Γ ⊢ t ⇒ u′ ∷ A′ ^ r') → u PE.≡ u′
-- whrDetTerm (conv d x) d′ = whrDetTerm d d′
-- whrDetTerm d (conv d′ x₁) = whrDetTerm d d′
-- whrDetTerm (app-subst d x) (app-subst d′ x₁) rewrite whrDetTerm d d′ = PE.refl
-- whrDetTerm (app-subst d x) (β-red x₁ x₂ x₃) = ⊥-elim (whnfRedTerm d lamₙ)
-- whrDetTerm (β-red x x₁ x₂) (app-subst d x₃) = ⊥-elim (whnfRedTerm d lamₙ)
-- whrDetTerm (β-red x x₁ x₂) (β-red x₃ x₄ x₅) = PE.refl
-- whrDetTerm (natrec-subst x x₁ x₂ d) (natrec-subst x₃ x₄ x₅ d′) rewrite whrDetTerm d d′ = PE.refl
-- whrDetTerm (natrec-subst x x₁ x₂ d) (natrec-zero x₃ x₄ x₅) = ⊥-elim (whnfRedTerm d zeroₙ)
-- whrDetTerm (natrec-subst x x₁ x₂ d) (natrec-suc x₃ x₄ x₅ x₆) = ⊥-elim (whnfRedTerm d sucₙ)
-- whrDetTerm (natrec-zero x x₁ x₂) (natrec-subst x₃ x₄ x₅ d′) = ⊥-elim (whnfRedTerm d′ zeroₙ)
-- whrDetTerm (natrec-zero x x₁ x₂) (natrec-zero x₃ x₄ x₅) = PE.refl
-- whrDetTerm (natrec-suc x x₁ x₂ x₃) (natrec-subst x₄ x₅ x₆ d′) = ⊥-elim (whnfRedTerm d′ sucₙ)
-- whrDetTerm (natrec-suc x x₁ x₂ x₃) (natrec-suc x₄ x₅ x₆ x₇) = PE.refl
-- whrDetTerm (Emptyrec-subst x d) (Emptyrec-subst x₂ d′) rewrite whrDetTerm d d′ = PE.refl

-- whrDet : ∀{Γ A B B′ r r'} (d : Γ ⊢ A ⇒ B ^ r) (d′ : Γ ⊢ A ⇒ B′ ^ r') → B PE.≡ B′
-- whrDet (univ x) (univ x₁) = whrDetTerm x x₁

-- whrDet↘Term : ∀{Γ t u A u′ r r'} (d : Γ ⊢ t ↘ u ∷ A ^ r) (d′ : Γ ⊢ t ⇒* u′ ∷ A ^ r')
--   → Γ ⊢ u′ ⇒* u ∷ A ^ r
-- whrDet↘Term (proj₁ , proj₂) (id x) = proj₁
-- whrDet↘Term (id x , proj₂) (x₁ ⇨ d′) = ⊥-elim (whnfRedTerm x₁ proj₂)
-- whrDet↘Term (x ⇨ proj₁ , proj₂) (x₁ ⇨ d′) =
--   whrDet↘Term (PE.subst (λ x₂ → _ ⊢ x₂ ↘ _ ∷ _ ^ _) (whrDetTerm x x₁) (proj₁ , proj₂)) d′

-- whrDet*Term : ∀{Γ t u A A' u′ r r'} (d : Γ ⊢ t ↘ u ∷ A ^ r) (d′ : Γ ⊢ t ↘ u′ ∷ A' ^ r') → u PE.≡ u′
-- whrDet*Term (id x , proj₂) (id x₁ , proj₄) = PE.refl
-- whrDet*Term (id x , proj₂) (x₁ ⇨ proj₃ , proj₄) = ⊥-elim (whnfRedTerm x₁ proj₂)
-- whrDet*Term (x ⇨ proj₁ , proj₂) (id x₁ , proj₄) = ⊥-elim (whnfRedTerm x proj₄)
-- whrDet*Term (x ⇨ proj₁ , proj₂) (x₁ ⇨ proj₃ , proj₄) =
--   whrDet*Term (proj₁ , proj₂) (PE.subst (λ x₂ → _ ⊢ x₂ ↘ _ ∷ _ ^ _)
--                                     (whrDetTerm x₁ x) (proj₃ , proj₄))

-- whrDet* : ∀{Γ A B B′ r r'} (d : Γ ⊢ A ↘ B ^ r) (d′ : Γ ⊢ A ↘ B′ ^ r') → B PE.≡ B′
-- whrDet* (id x , proj₂) (id x₁ , proj₄) = PE.refl
-- whrDet* (id x , proj₂) (x₁ ⇨ proj₃ , proj₄) = ⊥-elim (whnfRed x₁ proj₂)
-- whrDet* (x ⇨ proj₁ , proj₂) (id x₁ , proj₄) = ⊥-elim (whnfRed x proj₄)
-- whrDet* (A⇒A′ ⇨ A′⇒*B , whnfB) (A⇒A″ ⇨ A″⇒*B′ , whnfB′) =
--   whrDet* (A′⇒*B , whnfB) (PE.subst (λ x → _ ⊢ x ↘ _ ^ _)
--                                      (whrDet A⇒A″ A⇒A′)
--                                      (A″⇒*B′ , whnfB′))

-- -- Identity of syntactic reduction

-- idRed:*: : ∀ {Γ A r} → Γ ⊢ A ^ r → Γ ⊢ A :⇒*: A ^ r
-- idRed:*: A = [ A , A , id A ]

-- idRedTerm:*: : ∀ {Γ A t r} → Γ ⊢ t ∷ A ^ r → Γ ⊢ t :⇒*: t ∷ A ^ r
-- idRedTerm:*: t = [ t , t , id t ]

-- -- U cannot be a term

-- UnotInA : ∀ {A Γ r r'} → Γ ⊢ (Univ r) ∷ A ^ r' → ⊥
-- UnotInA (conv U∷U x) = UnotInA U∷U

-- UnotInA[t] : ∀ {A B t a Γ r r' r'' r'''}
--          → t [ a ] PE.≡ (Univ r)
--          → Γ ⊢ a ∷ A ^ r'
--          → Γ ∙ A ^ r'' ⊢ t ∷ B ^ r'''
--          → ⊥
-- UnotInA[t] () x₁ (ℕⱼ x₂)
-- UnotInA[t] () x₁ (Emptyⱼ x₂)
-- UnotInA[t] () x₁ (Πⱼ x₂ ▹ x₃)
-- UnotInA[t] x₁ x₂ (var x₃ here) rewrite x₁ = UnotInA x₂
-- UnotInA[t] () x₂ (var x₃ (there x₄))
-- UnotInA[t] () x₁ (lamⱼ x₂ x₃)
-- UnotInA[t] () x₁ (x₂ ∘ⱼ x₃)
-- UnotInA[t] () x₁ (zeroⱼ x₂)
-- UnotInA[t] () x₁ (sucⱼ x₂)
-- UnotInA[t] () x₁ (natrecⱼ x₂ x₃ x₄ x₅)
-- UnotInA[t] () x₁ (Emptyrecⱼ x₂ x₃)
-- UnotInA[t] x x₁ (conv x₂ x₃) = UnotInA[t] x x₁ x₂

-- redU*Term′ : ∀ {A B U′ Γ r r'} → U′ PE.≡ (Univ r) → Γ ⊢ A ⇒ U′ ∷ B ^ r' → ⊥
-- redU*Term′ U′≡U (conv A⇒U x) = redU*Term′ U′≡U A⇒U
-- redU*Term′ () (app-subst A⇒U x)
-- redU*Term′ U′≡U (β-red x x₁ x₂) = UnotInA[t] U′≡U x₂ x₁
-- redU*Term′ () (natrec-subst x x₁ x₂ A⇒U)
-- redU*Term′ U′≡U (natrec-zero x x₁ x₂) rewrite U′≡U = UnotInA x₁
-- redU*Term′ () (natrec-suc x x₁ x₂ x₃)
-- redU*Term′ () (Emptyrec-subst x A⇒U)

-- redU*Term : ∀ {A B Γ r r'} → Γ ⊢ A ⇒* (Univ r) ∷ B ^ r' → ⊥
-- redU*Term (id x) = UnotInA x
-- redU*Term (x ⇨ A⇒*U) = redU*Term A⇒*U

-- -- Nothing reduces to U

-- redU : ∀ {A Γ r r'} → Γ ⊢ A ⇒ (Univ r) ^ r' → ⊥
-- redU (univ x) = redU*Term′ PE.refl x

-- redU* : ∀ {A Γ r r'} → Γ ⊢ A ⇒* (Univ r) ^ r' → A PE.≡ (Univ r)
-- redU* (id x) = PE.refl
-- redU* (x ⇨ A⇒*U) rewrite redU* A⇒*U = ⊥-elim (redU x)
