{-# OPTIONS  --safe #-}

module Definition.Typed.Properties where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.RedSteps
import Definition.Typed.Weakening as Twk

open import Tools.Empty using (⊥; ⊥-elim)
open import Tools.Product
open import Tools.Sum hiding (id ; sym)
import Tools.PropositionalEquality as PE

import Data.Fin as Fin
import Data.Nat as Nat

-- Escape context extraction

wfTerm : ∀ {Γ A t r} → Γ ⊢ t ∷ A ^ r → ⊢ Γ
wfTerm (univ <l ⊢Γ) = ⊢Γ
wfTerm (ℕⱼ ⊢Γ) = ⊢Γ
wfTerm (Emptyⱼ ⊢Γ) = ⊢Γ
wfTerm (Πⱼ <l ▹ <l' ▹ F ▹ G) = wfTerm F
wfTerm (∃ⱼ F ▹ G) = wfTerm F
wfTerm (var ⊢Γ x₁) = ⊢Γ
wfTerm (lamⱼ _ _ F t) with wfTerm t
wfTerm (lamⱼ _ _ F t) | ⊢Γ ∙ F′ = ⊢Γ
wfTerm (g ∘ⱼ a) = wfTerm a
wfTerm (⦅ F , G , t , u ⦆ⱼ) = wfTerm t
wfTerm (fstⱼ A B t) = wfTerm t
wfTerm (sndⱼ A B t) = wfTerm t
wfTerm (zeroⱼ ⊢Γ) = ⊢Γ
wfTerm (sucⱼ n) = wfTerm n
wfTerm (natrecⱼ F z s n) = wfTerm z
wfTerm (Emptyrecⱼ A e) = wfTerm e
wfTerm (Idⱼ A t u) = wfTerm t
wfTerm (Idreflⱼ t) = wfTerm t
wfTerm (transpⱼ A P t s u e) = wfTerm t
wfTerm (castⱼ A B e t) = wfTerm t
wfTerm (castreflⱼ A t) = wfTerm t
wfTerm (conv t A≡B) = wfTerm t

wf : ∀ {Γ A r} → Γ ⊢ A ^ r → ⊢ Γ
wf (Uⱼ ⊢Γ) = ⊢Γ
wf (univ A) = wfTerm A

mutual
  wfEqTerm : ∀ {Γ A t u r} → Γ ⊢ t ≡ u ∷ A ^ r → ⊢ Γ
  wfEqTerm (refl t) = wfTerm t
  wfEqTerm (sym t≡u) = wfEqTerm t≡u
  wfEqTerm (trans t≡u u≡r) = wfEqTerm t≡u
  wfEqTerm (conv t≡u A≡B) = wfEqTerm t≡u
  wfEqTerm (Π-cong _ _ F F≡H G≡E) = wfEqTerm F≡H
  wfEqTerm (∃-cong F F≡H G≡E) = wfEqTerm F≡H
  wfEqTerm (app-cong f≡g a≡b) = wfEqTerm f≡g
  wfEqTerm (β-red F t a) = wfTerm a
  wfEqTerm (η-eq _ _ F f g f0≡g0) = wfTerm f
  wfEqTerm (suc-cong n) = wfEqTerm n
  wfEqTerm (natrec-cong F≡F′ z≡z′ s≡s′ n≡n′) = wfEqTerm z≡z′
  wfEqTerm (natrec-zero F z s) = wfTerm z
  wfEqTerm (natrec-suc n F z s) = wfTerm n
  wfEqTerm (Emptyrec-cong A≡A' _ _) = wfEq A≡A'
  wfEqTerm (proof-irrelevance t u) = wfTerm t
  wfEqTerm (Id-cong A t u) = wfEqTerm u
  wfEqTerm (Id-Π _ _ A B t u) = wfTerm t
  wfEqTerm (Id-ℕ-00 ⊢Γ) = ⊢Γ
  wfEqTerm (Id-ℕ-SS m n) = wfTerm n
  wfEqTerm (Id-U-ΠΠ A B A' B') = wfTerm A
  wfEqTerm (Id-U-ℕℕ ⊢Γ) = ⊢Γ
  wfEqTerm (Id-SProp A B) = wfTerm A
  wfEqTerm (Id-ℕ-0S n) = wfTerm n
  wfEqTerm (Id-ℕ-S0 n) = wfTerm n
  wfEqTerm (Id-U-ℕΠ A B) = wfTerm A
  wfEqTerm (Id-U-Πℕ A B) = wfTerm A
  wfEqTerm (cast-cong A B t _ _) = wfEqTerm t
  wfEqTerm (cast-Π A B A' B' e f) = wfTerm f
  wfEqTerm (cast-ℕ-0 e) = wfTerm e
  wfEqTerm (cast-ℕ-S e n) = wfTerm n

  wfEq : ∀ {Γ A B r} → Γ ⊢ A ≡ B ^ r → ⊢ Γ
  wfEq (univ A≡B) = wfEqTerm A≡B
  wfEq (refl A) = wf A
  wfEq (sym A≡B) = wfEq A≡B
  wfEq (trans A≡B B≡C) = wfEq A≡B

-- Reduction is a subset of conversion

subsetTerm : ∀ {Γ A t u l} → Γ ⊢ t ⇒ u ∷ A ^ l → Γ ⊢ t ≡ u ∷ A ^ [ ! , l ]
subset : ∀ {Γ A B r} → Γ ⊢ A ⇒ B ^ r → Γ ⊢ A ≡ B ^ r

subsetTerm (natrec-subst F z s n⇒n′) =
  natrec-cong (refl F) (refl z) (refl s) (subsetTerm n⇒n′)
subsetTerm (natrec-zero F z s) = natrec-zero F z s
subsetTerm (natrec-suc n F z s) = natrec-suc n F z s
subsetTerm (app-subst {rA = !} t⇒u a) = app-cong (subsetTerm t⇒u) (refl a)
subsetTerm (app-subst {rA = %} t⇒u a) = app-cong (subsetTerm t⇒u) (proof-irrelevance a a)
subsetTerm (β-red A t a) = β-red A t a
subsetTerm (conv t⇒u A≡B) = conv (subsetTerm t⇒u) A≡B
subsetTerm (Id-subst A t u) = Id-cong (subsetTerm A) (refl t) (refl u)
subsetTerm (Id-ℕ-subst m n) = Id-cong (refl (ℕⱼ (wfTerm n))) (subsetTerm m) (refl n)
subsetTerm (Id-ℕ-0-subst n) = let ⊢Γ = wfEqTerm (subsetTerm n) in Id-cong (refl (ℕⱼ ⊢Γ)) (refl (zeroⱼ ⊢Γ)) (subsetTerm n)
subsetTerm (Id-ℕ-S-subst m n) = Id-cong (refl (ℕⱼ (wfTerm m))) (refl (sucⱼ m)) (subsetTerm n)
subsetTerm (Id-U-subst A B) = Id-cong (refl (univ 0<1 (wfTerm B))) (subsetTerm A) (refl B)
subsetTerm (Id-U-ℕ-subst B) = let ⊢Γ = wfEqTerm (subsetTerm B) in Id-cong (refl (univ 0<1 ⊢Γ)) (refl (ℕⱼ ⊢Γ)) (subsetTerm B)
subsetTerm (Id-U-Π-subst A P B) = Id-cong (refl (univ 0<1 (wfTerm A))) (refl (Πⱼ (≡is≤ PE.refl) ▹ (≡is≤ PE.refl) ▹ A ▹ P)) (subsetTerm B)
subsetTerm (Id-Π <l <l' A B t u) = Id-Π <l <l' A B t u
subsetTerm (Id-ℕ-00 ⊢Γ) = Id-ℕ-00 ⊢Γ
subsetTerm (Id-ℕ-SS m n) = Id-ℕ-SS m n
subsetTerm (Id-U-ΠΠ A B A' B') = Id-U-ΠΠ A B A' B'
subsetTerm (Id-U-ℕℕ ⊢Γ) = Id-U-ℕℕ ⊢Γ
subsetTerm (Id-SProp A B) = Id-SProp A B
subsetTerm (Id-ℕ-0S n) = Id-ℕ-0S n
subsetTerm (Id-ℕ-S0 n) = Id-ℕ-S0 n
subsetTerm (Id-U-ℕΠ A B) = Id-U-ℕΠ A B
subsetTerm (Id-U-Πℕ A B) = Id-U-Πℕ A B
subsetTerm (cast-subst A B e t) = let ⊢Γ = wfEqTerm (subsetTerm A)
                                  in cast-cong (subsetTerm A) (refl B) (refl t) e (conv e (univ (Id-cong (refl (univ 0<1 ⊢Γ)) (subsetTerm A) (refl B))))
subsetTerm (cast-ℕ-subst B e t) = let ⊢Γ = wfEqTerm (subsetTerm B)
                                  in cast-cong (refl (ℕⱼ (wfTerm t))) (subsetTerm B) (refl t) e (conv e (univ (Id-cong (refl (univ 0<1 ⊢Γ)) (refl (ℕⱼ ⊢Γ)) (subsetTerm B))))
subsetTerm (cast-Π-subst A P B e t) = let ⊢Γ = wfTerm A
                                      in cast-cong (refl (Πⱼ (≡is≤ PE.refl) ▹ (≡is≤ PE.refl) ▹ A ▹ P)) (subsetTerm B) (refl t) e
                                                   (conv e (univ (Id-cong (refl (univ 0<1 ⊢Γ)) (refl (Πⱼ ≡is≤ PE.refl ▹ ≡is≤ PE.refl ▹ A ▹ P)) (subsetTerm B) )))
subsetTerm (cast-Π A B A' B' e f) = cast-Π A B A' B' e f
subsetTerm (cast-ℕ-0 e) = cast-ℕ-0 e
subsetTerm (cast-ℕ-S e n) = cast-ℕ-S e n
subsetTerm (cast-ℕ-cong e n) = let ⊢Γ = wfTerm e
                                   ⊢ℕ = ℕⱼ ⊢Γ
                               in cast-cong (refl ⊢ℕ) (refl ⊢ℕ) (subsetTerm n) e e

subset (univ A⇒B) = univ (subsetTerm A⇒B)

subset*Term : ∀ {Γ A t u l } → Γ ⊢ t ⇒* u ∷ A ^ l → Γ ⊢ t ≡ u ∷ A ^ [ ! , l ]
subset*Term (id t) = refl t
subset*Term (t⇒t′ ⇨ t⇒*u) = trans (subsetTerm t⇒t′) (subset*Term t⇒*u)

subset* : ∀ {Γ A B r} → Γ ⊢ A ⇒* B ^ r → Γ ⊢ A ≡ B ^ r
subset* (id A) = refl A
subset* (A⇒A′ ⇨ A′⇒*B) = trans (subset A⇒A′) (subset* A′⇒*B)

-- Transitivity of reduction

transTerm⇒* : ∀ {Γ A t u v l } → Γ ⊢ t ⇒* u ∷ A ^ l → Γ ⊢ u ⇒* v ∷ A ^ l → Γ ⊢ t ⇒* v ∷ A ^ l
transTerm⇒* (id x) y = y
transTerm⇒* (x ⇨ x₁) y = x ⇨ transTerm⇒* x₁ y

trans⇒* : ∀ {Γ A B C r} → Γ ⊢ A ⇒* B ^ r → Γ ⊢ B ⇒* C ^ r → Γ ⊢ A ⇒* C ^ r
trans⇒* (id x) y = y
trans⇒* (x ⇨ x₁) y = x ⇨ trans⇒* x₁ y

transTerm:⇒:* : ∀ {Γ A t u v l } → Γ ⊢ t :⇒*: u ∷ A ^ l → Γ ⊢ u :⇒*: v ∷ A ^ l → Γ ⊢ t :⇒*: v ∷ A ^ l
transTerm:⇒:* [[ ⊢t , ⊢u , d ]] [[ ⊢t₁ , ⊢u₁ , d₁ ]] = [[ ⊢t , ⊢u₁ , (transTerm⇒* d d₁) ]]

conv⇒* : ∀ {Γ A B l t u} → Γ ⊢ t ⇒* u ∷ A ^ l → Γ ⊢ A ≡ B ^ [ ! , l ] → Γ ⊢ t ⇒* u ∷ B ^ l
conv⇒* (id x) e = id (conv x e)
conv⇒* (x ⇨ D) e = conv x e ⇨ conv⇒* D e

conv:⇒*: : ∀ {Γ A B l t u} → Γ ⊢ t :⇒*: u ∷ A ^ l → Γ ⊢ A ≡ B ^ [ ! , l ] → Γ ⊢ t :⇒*: u ∷ B ^ l
conv:⇒*: [[ ⊢t , ⊢u , d ]] e = [[ (conv ⊢t e) , (conv ⊢u e) , (conv⇒* d e) ]]


-- Can extract left-part of a reduction

redFirstTerm : ∀ {Γ t u A l } → Γ ⊢ t ⇒ u ∷ A ^ l → Γ ⊢ t ∷ A ^ [ ! , l ]
redFirst : ∀ {Γ A B r} → Γ ⊢ A ⇒ B ^ r → Γ ⊢ A ^ r

redFirstTerm (conv t⇒u A≡B) = conv (redFirstTerm t⇒u) A≡B
redFirstTerm (app-subst t⇒u a) = (redFirstTerm t⇒u) ∘ⱼ a
redFirstTerm (β-red {lA = lA} {lB = lB} ⊢A ⊢t ⊢a) = let _ , ( lA< , lB< ) = maxLevel lA lB in (lamⱼ lA< lB< ⊢A ⊢t) ∘ⱼ ⊢a
redFirstTerm (natrec-subst F z s n⇒n′) = natrecⱼ F z s (redFirstTerm n⇒n′)
redFirstTerm (natrec-zero F z s) = natrecⱼ F z s (zeroⱼ (wfTerm z))
redFirstTerm (natrec-suc n F z s) = natrecⱼ F z s (sucⱼ n)
redFirstTerm (Id-subst A t u) = Idⱼ (redFirstTerm A) t u
redFirstTerm (Id-ℕ-subst m n) = Idⱼ (ℕⱼ (wfTerm n)) (redFirstTerm m) n
redFirstTerm (Id-ℕ-0-subst n) = Idⱼ (ℕⱼ (wfEqTerm (subsetTerm n))) (zeroⱼ (wfEqTerm (subsetTerm n))) (redFirstTerm n)
redFirstTerm (Id-ℕ-S-subst m n) = Idⱼ (ℕⱼ (wfTerm m)) (sucⱼ m) (redFirstTerm n)
redFirstTerm (Id-U-subst A B) = Idⱼ (univ 0<1 (wfTerm B)) (redFirstTerm A) B
redFirstTerm (Id-U-ℕ-subst B) = let ⊢Γ = (wfEqTerm (subsetTerm B)) in Idⱼ (univ 0<1 ⊢Γ) (ℕⱼ ⊢Γ) (redFirstTerm B)
redFirstTerm (Id-U-Π-subst A P B) = Idⱼ (univ 0<1 (wfTerm A)) (Πⱼ (≡is≤ PE.refl) ▹ (≡is≤ PE.refl) ▹ A ▹ P) (redFirstTerm B)
redFirstTerm (Id-Π {rA = rA} <l <l' A B t u) = Idⱼ (Πⱼ <l ▹ <l' ▹ A ▹ B) t u
redFirstTerm (Id-ℕ-00 ⊢Γ) = Idⱼ (ℕⱼ ⊢Γ) (zeroⱼ ⊢Γ) (zeroⱼ ⊢Γ)
redFirstTerm (Id-ℕ-SS m n) = Idⱼ (ℕⱼ (wfTerm m)) (sucⱼ m) (sucⱼ n)
redFirstTerm (Id-U-ΠΠ A B A' B') = Idⱼ (univ 0<1 (wfTerm A)) (Πⱼ (≡is≤ PE.refl) ▹ (≡is≤ PE.refl) ▹ A ▹ B) (Πⱼ (≡is≤ PE.refl) ▹ (≡is≤ PE.refl) ▹ A' ▹ B')
redFirstTerm (Id-U-ℕℕ ⊢Γ) = Idⱼ (univ 0<1 ⊢Γ) (ℕⱼ ⊢Γ) (ℕⱼ ⊢Γ)
redFirstTerm (Id-SProp A B) = Idⱼ (univ 0<1 (wfTerm A)) A B
redFirstTerm (Id-ℕ-0S n) = Idⱼ (ℕⱼ (wfTerm n)) (zeroⱼ (wfTerm n)) (sucⱼ n)
redFirstTerm (Id-ℕ-S0 n) = Idⱼ (ℕⱼ (wfTerm n)) (sucⱼ n) (zeroⱼ (wfTerm n))
redFirstTerm (Id-U-ℕΠ A B) = Idⱼ (univ 0<1 (wfTerm A)) (ℕⱼ (wfTerm A)) (Πⱼ (≡is≤ PE.refl) ▹ (≡is≤ PE.refl) ▹ A ▹ B)
redFirstTerm (Id-U-Πℕ A B) = Idⱼ (univ 0<1 (wfTerm A)) (Πⱼ (≡is≤ PE.refl) ▹ (≡is≤ PE.refl) ▹ A ▹ B) (ℕⱼ (wfTerm A))
redFirstTerm (cast-subst A B e t) = castⱼ (redFirstTerm A) B e t
redFirstTerm (cast-ℕ-subst B e t) = castⱼ (ℕⱼ (wfTerm t)) (redFirstTerm B) e t
redFirstTerm (cast-Π-subst A P B e t) = castⱼ (Πⱼ (≡is≤ PE.refl) ▹ (≡is≤ PE.refl) ▹ A ▹ P) (redFirstTerm B) e t
redFirstTerm (cast-Π A B A' B' e f) = castⱼ (Πⱼ (≡is≤ PE.refl) ▹ (≡is≤ PE.refl) ▹ A ▹ B) (Πⱼ (≡is≤ PE.refl) ▹ (≡is≤ PE.refl) ▹ A' ▹ B') e f
redFirstTerm (cast-ℕ-0 e) = castⱼ (ℕⱼ (wfTerm e)) (ℕⱼ (wfTerm e)) e (zeroⱼ (wfTerm e))
redFirstTerm (cast-ℕ-S e n) = castⱼ (ℕⱼ (wfTerm e)) (ℕⱼ (wfTerm e)) e (sucⱼ n)
redFirstTerm (cast-ℕ-cong e n) = castⱼ (ℕⱼ (wfTerm e)) (ℕⱼ (wfTerm e)) e (redFirstTerm n)

redFirst (univ A⇒B) = univ (redFirstTerm A⇒B)

redFirst*Term : ∀ {Γ t u A l} → Γ ⊢ t ⇒* u ∷ A ^ l → Γ ⊢ t ∷ A ^ [ ! , l ]
redFirst*Term (id t) = t
redFirst*Term (t⇒t′ ⇨ t′⇒*u) = redFirstTerm t⇒t′

redFirst* : ∀ {Γ A B r} → Γ ⊢ A ⇒* B ^ r → Γ ⊢ A ^ r
redFirst* (id A) = A
redFirst* (A⇒A′ ⇨ A′⇒*B) = redFirst A⇒A′

-- Neutral types are always small

-- tyNe : ∀ {Γ t r} → Γ ⊢ t ^ r → Neutral t → Γ ⊢ t ∷ (Univ r) ^ !
-- tyNe (univ x) tn = x
-- tyNe (Idⱼ A x y) tn = Idⱼ A x y


-- Neutrals do not weak head reduce

neRedTerm : ∀ {Γ t u l A} (d : Γ ⊢ t ⇒ u ∷ A ^ l) (n : Neutral t) → ⊥
neRed : ∀ {Γ t u r} (d : Γ ⊢ t ⇒ u ^ r) (n : Neutral t) → ⊥
whnfRedTerm : ∀ {Γ t u A l} (d : Γ ⊢ t ⇒ u ∷ A ^ l) (w : Whnf t) → ⊥
whnfRed : ∀ {Γ A B r} (d : Γ ⊢ A ⇒ B ^ r) (w : Whnf A) → ⊥

neRedTerm (conv d x) n = neRedTerm d n
neRedTerm (app-subst d x) (∘ₙ n) = neRedTerm d n
neRedTerm (β-red x x₁ x₂) (∘ₙ ())
neRedTerm (natrec-zero x x₁ x₂) (natrecₙ ())
neRedTerm (natrec-suc x x₁ x₂ x₃) (natrecₙ ())
neRedTerm (natrec-subst x x₁ x₂ tr) (natrecₙ tn) = neRedTerm tr tn
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
neRedTerm (Id-Π _ _ A B t u) (Idₙ ())
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
neRedTerm (Id-ℕ-0S x) (Idₙ ())
neRedTerm (Id-ℕ-S0 x) (Idₙ ())
neRedTerm (Id-U-ℕΠ A B) (Idₙ ())
neRedTerm (Id-U-Πℕ A B) (Idₙ ())
neRedTerm (cast-subst tr B e x) (castₙ tn) = neRedTerm tr tn
neRedTerm (cast-ℕ-subst tr e x) (castℕₙ tn) = neRedTerm tr tn
neRedTerm (cast-Π-subst A B tr e x) (castΠₙ tn) = neRedTerm tr tn
neRedTerm (cast-Π-subst A B tr e x) (castΠℕₙ) = whnfRedTerm tr ℕₙ
neRedTerm (cast-subst tr x x₁ x₂) (castℕₙ tn) = whnfRedTerm tr ℕₙ
neRedTerm (cast-subst tr x x₁ x₂) (castΠₙ tn) = whnfRedTerm tr Πₙ
neRedTerm (cast-subst tr x x₁ x₂) (castℕℕₙ tn) = whnfRedTerm tr ℕₙ
neRedTerm (cast-subst tr x x₁ x₂) (castℕΠₙ) = whnfRedTerm tr ℕₙ
neRedTerm (cast-subst tr x x₁ x₂) (castΠℕₙ) = whnfRedTerm tr Πₙ
neRedTerm (cast-ℕ-subst tr x x₁) (castℕℕₙ tn) = whnfRedTerm tr ℕₙ
neRedTerm (cast-ℕ-subst tr x x₁) (castℕΠₙ) = whnfRedTerm tr Πₙ
neRedTerm (cast-Π A B A' B' e f) (castₙ ())
neRedTerm (cast-Π A B A' B' e f) (castΠₙ ())
neRedTerm (cast-ℕ-0 x) (castₙ ())
neRedTerm (cast-ℕ-0 x) (castℕₙ ())
neRedTerm (cast-ℕ-0 x) (castℕℕₙ ())
neRedTerm (cast-ℕ-S x x₁) (castₙ ())
neRedTerm (cast-ℕ-S x x₁) (castℕₙ ())
neRedTerm (cast-ℕ-S x x₁) (castℕℕₙ ())
neRedTerm (cast-ℕ-cong x x₁) (castₙ ())
neRedTerm (cast-ℕ-cong x x₁) (castℕₙ ())
neRedTerm (cast-ℕ-cong x x₁) (castℕℕₙ t) = neRedTerm x₁ t 
neRedTerm (cast-subst d x x₁ x₂) castΠΠ%!ₙ = whnfRedTerm d Πₙ
neRedTerm (cast-subst d x x₁ x₂) castΠΠ!%ₙ = whnfRedTerm d Πₙ
neRedTerm (cast-Π-subst x x₁ d x₂ x₃) castΠΠ%!ₙ = whnfRedTerm d Πₙ
neRedTerm (cast-Π-subst x x₁ d x₂ x₃) castΠΠ!%ₙ = whnfRedTerm d Πₙ

neRed (univ x) N = neRedTerm x N

whnfRedTerm (conv d x) w = whnfRedTerm d w
whnfRedTerm (app-subst d x) (ne (∘ₙ x₁)) = neRedTerm d x₁
whnfRedTerm (β-red x x₁ x₂) (ne (∘ₙ ()))
whnfRedTerm (natrec-subst x x₁ x₂ d) (ne (natrecₙ x₃)) = neRedTerm d x₃
whnfRedTerm (natrec-zero x x₁ x₂) (ne (natrecₙ ()))
whnfRedTerm (natrec-suc x x₁ x₂ x₃) (ne (natrecₙ ()))
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
whnfRedTerm (Id-Π _ _ x x₁ x₂ x₃) (ne (Idₙ ()))
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
whnfRedTerm (Id-ℕ-0S x) (ne (Idₙ ()))
whnfRedTerm (Id-ℕ-S0 x) (ne (Idₙ ()))
whnfRedTerm (Id-U-ℕΠ A B) (ne (Idₙ ()))
whnfRedTerm (Id-U-Πℕ A B) (ne (Idₙ ()))
whnfRedTerm (cast-subst d x x₁ x₂) (ne (castₙ x₃)) = neRedTerm d x₃
whnfRedTerm (cast-subst d x x₁ x₂) (ne (castℕₙ x₃)) = whnfRedTerm d ℕₙ
whnfRedTerm (cast-subst d x x₁ x₂) (ne (castΠₙ x₃)) = whnfRedTerm d Πₙ
whnfRedTerm (cast-subst d x x₁ x₂) (ne (castℕℕₙ x₃)) = whnfRedTerm d ℕₙ
whnfRedTerm (cast-subst d x x₁ x₂) (ne castℕΠₙ) = whnfRedTerm d ℕₙ
whnfRedTerm (cast-subst d x x₁ x₂) (ne castΠℕₙ) = whnfRedTerm d Πₙ
whnfRedTerm (cast-ℕ-subst d x x₁) (ne (castℕₙ x₂)) = neRedTerm d x₂
whnfRedTerm (cast-ℕ-subst d x x₁) (ne (castℕℕₙ x₂)) = whnfRedTerm d ℕₙ
whnfRedTerm (cast-ℕ-subst d x x₁) (ne castℕΠₙ) = whnfRedTerm d Πₙ
whnfRedTerm (cast-Π-subst x x₁ d x₂ x₃) (ne (castΠₙ x₄)) = neRedTerm d x₄
whnfRedTerm (cast-Π-subst x x₁ d x₂ x₃) (ne castΠℕₙ) = whnfRedTerm d ℕₙ
whnfRedTerm (cast-Π x x₁ x₂ x₃ x₄ x₅) (ne (castₙ ()))
whnfRedTerm (cast-Π x x₁ x₂ x₃ x₄ x₅) (ne (castΠₙ ()))
whnfRedTerm (cast-ℕ-0 x) (ne (castₙ ()))
whnfRedTerm (cast-ℕ-0 x) (ne (castℕₙ ()))
whnfRedTerm (cast-ℕ-0 x) (ne (castℕℕₙ ()))
whnfRedTerm (cast-ℕ-S x x₁) (ne (castₙ ()))
whnfRedTerm (cast-ℕ-S x x₁) (ne (castℕₙ ()))
whnfRedTerm (cast-ℕ-S x x₁) (ne (castℕℕₙ ()))
whnfRedTerm (cast-ℕ-cong x x₁) (ne (castₙ ()))
whnfRedTerm (cast-ℕ-cong x x₁) (ne (castℕₙ ()))
whnfRedTerm (cast-ℕ-cong x x₁) (ne (castℕℕₙ t)) = neRedTerm x₁ t
whnfRedTerm (cast-subst d x x₁ x₂) (ne castΠΠ%!ₙ) = whnfRedTerm d Πₙ
whnfRedTerm (cast-subst d x x₁ x₂) (ne castΠΠ!%ₙ) = whnfRedTerm d Πₙ
whnfRedTerm (cast-Π-subst x x₁ d x₂ x₃) (ne castΠΠ%!ₙ) = whnfRedTerm d Πₙ
whnfRedTerm (cast-Π-subst x x₁ d x₂ x₃) (ne castΠΠ!%ₙ) = whnfRedTerm d Πₙ

whnfRed (univ x) w = whnfRedTerm x w

whnfRed*Term : ∀ {Γ t u A l} (d : Γ ⊢ t ⇒* u ∷ A ^ l) (w : Whnf t) → t PE.≡ u
whnfRed*Term (id x) Uₙ = PE.refl
whnfRed*Term (id x) Πₙ = PE.refl
whnfRed*Term (id x) ∃ₙ = PE.refl
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

-- Whr is deterministic

-- somehow the cases (cast-Π, cast-Π) and (Id-U-ΠΠ, Id-U-ΠΠ) fail if
-- I do not introduce a dummy relevance rA'. This is why I need the two
-- auxiliary functions. What the hell Agda?
whrDetTerm-aux1 : ∀{Γ t u F lF A A' rA lA lB rA' l B B' e f}
  → (d :  t PE.≡ cast l (Π A ^ rA ° lA ▹ B ° lB) (Π A' ^ rA' ° lA ▹ B' ° lB ) e f)
  → (d′ : Γ ⊢ t ⇒ u ∷ F ^ lF)
  → (lam A' ▹ let a = cast l (wk1 A') (wk1 A) (Idsym (Univ rA l) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) in cast l (B [ a ]↑) B' ((snd (wk1 e)) ∘ (var 0)) ((wk1 f) ∘ a)) PE.≡ u
whrDetTerm-aux1 d (conv d' x) = whrDetTerm-aux1 d d'
whrDetTerm-aux1 PE.refl (cast-subst d' x x₁ x₂) = ⊥-elim (whnfRedTerm d' Πₙ)
whrDetTerm-aux1 PE.refl (cast-Π-subst x x₁ d' x₂ x₃) = ⊥-elim (whnfRedTerm d' Πₙ)
whrDetTerm-aux1 PE.refl (cast-Π x x₁ x₂ x₃ x₄ x₅) = PE.refl

whrDetTerm-aux2 : ∀{Γ t u F lF A rA B A' rA' B'}
  → (d : t PE.≡ Id (U ⁰) (Π A ^ rA ° ⁰ ▹ B ° ⁰ ) (Π A' ^ rA' ° ⁰ ▹ B' ° ⁰))
  → (d' : Γ ⊢ t ⇒ u ∷ F ^ lF)
  → (∃ (Id (Univ rA ⁰) A A') ▹ (Π (wk1 A') ^ rA ° ⁰ ▹ Id (U ⁰) ((wk (lift (step id)) B) [ cast ⁰ (wk1 (wk1 A')) (wk1 (wk1 A)) (Idsym (Univ rA ⁰) (wk1 (wk1 A)) (wk1 (wk1 A')) (var 1)) (var 0) ]↑) (wk (lift (step id)) B') ° ¹ ) ) PE.≡ u
whrDetTerm-aux2 d (conv d' x) = whrDetTerm-aux2 d d'
whrDetTerm-aux2 PE.refl (Id-subst d' x x₁) = ⊥-elim (whnfRedTerm d' Uₙ)
whrDetTerm-aux2 PE.refl (Id-U-subst d' x) = ⊥-elim (whnfRedTerm d' Πₙ)
whrDetTerm-aux2 PE.refl (Id-U-Π-subst x x₁ d') = ⊥-elim (whnfRedTerm d' Πₙ)
whrDetTerm-aux2 PE.refl (Id-U-ΠΠ x x₁ x₂ x₃) = PE.refl

whrDetTerm : ∀{Γ t u A l u′ A′ l′} (d : Γ ⊢ t ⇒ u ∷ A ^ l) (d′ : Γ ⊢ t ⇒ u′ ∷ A′ ^ l′) → u PE.≡ u′
whrDet : ∀{Γ A B B′ r r'} (d : Γ ⊢ A ⇒ B ^ r) (d′ : Γ ⊢ A ⇒ B′ ^ r') → B PE.≡ B′

whrDetTerm (conv d x) d′ = whrDetTerm d d′
whrDetTerm (app-subst d x) (app-subst d′ x₁) rewrite whrDetTerm d d′ = PE.refl
whrDetTerm (app-subst d x) (β-red x₁ x₂ x₃) = ⊥-elim (whnfRedTerm d lamₙ)
whrDetTerm (β-red x x₁ x₂) (app-subst d' x₃) = ⊥-elim (whnfRedTerm d' lamₙ)
whrDetTerm (β-red x x₁ x₂) (β-red x₃ x₄ x₅) = PE.refl
whrDetTerm (natrec-subst x x₁ x₂ d) (natrec-subst x₃ x₄ x₅ d') rewrite whrDetTerm d d' = PE.refl
whrDetTerm (natrec-subst x x₁ x₂ d) (natrec-zero x₃ x₄ x₅) = ⊥-elim (whnfRedTerm d zeroₙ)
whrDetTerm (natrec-subst x x₁ x₂ d) (natrec-suc x₃ x₄ x₅ x₆) = ⊥-elim (whnfRedTerm d sucₙ)
whrDetTerm (natrec-zero x x₁ x₂) (natrec-subst x₃ x₄ x₅ d') = ⊥-elim (whnfRedTerm d' zeroₙ)
whrDetTerm (natrec-zero x x₁ x₂) (natrec-zero x₃ x₄ x₅) = PE.refl
whrDetTerm (natrec-suc x x₁ x₂ x₃) (natrec-subst x₄ x₅ x₆ d') = ⊥-elim (whnfRedTerm d' sucₙ)
whrDetTerm (natrec-suc x x₁ x₂ x₃) (natrec-suc x₄ x₅ x₆ x₇) = PE.refl
whrDetTerm (Id-subst d x x₁) (Id-subst d' x₂ x₃) rewrite whrDetTerm d d' = PE.refl
whrDetTerm (Id-subst d x x₁) (Id-ℕ-subst d' x₂) = ⊥-elim (whnfRedTerm d ℕₙ)
whrDetTerm (Id-subst d x x₁) (Id-ℕ-0-subst d') = ⊥-elim (whnfRedTerm d ℕₙ)
whrDetTerm (Id-subst d x x₁) (Id-ℕ-S-subst x₂ d') = ⊥-elim (whnfRedTerm d ℕₙ)
whrDetTerm (Id-subst d x x₁) (Id-U-subst d' x₂) = ⊥-elim (whnfRedTerm d Uₙ)
whrDetTerm (Id-subst d x x₁) (Id-U-ℕ-subst d') = ⊥-elim (whnfRedTerm d Uₙ)
whrDetTerm (Id-subst d x x₁) (Id-U-Π-subst x₂ x₃ d') = ⊥-elim (whnfRedTerm d Uₙ)
whrDetTerm (Id-subst d x x₁) (Id-Π _ _ x₂ x₃ x₄ x₅) = ⊥-elim (whnfRedTerm d Πₙ)
whrDetTerm (Id-subst d x x₁) (Id-ℕ-00 x₂) = ⊥-elim (whnfRedTerm d ℕₙ)
whrDetTerm (Id-subst d x x₁) (Id-ℕ-SS x₂ x₃) = ⊥-elim (whnfRedTerm d ℕₙ)
whrDetTerm (Id-subst d x x₁) (Id-U-ΠΠ x₂ x₃ x₄ x₅) = ⊥-elim (whnfRedTerm d Uₙ)
whrDetTerm (Id-subst d x x₁) (Id-U-ℕℕ x₂) = ⊥-elim (whnfRedTerm d Uₙ)
whrDetTerm (Id-subst d x x₁) (Id-SProp x₂ x₃) = ⊥-elim (whnfRedTerm d Uₙ)
whrDetTerm (Id-subst d x x₁) (Id-ℕ-0S x₂) = ⊥-elim (whnfRedTerm d ℕₙ)
whrDetTerm (Id-subst d x x₁) (Id-ℕ-S0 x₂) = ⊥-elim (whnfRedTerm d ℕₙ)
whrDetTerm (Id-subst d x x₁) (Id-U-ℕΠ x₂ x₃) = ⊥-elim (whnfRedTerm d Uₙ)
whrDetTerm (Id-subst d x x₁) (Id-U-Πℕ x₂ x₃) = ⊥-elim (whnfRedTerm d Uₙ)
whrDetTerm (Id-ℕ-subst d x) (Id-subst d' x₁ x₂) = ⊥-elim (whnfRedTerm d' ℕₙ)
whrDetTerm (Id-ℕ-subst d x) (Id-ℕ-subst d' x₁) rewrite whrDetTerm d d' = PE.refl
whrDetTerm (Id-ℕ-subst d x) (Id-ℕ-0-subst d') = ⊥-elim (whnfRedTerm d zeroₙ)
whrDetTerm (Id-ℕ-subst d x) (Id-ℕ-S-subst x₁ d') = ⊥-elim (whnfRedTerm d sucₙ)
whrDetTerm (Id-ℕ-subst d x) (Id-ℕ-00 x₁) = ⊥-elim (whnfRedTerm d zeroₙ)
whrDetTerm (Id-ℕ-subst d x) (Id-ℕ-SS x₁ x₂) = ⊥-elim (whnfRedTerm d sucₙ)
whrDetTerm (Id-ℕ-subst d x) (Id-ℕ-0S x₁) = ⊥-elim (whnfRedTerm d zeroₙ)
whrDetTerm (Id-ℕ-subst d x) (Id-ℕ-S0 x₁) = ⊥-elim (whnfRedTerm d sucₙ)
whrDetTerm (Id-ℕ-0-subst d) (Id-subst d' x x₁) = ⊥-elim (whnfRedTerm d' ℕₙ)
whrDetTerm (Id-ℕ-0-subst d) (Id-ℕ-subst d' x) = ⊥-elim (whnfRedTerm d' zeroₙ)
whrDetTerm (Id-ℕ-0-subst d) (Id-ℕ-0-subst d') rewrite whrDetTerm d d' = PE.refl
whrDetTerm (Id-ℕ-0-subst d) (Id-ℕ-00 x) = ⊥-elim (whnfRedTerm d zeroₙ)
whrDetTerm (Id-ℕ-0-subst d) (Id-ℕ-0S x) = ⊥-elim (whnfRedTerm d sucₙ)
whrDetTerm (Id-ℕ-S-subst x d) (Id-subst d' x₁ x₂) = ⊥-elim (whnfRedTerm d' ℕₙ)
whrDetTerm (Id-ℕ-S-subst x d) (Id-ℕ-subst d' x₁) = ⊥-elim (whnfRedTerm d' sucₙ)
whrDetTerm (Id-ℕ-S-subst x d) (Id-ℕ-S-subst x₁ d') rewrite whrDetTerm d d' = PE.refl
whrDetTerm (Id-ℕ-S-subst x d) (Id-ℕ-SS x₁ x₂) = ⊥-elim (whnfRedTerm d sucₙ)
whrDetTerm (Id-ℕ-S-subst x d) (Id-ℕ-S0 x₁) = ⊥-elim (whnfRedTerm d zeroₙ)
whrDetTerm (Id-U-subst d x) (Id-subst d' x₁ x₂) = ⊥-elim (whnfRedTerm d' Uₙ)
whrDetTerm (Id-U-subst d x) (Id-U-subst d' x₁) rewrite whrDetTerm d d' = PE.refl
whrDetTerm (Id-U-subst d x) (Id-U-ℕ-subst d') = ⊥-elim (whnfRedTerm d ℕₙ)
whrDetTerm (Id-U-subst d x) (Id-U-Π-subst x₁ x₂ d') = ⊥-elim (whnfRedTerm d Πₙ)
whrDetTerm (Id-U-subst d x) (Id-U-ΠΠ x₁ x₂ x₃ x₄) = ⊥-elim (whnfRedTerm d Πₙ)
whrDetTerm (Id-U-subst d x) (Id-U-ℕℕ x₁) = ⊥-elim (whnfRedTerm d ℕₙ)
whrDetTerm (Id-U-subst d x) (Id-U-ℕΠ x₁ x₂) = ⊥-elim (whnfRedTerm d ℕₙ)
whrDetTerm (Id-U-subst d x) (Id-U-Πℕ x₁ x₂) = ⊥-elim (whnfRedTerm d Πₙ)
whrDetTerm (Id-U-ℕ-subst d) (Id-subst d' x x₁) = ⊥-elim (whnfRedTerm d' Uₙ)
whrDetTerm (Id-U-ℕ-subst d) (Id-U-subst d' x) = ⊥-elim (whnfRedTerm d' ℕₙ)
whrDetTerm (Id-U-ℕ-subst d) (Id-U-ℕ-subst d') rewrite whrDetTerm d d' = PE.refl
whrDetTerm (Id-U-ℕ-subst d) (Id-U-ℕℕ x) = ⊥-elim (whnfRedTerm d ℕₙ)
whrDetTerm (Id-U-ℕ-subst d) (Id-U-ℕΠ x x₁) = ⊥-elim (whnfRedTerm d Πₙ)
whrDetTerm (Id-U-Π-subst x x₁ d) (Id-subst d' x₂ x₃) = ⊥-elim (whnfRedTerm d' Uₙ)
whrDetTerm (Id-U-Π-subst x x₁ d) (Id-U-subst d' x₂) = ⊥-elim (whnfRedTerm d' Πₙ)
whrDetTerm (Id-U-Π-subst x x₁ d) (Id-U-Π-subst x₂ x₃ d') rewrite whrDetTerm d d' = PE.refl
whrDetTerm (Id-U-Π-subst x x₁ d) (Id-U-ΠΠ x₂ x₃ x₄ x₅) = ⊥-elim (whnfRedTerm d Πₙ)
whrDetTerm (Id-U-Π-subst x x₁ d) (Id-U-Πℕ x₂ x₃) = ⊥-elim (whnfRedTerm d ℕₙ)
whrDetTerm (Id-Π _ _ x x₁ x₂ x₃) (Id-subst d' x₄ x₅) = ⊥-elim (whnfRedTerm d' Πₙ)
whrDetTerm (Id-Π _ _ x x₁ x₂ x₃) (Id-Π _ _ x₄ x₅ x₆ x₇) = PE.refl
whrDetTerm (Id-ℕ-00 x) (Id-subst d' x₁ x₂) = ⊥-elim (whnfRedTerm d' ℕₙ)
whrDetTerm (Id-ℕ-00 x) (Id-ℕ-subst d' x₁) = ⊥-elim (whnfRedTerm d' zeroₙ)
whrDetTerm (Id-ℕ-00 x) (Id-ℕ-0-subst d') = ⊥-elim (whnfRedTerm d' zeroₙ)
whrDetTerm (Id-ℕ-00 x) (Id-ℕ-00 x₁) = PE.refl
whrDetTerm (Id-ℕ-SS x x₁) (Id-subst d' x₂ x₃) = ⊥-elim (whnfRedTerm d' ℕₙ)
whrDetTerm (Id-ℕ-SS x x₁) (Id-ℕ-subst d' x₂) = ⊥-elim (whnfRedTerm d' sucₙ)
whrDetTerm (Id-ℕ-SS x x₁) (Id-ℕ-S-subst x₂ d') = ⊥-elim (whnfRedTerm d' sucₙ)
whrDetTerm (Id-ℕ-SS x x₁) (Id-ℕ-SS x₂ x₃) = PE.refl
whrDetTerm (Id-U-ΠΠ x x₁ x₂ x₃) d' = whrDetTerm-aux2 PE.refl d'
whrDetTerm (Id-U-ℕℕ x) (Id-subst d' x₁ x₂) = ⊥-elim (whnfRedTerm d' Uₙ)
whrDetTerm (Id-U-ℕℕ x) (Id-U-subst d' x₁) = ⊥-elim (whnfRedTerm d' ℕₙ)
whrDetTerm (Id-U-ℕℕ x) (Id-U-ℕ-subst d') = ⊥-elim (whnfRedTerm d' ℕₙ)
whrDetTerm (Id-U-ℕℕ x) (Id-U-ℕℕ x₁) = PE.refl
whrDetTerm (Id-SProp x x₁) (Id-subst d' x₂ x₃) = ⊥-elim (whnfRedTerm d' Uₙ)
whrDetTerm (Id-SProp x x₁) (Id-SProp x₂ x₃) = PE.refl
whrDetTerm (Id-ℕ-0S x) (Id-subst d' x₁ x₂) = ⊥-elim (whnfRedTerm d' ℕₙ)
whrDetTerm (Id-ℕ-0S x) (Id-ℕ-subst d' x₁) = ⊥-elim (whnfRedTerm d' zeroₙ)
whrDetTerm (Id-ℕ-0S x) (Id-ℕ-0-subst d') = ⊥-elim (whnfRedTerm d' sucₙ)
whrDetTerm (Id-ℕ-0S x) (Id-ℕ-0S x₁) = PE.refl
whrDetTerm (Id-ℕ-S0 x) (Id-subst d' x₁ x₂) = ⊥-elim (whnfRedTerm d' ℕₙ)
whrDetTerm (Id-ℕ-S0 x) (Id-ℕ-subst d' x₁) = ⊥-elim (whnfRedTerm d' sucₙ)
whrDetTerm (Id-ℕ-S0 x) (Id-ℕ-S-subst x₁ d') = ⊥-elim (whnfRedTerm d' zeroₙ)
whrDetTerm (Id-ℕ-S0 x) (Id-ℕ-S0 x₁) = PE.refl
whrDetTerm (Id-U-ℕΠ x x₁) (Id-subst d' x₂ x₃) = ⊥-elim (whnfRedTerm d' Uₙ)
whrDetTerm (Id-U-ℕΠ x x₁) (Id-U-subst d' x₂) = ⊥-elim (whnfRedTerm d' ℕₙ)
whrDetTerm (Id-U-ℕΠ x x₁) (Id-U-ℕ-subst d') = ⊥-elim (whnfRedTerm d' Πₙ)
whrDetTerm (Id-U-ℕΠ x x₁) (Id-U-ℕΠ x₂ x₃) = PE.refl
whrDetTerm (Id-U-Πℕ x x₁) (Id-subst d' x₂ x₃) = ⊥-elim (whnfRedTerm d' Uₙ)
whrDetTerm (Id-U-Πℕ x x₁) (Id-U-subst d' x₂) = ⊥-elim (whnfRedTerm d' Πₙ)
whrDetTerm (Id-U-Πℕ x x₁) (Id-U-Π-subst x₂ x₃ d') = ⊥-elim (whnfRedTerm d' ℕₙ)
whrDetTerm (Id-U-Πℕ x x₁) (Id-U-Πℕ x₂ x₃) = PE.refl
whrDetTerm (cast-subst d x x₁ x₂) (cast-subst d' x₃ x₄ x₅) rewrite whrDetTerm d d' = PE.refl
whrDetTerm (cast-subst d x x₁ x₂) (cast-ℕ-subst d' x₃ x₄) = ⊥-elim (whnfRedTerm d ℕₙ)
whrDetTerm (cast-subst d x x₁ x₂) (cast-Π-subst x₃ x₄ d' x₅ x₆) = ⊥-elim (whnfRedTerm d Πₙ)
whrDetTerm (cast-subst d x x₁ x₂) (cast-Π x₃ x₄ x₅ x₆ x₇ x₈) = ⊥-elim (whnfRedTerm d Πₙ)
whrDetTerm (cast-subst d x x₁ x₂) (cast-ℕ-0 x₃) = ⊥-elim (whnfRedTerm d ℕₙ)
whrDetTerm (cast-subst d x x₁ x₂) (cast-ℕ-S x₃ x₄) = ⊥-elim (whnfRedTerm d ℕₙ)
whrDetTerm (cast-ℕ-subst d x x₁) (cast-subst d' x₂ x₃ x₄) = ⊥-elim (whnfRedTerm d' ℕₙ)
whrDetTerm (cast-ℕ-subst d x x₁) (cast-ℕ-subst d' x₂ x₃) rewrite whrDetTerm d d' = PE.refl
whrDetTerm (cast-ℕ-subst d x x₁) (cast-ℕ-0 x₂) = ⊥-elim (whnfRedTerm d ℕₙ)
whrDetTerm (cast-ℕ-subst d x x₁) (cast-ℕ-S x₂ x₃) = ⊥-elim (whnfRedTerm d ℕₙ)
whrDetTerm (cast-Π-subst x x₁ d x₂ x₃) (cast-subst d' x₄ x₅ x₆) = ⊥-elim (whnfRedTerm d' Πₙ)
whrDetTerm (cast-Π-subst x x₁ d x₂ x₃) (cast-Π-subst x₄ x₅ d' x₆ x₇) rewrite whrDetTerm d d' = PE.refl
whrDetTerm (cast-Π-subst x x₁ d x₂ x₃) (cast-Π x₄ x₅ x₆ x₇ x₈ x₉) = ⊥-elim (whnfRedTerm d Πₙ)
whrDetTerm (cast-Π x x₁ x₂ x₃ x₄ x₅) d' = whrDetTerm-aux1 (PE.refl) d'
whrDetTerm (cast-ℕ-0 x) (cast-subst d' x₁ x₂ x₃) = ⊥-elim (whnfRedTerm d' ℕₙ)
whrDetTerm (cast-ℕ-0 x) (cast-ℕ-subst d' x₁ x₂) = ⊥-elim (whnfRedTerm d' ℕₙ)
whrDetTerm (cast-ℕ-0 x) (cast-ℕ-0 x₁) = PE.refl
whrDetTerm (cast-ℕ-S x x₁) (cast-subst d' x₂ x₃ x₄) = ⊥-elim (whnfRedTerm d' ℕₙ)
whrDetTerm (cast-ℕ-S x x₁) (cast-ℕ-subst d' x₂ x₃) = ⊥-elim (whnfRedTerm d' ℕₙ)
whrDetTerm (cast-ℕ-S x x₁) (cast-ℕ-S x₂ x₃) = PE.refl
whrDetTerm (cast-ℕ-cong x x₁) (cast-subst d' x₂ x₃ x₄) = ⊥-elim (whnfRedTerm d' ℕₙ)
whrDetTerm (cast-ℕ-cong x x₁) (cast-ℕ-subst d' x₂ x₃) = ⊥-elim (whnfRedTerm d' ℕₙ)
whrDetTerm (cast-ℕ-cong x x₁) (cast-ℕ-cong x₂ x₃) rewrite whrDetTerm x₁ x₃ = PE.refl -- 
whrDetTerm (cast-subst d x x₁ x₂) (cast-ℕ-cong x₃ d′) = ⊥-elim (whnfRedTerm d ℕₙ)
whrDetTerm (cast-ℕ-subst d x x₁) (cast-ℕ-cong x₂ d′) = ⊥-elim (whnfRedTerm d ℕₙ)
whrDetTerm (cast-ℕ-0 x) (cast-ℕ-cong x₁ d′) = ⊥-elim (whnfRedTerm d′ zeroₙ)
whrDetTerm (cast-ℕ-S x x₁) (cast-ℕ-cong x₂ d′) = ⊥-elim (whnfRedTerm d′ sucₙ)
whrDetTerm (cast-ℕ-cong x d) (cast-ℕ-0 x₁) = ⊥-elim (whnfRedTerm d zeroₙ)
whrDetTerm (cast-ℕ-cong x d) (cast-ℕ-S x₁ x₂) = ⊥-elim (whnfRedTerm d sucₙ)

{-# CATCHALL #-}
whrDetTerm d (conv d′ x₁) = whrDetTerm d d′

whrDet (univ x) (univ x₁) = whrDetTerm x x₁

whrDet↘Term : ∀{Γ t u A l u′} (d : Γ ⊢ t ↘ u ∷ A ^ l) (d′ : Γ ⊢ t ⇒* u′ ∷ A ^ l)
  → Γ ⊢ u′ ⇒* u ∷ A ^ l
whrDet↘Term (proj₁ , proj₂) (id x) = proj₁
whrDet↘Term (id x , proj₂) (x₁ ⇨ d′) = ⊥-elim (whnfRedTerm x₁ proj₂)
whrDet↘Term (x ⇨ proj₁ , proj₂) (x₁ ⇨ d′) =
  whrDet↘Term (PE.subst (λ x₂ → _ ⊢ x₂ ↘ _ ∷ _ ^ _) (whrDetTerm x x₁) (proj₁ , proj₂)) d′

whrDet*Term : ∀{Γ t u A A' l u′ } (d : Γ ⊢ t ↘ u ∷ A ^ l) (d′ : Γ ⊢ t ↘ u′ ∷ A' ^ l) → u PE.≡ u′
whrDet*Term (id x , proj₂) (id x₁ , proj₄) = PE.refl
whrDet*Term (id x , proj₂) (x₁ ⇨ proj₃ , proj₄) = ⊥-elim (whnfRedTerm x₁ proj₂)
whrDet*Term (x ⇨ proj₁ , proj₂) (id x₁ , proj₄) = ⊥-elim (whnfRedTerm x proj₄)
whrDet*Term (x ⇨ proj₁ , proj₂) (x₁ ⇨ proj₃ , proj₄) =
  whrDet*Term (proj₁ , proj₂) (PE.subst (λ x₂ → _ ⊢ x₂ ↘ _ ∷ _ ^ _)
                                    (whrDetTerm x₁ x) (proj₃ , proj₄))

whrDet* : ∀{Γ A B B′ r r'} (d : Γ ⊢ A ↘ B ^ r) (d′ : Γ ⊢ A ↘ B′ ^ r') → B PE.≡ B′
whrDet* (id x , proj₂) (id x₁ , proj₄) = PE.refl
whrDet* (id x , proj₂) (x₁ ⇨ proj₃ , proj₄) = ⊥-elim (whnfRed x₁ proj₂)
whrDet* (x ⇨ proj₁ , proj₂) (id x₁ , proj₄) = ⊥-elim (whnfRed x proj₄)
whrDet* (A⇒A′ ⇨ A′⇒*B , whnfB) (A⇒A″ ⇨ A″⇒*B′ , whnfB′) =
  whrDet* (A′⇒*B , whnfB) (PE.subst (λ x → _ ⊢ x ↘ _ ^ _ )
                                     (whrDet A⇒A″ A⇒A′)
                                     (A″⇒*B′ , whnfB′))

-- Identity of syntactic reduction

idRed:*: : ∀ {Γ A r} → Γ ⊢ A ^ r → Γ ⊢ A :⇒*: A ^ r
idRed:*: A = [[ A , A , id A ]]

idRedTerm:*: : ∀ {Γ A l t} → Γ ⊢ t ∷ A ^ [ ! , l ] → Γ ⊢ t :⇒*: t ∷ A ^ l
idRedTerm:*: t = [[ t , t , id t ]]

-- U cannot be a term

UnotInA : ∀ {A Γ r r'} → Γ ⊢ (Univ r ¹) ∷ A ^ r' → ⊥
UnotInA (conv U∷U x) = UnotInA U∷U

UnotInA[t] : ∀ {A B t a Γ r r' r'' r'''}
         → t [ a ] PE.≡ (Univ r ¹)
         → Γ ⊢ a ∷ A ^ r'
         → Γ ∙ A ^ r'' ⊢ t ∷ B ^ r'''
         → ⊥
UnotInA[t] () x₁ (univ 0<1 x₂)
UnotInA[t] () x₁ (ℕⱼ x₂)
UnotInA[t] () x₁ (Emptyⱼ x₂)
UnotInA[t] () x₁ (Πⱼ _ ▹ _ ▹ x₂ ▹ x₃)
UnotInA[t] x₁ x₂ (var x₃ here) rewrite x₁ = UnotInA x₂
UnotInA[t] () x₂ (var x₃ (there x₄))
UnotInA[t] () x₁ (lamⱼ _ _ x₂ x₃)
UnotInA[t] () x₁ (x₂ ∘ⱼ x₃)
UnotInA[t] () x₁ (zeroⱼ x₂)
UnotInA[t] () x₁ (sucⱼ x₂)
UnotInA[t] () x₁ (natrecⱼ x₂ x₃ x₄ x₅)
UnotInA[t] () x₁ (Emptyrecⱼ x₂ x₃)
UnotInA[t] x x₁ (conv x₂ x₃) = UnotInA[t] x x₁ x₂

redU*Term′ : ∀ {A B U′ l Γ r} → U′ PE.≡ (Univ r ¹) → Γ ⊢ A ⇒ U′ ∷ B ^ l → ⊥
redU*Term′ U′≡U (conv A⇒U x) = redU*Term′ U′≡U A⇒U
redU*Term′ () (app-subst A⇒U x)
redU*Term′ U′≡U (β-red x x₁ x₂) = UnotInA[t] U′≡U x₂ x₁
redU*Term′ () (natrec-subst x x₁ x₂ A⇒U)
redU*Term′ U′≡U (natrec-zero x x₁ x₂) rewrite U′≡U = UnotInA x₁
redU*Term′ () (natrec-suc x x₁ x₂ x₃)

redU*Term : ∀ {A B l Γ r} → Γ ⊢ A ⇒* (Univ r ¹) ∷ B ^ l → ⊥
redU*Term (id x) = UnotInA x
redU*Term (x ⇨ A⇒*U) = redU*Term A⇒*U

-- Nothing reduces to U

redU : ∀ {A Γ r l } → Γ ⊢ A ⇒ (Univ r ¹) ^ [ ! , l ] → ⊥
redU (univ x) = redU*Term′ PE.refl x

redU* : ∀ {A Γ r l } → Γ ⊢ A ⇒* (Univ r ¹) ^ [ ! , l ] → A PE.≡ (Univ r ¹)
redU* (id x) = PE.refl
redU* (x ⇨ A⇒*U) rewrite redU* A⇒*U = ⊥-elim (redU x)

-- convertibility for irrelevant terms implies typing

typeInversion : ∀ {t u A l Γ} → Γ ⊢ t ≡ u ∷ A ^ [ % , l ] → Γ ⊢ t ∷ A ^ [ % , l ]
typeInversion (conv X x) = let d = typeInversion X in conv d x
typeInversion (proof-irrelevance x x₁) = x

-- general version of reflexivity, symmetry and transitivity

genRefl : ∀ {A Γ t r l } → Γ ⊢ t ∷ A ^ [ r , l ] → Γ ⊢ t ≡ t ∷ A ^ [ r , l ]
genRefl {r = !} d = refl d
genRefl {r = %} d = proof-irrelevance d d

-- Judgmental instance of the equality relation

genSym : ∀ {k l A Γ r lA } → Γ ⊢ k ≡ l ∷ A ^ [ r , lA ] → Γ ⊢ l ≡ k ∷ A ^ [ r , lA ]
genSym {r = !} = sym
genSym {r = %} (proof-irrelevance x x₁) = proof-irrelevance x₁ x
genSym {r = %} (conv x x₁) = conv (genSym x) x₁


genTrans : ∀ {k l m A r Γ lA } → Γ ⊢ k ≡ l ∷ A ^ [ r , lA ] → Γ ⊢ l ≡ m ∷ A ^ [ r , lA ] → Γ ⊢ k ≡ m ∷ A ^ [ r , lA ]
genTrans {r = !} = trans
genTrans {r = %} (conv X x) (conv Y x₁) = conv (genTrans X (conv Y (trans x₁ (sym x)))) x
genTrans {r = %} (conv X x) (proof-irrelevance x₁ x₂) = proof-irrelevance (conv (typeInversion X) x) x₂
genTrans {r = %} (proof-irrelevance x x₁) (conv Y x₂) = proof-irrelevance x (conv (typeInversion (genSym Y)) x₂)
genTrans {r = %} (proof-irrelevance x x₁) (proof-irrelevance x₂ x₃) = proof-irrelevance x x₃

genVar : ∀ {x A Γ r l } → Γ ⊢ var x ∷ A ^ [ r , l ] → Γ ⊢ var x ≡ var x ∷ A ^ [ r , l ]
genVar {r = !} = refl
genVar {r = %} d = proof-irrelevance d d

toLevelInj : ∀ {l₁ l₁′ : TypeLevel} {l<₁ : l₁′ <∞ l₁} {l₂ l₂′ : TypeLevel} {l<₂ : l₂′ <∞ l₂} →
               toLevel l₁′ PE.≡ toLevel l₂′ → l₁′ PE.≡ l₂′
toLevelInj {.(ι ¹)} {.(ι ⁰)} {emb<} {.(ι ¹)} {.(ι ⁰)} {emb<} e = PE.refl
toLevelInj {.∞} {.(ι ¹)} {∞<} {.(ι ¹)} {.(ι ⁰)} {emb<} ()
toLevelInj {.∞} {.(ι ¹)} {∞<} {.∞} {.(ι ¹)} {∞<} e = PE.refl
-- toLevelInj {l<₁ = ∞<⁰} {l<₂ = emb<} x = PE.refl
-- toLevelInj {l<₁ = emb<} {l<₂ = ∞<⁰} x = PE.refl
-- toLevelInj {l<₁ = ∞<⁰} {l<₂ = ∞<⁰} x = PE.refl

redSProp′ : ∀ {Γ A B l}
           (D : Γ ⊢ A ⇒* B ∷ SProp l ^ next l )
         → Γ ⊢ A ⇒* B ^ [ % , ι l ]
redSProp′ (id x) = id (univ x)
redSProp′ (x ⇨ D) = univ x ⇨ redSProp′ D

redSProp : ∀ {Γ A B l}
           (D : Γ ⊢ A :⇒*: B ∷ SProp l ^ next l )
         → Γ ⊢ A :⇒*: B ^ [ % , ι l ]
redSProp [[ ⊢t , ⊢u , d ]] = [[ (univ ⊢t) , (univ ⊢u) , redSProp′ d ]]

un-univ : ∀ {A r Γ l} → Γ ⊢ A ^ [ r , ι l ] → Γ ⊢ A ∷ Univ r l ^ [ ! , next l ]
un-univ (univ x) = x

un-univ≡ : ∀ {A B r Γ l} → Γ ⊢ A ≡ B ^ [ r , ι l ] → Γ ⊢ A ≡ B ∷ Univ r l ^ [ ! , next l ]
un-univ≡ (univ x) = x
un-univ≡ (refl x) = refl (un-univ x)
un-univ≡ (sym X) = sym (un-univ≡ X)
un-univ≡ (trans X Y) = trans (un-univ≡ X) (un-univ≡ Y)

univ-gen : ∀ {r Γ l} → (⊢Γ : ⊢ Γ) → Γ ⊢ Univ r l ^ [ ! , next l ]
univ-gen {l = ⁰} ⊢Γ = univ (univ 0<1 ⊢Γ )
univ-gen {l = ¹} ⊢Γ = Uⱼ ⊢Γ


un-univ⇒ : ∀ {l Γ A B r} → Γ ⊢ A ⇒ B ^ [ r , ι l ] → Γ ⊢ A ⇒ B ∷ Univ r l ^ next l
un-univ⇒ (univ x) = x

univ⇒* : ∀ {l Γ A B r} → Γ ⊢ A ⇒* B ∷ Univ r l ^ next l → Γ ⊢ A ⇒* B ^ [ r , ι l ]
univ⇒* (id x) = id (univ x)
univ⇒* (x ⇨ D) = univ x ⇨ univ⇒* D

un-univ⇒* : ∀ {l Γ A B r} → Γ ⊢ A ⇒* B ^ [ r , ι l ] → Γ ⊢ A ⇒* B ∷ Univ r l ^ next l
un-univ⇒* (id x) = id (un-univ x)
un-univ⇒* (x ⇨ D) = un-univ⇒ x ⇨ un-univ⇒* D

univ:⇒*: : ∀ {l Γ A B r} →  Γ ⊢ A :⇒*: B ∷ Univ r l ^ next l → Γ ⊢ A :⇒*: B ^ [ r , ι l ]
univ:⇒*: [[ ⊢A , ⊢B , D ]] = [[ (univ ⊢A) , (univ ⊢B) , (univ⇒* D) ]]

un-univ:⇒*: : ∀ {l Γ A B r} → Γ ⊢ A :⇒*: B ^ [ r , ι l ] → Γ ⊢ A :⇒*: B ∷ Univ r l ^ next l
un-univ:⇒*: [[ ⊢A , ⊢B , D ]] = [[ (un-univ ⊢A) , (un-univ ⊢B) , (un-univ⇒* D) ]]

IdRed*Term′ : ∀ {Γ A B t u l}
         (⊢t : Γ ⊢ t ∷ A ^ [ ! , ι l ])
         (⊢u : Γ ⊢ u ∷ A ^ [ ! , ι l ])
         (D : Γ ⊢ A ⇒* B ^ [ ! , ι l ])
       → Γ ⊢ Id A t u ⇒* Id B t u ∷ SProp l ^ next l
IdRed*Term′ ⊢t ⊢u (id (univ ⊢A)) = id (Idⱼ ⊢A ⊢t ⊢u)
IdRed*Term′ ⊢t ⊢u (univ d ⇨ D) = Id-subst d ⊢t ⊢u ⇨ IdRed*Term′ (conv ⊢t (subset (univ d))) (conv ⊢u (subset (univ d))) D

IdRed*Term : ∀ {Γ A B t u l}
          (⊢t : Γ ⊢ t ∷ A ^ [ ! , ι l ])
          (⊢u : Γ ⊢ u ∷ A ^ [ ! , ι l ])
          (D : Γ ⊢ A :⇒*: B ^ [ ! , ι l ])
        → Γ ⊢ Id A t u :⇒*: Id B t u ∷ SProp l ^ next l
IdRed*Term {Γ} {A} {B} ⊢t ⊢u [[ univ ⊢A , univ ⊢B , D ]] =
  [[ Idⱼ ⊢A ⊢t ⊢u , Idⱼ ⊢B (conv ⊢t (subset* D)) (conv ⊢u (subset* D)) ,
     IdRed*Term′ ⊢t ⊢u D ]]

IdRed* : ∀ {Γ A B t u l}
         (⊢t : Γ ⊢ t ∷ A ^ [ ! , ι l ])
         (⊢u : Γ ⊢ u ∷ A ^ [ ! , ι l ])
         (D : Γ ⊢ A ⇒* B ^ [ ! , ι l ])
       → Γ ⊢ Id A t u ⇒* Id B t u ^ [ % , ι l ]
IdRed* ⊢t ⊢u (id ⊢A) = id (univ (Idⱼ (un-univ ⊢A) ⊢t ⊢u))
IdRed* ⊢t ⊢u (d ⇨ D) = univ (Id-subst (un-univ⇒ d) ⊢t ⊢u) ⇨ IdRed* (conv ⊢t (subset d)) (conv ⊢u (subset d)) D

CastRed*Term′ : ∀ {Γ A B X e t}
         (⊢X : Γ ⊢ X ^ [ ! , ι ⁰ ])
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) A X ^ [ % , next ⁰ ])
         (⊢t : Γ ⊢ t ∷ A ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A ⇒* B ^ [ ! , ι ⁰ ])
       → Γ ⊢ cast ⁰ A X e t ⇒* cast ⁰ B X e t ∷ X ^ ι ⁰
CastRed*Term′ (univ ⊢X) ⊢e ⊢t  (id (univ ⊢A)) = id (castⱼ ⊢A ⊢X ⊢e ⊢t)
CastRed*Term′ (univ ⊢X) ⊢e ⊢t  (univ d ⇨ D) = cast-subst d ⊢X ⊢e ⊢t ⇨
              CastRed*Term′ (univ ⊢X) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢t))) (subsetTerm d) (refl ⊢X)) )) (conv ⊢t (subset (univ d))) D

CastRed*Term : ∀ {Γ A B X t e}
         (⊢X : Γ ⊢ X ^ [ ! , ι ⁰ ])
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) A X ^ [ % , next ⁰ ])
         (⊢t : Γ ⊢ t ∷ A ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A :⇒*: B ∷ U ⁰ ^ next ⁰)
       → Γ ⊢ cast ⁰ A X e t :⇒*: cast ⁰ B X e t ∷ X ^ ι ⁰
CastRed*Term {Γ} {A} {B} (univ ⊢X) ⊢e ⊢t [[ ⊢A , ⊢B , D ]] =
  [[ castⱼ ⊢A ⊢X ⊢e ⊢t , castⱼ ⊢B ⊢X (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢t))) (subset*Term D) (refl ⊢X)) )) (conv ⊢t (univ (subset*Term D))) ,
     CastRed*Term′ (univ ⊢X) ⊢e ⊢t (univ* D) ]]

CastRed*Termℕ′ : ∀ {Γ A B e t}
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) ℕ A ^ [ % , next ⁰ ])
         (⊢t : Γ ⊢ t ∷ ℕ ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A ⇒* B ^ [ ! , ι ⁰ ])
       → Γ ⊢ cast ⁰ ℕ A e t ⇒* cast ⁰ ℕ B e t ∷ A ^ ι ⁰
CastRed*Termℕ′ ⊢e ⊢t  (id (univ ⊢A)) = id (castⱼ (ℕⱼ (wfTerm ⊢A)) ⊢A ⊢e ⊢t)
CastRed*Termℕ′ ⊢e ⊢t  (univ d ⇨ D) = cast-ℕ-subst d ⊢e ⊢t ⇨
                                     conv* (CastRed*Termℕ′ (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢e))) (refl (ℕⱼ (wfTerm ⊢e))) (subsetTerm d))) ) ⊢t D)
                                           (sym (subset (univ d)))

CastRed*Termℕ : ∀ {Γ A B e t}
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) ℕ A ^ [ % , next ⁰ ])
         (⊢t : Γ ⊢ t ∷ ℕ ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A :⇒*: B ^ [ ! , ι ⁰ ])
       → Γ ⊢ cast ⁰ ℕ A e t :⇒*: cast ⁰ ℕ B e t ∷ A ^ ι ⁰
CastRed*Termℕ ⊢e ⊢t  [[ ⊢A , ⊢B , D ]] =
  [[ castⱼ (ℕⱼ (wfTerm ⊢e)) (un-univ ⊢A) ⊢e ⊢t ,
     conv (castⱼ (ℕⱼ (wfTerm ⊢e)) (un-univ ⊢B) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢e))) (refl (ℕⱼ (wfTerm ⊢e))) (subset*Term (un-univ⇒* D))))) ⊢t) (sym (subset* D)) ,
       CastRed*Termℕ′ ⊢e ⊢t D ]]

CastRed*Termℕℕ′ : ∀ {Γ e t u}
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) ℕ ℕ ^ [ % , next ⁰ ])
         (⊢t : Γ ⊢ t ⇒* u ∷ ℕ ^ ι ⁰ )
       → Γ ⊢ cast ⁰ ℕ ℕ e t ⇒* cast ⁰ ℕ ℕ e u ∷ ℕ ^ ι ⁰
CastRed*Termℕℕ′ ⊢e (id ⊢t) = id (castⱼ (ℕⱼ (wfTerm ⊢e)) (ℕⱼ (wfTerm ⊢e)) ⊢e ⊢t)
CastRed*Termℕℕ′ ⊢e (d ⇨ D) = cast-ℕ-cong ⊢e d ⇨ CastRed*Termℕℕ′ ⊢e D

CastRed*Termℕℕ : ∀ {Γ e t u}
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) ℕ ℕ ^ [ % , next ⁰ ])
         (⊢t : Γ ⊢ t :⇒*: u ∷ ℕ ^ ι ⁰ )
       → Γ ⊢ cast ⁰ ℕ ℕ e t :⇒*: cast ⁰ ℕ ℕ e u ∷ ℕ ^ ι ⁰
CastRed*Termℕℕ ⊢e [[ ⊢t , ⊢u , D ]] =
  [[ castⱼ (ℕⱼ (wfTerm ⊢e)) (ℕⱼ (wfTerm ⊢e)) ⊢e ⊢t ,
     castⱼ (ℕⱼ (wfTerm ⊢e)) (ℕⱼ (wfTerm ⊢e)) ⊢e ⊢u ,
       CastRed*Termℕℕ′ ⊢e D ]]

CastRed*Termℕsuc : ∀ {Γ e n}
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) ℕ ℕ ^ [ % , next ⁰ ])
         (⊢n : Γ ⊢ n ∷ ℕ ^ [ ! , ι ⁰ ])
       → Γ ⊢ cast ⁰ ℕ ℕ e (suc n) :⇒*: suc (cast ⁰ ℕ ℕ e n) ∷ ℕ ^ ι ⁰
CastRed*Termℕsuc ⊢e ⊢n =
  [[ castⱼ (ℕⱼ (wfTerm ⊢e)) (ℕⱼ (wfTerm ⊢e)) ⊢e (sucⱼ ⊢n) ,
     sucⱼ (castⱼ (ℕⱼ (wfTerm ⊢e)) (ℕⱼ (wfTerm ⊢e)) ⊢e ⊢n) ,
       cast-ℕ-S ⊢e ⊢n ⇨ id (sucⱼ (castⱼ (ℕⱼ (wfTerm ⊢e)) (ℕⱼ (wfTerm ⊢e)) ⊢e ⊢n)) ]]

CastRed*Termℕzero : ∀ {Γ e}
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) ℕ ℕ ^ [ % , next ⁰ ])
       → Γ ⊢ cast ⁰ ℕ ℕ e zero :⇒*: zero ∷ ℕ ^ ι ⁰
CastRed*Termℕzero ⊢e =
  [[ castⱼ (ℕⱼ (wfTerm ⊢e)) (ℕⱼ (wfTerm ⊢e)) ⊢e (zeroⱼ (wfTerm ⊢e)) ,
     zeroⱼ (wfTerm ⊢e) ,
       cast-ℕ-0 ⊢e ⇨ id (zeroⱼ (wfTerm ⊢e)) ]]


CastRed*TermΠ′ : ∀ {Γ F rF G A B e t}
         (⊢F : Γ ⊢ F ∷ (Univ rF ⁰) ^ [ ! , next ⁰ ])
         (⊢G : Γ ∙ F ^ [ rF , ι ⁰ ] ⊢ G ∷ U ⁰ ^ [ ! , next ⁰ ])
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) (Π F ^ rF ° ⁰ ▹ G ° ⁰) A ^ [ % , next ⁰ ])
         (⊢t : Γ ⊢ t ∷ (Π F ^ rF ° ⁰ ▹ G ° ⁰) ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A ⇒* B ^ [ ! , ι ⁰ ])
       → Γ ⊢ cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰) A e t ⇒* cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰) B e t ∷ A ^ ι ⁰
CastRed*TermΠ′ ⊢F ⊢G ⊢e ⊢t (id (univ ⊢A)) = id (castⱼ (Πⱼ ≡is≤ PE.refl ▹ ≡is≤ PE.refl ▹ ⊢F ▹ ⊢G) ⊢A ⊢e ⊢t)
CastRed*TermΠ′ ⊢F ⊢G ⊢e ⊢t (univ d ⇨ D) = cast-Π-subst ⊢F ⊢G d ⊢e ⊢t ⇨
                                     conv* (CastRed*TermΠ′ ⊢F ⊢G (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢e))) (refl (Πⱼ ≡is≤ PE.refl ▹ ≡is≤ PE.refl ▹ ⊢F ▹ ⊢G)) (subsetTerm d))) ) ⊢t D)
                                           (sym (subset (univ d)))

CastRed*TermΠ : ∀ {Γ F rF G A B e t}
         (⊢F : Γ ⊢ F ∷ (Univ rF ⁰) ^ [ ! , next ⁰ ])
         (⊢G : Γ ∙ F ^ [ rF , ι ⁰ ] ⊢ G ∷ U ⁰ ^ [ ! , next ⁰ ])
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) (Π F ^ rF ° ⁰ ▹ G ° ⁰) A ^ [ % , next ⁰ ])
         (⊢t : Γ ⊢ t ∷ (Π F ^ rF ° ⁰ ▹ G ° ⁰) ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A :⇒*: B ^ [ ! , ι ⁰ ])
       → Γ ⊢ cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰) A e t :⇒*: cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰) B e t ∷ A ^ ι ⁰
CastRed*TermΠ ⊢F ⊢G ⊢e ⊢t  [[ ⊢A , ⊢B , D ]] =
  let [Π] = Πⱼ ≡is≤ PE.refl ▹ ≡is≤ PE.refl ▹ ⊢F ▹ ⊢G
  in [[ castⱼ [Π] (un-univ ⊢A) ⊢e ⊢t ,
        conv (castⱼ [Π] (un-univ ⊢B) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢e))) (refl [Π]) (subset*Term (un-univ⇒* D))))) ⊢t) (sym (subset* D)) ,
          CastRed*TermΠ′ ⊢F ⊢G ⊢e ⊢t D ]]
          
IdℕRed*Term′ : ∀ {Γ t t′ u}
               (⊢t : Γ ⊢ t ∷ ℕ ^ [ ! , ι ⁰ ])
               (⊢t′ : Γ ⊢ t′ ∷ ℕ ^ [ ! , ι ⁰ ])
               (d : Γ ⊢ t ⇒* t′ ∷ ℕ ^ ι ⁰)
               (⊢u : Γ ⊢ u ∷ ℕ ^ [ ! , ι ⁰ ])
             → Γ ⊢ Id ℕ t u ⇒* Id ℕ t′ u ∷ SProp ⁰ ^ next ⁰
IdℕRed*Term′ ⊢t ⊢t′ (id x) ⊢u = id (Idⱼ (ℕⱼ (wfTerm ⊢u)) ⊢t ⊢u)
IdℕRed*Term′ ⊢t ⊢t′ (x ⇨ d) ⊢u = _⇨_ (Id-ℕ-subst x ⊢u) (IdℕRed*Term′ (redFirst*Term d) ⊢t′ d ⊢u)

Idℕ0Red*Term′ : ∀ {Γ t t′}
                (⊢t : Γ ⊢ t ∷ ℕ ^ [ ! , ι ⁰ ])
                (⊢t′ : Γ ⊢ t′ ∷ ℕ ^ [ ! , ι ⁰ ])
                (d : Γ ⊢ t ⇒* t′ ∷ ℕ ^ ι ⁰)
              → Γ ⊢ Id ℕ zero t ⇒* Id ℕ zero t′ ∷ SProp ⁰ ^ next ⁰
Idℕ0Red*Term′ ⊢t ⊢t′ (id x) = id (Idⱼ (ℕⱼ (wfTerm ⊢t)) (zeroⱼ (wfTerm ⊢t)) ⊢t)
Idℕ0Red*Term′ ⊢t ⊢t′ (x ⇨ d) = Id-ℕ-0-subst x ⇨ Idℕ0Red*Term′ (redFirst*Term d) ⊢t′ d

IdℕSRed*Term′ : ∀ {Γ t u u′}
                (⊢t : Γ ⊢ t ∷ ℕ ^ [ ! , ι ⁰ ])
                (⊢u : Γ ⊢ u ∷ ℕ ^ [ ! , ι ⁰ ])
                (⊢u′ : Γ ⊢ u′ ∷ ℕ ^ [ ! , ι ⁰ ])
                (d : Γ ⊢ u ⇒* u′ ∷ ℕ ^ ι ⁰)
              → Γ ⊢ Id ℕ (suc t) u ⇒* Id ℕ (suc t) u′ ∷ SProp ⁰ ^ next ⁰
IdℕSRed*Term′ ⊢t ⊢u ⊢u′ (id x) = id (Idⱼ (ℕⱼ (wfTerm ⊢t)) (sucⱼ ⊢t) ⊢u)
IdℕSRed*Term′ ⊢t ⊢u ⊢u′ (x ⇨ d) = Id-ℕ-S-subst ⊢t x ⇨ IdℕSRed*Term′ ⊢t (redFirst*Term d) ⊢u′ d

appRed* : ∀ {Γ a t u A B rA lA lB l}
          (⊢a : Γ ⊢ a ∷ A ^ [ rA , ι lA ])
          (D : Γ ⊢ t ⇒* u ∷ (Π A ^ rA ° lA ▹ B ° lB) ^ ι l)
        → Γ ⊢ t ∘ a ⇒* u ∘ a ∷ B [ a ] ^ ι lB
appRed* ⊢a (id x) = id (x ∘ⱼ ⊢a)
appRed* ⊢a (x ⇨ D) = app-subst x ⊢a ⇨ appRed* ⊢a D

castΠRed* : ∀ {Γ F rF G A B e t}
         (⊢F : Γ ⊢ F ^ [ rF , ι ⁰ ])
         (⊢G : Γ ∙ F ^ [ rF , ι ⁰ ] ⊢ G ^ [ ! , ι ⁰ ])
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) (Π F ^ rF ° ⁰ ▹ G ° ⁰) A ^ [ % , next ⁰ ])
         (⊢t : Γ ⊢ t ∷ Π F ^ rF ° ⁰ ▹ G ° ⁰ ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A ⇒* B ^ [ ! , ι ⁰ ])
       → Γ ⊢ cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰) A e t ⇒* cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰) B e t ∷ A ^ ι ⁰
castΠRed* ⊢F ⊢G ⊢e ⊢t (id (univ ⊢A)) = id (castⱼ (Πⱼ ≡is≤ PE.refl ▹ ≡is≤ PE.refl ▹ un-univ ⊢F ▹ un-univ ⊢G) ⊢A ⊢e ⊢t)
castΠRed* ⊢F ⊢G ⊢e ⊢t ((univ d) ⇨ D) = cast-Π-subst (un-univ ⊢F) (un-univ ⊢G) d ⊢e ⊢t ⇨ conv* (castΠRed* ⊢F ⊢G (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢F))) (refl (Πⱼ ≡is≤ PE.refl ▹ ≡is≤ PE.refl ▹ un-univ ⊢F ▹ un-univ ⊢G)) (subsetTerm d)))) ⊢t D) (sym (subset (univ d)))


notredUterm* : ∀ {Γ r l l' A B} → Γ ⊢ Univ r l ⇒ A ∷ B ^ l' → ⊥
notredUterm* (conv D x) = notredUterm* D

notredU* : ∀ {Γ r l l' A} → Γ ⊢ Univ r l ⇒ A ^ [ ! , l' ] → ⊥
notredU* (univ x) = notredUterm* x

redU*gen : ∀ {Γ r l r' l' l''} → Γ ⊢ Univ r l ⇒* Univ r' l' ^ [ ! , l'' ] → Univ r l PE.≡ Univ r' l'
redU*gen (id x) = PE.refl
redU*gen (univ (conv x x₁) ⇨ D) = ⊥-elim (notredUterm* x)

-- Typing of Idsym

Idsymⱼ : ∀ {Γ A l x y e}
       → Γ ⊢ A ∷ U l ^ [ ! , next l ]
       → Γ ⊢ x ∷ A ^ [ ! , ι l ]
       → Γ ⊢ y ∷ A ^ [ ! , ι l ]
       → Γ ⊢ e ∷ Id A x y ^ [ % , ι l ]
       → Γ ⊢ Idsym A x y e ∷ Id A y x ^ [ % , ι l ]
Idsymⱼ {Γ} {A} {l} {x} {y} {e} ⊢A ⊢x ⊢y ⊢e =
  let
    ⊢Γ = wfTerm ⊢A
    ⊢A = univ ⊢A
    ⊢P : Γ ∙ A ^ [ ! , ι l ] ⊢ Id (wk1 A) (var 0) (wk1 x) ^ [ % , ι l ]
    ⊢P = univ (Idⱼ (Twk.wkTerm (Twk.step Twk.id) (⊢Γ ∙ ⊢A) (un-univ ⊢A))
      (var (⊢Γ ∙ ⊢A) here)
      (Twk.wkTerm (Twk.step Twk.id) (⊢Γ ∙ ⊢A) ⊢x))
    ⊢refl : Γ ⊢ Idrefl A x ∷ Id (wk1 A) (var 0) (wk1 x) [ x ] ^ [ % , ι l ]
    ⊢refl = PE.subst₂ (λ X Y → Γ ⊢ Idrefl A x ∷ Id X x Y ^ [ % , ι l ])
      (PE.sym (wk1-singleSubst A x)) (PE.sym (wk1-singleSubst x x))
      (Idreflⱼ ⊢x)
  in PE.subst₂ (λ X Y → Γ ⊢ Idsym A x y e ∷ Id X y Y ^ [ % , ι l ])
    (wk1-singleSubst A y) (wk1-singleSubst x y)
    (transpⱼ ⊢A ⊢P ⊢x ⊢refl ⊢y ⊢e)
