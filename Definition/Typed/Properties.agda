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


-- Escape context extraction

wfTerm : ∀ {Γ A t r} → Γ ⊢ t ∷ A ^ r → ⊢ Γ
wfTerm (univ <l ⊢Γ) = ⊢Γ
wfTerm (ℕⱼ ⊢Γ) = ⊢Γ
wfTerm (Emptyⱼ ⊢Γ) = ⊢Γ
wfTerm (Πⱼ <l ▹ <l' ▹ F ▹ G) = wfTerm F
wfTerm (var ⊢Γ x₁) = ⊢Γ
wfTerm (lamⱼ _ _ F t) with wfTerm t
wfTerm (lamⱼ _ _ F t) | ⊢Γ ∙ F′ = ⊢Γ
wfTerm (_ ▹ _ ▹ _ ▹ g ∘ⱼ a) = wfTerm a
wfTerm (fstⱼ A B A' B' e) = wfTerm e
wfTerm (sndⱼ A B A' B' e) = wfTerm e
wfTerm (zeroⱼ ⊢Γ) = ⊢Γ
wfTerm (sucⱼ n) = wfTerm n
wfTerm (natrecⱼ _ F z s n) = wfTerm z
wfTerm (Emptyrecⱼ A e) = wfTerm e
wfTerm (Idⱼ A t u) = wfTerm t
wfTerm (Idreflⱼ t) = wfTerm t
wfTerm (transpⱼ A P t s u e) = wfTerm t
wfTerm (castⱼ A B e t) = wfTerm t
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
  wfEqTerm (app-cong f≡g a≡b) = wfEqTerm f≡g
  wfEqTerm (β-red _ _ F t a) = wfTerm a
  wfEqTerm (η-eq _ _ F f g f0≡g0) = wfTerm f
  wfEqTerm (suc-cong n) = wfEqTerm n
  wfEqTerm (natrec-cong F≡F′ z≡z′ s≡s′ n≡n′) = wfEqTerm z≡z′
  wfEqTerm (natrec-zero F z s) = wfTerm z
  wfEqTerm (natrec-suc n F z s) = wfTerm n
  wfEqTerm (Emptyrec-cong A≡A' _ _) = wfEq A≡A'
  wfEqTerm (proof-irrelevance t u) = wfTerm t
  wfEqTerm (Id-cong A t u) = wfEqTerm u
  wfEqTerm (cast-refl A e t) = wfTerm t
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

subsetTerm (suc-subst n⇒n′) = suc-cong (subsetTerm n⇒n′)
subsetTerm (natrec-subst F z s n⇒n′ _) =
  natrec-cong (refl F) (refl z) (refl s) (subsetTerm n⇒n′)
subsetTerm (natrec-substF F⇒F′ z s n _) =
  natrec-cong (subset F⇒F′) (refl z) (refl s) (refl n)
subsetTerm (natrec-substZ F z⇒z′ s n _ _) =
  natrec-cong (refl F) (subsetTerm z⇒z′) (refl s) (refl n)
subsetTerm (natrec-substS F z s⇒s′ n _ _ _) =
  natrec-cong (refl F) (refl z) (subsetTerm s⇒s′) (refl n)
subsetTerm (natrec-zero F z s) = natrec-zero F z s
subsetTerm (natrec-suc n F z s) = natrec-suc n F z s
subsetTerm (app-subst {rA = !} ⊢F ⊢G t⇒u a _) = app-cong (subsetTerm t⇒u) (refl a)
subsetTerm (app-subst {rA = %} ⊢F ⊢G t⇒u a _) = app-cong (subsetTerm t⇒u) (proof-irrelevance a a)
subsetTerm (app-subst' ⊢F ⊢G t net a⇒b) = app-cong (refl t) (subsetTerm a⇒b) 
subsetTerm (β-red l< l<' A B t a) = β-red l< l<' A t a
subsetTerm (conv t⇒u A≡B) = conv (subsetTerm t⇒u) A≡B
subsetTerm (cast-subst A B e t _) = let ⊢Γ = wfEqTerm (subsetTerm A)
                                  in cast-cong (subsetTerm A) (refl B) (refl t) e (conv e (univ (Id-cong (refl (univ 0<1 ⊢Γ)) (subsetTerm A) (refl B))))
subsetTerm (cast-ne-subst A neA B e t _) = let ⊢Γ = wfEqTerm (subsetTerm B)
                                  in cast-cong (refl A) (subsetTerm B) (refl t) e (conv e (univ (Id-cong (refl (univ 0<1 ⊢Γ)) (refl A) (subsetTerm B))))
subsetTerm (cast-ℕ-subst B e t _) = let ⊢Γ = wfEqTerm (subsetTerm B)
                                  in cast-cong (refl (ℕⱼ (wfTerm t))) (subsetTerm B) (refl t) e (conv e (univ (Id-cong (refl (univ 0<1 ⊢Γ)) (refl (ℕⱼ ⊢Γ)) (subsetTerm B))))
subsetTerm (cast-Π-subst A P B e t _) = let ⊢Γ = wfTerm A
                                      in cast-cong (refl (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ A ▹ P)) (subsetTerm B) (refl t) e
                                                   (conv e (univ (Id-cong (refl (univ 0<1 ⊢Γ)) (refl (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ A ▹ P)) (subsetTerm B) )))
subsetTerm (cast-Π A B A' B' e f) = cast-Π A B A' B' e f
subsetTerm (cast-ℕ-0 e) = cast-ℕ-0 e
subsetTerm (cast-ℕ-S e n) = cast-ℕ-S e n
subsetTerm (cast-ℕ-cong e n _) = let ⊢Γ = wfTerm e
                                     ⊢ℕ = ℕⱼ ⊢Γ
                                 in cast-cong (refl ⊢ℕ) (refl ⊢ℕ) (subsetTerm n) e e
subsetTerm (cast-ne-cong A neA B neB e t) = let ⊢Γ = wfTerm A
                                  in cast-cong (refl A) (refl B) (subsetTerm t) e e

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
redFirstTerm (app-subst ⊢F ⊢G t⇒u a _) = (λ abs → ⊥-elim (!≢% abs)) ▹ ⊢F ▹ ⊢G ▹ (redFirstTerm t⇒u) ∘ⱼ a
redFirstTerm (app-subst' ⊢F ⊢G t net a⇒b) = (λ abs → ⊥-elim (!≢% abs)) ▹ ⊢F ▹ ⊢G ▹ t ∘ⱼ (redFirstTerm a⇒b)
redFirstTerm (β-red {lA = lA} {lB = lB} lA< lB< ⊢A ⊢B ⊢t ⊢a) = (λ abs → ⊥-elim (!≢% abs)) ▹ un-univ ⊢A ▹ ⊢B ▹ (lamⱼ (λ _ → lA< , lB<) (λ abs → ⊥-elim (!≢% abs)) ⊢A ⊢t) ∘ⱼ ⊢a
redFirstTerm (suc-subst n⇒n′) = sucⱼ (redFirstTerm n⇒n′)
redFirstTerm (natrec-subst F z s n⇒n′ _) = natrecⱼ (λ x → ⊥-elim (!≢% x)) F z s (redFirstTerm n⇒n′)
redFirstTerm (natrec-substF F⇒F′ z s n _) = natrecⱼ (λ x → ⊥-elim (!≢% x)) (redFirst F⇒F′) z s n
redFirstTerm (natrec-substZ F z⇒z′ s n _ _) = natrecⱼ (λ x → ⊥-elim (!≢% x)) F (redFirstTerm z⇒z′) s n
redFirstTerm (natrec-substS F z s⇒s′ n _ _ _) = natrecⱼ (λ x → ⊥-elim (!≢% x)) F z (redFirstTerm s⇒s′) n
redFirstTerm (natrec-zero F z s) = natrecⱼ (λ x → ⊥-elim (!≢% x)) F z s (zeroⱼ (wfTerm z))
redFirstTerm (natrec-suc n F z s) = natrecⱼ (λ x → ⊥-elim (!≢% x)) F z s (sucⱼ n)
redFirstTerm (cast-subst A B e t _) = castⱼ (redFirstTerm A) B e t
redFirstTerm (cast-ne-subst A neA B e t _) = castⱼ A (redFirstTerm B) e t
redFirstTerm (cast-ℕ-subst B e t _) = castⱼ (ℕⱼ (wfTerm t)) (redFirstTerm B) e t
redFirstTerm (cast-Π-subst A P B e t _) = castⱼ (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ A ▹ P) (redFirstTerm B) e t
redFirstTerm (cast-Π A B A' B' e f) = castⱼ (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ A ▹ B) (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ A' ▹ B') e f
redFirstTerm (cast-ℕ-0 e) = castⱼ (ℕⱼ (wfTerm e)) (ℕⱼ (wfTerm e)) e (zeroⱼ (wfTerm e))
redFirstTerm (cast-ℕ-S e n) = castⱼ (ℕⱼ (wfTerm e)) (ℕⱼ (wfTerm e)) e (sucⱼ n)
redFirstTerm (cast-ℕ-cong e n _) = castⱼ (ℕⱼ (wfTerm e)) (ℕⱼ (wfTerm e)) e (redFirstTerm n)
redFirstTerm (cast-ne-cong K neK L neL e n) = castⱼ K L e (redFirstTerm n)

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
nfRedTerm : ∀ {Γ t u A l} (d : Γ ⊢ t ⇒ u ∷ A ^ l) (w : Nf t) → ⊥
nfRed : ∀ {Γ A B r} (d : Γ ⊢ A ⇒ B ^ r) (w : Nf A) → ⊥

neRedTerm (conv d x) n = neRedTerm d n
neRedTerm (app-subst _ _ d x _) (∘ₙ n _) = neRedTerm d n
neRedTerm (app-subst' _ _ _ _ d) (∘ₙ n u) = nfRedTerm d u
neRedTerm (β-red _ _ _ x x₁ x₂) (∘ₙ () _)
neRedTerm (natrec-zero x x₁ x₂) (natrecₙ () _ _ _)
neRedTerm (natrec-suc x x₁ x₂ x₃) (natrecₙ () _ _ _)
neRedTerm (natrec-subst _ _ _ tr _) (natrecₙ tn _ _ _) = neRedTerm tr tn
neRedTerm (natrec-substF tr _ _ _ _) (natrecₙ _ tF _ _) = nfRed tr tF
neRedTerm (natrec-substZ _ tr _ _ _ _) (natrecₙ _ _ tz _) = nfRedTerm tr tz
neRedTerm (natrec-substS _ _ tr _ _ _ _) (natrecₙ _ _ _ ts) = nfRedTerm tr ts
neRedTerm (cast-subst tr B e x _) (castₙ tn un _) = neRedTerm tr tn
neRedTerm (cast-ne-subst A neA tr e x _) (castₙ tn un _) = neRedTerm tr un
neRedTerm (cast-ne-subst A neA tr e x _) (castnΠₙ Bn An Pn tn) = nfRedTerm tr (Πₙ An Pn)
neRedTerm (cast-ne-subst A neA tr e x _) (castnℕₙ tn _) = nfRedTerm tr ℕₙ
neRedTerm (cast-Π-subst A B tr e x _) (castΠₙ tn An Pn _) = neRedTerm tr tn
neRedTerm (cast-Π-subst A B tr e x _) (castΠℕₙ An Pn _) = nfRedTerm tr ℕₙ
neRedTerm (cast-subst tr x x₁ x₂ _) (castℕₙ tn _) = nfRedTerm tr ℕₙ
neRedTerm (cast-subst tr x x₁ x₂ _) (castΠₙ tn An Pn _) = nfRedTerm tr (Πₙ An Pn)
neRedTerm (cast-subst tr x x₁ x₂ _) (castnℕₙ tn _) = neRedTerm tr tn
neRedTerm (cast-subst tr x x₁ x₂ _) (castnΠₙ tn An Pn _) = neRedTerm tr tn
neRedTerm (cast-subst tr x x₁ x₂ _) (castℕℕₙ tn) = nfRedTerm tr ℕₙ
neRedTerm (cast-subst tr x x₁ x₂ _) (castℕΠₙ An Pn _) = nfRedTerm tr ℕₙ
neRedTerm (cast-subst tr x x₁ x₂ _) (castΠℕₙ An Pn _) = nfRedTerm tr (Πₙ An Pn)
neRedTerm (cast-ℕ-subst tr x x₁ _) (castℕₙ tn _) = neRedTerm tr tn
neRedTerm (cast-ℕ-subst tr x x₁ _) (castℕℕₙ tn) = nfRedTerm tr ℕₙ
neRedTerm (cast-ℕ-subst tr x x₁ _) (castℕΠₙ An Pn _) = nfRedTerm tr (Πₙ An Pn)
neRedTerm (cast-Π A B A' B' e f) (castₙ () _ _)
neRedTerm (cast-Π A B A' B' e f) (castΠₙ () An Pn _)
neRedTerm (cast-ℕ-0 x) (castₙ () _ _)
neRedTerm (cast-ℕ-0 x) (castℕₙ () _)
neRedTerm (cast-ℕ-0 x) (castℕℕₙ ())
neRedTerm (cast-ℕ-S x x₁) (castₙ () _ _)
neRedTerm (cast-ℕ-S x x₁) (castℕₙ () _)
neRedTerm (cast-ℕ-S x x₁) (castℕℕₙ ())
neRedTerm (cast-ℕ-cong x x₁ _) (castₙ () _ _)
neRedTerm (cast-ℕ-cong x x₁ _) (castℕₙ () _)
neRedTerm (cast-ℕ-cong x x₁ _) (castℕℕₙ t) = neRedTerm x₁ t
neRedTerm (cast-subst d x x₁ x₂ _) (castΠΠ%!ₙ An Pn An' Pn' _) = nfRedTerm d (Πₙ An Pn)
neRedTerm (cast-subst d x x₁ x₂ _) (castΠΠ!%ₙ An Pn An' Pn' _) = nfRedTerm d (Πₙ An Pn)
neRedTerm (cast-Π-subst x x₁ d x₂ x₃ _) (castΠΠ%!ₙ An Pn An' Pn' _) = nfRedTerm d (Πₙ An' Pn')
neRedTerm (cast-Π-subst x x₁ d x₂ x₃ _) (castΠΠ!%ₙ An Pn An' Pn' _) = nfRedTerm d (Πₙ An' Pn')
neRedTerm (cast-ne-cong K neK L neL e tr) (castₙ X X₁ X₂) = neRedTerm tr X₂

neRed (univ x) N = neRedTerm x N

nfRedTerm (conv d x) w = nfRedTerm d w
nfRedTerm (app-subst _ _ d x _) (ne (∘ₙ x₁ _)) = neRedTerm d x₁
nfRedTerm (app-subst' _ _ _ _ d) (ne (∘ₙ _ x₁)) = nfRedTerm d x₁
nfRedTerm (β-red _ _ _ x x₁ x₂) (ne (∘ₙ () _))
nfRedTerm (suc-subst d) (sucₙ n) = nfRedTerm d n
nfRedTerm (natrec-subst x x₁ x₂ d _) (ne (natrecₙ x₃ _ _ _)) = neRedTerm d x₃
nfRedTerm (natrec-substF tr _ _ _ _) (ne (natrecₙ _ tF _ _)) = nfRed tr tF
nfRedTerm (natrec-substZ _ tr _ _ _ _) (ne (natrecₙ _ _ tz _)) = nfRedTerm tr tz
nfRedTerm (natrec-substS _ _ tr _ _ _ _) (ne (natrecₙ _ _ _ ts)) = nfRedTerm tr ts
nfRedTerm (natrec-zero x x₁ x₂) (ne (natrecₙ () _ _ _))
nfRedTerm (natrec-suc x x₁ x₂ x₃) (ne (natrecₙ () _ _ _))
nfRedTerm (cast-subst d x x₁ x₂ _) (ne (castₙ x₃ y _)) = neRedTerm d x₃
nfRedTerm (cast-subst d x x₁ x₂ _) (ne (castnℕₙ x₃ _)) = neRedTerm d x₃
nfRedTerm (cast-subst d x x₁ x₂ _) (ne (castnΠₙ x₃ An Pn _)) = neRedTerm d x₃
nfRedTerm (cast-subst d x x₁ x₂ _) (ne (castℕₙ x₃ _)) = nfRedTerm d ℕₙ
nfRedTerm (cast-subst d x x₁ x₂ _) (ne (castΠₙ x₃ An Pn _)) = nfRedTerm d (Πₙ An Pn)
nfRedTerm (cast-subst d x x₁ x₂ _) (ne (castℕℕₙ x₃)) = nfRedTerm d ℕₙ
nfRedTerm (cast-subst d x x₁ x₂ _) (ne (castℕΠₙ An Pn _)) = nfRedTerm d ℕₙ
nfRedTerm (cast-subst d x x₁ x₂ _) (ne (castΠℕₙ An Pn _)) = nfRedTerm d (Πₙ An Pn)
nfRedTerm (cast-ne-subst x nex d x₁ x₂ _) (ne (castₙ x₃ y _)) = neRedTerm d y 
nfRedTerm (cast-ne-subst x nex d x₁ x₂ _) (ne (castnℕₙ x₃ _)) = nfRedTerm d ℕₙ
nfRedTerm (cast-ne-subst x nex d x₁ x₂ _) (ne (castnΠₙ x₃ An Pn _)) =  nfRedTerm d (Πₙ An Pn)
nfRedTerm (cast-ne-subst x () d x₁ x₂ _) (ne (castℕₙ x₃ _)) 
nfRedTerm (cast-ne-subst x () d x₁ x₂ _) (ne (castΠₙ x₃ An Pn _)) 
nfRedTerm (cast-ne-subst x () d x₁ x₂ _) (ne (castℕℕₙ x₃))
nfRedTerm (cast-ne-subst x () d x₁ x₂ _) (ne (castℕΠₙ An Pn _))
nfRedTerm (cast-ne-subst x () d x₁ x₂ _) (ne (castΠℕₙ An Pn _))
nfRedTerm (cast-ℕ-subst d x x₁ _) (ne (castℕₙ x₂ _)) = neRedTerm d x₂
nfRedTerm (cast-ℕ-subst d x x₁ _) (ne (castℕℕₙ x₂)) = nfRedTerm d ℕₙ
nfRedTerm (cast-ℕ-subst d x x₁ _) (ne (castℕΠₙ An Pn _)) = nfRedTerm d (Πₙ An Pn)
nfRedTerm (cast-Π-subst x x₁ d x₂ x₃ _) (ne (castΠₙ x₄ An Pn _)) = neRedTerm d x₄
nfRedTerm (cast-Π-subst x x₁ d x₂ x₃ _) (ne (castΠℕₙ An Pn _)) = nfRedTerm d ℕₙ
nfRedTerm (cast-Π x x₁ x₂ x₃ x₄ x₅) (ne (castₙ () _ _))
nfRedTerm (cast-Π x x₁ x₂ x₃ x₄ x₅) (ne (castΠₙ () An Pn _))
nfRedTerm (cast-ℕ-0 x) (ne (castₙ () _ _))
nfRedTerm (cast-ℕ-0 x) (ne (castℕₙ () _))
nfRedTerm (cast-ℕ-0 x) (ne (castℕℕₙ ()))
nfRedTerm (cast-ℕ-S x x₁) (ne (castₙ () _ _))
nfRedTerm (cast-ℕ-S x x₁) (ne (castℕₙ () _))
nfRedTerm (cast-ℕ-S x x₁) (ne (castℕℕₙ ()))
nfRedTerm (cast-ℕ-cong x x₁ _) (ne (castₙ () _ _))
nfRedTerm (cast-ℕ-cong x x₁ _) (ne (castℕₙ () _))
nfRedTerm (cast-ℕ-cong x x₁ _) (ne (castℕℕₙ t)) = neRedTerm x₁ t
nfRedTerm (cast-subst d x x₁ x₂ _) (ne (castΠΠ%!ₙ An Pn An' Pn' _)) = nfRedTerm d (Πₙ An Pn)
nfRedTerm (cast-subst d x x₁ x₂ _) (ne (castΠΠ!%ₙ An Pn An' Pn' _)) = nfRedTerm d (Πₙ An Pn)
nfRedTerm (cast-Π-subst x x₁ d x₂ x₃ _) (ne (castΠΠ%!ₙ An Pn An' Pn' _)) = nfRedTerm d (Πₙ An' Pn')
nfRedTerm (cast-Π-subst x x₁ d x₂ x₃ _) (ne (castΠΠ!%ₙ An Pn An' Pn' _)) = nfRedTerm d (Πₙ An' Pn')
nfRedTerm (cast-ne-cong K neK L neL e tr) (ne (castₙ x x₁ x₂)) = neRedTerm tr x₂

nfRed (univ x) w = nfRedTerm x w

nfRed*Term : ∀ {Γ t u A l} (d : Γ ⊢ t ⇒* u ∷ A ^ l) (w : Nf t) → t PE.≡ u
nfRed*Term (id x) Uₙ = PE.refl
nfRed*Term (id x) (Πₙ _ _) = PE.refl
nfRed*Term (id x) (Idₙ _ _ _) = PE.refl
nfRed*Term (id x) ℕₙ = PE.refl
nfRed*Term (id x) Emptyₙ = PE.refl
nfRed*Term (id x) (sucₙ _) = PE.refl
nfRed*Term (id x) (lamₙ _) = PE.refl
nfRed*Term (id x) zeroₙ = PE.refl
nfRed*Term (id x) (ne x₁) = PE.refl
nfRed*Term (x ⇨ d) x₁ = ⊥-elim (nfRedTerm x x₁)

nfRed* : ∀ {Γ A B r} (d : Γ ⊢ A ⇒* B ^ r) (w : Nf A) → A PE.≡ B
nfRed* (id x) w = PE.refl
nfRed* (x ⇨ d) w = ⊥-elim (nfRed x w)

-- Whr is deterministic

-- somehow the cases (cast-Π, cast-Π) and (Id-U-ΠΠ, Id-U-ΠΠ) fail if
-- we do not introduce a dummy relevance rA'. This is why we need the two
-- auxiliary functions. 
whrDetTerm-aux1 : ∀{Γ t u F lF A A' rA lA lB rA' l B B' e f}
  → (d :  t PE.≡ cast l (Π A ^ rA ° lA ▹ B ° lB ° l ^ !) (Π A' ^ rA' ° lA ▹ B' ° lB ° l ^ !) e f)
  → (d′ : Γ ⊢ t ⇒ u ∷ F ^ lF)
  → (lam A' ▹ (let a = cast l (wk1 A') (wk1 A) (Idsym (Univ rA l) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0) in cast l (B [ a ]↑) B' ((snd (wk1 e)) ∘ (var 0) ^ ⁰) ((wk1 f) ∘ a ^ l)) ^ l) PE.≡ u
whrDetTerm-aux1 d (conv d' x) = whrDetTerm-aux1 d d'
whrDetTerm-aux1 PE.refl (cast-subst d' x x₁ x₂ notType) = ⊥-elim (notType Πₙ)
whrDetTerm-aux1 PE.refl (cast-ne-subst x nex d' x₁ x₂ notType) = ⊥-elim (notType Πₙ)
whrDetTerm-aux1 PE.refl (cast-Π-subst x x₁ d' x₂ x₃ notType) = ⊥-elim (notType Πₙ)
whrDetTerm-aux1 PE.refl (cast-Π x x₁ x₂ x₃ x₄ x₅) = PE.refl
whrDetTerm-aux1 PE.refl (cast-ne-cong K () L neL e tr)

whrDetTerm : ∀{Γ t u A l u′ A′ l′} (d : Γ ⊢ t ⇒ u ∷ A ^ l) (d′ : Γ ⊢ t ⇒ u′ ∷ A′ ^ l′) → u PE.≡ u′
whrDet : ∀{Γ A B B′ r r'} (d : Γ ⊢ A ⇒ B ^ r) (d′ : Γ ⊢ A ⇒ B′ ^ r') → B PE.≡ B′

whrDetTerm (conv d x) d′ = whrDetTerm d d′
whrDetTerm (app-subst _ _ d x _) (app-subst _ _ d′ x₁ _) rewrite whrDetTerm d d′ = PE.refl
whrDetTerm (app-subst _ _ d x notLam) (β-red _ _ _ x₁ x₂ x₃) = ⊥-elim (notLam lamₙ)
whrDetTerm (β-red _ _ _ x x₁ x₂) (app-subst _ _ d' x₃ notLam) = ⊥-elim (notLam lamₙ)
whrDetTerm (β-red _ _ _ x x₁ x₂) (β-red _ _ _ x₃ x₄ x₅) = PE.refl
whrDetTerm (natrec-subst x x₁ x₂ d _) (natrec-subst x₃ x₄ x₅ d' _) rewrite whrDetTerm d d' = PE.refl
whrDetTerm (suc-subst d) (suc-subst d') rewrite whrDetTerm d d' = PE.refl
whrDetTerm (natrec-subst x x₁ x₂ d _) (natrec-zero x₃ x₄ x₅) =  ⊥-elim (nfRedTerm d zeroₙ)
whrDetTerm (natrec-subst x x₁ x₂ d notNat) (natrec-suc x₃ x₄ x₅ x₆) = ⊥-elim (notNat sucₙ) 
whrDetTerm (natrec-zero x x₁ x₂) (natrec-subst x₃ x₄ x₅ d' notNat) = ⊥-elim (nfRedTerm d' zeroₙ)
whrDetTerm (natrec-zero x x₁ x₂) (natrec-zero x₃ x₄ x₅) = PE.refl
whrDetTerm (natrec-suc x x₁ x₂ x₃) (natrec-subst x₄ x₅ x₆ d' notNat) = ⊥-elim (notNat sucₙ)
whrDetTerm (natrec-suc x x₁ x₂ x₃) (natrec-suc x₄ x₅ x₆ x₇) = PE.refl
whrDetTerm (cast-subst d x x₁ x₂ notType) (cast-subst d' x₃ x₄ x₅ notType') rewrite whrDetTerm d d' = PE.refl
whrDetTerm (cast-subst d x x₁ x₂ notType) (cast-ℕ-subst d' x₃ x₄ notType') = ⊥-elim (nfRedTerm d ℕₙ)
whrDetTerm (cast-subst d x x₁ x₂ notType) (cast-Π-subst x₃ x₄ d' x₅ x₆ notType') = ⊥-elim (notType Πₙ)
whrDetTerm (cast-subst d x x₁ x₂ notType) (cast-Π x₃ x₄ x₅ x₆ x₇ x₈) = ⊥-elim (notType Πₙ)
whrDetTerm (cast-subst d x x₁ x₂ notType) (cast-ℕ-0 x₃) = ⊥-elim (nfRedTerm d ℕₙ)
whrDetTerm (cast-subst d x x₁ x₂ notType) (cast-ℕ-S x₃ x₄) = ⊥-elim (nfRedTerm d ℕₙ)
whrDetTerm (cast-subst d x x₁ x₂ notType) (cast-ne-subst y ney d' x₄ x₅ notType') = ⊥-elim (neRedTerm d ney)
whrDetTerm (cast-ne-subst x nex d x₁ x₂ notType) (cast-subst d' x₃ x₄ x₅ notType') = ⊥-elim (neRedTerm d' nex) 
whrDetTerm (cast-ne-subst x () d x₁ x₂ notType) (cast-ℕ-subst d' x₃ x₄ notType') 
whrDetTerm (cast-ne-subst x () d x₁ x₂ notType) (cast-Π-subst x₃ x₄ d' x₅ x₆ notType')
whrDetTerm (cast-ne-subst x () d x₁ x₂ notType) (cast-Π x₃ x₄ x₅ x₆ x₇ x₈)
whrDetTerm (cast-ne-subst x () d x₁ x₂ notType) (cast-ℕ-0 x₃) 
whrDetTerm (cast-ne-subst x () d x₁ x₂ notType) (cast-ℕ-S x₃ x₄) 
whrDetTerm (cast-ne-subst x nex d x₁ x₂ notType) (cast-ne-subst y ney d' x₄ x₅ notType') rewrite whrDetTerm d d' = PE.refl
whrDetTerm (cast-ℕ-subst d x x₁ notType) (cast-subst d' x₂ x₃ x₄ notType') = ⊥-elim (nfRedTerm d' ℕₙ)
whrDetTerm (cast-ℕ-subst d x x₁ notType) (cast-ℕ-subst d' x₂ x₃ notType') rewrite whrDetTerm d d' = PE.refl
whrDetTerm (cast-ℕ-subst d x x₁ notType) (cast-ℕ-0 x₂) = ⊥-elim (nfRedTerm d ℕₙ)
whrDetTerm (cast-ℕ-subst d x x₁ notType) (cast-ℕ-S x₂ x₃) = ⊥-elim (nfRedTerm d ℕₙ)
whrDetTerm (cast-Π-subst x x₁ d x₂ x₃ notType) (cast-subst d' x₄ x₅ x₆ notType') = ⊥-elim (notType' Πₙ)
whrDetTerm (cast-Π-subst x x₁ d x₂ x₃ notType) (cast-Π-subst x₄ x₅ d' x₆ x₇ notType') rewrite whrDetTerm d d' = PE.refl
whrDetTerm (cast-Π-subst x x₁ d x₂ x₃ notType) (cast-Π x₄ x₅ x₆ x₇ x₈ x₉) = ⊥-elim (notType Πₙ)
whrDetTerm (cast-Π x x₁ x₂ x₃ x₄ x₅) d' = whrDetTerm-aux1 (PE.refl) d'
whrDetTerm (cast-ℕ-0 x) (cast-subst d' x₁ x₂ x₃ notType) = ⊥-elim (nfRedTerm d' ℕₙ)
whrDetTerm (cast-ℕ-0 x) (cast-ℕ-subst d' x₁ x₂ notType) = ⊥-elim (nfRedTerm d' ℕₙ)
whrDetTerm (cast-ℕ-0 x) (cast-ℕ-0 x₁) = PE.refl
whrDetTerm (cast-ℕ-S x x₁) (cast-subst d' x₂ x₃ x₄ notType) = ⊥-elim (nfRedTerm d' ℕₙ)
whrDetTerm (cast-ℕ-S x x₁) (cast-ℕ-subst d' x₂ x₃ notType) = ⊥-elim (nfRedTerm d' ℕₙ)
whrDetTerm (cast-ℕ-S x x₁) (cast-ℕ-S x₂ x₃) = PE.refl
whrDetTerm (cast-ℕ-cong x x₁ notNat) (cast-subst d' x₂ x₃ x₄ notType) = ⊥-elim (nfRedTerm d' ℕₙ)
whrDetTerm (cast-ℕ-cong x x₁ notNat) (cast-ℕ-subst d' x₂ x₃ notType) = ⊥-elim (nfRedTerm d' ℕₙ)
whrDetTerm (cast-ℕ-cong x x₁ notNat) (cast-ℕ-cong x₂ x₃ notNat') rewrite whrDetTerm x₁ x₃ = PE.refl
whrDetTerm (cast-subst d x x₁ x₂ notType) (cast-ℕ-cong x₃ d′ notNat) = ⊥-elim (nfRedTerm d ℕₙ)
whrDetTerm (cast-ℕ-subst d x x₁ notType) (cast-ℕ-cong x₂ d′ notNat) = ⊥-elim (nfRedTerm d ℕₙ)
whrDetTerm (cast-ℕ-0 x) (cast-ℕ-cong x₁ d′ notNat) = ⊥-elim (nfRedTerm d′ zeroₙ)
whrDetTerm (cast-ℕ-S x x₁) (cast-ℕ-cong x₂ d′ notNat) = ⊥-elim (notNat sucₙ)
whrDetTerm (cast-ℕ-cong x d notNat) (cast-ℕ-0 x₁) = ⊥-elim (nfRedTerm d zeroₙ)
whrDetTerm (cast-ℕ-cong x d notNat) (cast-ℕ-S x₁ x₂) = ⊥-elim (notNat sucₙ)
whrDetTerm (cast-ne-cong K neK L neL x d) (cast-subst X x₁ x₂ x₃ notType) = ⊥-elim (neRedTerm X neK) 
whrDetTerm (cast-ne-cong K neK L neL x d) (cast-ne-subst x₁ x₂ X x₃ x₄ notType) = ⊥-elim (neRedTerm X neL) 
whrDetTerm (cast-ne-cong K neK L neL x d) (cast-ne-cong x₁ x₂ x₃ x₄ x₅ X) rewrite whrDetTerm d X = PE.refl
whrDetTerm (cast-subst X x x₁ x₂ notType) (cast-ne-cong K neK L neL e tr) = ⊥-elim (neRedTerm X neK)
whrDetTerm (cast-ne-subst x x₁ X x₂ x₃ notType) (cast-ne-cong K neK L neL e tr) = ⊥-elim (neRedTerm X neL) 
whrDetTerm (app-subst x₁ x₂ d x₃ notLam) (app-subst' x₅ x₆ x₇ x₈ d′) = ⊥-elim (neRedTerm d x₈)
whrDetTerm (app-subst' x x₁ x₂ x₃ d) (app-subst x₄ x₅ d′ x₆ notLam) = ⊥-elim (neRedTerm d′ x₃)
whrDetTerm (app-subst' x x₁ x₂ x₃ d) (app-subst' x₄ x₅ x₆ x₇ d′) rewrite whrDetTerm d d′ = PE.refl
whrDetTerm (natrec-subst x₁ x₂ x₃ d notNat) (natrec-substF x₅ x₆ x₇ x₈ x₉) = ⊥-elim (neRedTerm d x₉)
whrDetTerm (natrec-subst x₁ x₂ x₃ d notNat) (natrec-substZ x₅ d′ x₆ x₇ x₈ x₉) = ⊥-elim (neRedTerm d x₈)
whrDetTerm (natrec-subst x₁ x₂ x₃ d notNat) (natrec-substS x₅ x₆ d′ x₇ x₈ x₉ x₁₀) = ⊥-elim (neRedTerm d x₈)
whrDetTerm (natrec-substF x x₁ x₂ x₃ x₄) (natrec-subst x₅ x₆ x₇ d′ notNat) = ⊥-elim (neRedTerm d′ x₄)
whrDetTerm (natrec-substF x x₁ x₂ x₃ x₄) (natrec-substF x₅ x₆ x₇ x₈ x₉) rewrite whrDet x x₅ = PE.refl
whrDetTerm (natrec-substF x x₁ x₂ x₃ x₄) (natrec-substZ x₅ d′ x₆ x₇ x₈ x₉) = ⊥-elim (nfRed x x₉)
whrDetTerm (natrec-substF x x₁ x₂ x₃ x₄) (natrec-substS x₅ x₆ d′ x₇ x₈ x₉ x₁₀) = ⊥-elim (nfRed x x₉)
whrDetTerm (natrec-substZ x d x₁ x₂ x₃ x₄) (natrec-subst x₅ x₆ x₇ d′ x₈notNat) = ⊥-elim (neRedTerm d′ x₃)
whrDetTerm (natrec-substZ x d x₁ x₂ x₃ x₄) (natrec-substF x₅ x₆ x₇ x₈ x₉) = ⊥-elim (nfRed x₅ x₄)
whrDetTerm (natrec-substZ x d x₁ x₂ x₃ x₄) (natrec-substZ x₅ d′ x₆ x₇ x₈ x₉) rewrite whrDetTerm d d′ = PE.refl
whrDetTerm (natrec-substZ x d x₁ x₂ x₃ x₄) (natrec-substS x₅ x₆ d′ x₇ x₈ x₉ x₁₀) = ⊥-elim (nfRedTerm d x₁₀)
whrDetTerm (natrec-substS x x₁ d x₂ x₃ x₄ x₅) (natrec-subst x₆ x₇ x₈ d′ notNat) = ⊥-elim (neRedTerm d′ x₃)
whrDetTerm (natrec-substS x x₁ d x₂ x₃ x₄ x₅) (natrec-substF x₆ x₇ x₈ x₉ x₁₀) = ⊥-elim (nfRed x₆ x₄)
whrDetTerm (natrec-substS x x₁ d x₂ x₃ x₄ x₅) (natrec-substZ x₆ d′ x₇ x₈ x₉ x₁₀) = ⊥-elim (nfRedTerm d′ x₅)
whrDetTerm (natrec-substS x x₁ d x₂ x₃ x₄ x₅) (natrec-substS x₆ x₇ d′ x₈ x₉ x₁₀ x₁₁) rewrite whrDetTerm d d′ = PE.refl

{-# CATCHALL #-}
whrDetTerm d (conv d′ x₁) = whrDetTerm d d′

whrDet (univ x) (univ x₁) = whrDetTerm x x₁

whrDet↘Term : ∀{Γ t u A l u′} (d : Γ ⊢ t ↘ u ∷ A ^ l) (d′ : Γ ⊢ t ⇒* u′ ∷ A ^ l)
  → Γ ⊢ u′ ⇒* u ∷ A ^ l
whrDet↘Term (proj₁ , proj₂) (id x) = proj₁
whrDet↘Term (id x , proj₂) (x₁ ⇨ d′) = ⊥-elim (nfRedTerm x₁ proj₂)
whrDet↘Term (x ⇨ proj₁ , proj₂) (x₁ ⇨ d′) =
  whrDet↘Term (PE.subst (λ x₂ → _ ⊢ x₂ ↘ _ ∷ _ ^ _) (whrDetTerm x x₁) (proj₁ , proj₂)) d′

whrDet*Term : ∀{Γ t u A A' l u′ } (d : Γ ⊢ t ↘ u ∷ A ^ l) (d′ : Γ ⊢ t ↘ u′ ∷ A' ^ l) → u PE.≡ u′
whrDet*Term (id x , proj₂) (id x₁ , proj₄) = PE.refl
whrDet*Term (id x , proj₂) (x₁ ⇨ proj₃ , proj₄) = ⊥-elim (nfRedTerm x₁ proj₂)
whrDet*Term (x ⇨ proj₁ , proj₂) (id x₁ , proj₄) = ⊥-elim (nfRedTerm x proj₄)
whrDet*Term (x ⇨ proj₁ , proj₂) (x₁ ⇨ proj₃ , proj₄) =
  whrDet*Term (proj₁ , proj₂) (PE.subst (λ x₂ → _ ⊢ x₂ ↘ _ ∷ _ ^ _)
                                    (whrDetTerm x₁ x) (proj₃ , proj₄))

whrDet* : ∀{Γ A B B′ r r'} (d : Γ ⊢ A ↘ B ^ r) (d′ : Γ ⊢ A ↘ B′ ^ r') → B PE.≡ B′
whrDet* (id x , proj₂) (id x₁ , proj₄) = PE.refl
whrDet* (id x , proj₂) (x₁ ⇨ proj₃ , proj₄) = ⊥-elim (nfRed x₁ proj₂)
whrDet* (x ⇨ proj₁ , proj₂) (id x₁ , proj₄) = ⊥-elim (nfRed x proj₄)
whrDet* (A⇒A′ ⇨ A′⇒*B , nfB) (A⇒A″ ⇨ A″⇒*B′ , nfB′) =
  whrDet* (A′⇒*B , nfB) (PE.subst (λ x → _ ⊢ x ↘ _ ^ _ )
                                     (whrDet A⇒A″ A⇒A′)
                                     (A″⇒*B′ , nfB′))

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
UnotInA[t] () x₁ (_ ▹ _ ▹ _ ▹ x₂ ∘ⱼ x₃)
UnotInA[t] () x₁ (zeroⱼ x₂)
UnotInA[t] () x₁ (sucⱼ x₂)
UnotInA[t] () x₁ (natrecⱼ _ x₂ x₃ x₄ x₅)
UnotInA[t] () x₁ (Emptyrecⱼ x₂ x₃)
UnotInA[t] x x₁ (conv x₂ x₃) = UnotInA[t] x x₁ x₂

redU*Term′ : ∀ {A B U′ l Γ r} → U′ PE.≡ (Univ r ¹) → Γ ⊢ A ⇒ U′ ∷ B ^ l → ⊥
redU*Term′ U′≡U (conv A⇒U x) = redU*Term′ U′≡U A⇒U
redU*Term′ () (app-subst _ _ A⇒U x _)
redU*Term′ U′≡U (β-red _ _ _ x x₁ x₂) = UnotInA[t] U′≡U x₂ x₁
redU*Term′ () (natrec-subst x x₁ x₂ A⇒U _)
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

redSProp′ : ∀ {Γ A B}
           (D : Γ ⊢ A ⇒* B ∷ SProp ^ next ⁰ )
         → Γ ⊢ A ⇒* B ^ [ % , ι ⁰ ]
redSProp′ (id x) = id (univ x)
redSProp′ (x ⇨ D) = univ x ⇨ redSProp′ D

redSProp : ∀ {Γ A B}
           (D : Γ ⊢ A :⇒*: B ∷ SProp ^ next ⁰ )
         → Γ ⊢ A :⇒*: B ^ [ % , ι ⁰ ]
redSProp [[ ⊢t , ⊢u , d ]] = [[ (univ ⊢t) , (univ ⊢u) , redSProp′ d ]]

notType:⇒*: : ∀ {Γ A B l} → Γ ⊢ A :⇒*: B ^ l → Set
notType:⇒*: [[ ⊢A , ⊢B , D ]] = notType* D

notNatural:⇒*: : ∀ {Γ t u} → Γ ⊢ t :⇒*: u ∷ ℕ ^ ι ⁰ → Set
notNatural:⇒*: [[ ⊢A , ⊢B , D ]] = notNatural* D

CastRed*Term′ : ∀ {Γ A B X e t}
         (⊢X : Γ ⊢ X ^ [ ! , ι ⁰ ])
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) A X ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t ∷ A ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A ⇒* B ^ [ ! , ι ⁰ ])
       → notType* D
       → Γ ⊢ cast ⁰ A X e t ⇒* cast ⁰ B X e t ∷ X ^ ι ⁰
CastRed*Term′ (univ ⊢X) ⊢e ⊢t  (id (univ ⊢A)) _ = id (castⱼ ⊢A ⊢X ⊢e ⊢t)
CastRed*Term′ (univ ⊢X) ⊢e ⊢t  (univ d ⇨ D) (notType , rec) = cast-subst d ⊢X ⊢e ⊢t notType ⇨
              CastRed*Term′ (univ ⊢X) (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢t))) (subsetTerm d) (refl ⊢X)) ))
                            (conv ⊢t (subset (univ d))) D rec

CastRed*Term : ∀ {Γ A B X t e}
         (⊢X : Γ ⊢ X ^ [ ! , ι ⁰ ])
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) A X ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t ∷ A ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A :⇒*: B ∷ U ⁰ ^ next ⁰)
       → notType:⇒*: (univ:⇒*: D)
       → Γ ⊢ cast ⁰ A X e t :⇒*: cast ⁰ B X e t ∷ X ^ ι ⁰
CastRed*Term {Γ} {A} {B} (univ ⊢X) ⊢e ⊢t [[ ⊢A , ⊢B , D ]] notType =
  [[ castⱼ ⊢A ⊢X ⊢e ⊢t , castⱼ ⊢B ⊢X
     (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢t))) (subset*Term D) (refl ⊢X)) ))
     (conv ⊢t (univ (subset*Term D))) ,
     CastRed*Term′ (univ ⊢X) ⊢e ⊢t (univ⇒* D) notType ]]

CastRedR*Term′ : ∀ {Γ A B X e t}
         (⊢X : Γ ⊢ X ^ [ ! , ι ⁰ ])
         (neX : Neutral X)
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) X A ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t ∷ X ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A ⇒* B ^ [ ! , ι ⁰ ])
       → notType* D
       → Γ ⊢ cast ⁰ X A e t ⇒* cast ⁰ X B e t ∷ A ^ ι ⁰
CastRedR*Term′ (univ ⊢X) neX ⊢e ⊢t (id (univ ⊢A)) _ = id (castⱼ ⊢X ⊢A ⊢e ⊢t)
CastRedR*Term′ (univ ⊢X) neX ⊢e ⊢t (univ d ⇨ D) (notType , rec)=
  cast-ne-subst ⊢X neX d ⊢e ⊢t notType ⇨
              conv⇒* (CastRedR*Term′ (univ ⊢X) neX (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢t))) (refl ⊢X) (subsetTerm d)) ))
                                     ⊢t D rec) (sym (subset (univ d)))

CastRedR*Term : ∀ {Γ A B X t e}
         (⊢X : Γ ⊢ X ^ [ ! , ι ⁰ ])
         (neX : Neutral X)
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) X A ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t ∷ X ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A :⇒*: B ∷ U ⁰ ^ next ⁰)
       → notType:⇒*: (univ:⇒*: D)
       → Γ ⊢ cast ⁰ X A e t :⇒*: cast ⁰ X B e t ∷ A ^ ι ⁰
CastRedR*Term {Γ} {A} {B} (univ ⊢X) neX ⊢e ⊢t [[ ⊢A , ⊢B , D ]] notType =
  [[ castⱼ ⊢X ⊢A ⊢e ⊢t , conv (castⱼ ⊢X ⊢B (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢t))) (refl ⊢X) (subset*Term D)) )) ⊢t) (sym (univ (subset*Term D))) ,
     CastRedR*Term′ (univ ⊢X) neX ⊢e ⊢t (univ⇒* D) notType ]]

CastRedTerm*Term′ : ∀ {Γ X Y e t u}
         (⊢X : Γ ⊢ X ^ [ ! , ι ⁰ ])
         (neX : Neutral X)
         (⊢Y : Γ ⊢ Y ^ [ ! , ι ⁰ ])
         (neY : Neutral Y)
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) X Y ^ [ % , ι ⁰ ])
         (D : Γ ⊢ t ⇒* u ∷ X ^ ι ⁰)
       → Γ ⊢ cast ⁰ X Y e t ⇒* cast ⁰ X Y e u ∷ Y ^ ι ⁰
CastRedTerm*Term′ (univ ⊢X) neX (univ ⊢Y) neY ⊢e (id ⊢t) = id (castⱼ ⊢X ⊢Y ⊢e ⊢t)
CastRedTerm*Term′ (univ ⊢X) neX (univ ⊢Y) neY ⊢e (d ⇨ D) = cast-ne-cong ⊢X neX ⊢Y neY ⊢e d ⇨ CastRedTerm*Term′ (univ ⊢X) neX (univ ⊢Y) neY ⊢e D

CastRedTerm*Term : ∀ {Γ X Y t u e}
         (⊢X : Γ ⊢ X ^ [ ! , ι ⁰ ])
         (neX : Neutral X)
         (⊢Y : Γ ⊢ Y ^ [ ! , ι ⁰ ])
         (neY : Neutral Y)
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) X Y ^ [ % , ι ⁰ ])
         (D : Γ ⊢ t :⇒*: u ∷ X ^ ι ⁰)
       → Γ ⊢ cast ⁰ X Y e t :⇒*: cast ⁰ X Y e u ∷ Y ^ ι ⁰
CastRedTerm*Term {Γ} {A} {B} (univ ⊢X) neX (univ ⊢Y) neY ⊢e [[ ⊢t , ⊢u , D ]] =
  [[ castⱼ ⊢X ⊢Y ⊢e ⊢t , castⱼ ⊢X ⊢Y ⊢e ⊢u ,
     CastRedTerm*Term′ (univ ⊢X) neX (univ ⊢Y) neY ⊢e D ]]

CastRed*Termℕ′ : ∀ {Γ A B e t}
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) ℕ A ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t ∷ ℕ ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A ⇒* B ^ [ ! , ι ⁰ ])
       → notType* D
       → Γ ⊢ cast ⁰ ℕ A e t ⇒* cast ⁰ ℕ B e t ∷ A ^ ι ⁰
CastRed*Termℕ′ ⊢e ⊢t  (id (univ ⊢A)) _ = id (castⱼ (ℕⱼ (wfTerm ⊢A)) ⊢A ⊢e ⊢t)
CastRed*Termℕ′ ⊢e ⊢t  (univ d ⇨ D) (notType , rec) = cast-ℕ-subst d ⊢e ⊢t notType ⇨
                                     conv* (CastRed*Termℕ′
                                             (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢e))) (refl (ℕⱼ (wfTerm ⊢e))) (subsetTerm d))) )
                                             ⊢t D rec)
                                           (sym (subset (univ d)))

CastRed*Termℕ : ∀ {Γ A B e t}
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) ℕ A ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t ∷ ℕ ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A :⇒*: B ^ [ ! , ι ⁰ ])
       → notType:⇒*: D
       → Γ ⊢ cast ⁰ ℕ A e t :⇒*: cast ⁰ ℕ B e t ∷ A ^ ι ⁰
CastRed*Termℕ ⊢e ⊢t  [[ ⊢A , ⊢B , D ]] notType =
  [[ castⱼ (ℕⱼ (wfTerm ⊢e)) (un-univ ⊢A) ⊢e ⊢t ,
     conv (castⱼ (ℕⱼ (wfTerm ⊢e)) (un-univ ⊢B)
          (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢e))) (refl (ℕⱼ (wfTerm ⊢e))) (subset*Term (un-univ⇒* D)))))
          ⊢t) (sym (subset* D)) ,
       CastRed*Termℕ′ ⊢e ⊢t D notType ]]

CastRed*Termℕℕ′ : ∀ {Γ e t u}
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) ℕ ℕ ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t ⇒* u ∷ ℕ ^ ι ⁰ )
       → notNatural* ⊢t
       → Γ ⊢ cast ⁰ ℕ ℕ e t ⇒* cast ⁰ ℕ ℕ e u ∷ ℕ ^ ι ⁰
CastRed*Termℕℕ′ ⊢e (id ⊢t) _ = id (castⱼ (ℕⱼ (wfTerm ⊢e)) (ℕⱼ (wfTerm ⊢e)) ⊢e ⊢t)
CastRed*Termℕℕ′ ⊢e (d ⇨ D) (notNatural , rec) = cast-ℕ-cong ⊢e d notNatural ⇨ CastRed*Termℕℕ′ ⊢e D rec

CastRed*Termℕℕ : ∀ {Γ e t u}
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) ℕ ℕ ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t :⇒*: u ∷ ℕ ^ ι ⁰ )
         → notNatural:⇒*: ⊢t
         → Γ ⊢ cast ⁰ ℕ ℕ e t :⇒*: cast ⁰ ℕ ℕ e u ∷ ℕ ^ ι ⁰
CastRed*Termℕℕ ⊢e [[ ⊢t , ⊢u , D ]] notNatural =
  [[ castⱼ (ℕⱼ (wfTerm ⊢e)) (ℕⱼ (wfTerm ⊢e)) ⊢e ⊢t ,
     castⱼ (ℕⱼ (wfTerm ⊢e)) (ℕⱼ (wfTerm ⊢e)) ⊢e ⊢u ,
       CastRed*Termℕℕ′ ⊢e D notNatural ]]

CastRed*Termℕsuc : ∀ {Γ e n}
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) ℕ ℕ ^ [ % , ι ⁰ ])
         (⊢n : Γ ⊢ n ∷ ℕ ^ [ ! , ι ⁰ ])
       → Γ ⊢ cast ⁰ ℕ ℕ e (suc n) :⇒*: suc (cast ⁰ ℕ ℕ e n) ∷ ℕ ^ ι ⁰
CastRed*Termℕsuc ⊢e ⊢n =
  [[ castⱼ (ℕⱼ (wfTerm ⊢e)) (ℕⱼ (wfTerm ⊢e)) ⊢e (sucⱼ ⊢n) ,
     sucⱼ (castⱼ (ℕⱼ (wfTerm ⊢e)) (ℕⱼ (wfTerm ⊢e)) ⊢e ⊢n) ,
       cast-ℕ-S ⊢e ⊢n ⇨ id (sucⱼ (castⱼ (ℕⱼ (wfTerm ⊢e)) (ℕⱼ (wfTerm ⊢e)) ⊢e ⊢n)) ]]

CastRed*Termℕzero : ∀ {Γ e}
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) ℕ ℕ ^ [ % , ι ⁰ ])
       → Γ ⊢ cast ⁰ ℕ ℕ e zero :⇒*: zero ∷ ℕ ^ ι ⁰
CastRed*Termℕzero ⊢e =
  [[ castⱼ (ℕⱼ (wfTerm ⊢e)) (ℕⱼ (wfTerm ⊢e)) ⊢e (zeroⱼ (wfTerm ⊢e)) ,
     zeroⱼ (wfTerm ⊢e) ,
       cast-ℕ-0 ⊢e ⇨ id (zeroⱼ (wfTerm ⊢e)) ]]


CastRed*TermΠ′ : ∀ {Γ F rF G A B e t}
         (⊢F : Γ ⊢ F ∷ (Univ rF ⁰) ^ [ ! , next ⁰ ])
         (⊢G : Γ ∙ F ^ [ rF , ι ⁰ ] ⊢ G ∷ U ⁰ ^ [ ! , next ⁰ ])
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) A ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t ∷ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A ⇒* B ^ [ ! , ι ⁰ ])
       → notType* D
       → Γ ⊢ cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) A e t ⇒* cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) B e t ∷ A ^ ι ⁰
CastRed*TermΠ′ ⊢F ⊢G ⊢e ⊢t (id (univ ⊢A)) _ = id (castⱼ (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ ⊢F ▹ ⊢G) ⊢A ⊢e ⊢t)
CastRed*TermΠ′ ⊢F ⊢G ⊢e ⊢t (univ d ⇨ D) (notType , rec) = cast-Π-subst ⊢F ⊢G d ⊢e ⊢t notType ⇨
                                     conv* (CastRed*TermΠ′ ⊢F ⊢G
                                                           (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢e))) (refl (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ ⊢F ▹ ⊢G)) (subsetTerm d))) )
                                                           ⊢t D rec)
                                           (sym (subset (univ d)))

CastRed*TermΠ : ∀ {Γ F rF G A B e t}
         (⊢F : Γ ⊢ F ∷ (Univ rF ⁰) ^ [ ! , next ⁰ ])
         (⊢G : Γ ∙ F ^ [ rF , ι ⁰ ] ⊢ G ∷ U ⁰ ^ [ ! , next ⁰ ])
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) A ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t ∷ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A :⇒*: B ^ [ ! , ι ⁰ ])
       → notType:⇒*: D
       → Γ ⊢ cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) A e t :⇒*: cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) B e t ∷ A ^ ι ⁰
CastRed*TermΠ ⊢F ⊢G ⊢e ⊢t  [[ ⊢A , ⊢B , D ]] notType =
  let [Π] = Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ ⊢F ▹ ⊢G
  in [[ castⱼ [Π] (un-univ ⊢A) ⊢e ⊢t ,
        conv (castⱼ [Π] (un-univ ⊢B)
          (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢e))) (refl [Π]) (subset*Term (un-univ⇒* D)))))
          ⊢t) (sym (subset* D)) ,
          CastRed*TermΠ′ ⊢F ⊢G ⊢e ⊢t D notType ]]


appRed* : ∀ {Γ a t u A B rA lA lB l}
         → Γ     ⊢ A ∷ (Univ rA lA) ^ [ ! , next lA ]
         → Γ ∙ A ^ [ rA , ι lA ] ⊢ B ∷ (U lB) ^ [ ! , next lB ]
         → (⊢a : Γ ⊢ a ∷ A ^ [ rA , ι lA ])
           (D : Γ ⊢ t ⇒* u ∷ (Π A ^ rA ° lA ▹ B ° lB ° l ^ !) ^ ι l)
         → notLambda* D
         → Γ ⊢ t ∘ a ^ l ⇒* u ∘ a ^ l ∷ B [ a ] ^ ι lB
appRed* ⊢F ⊢G ⊢a (id x) _ = id ((λ abs → ⊥-elim (!≢% abs)) ▹ ⊢F ▹ ⊢G ▹ x ∘ⱼ ⊢a)
appRed* ⊢F ⊢G ⊢a (x ⇨ D) (notLam , notLamRec) = app-subst ⊢F ⊢G x ⊢a notLam ⇨ appRed* ⊢F ⊢G ⊢a D notLamRec

suc* : ∀ {Γ n n'}
           (D : Γ ⊢ n ⇒* n' ∷ ℕ ^ ι ⁰)
         → Γ ⊢ suc n ⇒* suc n' ∷ ℕ ^ ι ⁰
suc* (id x) = id (sucⱼ x)
suc* (x ⇨ D) = suc-subst x ⇨ suc* D

suc'* : ∀ {Γ n n'}
           (D : Γ ⊢ n :⇒*: n' ∷ ℕ ^ ι ⁰)
         → Γ ⊢ suc n :⇒*: suc n' ∷ ℕ ^ ι ⁰
suc'* [[ ⊢n , ⊢n' , D ]] = [[ sucⱼ ⊢n , sucⱼ ⊢n' , suc* D ]]


castΠRed* : ∀ {Γ F rF G A B e t}
         (⊢F : Γ ⊢ F ^ [ rF , ι ⁰ ])
         (⊢G : Γ ∙ F ^ [ rF , ι ⁰ ] ⊢ G ^ [ ! , ι ⁰ ])
         (⊢e : Γ ⊢ e ∷ Id (U ⁰) (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) A ^ [ % , ι ⁰ ])
         (⊢t : Γ ⊢ t ∷ Π F ^ rF ° ⁰ ▹ G ° ⁰  ° ⁰ ^ ! ^ [ ! , ι ⁰ ])
         (D : Γ ⊢ A ⇒* B ^ [ ! , ι ⁰ ])
       → notType* D
       → Γ ⊢ cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) A e t ⇒* cast ⁰ (Π F ^ rF ° ⁰ ▹ G ° ⁰ ° ⁰ ^ !) B e t ∷ A ^ ι ⁰
castΠRed* ⊢F ⊢G ⊢e ⊢t (id (univ ⊢A)) _ = id (castⱼ (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ un-univ ⊢F ▹ un-univ ⊢G) ⊢A ⊢e ⊢t)
castΠRed* ⊢F ⊢G ⊢e ⊢t ((univ d) ⇨ D) (notType , rec) = cast-Π-subst (un-univ ⊢F) (un-univ ⊢G) d ⊢e ⊢t notType ⇨ conv* (castΠRed* ⊢F ⊢G
             (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wf ⊢F))) (refl (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ un-univ ⊢F ▹ un-univ ⊢G)) (subsetTerm d))))
             ⊢t D rec) (sym (subset (univ d)))


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
       → Γ ⊢ e ∷ Id A x y ^ [ % , ι ⁰ ]
       → Γ ⊢ Idsym A x y e ∷ Id A y x ^ [ % , ι ⁰ ]
Idsymⱼ {Γ} {A} {l} {x} {y} {e} ⊢A ⊢x ⊢y ⊢e =
  let
    ⊢Γ = wfTerm ⊢A
    ⊢A = univ ⊢A
    ⊢P : Γ ∙ A ^ [ ! , ι l ] ⊢ Id (wk1 A) (var 0) (wk1 x) ^ [ % , ι ⁰ ]
    ⊢P = univ (Idⱼ (Twk.wkTerm (Twk.step Twk.id) (⊢Γ ∙ ⊢A) (un-univ ⊢A))
      (var (⊢Γ ∙ ⊢A) here)
      (Twk.wkTerm (Twk.step Twk.id) (⊢Γ ∙ ⊢A) ⊢x))
    ⊢refl : Γ ⊢ Idrefl A x ∷ Id (wk1 A) (var 0) (wk1 x) [ x ] ^ [ % , ι ⁰ ]
    ⊢refl = PE.subst₂ (λ X Y → Γ ⊢ Idrefl A x ∷ Id X x Y ^ [ % , ι ⁰ ])
      (PE.sym (wk1-singleSubst A x)) (PE.sym (wk1-singleSubst x x))
      (Idreflⱼ ⊢x)
  in PE.subst₂ (λ X Y → Γ ⊢ Idsym A x y e ∷ Id X y Y ^ [ % , ι ⁰ ])
    (wk1-singleSubst A y) (wk1-singleSubst x y)
    (transpⱼ ⊢A ⊢P ⊢x ⊢refl ⊢y ⊢e)

▹▹ⱼ_▹_▹_▹_ : ∀ {Γ F rF lF G lG r l}
             → (r PE.≡ ! → lF ≤ l × lG ≤ l)
             → (r PE.≡ % → lG PE.≡ ⁰ × l PE.≡ ⁰)
             → Γ ⊢ F ∷ (Univ rF lF) ^ [ ! , next lF ]
             → Γ ⊢ G ∷ (Univ r lG) ^ [ ! , next lG ]
             → Γ ⊢ F ^ rF ° lF ▹▹ G ° lG ° l ^ r ∷ (Univ r l) ^ [ ! , next l ]
▹▹ⱼ lF≤ ▹ lG≤ ▹ F ▹ G = Πⱼ lF≤ ▹ lG≤ ▹ F ▹ un-univ (Twk.wk (Twk.step Twk.id) ((wf (univ F)) ∙ (univ F)) (univ G))
