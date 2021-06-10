{-# OPTIONS --without-K  #-}

module Definition.Typed.Consequences.𝕊Unicity where

open import Definition.Untyped hiding (U≢ℕ; U≢Π; U≢ne; ℕ≢Π; ℕ≢ne; Π≢ne; U≢Empty; ℕ≢Empty; Empty≢Π; Empty≢ne)
open import Definition.Untyped.Properties using (subst-Univ-either)
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.Typed.Consequences.Equality
import Definition.Typed.Consequences.Inequality as Ineq
open import Definition.Typed.Consequences.Inversion
open import Definition.Typed.Consequences.InverseUniv
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.NeTypeEq
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.PiNorm

open import Tools.Product
open import Tools.Empty
open import Tools.Sum using (_⊎_; inj₁; inj₂)
import Tools.PropositionalEquality as PE

ℕ-relevant-term : ∀ {Γ A} → Γ ⊢ ℕ ∷ A ⦂ 𝕥y → A PE.≡ Univ 𝕥y
ℕ-relevant-term [ℕ] = U≡A (sym (proj₁ (inversion-ℕ [ℕ])))

ℕ-relevant : ∀ {Γ s} → Γ ⊢ ℕ ⦂ s → s PE.≡ 𝕥y
ℕ-relevant (ℕⱼ _) = PE.refl
ℕ-relevant (univ [ℕ]) = Univ-PE-injectivity (ℕ-relevant-term [ℕ])

Empty-irrelevant-term : ∀ {Γ A} → Γ ⊢ Empty ∷ A ⦂ 𝕥y → A PE.≡ Univ 𝕥y
Empty-irrelevant-term (Emptyⱼ _) = PE.refl
Empty-irrelevant-term (conv [Empty] [A₁≡A]) rewrite Empty-irrelevant-term [Empty] =
  U≡A [A₁≡A]

Empty-irrelevant : ∀ {Γ s} → Γ ⊢ Empty ⦂ s → s PE.≡ 𝕥y
Empty-irrelevant (Emptyⱼ _) = PE.refl
Empty-irrelevant (univ [Empty]) = Univ-PE-injectivity (Empty-irrelevant-term [Empty])

-- helper
subst-Univ-typed : ∀ {s Γ a T sT b}
                 → Γ ⊢ a ∷ T ⦂ sT
                 → subst (sgSubst a) b PE.≡ Univ s
                 → b PE.≡ Univ s
subst-Univ-typed {s} {Γ} {a} {T} {sT} {b} [a] e with subst-Univ-either a b e
... | inj₁ (PE.refl , PE.refl) = ⊥-elim (noU [a] ∃U)
... | inj₂ x = x

Univ-relevant : ∀ {Γ sU s} → Γ ⊢ Univ sU ⦂ s → s PE.≡ 𝕥y
Univ-relevant (Uⱼ _) = PE.refl
Univ-relevant (univ [U]) = ⊥-elim (noU [U] ∃U)

Univ-uniq′ : ∀ {Γ A T₁ T₂ s₁ s₂} → Γ ⊢ T₁ ≡ Univ s₁ ⦂ 𝕥y → Γ ⊢ T₂ ≡ Univ s₂ ⦂ 𝕥y → ΠNorm A
  → Γ ⊢ A ∷ T₁ ⦂ 𝕥y → Γ ⊢ A ∷ T₂ ⦂ 𝕥y → s₁ PE.≡ s₂
Univ-uniq′ e₁ e₂ w (conv x x₁) y = Univ-uniq′ (trans x₁ e₁) e₂ w x y
Univ-uniq′ e₁ e₂ w x (conv y y₁) = Univ-uniq′ e₁ (trans y₁ e₂) w x y
Univ-uniq′ e₁ e₂ w (ℕⱼ x) y =
  let e₁′ = Uinjectivity e₁
      e₃ = Uinjectivity (trans (sym e₂) (proj₁ (inversion-ℕ y)))
  in PE.sym (PE.trans e₃ e₁′)
Univ-uniq′ e₁ e₂ w (Emptyⱼ x) y =
  let e₁′ = Uinjectivity e₁
      e₃ = Uinjectivity (trans (sym e₂) (proj₁ (inversion-Empty y)))
  in PE.sym (PE.trans e₃ e₁′)
Univ-uniq′ e₁ e₂ w (Πⱼ x ▹ x₁) (Πⱼ y ▹ y₁) =
  Univ-uniq′ (wkEq (step id) (wfTerm x₁) e₁) (wkEq (step id) (wfTerm x₁) e₂) (ΠNorm-Π w) x₁ y₁
Univ-uniq′ e₁ e₂ w (var _ x) (var _ y) =
  let T≡T = proj₁ (vasTypeEq′ x y )
      ⊢T≡T = PE.subst (λ T → _ ⊢ _ ≡ T ⦂ _) T≡T (refl (proj₁ (syntacticEq e₁)))
  in Uinjectivity (trans (trans (sym e₁) ⊢T≡T) e₂)
Univ-uniq′ e₁ e₂ w (natrecⱼ x x₁ x₂ x₃) (natrecⱼ x₄ y y₁ y₂) = Uinjectivity (trans (sym e₁) e₂)
Univ-uniq′ e₁ e₂ w (Emptyrecⱼ x x₁) (Emptyrecⱼ x₂ y) = Uinjectivity (trans (sym e₁) e₂)
Univ-uniq′ e₁ e₂ (ne ()) (lamⱼ x x₁) y
Univ-uniq′ e₁ e₂ (ne (∘ₙ n)) (_∘ⱼ_ {G = G} x x₁) (_∘ⱼ_ {G = G₁} y y₁) =
  let e₁′ = subst-Univ-typed {b = G} x₁ (U≡A (sym e₁))
      e₂′ = subst-Univ-typed {b = G₁} y₁ (U≡A (sym e₂))
      F≡F , sF≡sF , G≡G = injectivity (neTypeEq n x y)
  in Uinjectivity (PE.subst₂ (λ a b → _ ⊢ a ≡ b ⦂ _) e₁′ e₂′ G≡G)
Univ-uniq′ e₁ e₂ (ne ()) (zeroⱼ x) y
Univ-uniq′ e₁ e₂ (ne ()) (sucⱼ x) y

Univ-uniq : ∀ {Γ A s₁ s₂} → ΠNorm A
  → Γ ⊢ A ∷ Univ s₁ ⦂ 𝕥y → Γ ⊢ A ∷ Univ s₂ ⦂ 𝕥y → s₁ PE.≡ s₂
Univ-uniq n ⊢A₁ ⊢A₂ =
   let ⊢Γ = wfTerm ⊢A₁
   in Univ-uniq′ (refl (Uⱼ ⊢Γ)) (refl (Uⱼ ⊢Γ)) n ⊢A₁ ⊢A₂

relevance-unicity′ : ∀ {Γ A r1 r2} → ΠNorm A → Γ ⊢ A ⦂ s1 → Γ ⊢ A ⦂ s2 → r1 PE.≡ r2
relevance-unicity′ (Πₙ n) (Πⱼ F ▹ G) (Πⱼ F' ▹ G') = relevance-unicity′ n G G'
relevance-unicity′ (ne ()) _ (Πⱼ _ ▹ _)
relevance-unicity′ (ne ()) (Πⱼ _ ▹ _) _
relevance-unicity′ n (ℕⱼ _) b = PE.sym (ℕ-relevant b)
relevance-unicity′ n a (ℕⱼ x) = ℕ-relevant a
relevance-unicity′ n (Emptyⱼ _) b = PE.sym (Empty-irrelevant b)
relevance-unicity′ n a (Emptyⱼ x) = Empty-irrelevant a
relevance-unicity′ n (Uⱼ _) b = PE.sym (Univ-relevant b)
relevance-unicity′ n a (Uⱼ x) = Univ-relevant a
relevance-unicity′ (Πₙ n) (Πⱼ a ▹ a₁) (univ x) with inversion-Π x
... | sG , [F] , [G] , [eq] , _ with Uinjectivity [eq]
... | PE.refl = relevance-unicity′ n a₁ (univ [G])
relevance-unicity′ (Πₙ n) (univ a) (Πⱼ b ▹ b₁) with inversion-Π a
... | sG , [F] , [G] , [eq] , _ with Uinjectivity [eq]
... | PE.refl = relevance-unicity′ n (univ [G]) b₁
relevance-unicity′ n (univ a) (univ x) = Univ-uniq n a x

relevance-unicity : ∀ {Γ A r1 r2} → Γ ⊢ A ⦂ s1 → Γ ⊢ A ⦂ s2 → r1 PE.≡ r2
relevance-unicity ⊢A₁ ⊢A₂ with doΠNorm ⊢A₁
... | _ with doΠNorm ⊢A₂
relevance-unicity ⊢A₁ ⊢A₂ | B , nB , ⊢B , sB | C , nC , ⊢C , sC =
  let e = detΠNorm* nB nC sB sC
  in relevance-unicity′ nC (PE.subst _ e ⊢B) ⊢C

univ-unicity : ∀ {Γ A s₁ s₂} → Γ ⊢ A ∷ Univ s₁ ⦂ 𝕥y → Γ ⊢ A ∷ Univ s₂ ⦂ 𝕥y → s₁ PE.≡ s₂
univ-unicity ⊢₁ ⊢₂ = relevance-unicity (univ ⊢₁) (univ ⊢₂)

-- inequalities at any relevance
U≢ℕ : ∀ {s s′ Γ} → Γ ⊢ Univ s ≡ ℕ ⦂ s′ → ⊥
U≢ℕ U≡ℕ = Ineq.U≢ℕ𝕥y (PE.subst (λ rx → _ ⊢ _ ≡ _ ⦂ sx)
                   (relevance-unicity (proj₂ (syntacticEq U≡ℕ))
                                      (ℕⱼ (wfEq U≡ℕ)))
                   U≡ℕ)

U≢Π : ∀ {sU F sF G s Γ} → Γ ⊢ Univ sU ≡ Π F ⦂ sF ▹ G ⦂ s → ⊥
U≢Π U≡Π =
  let s≡𝕥y = relevance-unicity (proj₁ (syntacticEq U≡Π)) (Uⱼ (wfEq U≡Π))
  in Ineq.U≢Π𝕥y (PE.subst (λ rx → _ ⊢ _ ≡ _ ⦂ sx) s≡𝕥y U≡Π)

U≢ne : ∀ {sU s K Γ} → Neutral K → Γ ⊢ Univ sU ≡ K ⦂ s → ⊥
U≢ne neK U≡K =
  let s≡𝕥y = relevance-unicity (proj₁ (syntacticEq U≡K)) (Uⱼ (wfEq U≡K))
  in Ineq.U≢ne𝕥y neK (PE.subst (λ rx → _ ⊢ _ ≡ _ ⦂ sx) s≡𝕥y U≡K)

ℕ≢Π : ∀ {F sF G s Γ} → Γ ⊢ ℕ ≡ Π F ⦂ sF ▹ G ⦂ s → ⊥
ℕ≢Π ℕ≡Π =
  let s≡𝕥y = relevance-unicity (proj₁ (syntacticEq ℕ≡Π)) (ℕⱼ (wfEq ℕ≡Π))
  in Ineq.ℕ≢Π𝕥y (PE.subst (λ rx → _ ⊢ _ ≡ _ ⦂ sx) s≡𝕥y ℕ≡Π)

Empty≢Π : ∀ {F sF G s Γ} → Γ ⊢ Empty ≡ Π F ⦂ sF ▹ G ⦂ s → ⊥
Empty≢Π Empty≡Π =
  let s≡𝕥y = relevance-unicity (proj₁ (syntacticEq Empty≡Π)) (Emptyⱼ (wfEq Empty≡Π))
  in Ineq.Empty≢Π𝕥y (PE.subst (λ rx → _ ⊢ _ ≡ _ ⦂ sx) s≡𝕥y Empty≡Π)

ℕ≢ne : ∀ {K s Γ} → Neutral K → Γ ⊢ ℕ ≡ K ⦂ s → ⊥
ℕ≢ne neK ℕ≡K =
  let s≡𝕥y = relevance-unicity (proj₁ (syntacticEq ℕ≡K)) (ℕⱼ (wfEq ℕ≡K))
  in Ineq.ℕ≢ne𝕥y neK (PE.subst (λ rx → _ ⊢ _ ≡ _ ⦂ sx) s≡𝕥y ℕ≡K)

Empty≢ne : ∀ {K s Γ} → Neutral K → Γ ⊢ Empty ≡ K ⦂ s → ⊥
Empty≢ne neK Empty≡K =
  let s≡𝕥y = relevance-unicity (proj₁ (syntacticEq Empty≡K)) (Emptyⱼ (wfEq Empty≡K))
  in Ineq.Empty≢ne𝕥y neK (PE.subst (λ rx → _ ⊢ _ ≡ _ ⦂ sx) s≡𝕥y Empty≡K)

-- U 𝕥y= Empty is given easily by relevances
U≢Empty : ∀ {Γ s s′} → Γ ⊢ Univ s ≡ Empty ⦂ s′ → ⊥
U≢Empty U≡Empty =
  let ⊢U , ⊢Empty = syntacticEq U≡Empty
      e₁ = relevance-unicity ⊢U (Uⱼ (wfEq U≡Empty))
      e₂ = relevance-unicity ⊢Empty (Emptyⱼ (wfEq U≡Empty))
  in 𝕥y≢𝕥y (PE.trans (PE.sym e₁) e₂)

-- ℕ and Empty also by relevance
ℕ≢Empty : ∀ {Γ s} → Γ ⊢ ℕ ≡ Empty ⦂ s → ⊥
ℕ≢Empty ℕ≡Empty =
  let ⊢ℕ , ⊢Empty = syntacticEq ℕ≡Empty
      e₁ = relevance-unicity ⊢ℕ (ℕⱼ (wfEq ℕ≡Empty))
      e₂ = relevance-unicity ⊢Empty (Emptyⱼ (wfEq ℕ≡Empty))
  in 𝕥y≢𝕥y (PE.trans (PE.sym e₁) e₂)
