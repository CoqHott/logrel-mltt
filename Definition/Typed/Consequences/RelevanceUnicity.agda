{-# OPTIONS --safe #-}

module Definition.Typed.Consequences.RelevanceUnicity where

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

ℕ-relevant-term : ∀ {Γ A} → Γ ⊢ ℕ ∷ A ^ ! → A PE.≡ Univ !
ℕ-relevant-term [ℕ] = U≡A (sym (proj₁ (inversion-ℕ [ℕ])))

ℕ-relevant : ∀ {Γ r} → Γ ⊢ ℕ ^ r → r PE.≡ !
ℕ-relevant (ℕⱼ _) = PE.refl
ℕ-relevant (univ [ℕ]) = Univ-PE-injectivity (ℕ-relevant-term [ℕ])

Empty-irrelevant-term : ∀ {Γ A} → Γ ⊢ Empty ∷ A ^ ! → A PE.≡ Univ %
Empty-irrelevant-term (Emptyⱼ _) = PE.refl
Empty-irrelevant-term (conv [Empty] [A₁≡A]) rewrite Empty-irrelevant-term [Empty] =
  U≡A [A₁≡A]

Empty-irrelevant : ∀ {Γ r} → Γ ⊢ Empty ^ r → r PE.≡ %
Empty-irrelevant (Emptyⱼ _) = PE.refl
Empty-irrelevant (univ [Empty]) = Univ-PE-injectivity (Empty-irrelevant-term [Empty])

-- helper
subst-Univ-typed : ∀ {r Γ a T rT b}
                 → Γ ⊢ a ∷ T ^ rT
                 → subst (sgSubst a) b PE.≡ Univ r
                 → b PE.≡ Univ r
subst-Univ-typed {r} {Γ} {a} {T} {rT} {b} [a] e with subst-Univ-either a b e
... | inj₁ (PE.refl , PE.refl) = ⊥-elim (noU [a] ∃U)
... | inj₂ x = x

Univ-relevant : ∀ {Γ rU r} → Γ ⊢ Univ rU ^ r → r PE.≡ !
Univ-relevant (Uⱼ _) = PE.refl
Univ-relevant (univ [U]) = ⊥-elim (noU [U] ∃U)

Univ-uniq′ : ∀ {Γ A T₁ T₂ r₁ r₂} → Γ ⊢ T₁ ≡ Univ r₁ ^ ! → Γ ⊢ T₂ ≡ Univ r₂ ^ ! → ΠNorm A
  → Γ ⊢ A ∷ T₁ ^ ! → Γ ⊢ A ∷ T₂ ^ ! → r₁ PE.≡ r₂
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
  let T≡T = proj₁ (varTypeEq′ x y )
      ⊢T≡T = PE.subst (λ T → _ ⊢ _ ≡ T ^ _) T≡T (refl (proj₁ (syntacticEq e₁)))
  in Uinjectivity (trans (trans (sym e₁) ⊢T≡T) e₂)
Univ-uniq′ e₁ e₂ w (natrecⱼ x x₁ x₂ x₃) (natrecⱼ x₄ y y₁ y₂) = Uinjectivity (trans (sym e₁) e₂)
Univ-uniq′ e₁ e₂ w (Emptyrecⱼ x x₁) (Emptyrecⱼ x₂ y) = Uinjectivity (trans (sym e₁) e₂)
Univ-uniq′ e₁ e₂ (ne ()) (lamⱼ x x₁) y
Univ-uniq′ e₁ e₂ (ne (∘ₙ n)) (_∘ⱼ_ {G = G} x x₁) (_∘ⱼ_ {G = G₁} y y₁) =
  let e₁′ = subst-Univ-typed {b = G} x₁ (U≡A (sym e₁))
      e₂′ = subst-Univ-typed {b = G₁} y₁ (U≡A (sym e₂))
      F≡F , rF≡rF , G≡G = injectivity (neTypeEq n x y)
  in Uinjectivity (PE.subst₂ (λ a b → _ ⊢ a ≡ b ^ _) e₁′ e₂′ G≡G)
Univ-uniq′ e₁ e₂ (ne ()) (zeroⱼ x) y
Univ-uniq′ e₁ e₂ (ne ()) (sucⱼ x) y

Univ-uniq : ∀ {Γ A r₁ r₂} → ΠNorm A
  → Γ ⊢ A ∷ Univ r₁ ^ ! → Γ ⊢ A ∷ Univ r₂ ^ ! → r₁ PE.≡ r₂
Univ-uniq n ⊢A₁ ⊢A₂ =
   let ⊢Γ = wfTerm ⊢A₁
   in Univ-uniq′ (refl (Uⱼ ⊢Γ)) (refl (Uⱼ ⊢Γ)) n ⊢A₁ ⊢A₂

relevance-unicity′ : ∀ {Γ A r1 r2} → ΠNorm A → Γ ⊢ A ^ r1 → Γ ⊢ A ^ r2 → r1 PE.≡ r2
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
... | rG , [F] , [G] , [eq] , _ with Uinjectivity [eq]
... | PE.refl = relevance-unicity′ n a₁ (univ [G])
relevance-unicity′ (Πₙ n) (univ a) (Πⱼ b ▹ b₁) with inversion-Π a
... | rG , [F] , [G] , [eq] , _ with Uinjectivity [eq]
... | PE.refl = relevance-unicity′ n (univ [G]) b₁
relevance-unicity′ n (univ a) (univ x) = Univ-uniq n a x

relevance-unicity : ∀ {Γ A r1 r2} → Γ ⊢ A ^ r1 → Γ ⊢ A ^ r2 → r1 PE.≡ r2
relevance-unicity ⊢A₁ ⊢A₂ with doΠNorm ⊢A₁
... | _ with doΠNorm ⊢A₂
relevance-unicity ⊢A₁ ⊢A₂ | B , nB , ⊢B , rB | C , nC , ⊢C , rC =
  let e = detΠNorm* nB nC rB rC
  in relevance-unicity′ nC (PE.subst _ e ⊢B) ⊢C

univ-unicity : ∀ {Γ A r₁ r₂} → Γ ⊢ A ∷ Univ r₁ ^ ! → Γ ⊢ A ∷ Univ r₂ ^ ! → r₁ PE.≡ r₂
univ-unicity ⊢₁ ⊢₂ = relevance-unicity (univ ⊢₁) (univ ⊢₂)

-- inequalities at any relevance
U≢ℕ : ∀ {r r′ Γ} → Γ ⊢ Univ r ≡ ℕ ^ r′ → ⊥
U≢ℕ U≡ℕ = Ineq.U≢ℕ! (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ rx)
                   (relevance-unicity (proj₂ (syntacticEq U≡ℕ))
                                      (ℕⱼ (wfEq U≡ℕ)))
                   U≡ℕ)

U≢Π : ∀ {rU F rF G r Γ} → Γ ⊢ Univ rU ≡ Π F ^ rF ▹ G ^ r → ⊥
U≢Π U≡Π =
  let r≡! = relevance-unicity (proj₁ (syntacticEq U≡Π)) (Uⱼ (wfEq U≡Π))
  in Ineq.U≢Π! (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ rx) r≡! U≡Π)

U≢ne : ∀ {rU r K Γ} → Neutral K → Γ ⊢ Univ rU ≡ K ^ r → ⊥
U≢ne neK U≡K =
  let r≡! = relevance-unicity (proj₁ (syntacticEq U≡K)) (Uⱼ (wfEq U≡K))
  in Ineq.U≢ne! neK (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ rx) r≡! U≡K)

ℕ≢Π : ∀ {F rF G r Γ} → Γ ⊢ ℕ ≡ Π F ^ rF ▹ G ^ r → ⊥
ℕ≢Π ℕ≡Π =
  let r≡! = relevance-unicity (proj₁ (syntacticEq ℕ≡Π)) (ℕⱼ (wfEq ℕ≡Π))
  in Ineq.ℕ≢Π! (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ rx) r≡! ℕ≡Π)

Empty≢Π : ∀ {F rF G r Γ} → Γ ⊢ Empty ≡ Π F ^ rF ▹ G ^ r → ⊥
Empty≢Π Empty≡Π =
  let r≡% = relevance-unicity (proj₁ (syntacticEq Empty≡Π)) (Emptyⱼ (wfEq Empty≡Π))
  in Ineq.Empty≢Π% (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ rx) r≡% Empty≡Π)

ℕ≢ne : ∀ {K r Γ} → Neutral K → Γ ⊢ ℕ ≡ K ^ r → ⊥
ℕ≢ne neK ℕ≡K =
  let r≡! = relevance-unicity (proj₁ (syntacticEq ℕ≡K)) (ℕⱼ (wfEq ℕ≡K))
  in Ineq.ℕ≢ne! neK (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ rx) r≡! ℕ≡K)

Empty≢ne : ∀ {K r Γ} → Neutral K → Γ ⊢ Empty ≡ K ^ r → ⊥
Empty≢ne neK Empty≡K =
  let r≡% = relevance-unicity (proj₁ (syntacticEq Empty≡K)) (Emptyⱼ (wfEq Empty≡K))
  in Ineq.Empty≢ne% neK (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ rx) r≡% Empty≡K)

-- U != Empty is given easily by relevances
U≢Empty : ∀ {Γ r r′} → Γ ⊢ Univ r ≡ Empty ^ r′ → ⊥
U≢Empty U≡Empty =
  let ⊢U , ⊢Empty = syntacticEq U≡Empty
      e₁ = relevance-unicity ⊢U (Uⱼ (wfEq U≡Empty))
      e₂ = relevance-unicity ⊢Empty (Emptyⱼ (wfEq U≡Empty))
  in !≢% (PE.trans (PE.sym e₁) e₂)

-- ℕ and Empty also by relevance
ℕ≢Empty : ∀ {Γ r} → Γ ⊢ ℕ ≡ Empty ^ r → ⊥
ℕ≢Empty ℕ≡Empty =
  let ⊢ℕ , ⊢Empty = syntacticEq ℕ≡Empty
      e₁ = relevance-unicity ⊢ℕ (ℕⱼ (wfEq ℕ≡Empty))
      e₂ = relevance-unicity ⊢Empty (Emptyⱼ (wfEq ℕ≡Empty))
  in !≢% (PE.trans (PE.sym e₁) e₂)
