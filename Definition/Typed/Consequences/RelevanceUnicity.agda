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
open import Definition.Typed.Consequences.Substitution

open import Tools.Product
open import Tools.Empty
open import Tools.Sum using (_⊎_; inj₁; inj₂)
import Tools.PropositionalEquality as PE

ℕ-relevant-term : ∀ {Γ A r} → Γ ⊢ ℕ ∷ A ^ r → Whnf A → A PE.≡ Univ ! ⁰
ℕ-relevant-term [ℕ] whnfA = let [[N]] , e = inversion-ℕ [ℕ]
                             in U≡A-whnf (sym (PE.subst (λ r → _ ⊢ _ ≡ _ ^ r) e [[N]])) whnfA

ℕ-relevant : ∀ {Γ r} → Γ ⊢ ℕ ^ r → r PE.≡ [ ! , ι ⁰ ]
ℕ-relevant (univ [ℕ]) = let er , el = Univ-PE-injectivity (ℕ-relevant-term [ℕ] Uₙ)
                         in PE.cong₂ (λ x y → [ x , ι y ]) er el

Empty-irrelevant-term : ∀ {Γ A lEmpty r} → Γ ⊢ Empty lEmpty ∷ A ^ r → Whnf A → A PE.≡ SProp lEmpty
Empty-irrelevant-term [Empty] whnfA = let [[Empty]] , e = inversion-Empty [Empty]
                                      in U≡A-whnf (sym (PE.subst (λ r → _ ⊢ _ ≡ _ ^ r) e [[Empty]])) whnfA

Empty-irrelevant : ∀ {Γ lEmpty r} → Γ ⊢ Empty lEmpty ^ r → r PE.≡ [ % , ι lEmpty ]
Empty-irrelevant (univ [Empty]) = let er , el = Univ-PE-injectivity (Empty-irrelevant-term [Empty] Uₙ)
                                  in PE.cong₂ (λ x y → [ x , ι y ]) er el

Univ-relevant-term : ∀ {Γ A rU lU r} → Γ ⊢ Univ rU lU ∷ A ^ r → Whnf A → A PE.≡ U ¹ × lU PE.≡ ⁰
Univ-relevant-term [U] whnfA = U≡A-whnf (sym (proj₁ (inversion-U [U]))) whnfA , proj₂ (proj₂ (inversion-U [U]))

Univ-relevant : ∀ {Γ rU lU r} → Γ ⊢ Univ rU lU ^ r → r PE.≡ [ ! , next lU ]
Univ-relevant (Uⱼ _) = PE.refl
Univ-relevant (univ [U]) = let er , el = Univ-PE-injectivity (proj₁ (Univ-relevant-term [U] Uₙ))
                           in PE.cong₂ (λ x y → [ x , y ]) er
                                       (PE.trans (PE.cong ι el) (PE.cong next (PE.sym  (proj₂ (Univ-relevant-term [U] Uₙ)))))


Univ-uniq′ : ∀ {Γ A T₁ T₂ r₁ r₂ l₁ l₁' l₂ l₂'} → Γ ⊢ T₁ ≡ Univ r₁ l₁ ^ [ ! , l₁' ] → Γ ⊢ T₂ ≡ Univ r₂ l₂ ^ [ ! , l₂' ]
  → next l₁ PE.≡ l₁' → next l₂ PE.≡ l₂' → l₁' PE.≡ l₂' 
  → ΠNorm A
  → Γ ⊢ A ∷ T₁ ^ [ ! , l₁' ] → Γ ⊢ A ∷ T₂ ^ [ ! , l₂' ] → r₁ PE.≡ r₂
Univ-uniq′ e₁ e₂ el₁ el₂ ell w (univ x x₁) (univ x₂ x₃) =
  let er₁ , _ = Uinjectivity e₁ 
      er₂ , _ = Uinjectivity e₂
  in PE.trans (PE.sym er₁) er₂
Univ-uniq′ e₁ e₂ el₁ PE.refl ell w (ℕⱼ x) y =
  let e₁′ , el₁′  = Uinjectivity e₁
      e₂′ , el₂′ = Uinjectivity (trans (sym e₂) (proj₁ (inversion-ℕ y)) ) 
  in PE.sym (PE.trans e₂′ e₁′) 
Univ-uniq′ e₁ e₂ el₁ el₂ ell w (Emptyⱼ x) y =
  let e₁′ , el₁′  = Uinjectivity e₁
      e₂′ , el₂′ = Uinjectivity (trans (sym e₂) (proj₁ (inversion-Empty y)) ) 
  in PE.sym (PE.trans e₂′ e₁′)
Univ-uniq′ e₁ e₂ el₁ el₂ ell w (Πⱼ a ▹ b ▹ x ▹ x₁) (Πⱼ a' ▹ b' ▹ y ▹ y₁) =
  let er₁ , _ = Uinjectivity e₁ 
      er₂ , _ = Uinjectivity e₂
  in PE.trans (PE.sym er₁) (PE.trans (Univ-uniq′ (refl (Ugenⱼ (wfTerm x₁))) (refl (Ugenⱼ (wfTerm x₁)))
                                                 PE.refl PE.refl PE.refl (ΠNorm-Π w) x₁ y₁) er₂)
Univ-uniq′ e₁ e₂ el₁ el₂ ell w (∃ⱼ x ▹ x₁) (∃ⱼ y ▹ y₁) =
  let er₁ , _ = Uinjectivity e₁ 
      er₂ , _ = Uinjectivity e₂
  in  PE.trans (PE.sym er₁) er₂ 
Univ-uniq′ e₁ e₂ el₁ el₂ PE.refl w (var _ x) (var _ y) =
  let T≡T = proj₁ (varTypeEq′ x y )
      ⊢T≡T = PE.subst (λ T → _ ⊢ _ ≡ T ^ _) T≡T (refl (proj₁ (syntacticEq e₁)))
  in proj₁ (Uinjectivity (trans (trans (sym e₁) ⊢T≡T) e₂)) 
Univ-uniq′ e₁ e₂ el₁ el₂ ell (ne ()) (lamⱼ x x₁ x₂ X) y
Univ-uniq′ e₁ e₂ el₁ el₂ PE.refl (ne (∘ₙ n)) (_∘ⱼ_ {G = G} x x₁) (_∘ⱼ_ {G = G₁} y y₁) =
  let F≡F , rF≡rF , lF≡lF , lG≡lG , G≡G = injectivity (neTypeEq n PE.refl x y)
      r≡r , _ = Uinjectivity (trans (sym e₁) (trans (substitutionEq G≡G (substRefl (singleSubst x₁)) (wfEq F≡F)) e₂))
  in r≡r
Univ-uniq′ e₁ e₂ el₁ el₂ ell (ne ()) (zeroⱼ x) y 
Univ-uniq′ e₁ e₂ el₁ el₂ ell (ne ()) (sucⱼ X) y 
Univ-uniq′ e₁ e₂ el₁ el₂ PE.refl w (natrecⱼ x x₁ x₂ x₃) (natrecⱼ x₄ y y₁ y₂) = proj₁ (Uinjectivity (trans (sym e₁) e₂))
Univ-uniq′ e₁ e₂ el₁ el₂ PE.refl w (Emptyrecⱼ x x₁) (Emptyrecⱼ x₂ y) = proj₁ (Uinjectivity (trans (sym e₁) e₂))
Univ-uniq′ e₁ e₂ el₁ el₂ ell w (Idⱼ X X₁ X₂) (Idⱼ {l = ll} y y₁ y₂) =
  proj₁ (Uinjectivity (trans (sym e₁) (PE.subst (λ _l → _ ⊢ SProp _l ≡ Univ _ _ ^ [ _ , next _l ]) (PE.sym (next-inj ell)) e₂)))
Univ-uniq′ e₁ e₂ el₁ el₂ PE.refl w (castⱼ X X₁ X₂ X₃) (castⱼ y y₁ y₂ y₃) = proj₁ (Uinjectivity (trans (sym e₁) e₂))
Univ-uniq′ e₁ e₂ el₁ el₂ ell w (conv x x₁) y = Univ-uniq′ (trans x₁ e₁) e₂ el₁ el₂ ell w x y
Univ-uniq′ e₁ e₂ el₁ el₂ ell w x (conv y y₁) = Univ-uniq′ e₁ (trans y₁ e₂) el₁ el₂ ell w x y

Univ-uniq : ∀ {Γ A r₁ r₂ l} → ΠNorm A
  → Γ ⊢ A ∷ Univ r₁ l ^ [ ! , next l ] → Γ ⊢ A ∷ Univ r₂ l ^ [ ! , next l ] → r₁ PE.≡ r₂ 
Univ-uniq n ⊢A₁ ⊢A₂ =
  let ⊢Γ = wfTerm ⊢A₁
  in Univ-uniq′ (refl (Ugenⱼ ⊢Γ)) (refl (Ugenⱼ ⊢Γ)) PE.refl PE.refl PE.refl n ⊢A₁ ⊢A₂

relevance-unicity′ : ∀ {Γ A r₁ r₂ l₁ l₂} → ΠNorm A → l₁ PE.≡ l₂ → Γ ⊢ A ^ [ r₁ , l₁ ] → Γ ⊢ A ^ [ r₂ , l₂ ] → r₁ PE.≡ r₂
relevance-unicity′ n el (Uⱼ x) (Uⱼ x₁) = PE.refl
relevance-unicity′ n el (Uⱼ x) (univ x₁) = let _ , _ , ¹≡⁰ = inversion-U x₁ in ⊥-elim (⁰≢¹ (PE.sym  ¹≡⁰))
relevance-unicity′ n el (univ x) (Uⱼ x₁) = let _ , _ , ¹≡⁰ = inversion-U x in ⊥-elim (⁰≢¹ (PE.sym  ¹≡⁰))
relevance-unicity′ n PE.refl (univ x) (univ x₁) = Univ-uniq n x x₁

relevance-unicity : ∀ {Γ A r₁ r₂ l} → Γ ⊢ A ^ [ r₁ , l ] → Γ ⊢ A ^ [ r₂ , l ] → r₁ PE.≡ r₂
relevance-unicity ⊢A₁ ⊢A₂ with doΠNorm ⊢A₁
... | _ with doΠNorm ⊢A₂
relevance-unicity ⊢A₁ ⊢A₂ | B , nB , ⊢B , rB | C , nC , ⊢C , rC =
  let e = detΠNorm* nB nC rB rC
  in relevance-unicity′ nC PE.refl (PE.subst _ e ⊢B) ⊢C


univ-unicity : ∀ {Γ A r₁ r₂ l} → Γ ⊢ A ∷ Univ r₁ l ^ [ ! , next l ] → Γ ⊢ A ∷ Univ r₂ l ^ [ ! , next l ] → r₁ PE.≡ r₂
univ-unicity ⊢₁ ⊢₂ = relevance-unicity (univ ⊢₁) (univ ⊢₂)


{-

level-uniq′ : ∀ {Γ A T₁ T₂ l₁ l₂} → Γ ⊢ A ∷ T₁ ^ [ ! , l₁ ] → Γ ⊢ A ∷ T₂ ^ [ ! , l₂ ] → l₁ PE.≡ l₂
level-uniq′ (univ 0<1 x₁) (univ 0<1 x₃) = PE.refl
level-uniq′ (ℕⱼ x) (ℕⱼ x₁) = PE.refl
level-uniq′ (Emptyⱼ x) (Emptyⱼ x₁) = PE.refl
level-uniq′ (Πⱼ x ▹ x₁ ▹ X ▹ X₁) (Πⱼ x₂ ▹ x₃ ▹ Y ▹ Y₁) = PE.refl
level-uniq′ (∃ⱼ X ▹ X₁) (∃ⱼ Y ▹ Y₁) = level-uniq′ X Y
level-uniq′ (var _ x) (var _ y) = let _ , e = typelevel-injectivity (proj₂ (varTypeEq′ x y)) in e
level-uniq′ (lamⱼ x x₁ x₂ X) (lamⱼ x₃ x₄ x₅ Y) = {!!}
level-uniq′ (X ∘ⱼ X₁) (Y ∘ⱼ Y₁) = {!!}
level-uniq′ (zeroⱼ x) (zeroⱼ x₁) = PE.refl
level-uniq′ (sucⱼ X) (sucⱼ Y) = PE.refl
level-uniq′ (natrecⱼ x X X₁ X₂) (natrecⱼ x₁ Y Y₁ Y₂) = PE.refl
level-uniq′ (Emptyrecⱼ x X) (Emptyrecⱼ x₁ Y) = {!!}
level-uniq′ (Idⱼ X X₁ X₂) (Idⱼ Y Y₁ Y₂) = {!!}
level-uniq′ (castⱼ X X₁ X₂ X₃) (castⱼ Y Y₁ Y₂ Y₃) = PE.refl
level-uniq′ (conv X x) Y = level-uniq′ X Y
level-uniq′ X (conv Y x) = level-uniq′ X Y


mutual 
  Univ-uniq′ : ∀ {Γ A T₁ T₂ r₁ r₂ l₁ l₁' l₂ l₂'} → Γ ⊢ T₁ ≡ Univ r₁ l₁ ^ [ ! , l₁' ] → Γ ⊢ T₂ ≡ Univ r₂ l₂ ^ [ ! , l₂' ]
    → next l₁ PE.≡ l₁' → next l₂ PE.≡ l₂'
    → ΠNorm A
    → Γ ⊢ A ∷ T₁ ^ [ ! , l₁' ] → Γ ⊢ A ∷ T₂ ^ [ ! , l₂' ] → r₁ PE.≡ r₂ × l₁' PE.≡ l₂' 
  Univ-uniq′ e₁ e₂ el₁ el₂ w (univ 0<1 x₁) (univ 0<1 x₃) = 
    let er₁ , _ = Uinjectivity e₁ 
        er₂ , _ = Uinjectivity e₂
    in PE.trans (PE.sym er₁) er₂ , PE.refl
  Univ-uniq′ e₁ e₂ el₁ PE.refl w (ℕⱼ x) y =
    let e₁′ , el₁′  = Uinjectivity e₁
        e₂′ , el₂′ = Uinjectivity (trans (sym e₂) (proj₁ (inversion-ℕ y)) ) 
    in PE.sym (PE.trans e₂′ e₁′) , PE.cong next (PE.sym el₂′)
  Univ-uniq′ e₁ e₂ el₁ el₂ w (Emptyⱼ x) y =
    let e₁′ , el₁′  = Uinjectivity e₁
        e₂′ , el₂′ = Uinjectivity (trans (sym e₂) (proj₁ (inversion-Empty y)) ) 
    in PE.sym (PE.trans e₂′ e₁′) , PE.trans (PE.cong next (PE.sym el₂′)) el₂
  Univ-uniq′ e₁ e₂ el₁ el₂ w (Πⱼ a ▹ b ▹ x ▹ x₁) (Πⱼ a' ▹ b' ▹ y ▹ y₁) =
    let er₁ , _ = Uinjectivity e₁ 
        er₂ , _ = Uinjectivity e₂
        res = Univ-uniq′ (refl (Ugenⱼ (wfTerm x₁))) (refl (Ugenⱼ (wfTerm x₁)))
                                                    PE.refl PE.refl (ΠNorm-Π w) x₁ y₁
    in PE.trans (PE.sym er₁) (PE.trans (proj₁ res) er₂) , PE.refl
  Univ-uniq′ e₁ e₂ el₁ el₂ w (∃ⱼ x ▹ x₁) (∃ⱼ y ▹ y₁) =
    let er₁ , _ = Uinjectivity e₁ 
        er₂ , _ = Uinjectivity e₂
        _ , el = Univ-uniq {!!} x y
    in  PE.trans (PE.sym er₁) er₂ , PE.cong next el 
  Univ-uniq′ e₁ e₂ el₁ el₂ w (var _ x) (var _ y) =
    let T≡T , e = varTypeEq′ x y
        _ , el = typelevel-injectivity e
        ⊢T≡T = PE.subst (λ T → _ ⊢ _ ≡ T ^ _) T≡T (refl (proj₁ (syntacticEq e₁)))
    in proj₁ (Uinjectivity (trans (trans (sym e₁) ⊢T≡T) (PE.subst (λ lx → _ ⊢ _ ≡ _ ^ [ _ , lx ]) (PE.sym el) e₂))) , el
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne ()) (lamⱼ x x₁ x₂ X) y
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne (∘ₙ n)) (_∘ⱼ_ {G = G} x x₁) (_∘ⱼ_ {G = G₁} y y₁) =
    let F≡F , rF≡rF , lF≡lF , lG≡lG , G≡G = injectivity (neTypeEq n PE.refl x y)
        r≡r , _ = Uinjectivity (trans (sym e₁) (trans (substitutionEq G≡G (substRefl (singleSubst x₁)) (wfEq F≡F))
                                               (PE.subst (λ lx → _ ⊢ _ ≡ _ ^ [ _ , ι lx ]) (PE.sym lG≡lG) e₂))) 
    in r≡r , PE.cong ι lG≡lG
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne ()) (zeroⱼ x) y 
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne ()) (sucⱼ X) y 
  Univ-uniq′ e₁ e₂ el₁ el₂ w (natrecⱼ x x₁ x₂ x₃) (natrecⱼ x₄ y y₁ y₂) = proj₁ (Uinjectivity (trans (sym e₁) e₂)) , PE.refl
  Univ-uniq′ e₁ e₂ el₁ el₂ w (Emptyrecⱼ (Uⱼ x) x₁) (Emptyrecⱼ (Uⱼ x₃) x₂) = proj₁ (Uinjectivity (trans (sym e₁) e₂)) , PE.refl
  Univ-uniq′ e₁ e₂ el₁ el₂ w (Emptyrecⱼ (Uⱼ x) x₁) (Emptyrecⱼ (univ y) x₂) = ⊥-elim (UnotInA y)
  Univ-uniq′ e₁ e₂ el₁ el₂ w (Emptyrecⱼ (univ x) x₁) (Emptyrecⱼ (Uⱼ y) x₂) = ⊥-elim (UnotInA x)
  Univ-uniq′ e₁ e₂ el₁ el₂ w (Emptyrecⱼ (univ x) x₁) (Emptyrecⱼ (univ y) x₂) =
    let er , el  = Univ-uniq {!!} x y in proj₁ (Uinjectivity (trans (sym e₁)
                                                 (PE.subst (λ _l → _ ⊢ _ ≡ _ ^ [ _ , ι _l ]) (PE.sym el) e₂))) , PE.cong ι el
  Univ-uniq′ e₁ e₂ el₁ el₂ w (Idⱼ X X₁ X₂) (Idⱼ {l = ll} y y₁ y₂) = {!!}
    -- proj₁ (Uinjectivity (trans (sym e₁) (PE.subst (λ _l → _ ⊢ SProp _l ≡ Univ _ _ ^ [ _ , next _l ]) (PE.sym (next-inj ell)) e₂))) ,
    -- ?
  Univ-uniq′ e₁ e₂ el₁ el₂ w (castⱼ X X₁ X₂ X₃) (castⱼ y y₁ y₂ y₃) = proj₁ (Uinjectivity (trans (sym e₁) e₂)) , PE.refl
  Univ-uniq′ e₁ e₂ el₁ el₂ w (conv x x₁) y = Univ-uniq′ (trans x₁ e₁) e₂ el₁ el₂ w x y 
  Univ-uniq′ e₁ e₂ el₁ el₂ w x (conv y y₁) = Univ-uniq′ e₁ (trans y₁ e₂) el₁ el₂ w x y 
  
  Univ-uniq : ∀ {Γ A r₁ r₂ l₁ l₂} → ΠNorm A
    → Γ ⊢ A ∷ Univ r₁ l₁ ^ [ ! , next l₁ ] → Γ ⊢ A ∷ Univ r₂ l₂ ^ [ ! , next l₂ ] → r₁ PE.≡ r₂ × l₁ PE.≡ l₂
  Univ-uniq n ⊢A₁ ⊢A₂ =
    let ⊢Γ = wfTerm ⊢A₁
        er , el =  Univ-uniq′ (refl (Ugenⱼ ⊢Γ)) (refl (Ugenⱼ ⊢Γ)) PE.refl PE.refl n ⊢A₁ ⊢A₂
    in er , next-inj el

  relevance-unicity′ : ∀ {Γ A r₁ r₂ l₁ l₂} → ΠNorm A → Γ ⊢ A ^ [ r₁ , l₁ ] → Γ ⊢ A ^ [ r₂ , l₂ ] → r₁ PE.≡ r₂ × l₁ PE.≡ l₂
  relevance-unicity′ n (Uⱼ x) (Uⱼ x₁) = PE.refl , PE.refl 
  relevance-unicity′ n (Uⱼ x) (univ x₁) = let _ , _ , ¹≡⁰ = inversion-U x₁ in ⊥-elim (⁰≢¹ (PE.sym  ¹≡⁰))
  relevance-unicity′ n (univ x) (Uⱼ x₁) = let _ , _ , ¹≡⁰ = inversion-U x in ⊥-elim (⁰≢¹ (PE.sym  ¹≡⁰))
  relevance-unicity′ n (univ x) (univ x₁) = let er , el = Univ-uniq n x x₁ in er , PE.cong ι el 



-- inequalities at any relevance
U≢ℕ : ∀ {r r′ l l′ Γ} → Γ ⊢ Univ r l ≡ ℕ ^ [ r′ , l′ ] → ⊥
U≢ℕ U≡ℕ = Ineq.U≢ℕ! (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ [ rx , _ ]) (relevance-unicity {!!} (univ (ℕⱼ (wfEq U≡ℕ))))
                              -- (relevance-unicity (proj₂ (syntacticEq U≡ℕ))
                              --                    (ℕⱼ (wfEq U≡ℕ)))
                              U≡ℕ)
          


U≢Π : ∀ {rU lU  F rF G lF lG lΠ r Γ} → Γ ⊢ Univ rU lU ≡ Π F ^ rF ° lF ▹ G ° lG ° lΠ  ^ [ r , ι lΠ ] → ⊥
U≢Π U≡Π =
  let r≡! = relevance-unicity (proj₁ (syntacticEq U≡Π)) (Uⱼ (wfEq U≡Π))
  in Ineq.U≢Π! (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ rx) r≡! U≡Π)

U≢ne : ∀ {rU r K Γ} → Neutral K → Γ ⊢ Univ rU ≡ K ^ r → ⊥
U≢ne neK U≡K =
  let r≡! = relevance-unicity (proj₁ (syntacticEq U≡K)) (Uⱼ (wfEq U≡K))
  in Ineq.U≢ne! neK (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ rx) r≡! U≡K)

ℕ≢Π : ∀ {F rF G lF lG lΠ r Γ} → Γ ⊢ ℕ ≡ Π F ^ rF ° lF ▹ G ° lG ° lΠ  ^ [ r , ι lΠ ] → ⊥
ℕ≢Π ℕ≡Π =
  let r≡! = relevance-unicity (proj₁ (syntacticEq ℕ≡Π)) (ℕⱼ (wfEq ℕ≡Π))
  in Ineq.ℕ≢Π! (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ rx) r≡! ℕ≡Π)

Empty≢Π : ∀ {F rF G lF lG lΠ r Γ} → Γ ⊢ Empty ≡ Π F ^ rF ° lF ▹ G ° lG ° lΠ  ^ [ r , ι lΠ ] → ⊥
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
-}
