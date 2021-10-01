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
  Univ-uniq′ e₁ e₂ el₁ el₂ (∃ₙ w) (∃ⱼ x ▹ x₁) (∃ⱼ y ▹ y₁) = 
    let er₁ , _ = Uinjectivity e₁ 
        er₂ , _ = Uinjectivity e₂
        _ , el = Univ-uniq w x y
    in  PE.trans (PE.sym er₁) er₂ , PE.cong next el 
  Univ-uniq′ e₁ e₂ el₁ el₂ w (var _ x) (var _ y) =
    let T≡T , e = varTypeEq′ x y
        _ , el = typelevel-injectivity e
        ⊢T≡T = PE.subst (λ T → _ ⊢ _ ≡ T ^ _) T≡T (refl (proj₁ (syntacticEq e₁)))
    in proj₁ (Uinjectivity (trans (trans (sym e₁) ⊢T≡T) (PE.subst (λ lx → _ ⊢ _ ≡ _ ^ [ _ , lx ]) (PE.sym el) e₂))) , el
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne ()) (lamⱼ x x₁ x₂ X) y
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne (∘ₙ n)) (_∘ⱼ_ {G = G} x x₁) (_∘ⱼ_ {G = G₁} y y₁) =
    let F≡F , rF≡rF , lF≡lF , lG≡lG , G≡G = injectivity (proj₂ (neTypeEq n x y))
        r≡r , _ = Uinjectivity (trans (sym e₁) (trans (substitutionEq G≡G (substRefl (singleSubst x₁)) (wfEq F≡F))
                                               (PE.subst (λ lx → _ ⊢ _ ≡ _ ^ [ _ , ι lx ]) (PE.sym lG≡lG) e₂))) 
    in r≡r , PE.cong ι lG≡lG
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne ()) (zeroⱼ x) y 
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne ()) (sucⱼ X) y 
  Univ-uniq′ e₁ e₂ el₁ el₂ w (natrecⱼ x x₁ x₂ x₃) (natrecⱼ x₄ y y₁ y₂) = proj₁ (Uinjectivity (trans (sym e₁) e₂)) , PE.refl
  Univ-uniq′ e₁ e₂ el₁ el₂ w (Emptyrecⱼ x x₁) (Emptyrecⱼ y y₁) = proj₁ (Uinjectivity (trans (sym e₁) e₂)) , PE.refl
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne (Idₙ x)) (Idⱼ X X₁ X₂) (Idⱼ {l = ll} Y Y₁ Y₂) =
    let _ , el = Univ-uniq (ne x) X Y
        er₁ , _ = Uinjectivity e₁
        er₂ , _ = Uinjectivity e₂
    in PE.trans (PE.sym er₁) er₂ , PE.cong next el
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne (Idℕₙ x)) (Idⱼ X X₁ X₂) (Idⱼ {l = ll} Y Y₁ Y₂) =
    let _ , el = Univ-uniq ℕₙ X Y
        er₁ , _ = Uinjectivity e₁
        er₂ , _ = Uinjectivity e₂
    in PE.trans (PE.sym er₁) er₂ , PE.cong next el
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne (Idℕ0ₙ x)) (Idⱼ X X₁ X₂) (Idⱼ {l = ll} Y Y₁ Y₂) =
    let _ , el = Univ-uniq ℕₙ X Y
        er₁ , _ = Uinjectivity e₁
        er₂ , _ = Uinjectivity e₂
    in PE.trans (PE.sym er₁) er₂ , PE.cong next el
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne (IdℕSₙ x)) (Idⱼ X X₁ X₂) (Idⱼ {l = ll} Y Y₁ Y₂) =
    let _ , el = Univ-uniq ℕₙ X Y
        er₁ , _ = Uinjectivity e₁
        er₂ , _ = Uinjectivity e₂
    in PE.trans (PE.sym er₁) er₂ , PE.cong next el
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne (IdUₙ x)) (Idⱼ X X₁ X₂) (Idⱼ {l = ll} Y Y₁ Y₂) =
    let _ , el = Univ-uniq Uₙ X Y
        er₁ , _ = Uinjectivity e₁
        er₂ , _ = Uinjectivity e₂
    in PE.trans (PE.sym er₁) er₂ , PE.cong next el
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne (IdUℕₙ x)) (Idⱼ X X₁ X₂) (Idⱼ {l = ll} Y Y₁ Y₂) =
    let _ , el = Univ-uniq Uₙ X Y
        er₁ , _ = Uinjectivity e₁
        er₂ , _ = Uinjectivity e₂
    in PE.trans (PE.sym er₁) er₂ , PE.cong next el
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne (IdUΠₙ x)) (Idⱼ X X₁ X₂) (Idⱼ {l = ll} Y Y₁ Y₂) =
    let _ , el = Univ-uniq Uₙ X Y
        er₁ , _ = Uinjectivity e₁
        er₂ , _ = Uinjectivity e₂
    in PE.trans (PE.sym er₁) er₂ , PE.cong next el
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

relevance-unicity : ∀ {Γ A r₁ r₂ l₁ l₂} → Γ ⊢ A ^ [ r₁ , l₁ ] → Γ ⊢ A ^ [ r₂ , l₂ ] → r₁ PE.≡ r₂ × l₁ PE.≡ l₂
relevance-unicity ⊢A₁ ⊢A₂ with doΠNorm ⊢A₁
... | _ with doΠNorm ⊢A₂
relevance-unicity ⊢A₁ ⊢A₂ | B , nB , ⊢B , rB | C , nC , ⊢C , rC =
  let e = detΠNorm* nB nC rB rC
  in relevance-unicity′ nC (PE.subst _ e ⊢B) ⊢C

-- inequalities at any relevance
U≢ℕ : ∀ {r r′ l l′ Γ} → Γ ⊢ Univ r l ≡ ℕ ^ [ r′ , l′ ] → ⊥
U≢ℕ U≡ℕ = Ineq.U≢ℕ! (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ [ rx , _ ]) 
                              (proj₁ (relevance-unicity (proj₂ (syntacticEq U≡ℕ))
                                                 (univ (ℕⱼ (wfEq U≡ℕ)))))
                              U≡ℕ)
          
U≢Π : ∀ {rU lU  F rF G lF lG lΠ r Γ} → Γ ⊢ Univ rU lU ≡ Π F ^ rF ° lF ▹ G ° lG ° lΠ  ^ [ r , ι lΠ ] → ⊥
U≢Π U≡Π =
  let r≡! , _ = relevance-unicity (proj₁ (syntacticEq U≡Π)) (Ugenⱼ (wfEq U≡Π))
  in Ineq.U≢Π! (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ [ rx , _ ]) r≡! U≡Π)

U≢ne : ∀ {rU lU r l K Γ} → Neutral K → Γ ⊢ Univ rU lU ≡ K ^ [ r , ι l ] → ⊥
U≢ne neK U≡K =
  let r≡! , _ = relevance-unicity (proj₁ (syntacticEq U≡K)) (Ugenⱼ (wfEq U≡K))
  in Ineq.U≢ne! neK (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ [ rx , _ ]) r≡! U≡K)


ℕ≢Π : ∀ {F rF G lF lG r Γ} → Γ ⊢ ℕ ≡ Π F ^ rF ° lF ▹ G ° lG ° ⁰ ^ [ r , ι ⁰ ] → ⊥
ℕ≢Π ℕ≡Π =
  let r≡! , _ = relevance-unicity (proj₁ (syntacticEq ℕ≡Π)) (univ (ℕⱼ (wfEq ℕ≡Π)))
  in Ineq.ℕ≢Π! (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ [ rx , _ ]) r≡! ℕ≡Π)


Empty≢Π : ∀ {F rF G lF lG lΠ r Γ} → Γ ⊢ Empty lΠ ≡ Π F ^ rF ° lF ▹ G ° lG ° lΠ  ^ [ r , ι lΠ ] → ⊥
Empty≢Π Empty≡Π =
  let r≡% , _ = relevance-unicity (proj₁ (syntacticEq Empty≡Π)) (univ (Emptyⱼ (wfEq Empty≡Π)))
  in Ineq.Empty≢Π% (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ [ rx , _ ]) r≡% Empty≡Π)

ℕ≢ne : ∀ {K r Γ} → Neutral K → Γ ⊢ ℕ ≡ K ^ [ r , ι ⁰ ] → ⊥
ℕ≢ne neK ℕ≡K =
  let r≡! , _ = relevance-unicity (proj₁ (syntacticEq ℕ≡K)) (univ (ℕⱼ (wfEq ℕ≡K)))
  in Ineq.ℕ≢ne! neK (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ [ rx , _ ]) r≡! ℕ≡K)

Empty≢ne : ∀ {K r l Γ} → Neutral K → Γ ⊢ Empty l ≡ K ^ [ r , ι l ] → ⊥
Empty≢ne neK Empty≡K =
  let r≡% , _ = relevance-unicity (proj₁ (syntacticEq Empty≡K)) (univ (Emptyⱼ (wfEq Empty≡K)))
  in Ineq.Empty≢ne% neK (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ [ rx , _ ]) r≡% Empty≡K)


-- U != Empty is given easily by relevances
U≢Empty : ∀ {Γ rU lU lEmpty r′} → Γ ⊢ Univ rU lU ≡ Empty lEmpty ^ r′ → ⊥
U≢Empty U≡Empty =
  let ⊢U , ⊢Empty = syntacticEq U≡Empty
      e₁ , _ = relevance-unicity ⊢U (Ugenⱼ (wfEq U≡Empty))
      e₂ , _ = relevance-unicity ⊢Empty (univ (Emptyⱼ (wfEq U≡Empty)))
  in !≢% (PE.trans (PE.sym e₁) e₂)

-- ℕ and Empty also by relevance
ℕ≢Empty : ∀ {Γ r l} → Γ ⊢ ℕ ≡ Empty l ^ r → ⊥
ℕ≢Empty ℕ≡Empty =
  let ⊢ℕ , ⊢Empty = syntacticEq ℕ≡Empty
      e₁ , _ = relevance-unicity ⊢ℕ (univ (ℕⱼ (wfEq ℕ≡Empty)))
      e₂ , _ = relevance-unicity ⊢Empty (univ (Emptyⱼ (wfEq ℕ≡Empty)))
  in !≢% (PE.trans (PE.sym e₁) e₂)
