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

Empty-irrelevant-term : ∀ {Γ A r} → Γ ⊢ sEmpty ∷ A ^ r → Whnf A → A PE.≡ SProp
Empty-irrelevant-term [Empty] whnfA = let [[Empty]] , e = inversion-Empty [Empty]
                                      in U≡A-whnf (sym (PE.subst (λ r → _ ⊢ _ ≡ _ ^ r) e [[Empty]])) whnfA

Empty-irrelevant : ∀ {Γ r} → Γ ⊢ sEmpty  ^ r → r PE.≡ [ % , ι ⁰ ]
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
  Univ-uniq′ e₁ e₂ el₁ el₂ (Πₙ w) (Πⱼ a ▹ b ▹ x ▹ x₁) (Πⱼ a' ▹ b' ▹ y ▹ y₁) =
    let er₁ , _ = Uinjectivity e₁ 
        er₂ , _ = Uinjectivity e₂
    in PE.trans (PE.sym er₁) er₂ , PE.refl
  Univ-uniq′ e₁ e₂ el₁ el₂ Πirrₙ (Πⱼ a ▹ b ▹ x ▹ x₁) (Πⱼ a' ▹ b' ▹ y ▹ y₁) =
    let er₁ , _ = Uinjectivity e₁ 
        er₂ , _ = Uinjectivity e₂
    in PE.trans (PE.sym er₁) er₂ , PE.refl
  Univ-uniq′ e₁ e₂ el₁ el₂ ∃ₙ (∃ⱼ x ▹ x₁) (∃ⱼ y ▹ y₁) = 
    let er₁ , _ = Uinjectivity e₁ 
        er₂ , _ = Uinjectivity e₂
    in  PE.trans (PE.sym er₁) er₂ , PE.refl 
  Univ-uniq′ e₁ e₂ el₁ el₂ w (var _ x) (var _ y) =
    let T≡T , e = varTypeEq′ x y
        _ , el = typelevel-injectivity e
        ⊢T≡T = PE.subst (λ T → _ ⊢ _ ≡ T ^ _) T≡T (refl (proj₁ (syntacticEq e₁)))
    in proj₁ (Uinjectivity (trans (trans (sym e₁) ⊢T≡T) (PE.subst (λ lx → _ ⊢ _ ≡ _ ^ [ _ , lx ]) (PE.sym el) e₂))) , el
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne ()) (lamⱼ x x₁ x₂ X) y
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne (∘ₙ n)) (_▹_▹_▹_∘ⱼ_ {G = G} _ _ _ x x₁) (_▹_▹_▹_∘ⱼ_ {G = G₁} _ _ _ y y₁) =
    let F≡F , rF≡rF , lF≡lF , lG≡lG , G≡G = injectivity (proj₂ (neTypeEq n x y))
        r≡r , _ = Uinjectivity (trans (sym e₁) (trans (substitutionEq G≡G (substRefl (singleSubst x₁)) (wfEq F≡F))
                                               (PE.subst (λ lx → _ ⊢ _ ≡ _ ^ [ _ , ι lx ]) (PE.sym lG≡lG) e₂))) 
    in r≡r , PE.cong ι lG≡lG
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne ()) (zeroⱼ x) y 
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne ()) (sucⱼ X) y 
  Univ-uniq′ e₁ e₂ el₁ el₂ w (natrecⱼ _ x x₁ x₂ x₃) (natrecⱼ _ x₄ y y₁ y₂) = proj₁ (Uinjectivity (trans (sym e₁) e₂)) , PE.refl
  Univ-uniq′ e₁ e₂ el₁ el₂ w (Emptyrecⱼ x x₁) (Emptyrecⱼ y y₁) = proj₁ (Uinjectivity (trans (sym e₁) e₂)) , PE.refl
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne (Idₙ x)) (Idⱼ X X₁ X₂) (Idⱼ {l = ll} Y Y₁ Y₂) =
    let _ , el = Univ-uniq (ne x) X Y
        er₁ , _ = Uinjectivity e₁
        er₂ , _ = Uinjectivity e₂
    in PE.trans (PE.sym er₁) er₂ , PE.refl
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne (Idℕₙ x)) (Idⱼ X X₁ X₂) (Idⱼ {l = ll} Y Y₁ Y₂) =
    let _ , el = Univ-uniq ℕₙ X Y
        er₁ , _ = Uinjectivity e₁
        er₂ , _ = Uinjectivity e₂
    in PE.trans (PE.sym er₁) er₂ , PE.refl
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne (Idℕ0ₙ x)) (Idⱼ X X₁ X₂) (Idⱼ {l = ll} Y Y₁ Y₂) =
    let _ , el = Univ-uniq ℕₙ X Y
        er₁ , _ = Uinjectivity e₁
        er₂ , _ = Uinjectivity e₂
    in PE.trans (PE.sym er₁) er₂ , PE.refl
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne (IdℕSₙ x)) (Idⱼ X X₁ X₂) (Idⱼ {l = ll} Y Y₁ Y₂) =
    let _ , el = Univ-uniq ℕₙ X Y
        er₁ , _ = Uinjectivity e₁
        er₂ , _ = Uinjectivity e₂
    in PE.trans (PE.sym er₁) er₂ , PE.refl
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne (IdUₙ x)) (Idⱼ X X₁ X₂) (Idⱼ {l = ll} Y Y₁ Y₂) =
    let _ , el = Univ-uniq Uₙ X Y
        er₁ , _ = Uinjectivity e₁
        er₂ , _ = Uinjectivity e₂
    in PE.trans (PE.sym er₁) er₂ , PE.refl
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne (IdUℕₙ x)) (Idⱼ X X₁ X₂) (Idⱼ {l = ll} Y Y₁ Y₂) =
    let _ , el = Univ-uniq Uₙ X Y
        er₁ , _ = Uinjectivity e₁
        er₂ , _ = Uinjectivity e₂
    in PE.trans (PE.sym er₁) er₂ , PE.refl
  Univ-uniq′ e₁ e₂ el₁ el₂ (ne (IdUΠₙ x)) (Idⱼ X X₁ X₂) (Idⱼ {l = ll} Y Y₁ Y₂) =
    let _ , el = Univ-uniq Uₙ X Y
        er₁ , _ = Uinjectivity e₁
        er₂ , _ = Uinjectivity e₂
    in PE.trans (PE.sym er₁) er₂ , PE.refl
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

relevance-unicity-gen : ∀ {Γ A r₁ r₂} → Γ ⊢ A ^ r₁ → Γ ⊢ A ^ r₂ → r₁ PE.≡ r₂
relevance-unicity-gen {r₁ = [ r , l ]} {[ r₁ , l₁ ]} X Y = let er , el = relevance-unicity X Y in  PE.cong₂ [_,_] er el

-- inequalities at any relevance
U≢ℕ : ∀ {r r′ l l′ Γ} → Γ ⊢ Univ r l ≡ ℕ ^ [ r′ , l′ ] → ⊥
U≢ℕ U≡ℕ = Ineq.U≢ℕ! (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ [ rx , _ ]) 
                              (proj₁ (relevance-unicity (proj₂ (syntacticEq U≡ℕ))
                                                 (univ (ℕⱼ (wfEq U≡ℕ)))))
                              U≡ℕ)
          
U≢Π : ∀ {rU lU  F rF G lF lG lΠ r Γ} → Γ ⊢ Univ rU lU ≡ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ r ^ [ r , ι lΠ ] → ⊥
U≢Π U≡Π =
  let r≡! , _ = relevance-unicity (proj₁ (syntacticEq U≡Π)) (Ugenⱼ (wfEq U≡Π))
  in Ineq.U≢Π! (PE.subst (λ rx → _ ⊢ _ ≡ Π _ ^ _ ° _ ▹ _ ° _ ° _ ^ rx ^ [ rx , _ ]) r≡! U≡Π)

U≢ne : ∀ {rU lU r l K Γ} → Neutral K → Γ ⊢ Univ rU lU ≡ K ^ [ r , ι l ] → ⊥
U≢ne neK U≡K =
  let r≡! , _ = relevance-unicity (proj₁ (syntacticEq U≡K)) (Ugenⱼ (wfEq U≡K))
  in Ineq.U≢ne! neK (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ [ rx , _ ]) r≡! U≡K)


ℕ≢Π : ∀ {F rF G lF lG r Γ} → Γ ⊢ ℕ ≡ Π F ^ rF ° lF ▹ G ° lG ° ⁰  ^ r ^ [ r , ι ⁰ ] → ⊥
ℕ≢Π ℕ≡Π =
  let r≡! , _ = relevance-unicity (proj₁ (syntacticEq ℕ≡Π)) (univ (ℕⱼ (wfEq ℕ≡Π)))
  in Ineq.ℕ≢Π! (PE.subst (λ rx → _ ⊢ _ ≡ Π _ ^ _ ° _ ▹ _ ° _ ° _ ^ rx ^ [ rx , _ ]) r≡! ℕ≡Π)

Empty≢Π : ∀ {F rF G lF r Γ} → Γ ⊢ sEmpty ≡ Π F ^ rF ° lF ▹ G ° ⁰ ° ⁰ ^ r ^ [ r , ι ⁰ ] → ⊥
Empty≢Π Empty≡Π =
  let r≡% , _ = relevance-unicity (proj₁ (syntacticEq Empty≡Π)) (univ (Emptyⱼ (wfEq Empty≡Π)))
  in Ineq.Empty≢Π% (PE.subst (λ rx → _ ⊢ _ ≡ Π _ ^ _ ° _ ▹ _ ° _ ° _ ^ rx ^ [ rx , _ ]) r≡% Empty≡Π)

ℕ≢ne : ∀ {K r Γ} → Neutral K → Γ ⊢ ℕ ≡ K ^ [ r , ι ⁰ ] → ⊥
ℕ≢ne neK ℕ≡K =
  let r≡! , _ = relevance-unicity (proj₁ (syntacticEq ℕ≡K)) (univ (ℕⱼ (wfEq ℕ≡K)))
  in Ineq.ℕ≢ne! neK (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ [ rx , _ ]) r≡! ℕ≡K)

Empty≢ne : ∀ {K r Γ} → Neutral K → Γ ⊢ sEmpty ≡ K ^ [ r , ι ⁰ ] → ⊥
Empty≢ne neK Empty≡K =
  let r≡% , _ = relevance-unicity (proj₁ (syntacticEq Empty≡K)) (univ (Emptyⱼ (wfEq Empty≡K)))
  in Ineq.Empty≢ne% neK (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ [ rx , _ ]) r≡% Empty≡K)


-- U != Empty is given easily by relevances
U≢Empty : ∀ {Γ rU lU r′} → Γ ⊢ Univ rU lU ≡ sEmpty ^ r′ → ⊥
U≢Empty U≡Empty =
  let ⊢U , ⊢Empty = syntacticEq U≡Empty
      e₁ , _ = relevance-unicity ⊢U (Ugenⱼ (wfEq U≡Empty))
      e₂ , _ = relevance-unicity ⊢Empty (univ (Emptyⱼ (wfEq U≡Empty)))
  in !≢% (PE.trans (PE.sym e₁) e₂)

-- ℕ and Empty also by relevance
ℕ≢Empty : ∀ {Γ r} → Γ ⊢ ℕ ≡ sEmpty ^ r → ⊥
ℕ≢Empty ℕ≡Empty =
  let ⊢ℕ , ⊢Empty = syntacticEq ℕ≡Empty
      e₁ , _ = relevance-unicity ⊢ℕ (univ (ℕⱼ (wfEq ℕ≡Empty)))
      e₂ , _ = relevance-unicity ⊢Empty (univ (Emptyⱼ (wfEq ℕ≡Empty)))
  in !≢% (PE.trans (PE.sym e₁) e₂)


relevance-uniq : ∀ {Γ t T₁ T₂ r₁ r₂ l₁ l₂} → Γ ⊢ t ∷ T₁ ^ [ r₁ , l₁ ] → Γ ⊢ t ∷ T₂ ^ [ r₂ , l₂ ] →
                 r₁ PE.≡ r₂
relevance-uniq (univ 0<1 x) (univ 0<1 x') = PE.refl 
relevance-uniq (ℕⱼ x) (ℕⱼ x₁) = PE.refl 
relevance-uniq (Emptyⱼ x) (Emptyⱼ x₁) = PE.refl
relevance-uniq (Πⱼ x ▹ x₁ ▹ X ▹ X₁) (Πⱼ x₂ ▹ x₃ ▹ Y ▹ Y₁) =
          PE.refl 
relevance-uniq (∃ⱼ X ▹ X₁) (∃ⱼ Y ▹ Y₁) = PE.refl
relevance-uniq (var xx x) (var _ y) =
    let T≡T , e = varTypeEq′ x y
        er , el = typelevel-injectivity e
    in er
relevance-uniq (lamⱼ x x₁ x₂ X) (lamⱼ y y₁ y₂ Y) =
  let erF , elF  = relevance-unicity (univ x₂) (univ y₂)
  in relevance-uniq X (PE.subst₂ (λ r l → _ ∙ _ ^ [ r , ι l ] ⊢ _ ∷ _ ^ _) (PE.sym erF) (PE.sym (ιinj elF)) Y)
relevance-uniq (_ ▹ _ ▹ _ ▹ X ∘ⱼ X₁) (_ ▹ _ ▹ _ ▹ Y ∘ⱼ Y₁) = relevance-uniq X Y
relevance-uniq {Γ} ⦅ x , x₁ , X , X₁ ⦆ⱼ (⦅_,_,_,_⦆ⱼ {F = F} {G = G} y y₁ Y Y₁)  = PE.refl 
relevance-uniq (fstⱼ X X₁ X₂) (fstⱼ Y Y₁ Y₂) =
    PE.refl 
relevance-uniq (sndⱼ X X₁ X₂) (sndⱼ Y Y₁ Y₂) = PE.refl
relevance-uniq (zeroⱼ x) (zeroⱼ x₁) = PE.refl 
relevance-uniq (sucⱼ X) (sucⱼ Y) = PE.refl 
relevance-uniq (natrecⱼ _ x X X₁ X₂) (natrecⱼ _ y Y Y₁ Y₂) = relevance-uniq X₁ Y₁
relevance-uniq (Emptyrecⱼ x X) (Emptyrecⱼ y Y) = let er , el = relevance-unicity (univ x) (univ y) in er
relevance-uniq (Idⱼ X X₁ X₂) (Idⱼ Y Y₁ Y₂) =
    PE.refl 
relevance-uniq (Idreflⱼ X) (Idreflⱼ Y) =
    PE.refl 
relevance-uniq (transpⱼ x x₁ X X₁ X₂ X₃) (transpⱼ x₂ x₃ Y Y₁ Y₂ Y₃) =
    PE.refl 
relevance-uniq (castⱼ X X₁ X₂ X₃) (castⱼ Y Y₁ Y₂ Y₃) = relevance-uniq X₃ Y₃
relevance-uniq (castreflⱼ X X₁) (castreflⱼ Y Y₁) = PE.refl 
relevance-uniq (conv X x) Y = relevance-uniq X Y
relevance-uniq X (conv Y y) = relevance-uniq X Y
  

inversion-Π' : ∀ {F rF G r rΠ Γ lF lG lΠ}
            → Γ ⊢ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ rΠ ^ r
            → r PE.≡ [ rΠ , ι lΠ ]
inversion-Π' (univ x) = let rG , l! , l% , ⊢F , ⊢G , _ , req , _ = inversion-Π x
                            ⊢Π = Πⱼ l! ▹ l% ▹ ⊢F ▹ ⊢G
                        in relevance-unicity-gen (univ x) (univ (PE.subst (λ rr → _ ⊢ Π _ ^ _ ° _ ▹ _ ° _ ° _ ^ rr ∷  Univ rr _ ^ _) req ⊢Π)) 

inversion-∃' : ∀ {F G Γ r}
            → Γ ⊢ ∃ F ▹ G ^ r
            → r PE.≡ [ % , ι ⁰ ]
inversion-∃' (univ x) = let ⊢F , ⊢G , req , _ = inversion-∃ x
                            er , el = Uinjectivity req
                        in PE.cong₂ [_,_] er (PE.cong ι el) 

inversion-Id' : ∀ {A t u Γ r}
            → Γ ⊢ Id A t u ^ r
            → r PE.≡ [ % , ι ⁰ ]
inversion-Id' (univ x) = let _ , _ , _ , _ , req , _ = inversion-Id x
                             er , el = Uinjectivity req
                         in PE.cong₂ [_,_] er (PE.cong ι el) 
