{-# OPTIONS --safe #-}


module Definition.Typed.Consequences.PiNorm where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.Weakening
open import Definition.Typed.EqRelInstance
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Fundamental.Reducibility
open import Definition.Typed.Consequences.Inversion
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.Syntactic
open import Definition.Conversion.Stability

open import Tools.Product
open import Tools.Empty
import Tools.PropositionalEquality as PE

-- reduction including in the codomain of Pis
-- useful to get unicity of relevance

-- there are 2 kinds of fat arrows!!!
-- the constructor for transitivity closure is closed on the left ⇨
-- the ones in types aren't ⇒

data ΠNorm : Term → Set where
  Uₙ : ∀ {r l} → ΠNorm (Univ r l)
  Πₙ : ∀ {F rF lF G lG lΠ} → ΠNorm G → ΠNorm (Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ !)
  Πirrₙ : ∀ {F rF lF G} → ΠNorm (Π F ^ rF ° lF ▹ G ° ⁰ ° ⁰ ^ %)
  ∃ₙ : ∀ {F G} → ΠNorm (∃ F ▹ G)
  ℕₙ : ΠNorm ℕ
  Emptyₙ : ΠNorm sEmpty
  ne   : ∀ {n} → Neutral n → ΠNorm n

ΠNorm-Π : ∀ {F rF lF G lG lΠ} → ΠNorm (Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ !) → ΠNorm G 
ΠNorm-Π (Πₙ x) = x
ΠNorm-Π (ne ())


data _⊢_⇒Π_∷_^_ (Γ : Con Term) : Term → Term → Term → TypeLevel → Set where
  regular : ∀ {t u A l} → Γ ⊢ t ⇒ u ∷ A ^ l → Γ ⊢ t ⇒Π u ∷ A ^ l
  deepΠ : ∀ {F rF lF G G′ lG lΠ}
       → Γ ∙ F ^ [ rF , ι lF ] ⊢ G ⇒Π G′ ∷ Univ ! lG ^ next lG
       → Γ ⊢ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ ! ⇒Π Π F ^ rF ° lF ▹ G′ ° lG ° lΠ ^ ! ∷ Univ ! lΠ ^ next lΠ 

data _⊢_⇒Π_^_ (Γ : Con Term) : Term → Term → TypeInfo → Set where
  univ : ∀ {A B r l}
       → Γ ⊢ A ⇒Π B ∷ (Univ r l) ^ next l
       → Γ ⊢ A ⇒Π B ^ [ r , ι l ]

data _⊢_⇒*Π_∷_^_ (Γ : Con Term) : Term → Term → Term → TypeLevel → Set where
  id : ∀ {t T l} → Γ ⊢ t ⇒*Π t ∷ T ^ l
  _⇨_ : ∀ {t t' u T l}
      → Γ ⊢ t  ⇒Π t' ∷ T ^ l
      → Γ ⊢ t' ⇒*Π u ∷ T ^ l
      → Γ ⊢ t  ⇒*Π u ∷ T ^ l

data _⊢_⇒*Π_^_ (Γ : Con Term) : Term → Term → TypeInfo → Set where
  id : ∀ {A r} → Γ ⊢ A ⇒*Π A ^ r
  _⇨_ : ∀ {t t' u r}
      → Γ ⊢ t  ⇒Π t' ^ r
      → Γ ⊢ t' ⇒*Π u ^ r
      → Γ ⊢ t  ⇒*Π u ^ r

_⇨*_ : ∀ {Γ A B C r} → Γ ⊢ A ⇒*Π B ^ r → Γ ⊢ B ⇒*Π C ^ r → Γ ⊢ A ⇒*Π C ^ r
id ⇨* y = y
(x ⇨ x₁) ⇨* y = x ⇨ (x₁ ⇨* y)

regular* : ∀ {Γ t u r} → Γ ⊢ t ⇒* u ^ r → Γ ⊢ t ⇒*Π u ^ r
regular* (id _) = id
regular* (univ x ⇨ x₁) = univ (regular x) ⇨ regular* x₁

deep* : ∀ {Γ F rF lF G G′ lG lΠ}
      → Γ ∙ F ^ [ rF , ι lF ] ⊢ G ⇒*Π G′ ^ [ ! , ι lG ]
      → Γ ⊢ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ ! ⇒*Π Π F ^ rF ° lF ▹ G′ ° lG ° lΠ ^ ! ^ [ ! , ι lΠ ]
deep* id = id 
deep* (univ (regular x) ⇨ x₁) = univ (deepΠ (regular x)) ⇨ deep* x₁
deep* (univ (deepΠ x) ⇨ x₁) = univ (deepΠ (deepΠ x)) ⇨ deep* x₁

deep-correct-term : ∀ {Γ t u T l} → Γ ⊢ t ∷ T ^ [ ! , l ] → Γ ⊢ t ⇒Π u ∷ T ^ l → Γ ⊢ u ∷ T ^ [ ! , l ] × Γ ⊢ t ≡ u ∷ T ^ [ ! , l ]
deep-correct-term ⊢t (regular x) =
  let t≡u = subsetTerm x
      _ , _ , ⊢u = syntacticEqTerm t≡u
  in ⊢u , t≡u
deep-correct-term ⊢t (deepΠ X) =
  let _ , l< , l<' , ⊢F , ⊢G , e , _ = inversion-Π ⊢t
      erG , _ = Uinjectivity e
      ⊢G' , G≡G' = deep-correct-term (PE.subst (λ rr → _ ⊢ _ ∷ Univ rr _ ^ _ ) (PE.sym erG) ⊢G) X
  in Πⱼ (λ x → l< (PE.trans (PE.sym erG) x) ) ▹ (λ x → l<' (PE.trans (PE.sym erG) x) ) ▹ ⊢F ▹ ⊢G' ,
     Π-cong (λ x → l< (PE.trans (PE.sym erG) x)) (λ x → l<' (PE.trans (PE.sym erG) x))  (univ ⊢F) (refl ⊢F) G≡G'


deep-correct : ∀ {Γ A B r} → Γ ⊢ A ^ r → Γ ⊢ A ⇒Π B ^ r → Γ ⊢ B ^ r × Γ ⊢ A ≡ B ^ r
deep-correct ⊢A (univ x) =
  let ⊢B , A≡B = deep-correct-term (un-univ ⊢A) x
  in univ ⊢B , univ A≡B

deep*-correct-term : ∀ {Γ t u T l} → Γ ⊢ t ∷ T ^ [ ! , l ] → Γ ⊢ t ⇒*Π u ∷ T ^ l → Γ ⊢ t ≡ u ∷ T ^ [ ! , l ]
deep*-correct-term ⊢t id = refl ⊢t
deep*-correct-term ⊢t (x ⇨ X) =
  let ⊢u , t≡u = deep-correct-term ⊢t x
  in trans t≡u (deep*-correct-term ⊢u X)

deep*-correct : ∀ {Γ A B r} → Γ ⊢ A ^ r → Γ ⊢ A ⇒*Π B ^ r → Γ ⊢ A ≡ B ^ r
deep*-correct ⊢A id = refl ⊢A
deep*-correct ⊢A (x ⇨ X) =
  let ⊢B , A≡B = deep-correct ⊢A x
  in trans A≡B (deep*-correct ⊢B X)

doΠNorm′ : ∀ {A rA Γ l} ([A] : Γ ⊩⟨ l ⟩ A ^ rA)
         → ∃ λ B → ΠNorm B × Γ ⊢ B ^ rA × Γ ⊢ A ⇒*Π B ^ rA
doΠNorm′ (Uᵣ (Uᵣ r l′ l< PE.refl [[ A , U , d ]])) = Univ r l′ , Uₙ , Ugenⱼ (wf A) , regular* d
doΠNorm′ (ℕᵣ [[ ⊢A , ⊢B , D ]]) = ℕ , ℕₙ , ⊢B , regular* D
doΠNorm′ (Emptyᵣ [[ ⊢A , ⊢B , D ]]) = sEmpty , Emptyₙ , ⊢B , regular* D
doΠNorm′ (ne′ K [[ ⊢A , ⊢B , D ]] neK K≡K) = K , ne neK , ⊢B , regular* D
doΠNorm′ (Πᵣ′ rF lF lG lF≤ lG≤ F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext) =
  let redF₀ , red₀ = reducibleTerm (var (wf ⊢G) here)
      [F]′ = irrelevanceTerm redF₀ ([F] (step id) (wf ⊢G)) red₀
      G′ , nG′ , ⊢G′ , D′ = PE.subst (λ G′ → ∃ λ B → ΠNorm B × _ ⊢ B ^ _ × _ ⊢ G′ ⇒*Π B ^ _)
                              (wkSingleSubstId _)
                              (doΠNorm′ ([G] (step id) (wf ⊢G) [F]′))
  in Π F ^ rF ° lF ▹ G′ ° lG ° _ ^ ! , Πₙ nG′ , univ (Πⱼ (λ x → lF≤ , lG≤) ▹ (λ abs → ⊥-elim (!≢% abs)) ▹ (un-univ ⊢F) ▹ (un-univ ⊢G′)) , regular* D ⇨* deep* D′
doΠNorm′ (∃ᵣ′ F G D ⊢F ⊢G A≡A) = ∃ F ▹ G , ∃ₙ , univ (∃ⱼ un-univ ⊢F ▹ un-univ ⊢G) , regular* (red D) 
doΠNorm′ (Πirrᵣ′ rF lF F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A) =
                 Π F ^ rF ° lF ▹ G ° ⁰ ° ⁰  ^ % , Πirrₙ , univ (Πⱼ (λ abs → ⊥-elim (!≢% (PE.sym abs))) ▹ (λ x → PE.refl , PE.refl) ▹ (un-univ ⊢F) ▹ (un-univ ⊢G)) , regular* D 
doΠNorm′ (emb emb< [A]) = doΠNorm′ [A]
doΠNorm′ (emb ∞< [A]) = doΠNorm′ [A]

doΠNorm : ∀ {A rA Γ} → Γ ⊢ A ^ rA
        → ∃ λ B → ΠNorm B × Γ ⊢ B ^ rA × Γ ⊢ A ⇒*Π B ^ rA
doΠNorm ⊢A = doΠNorm′ (reducible ⊢A)

ΠNorm-whnf : ∀ {A} → ΠNorm A → Whnf A
ΠNorm-whnf Uₙ = Uₙ
ΠNorm-whnf (Πₙ _) = Πₙ
ΠNorm-whnf Πirrₙ = Πₙ
ΠNorm-whnf ∃ₙ = ∃ₙ
ΠNorm-whnf ℕₙ = ℕₙ
ΠNorm-whnf Emptyₙ = Emptyₙ
ΠNorm-whnf (ne x) = ne x

ΠNorm-noredTerm : ∀ {Γ A B T l} → Γ ⊢ A ⇒Π B ∷ T ^ l → ΠNorm A → ⊥
ΠNorm-noredTerm (regular x) w = whnfRedTerm x (ΠNorm-whnf w)
ΠNorm-noredTerm (deepΠ x) (Πₙ w) = ΠNorm-noredTerm x w
--ΠNorm-noredTerm (deepΠ x) Πirrₙ = {!!}
ΠNorm-noredTerm (deepΠ x) (ne ())

ΠNorm-nored : ∀ {Γ A B r} → Γ ⊢ A ⇒Π B ^ r → ΠNorm A → ⊥
ΠNorm-nored (univ x) w = ΠNorm-noredTerm x w

detΠRedTerm : ∀ {Γ A B B′ T T′ r r'} → Γ ⊢ A ⇒Π B ∷ T ^ r  → Γ ⊢ A ⇒Π B′ ∷ T′ ^ r' → B PE.≡ B′
detΠRedTerm (regular x) (regular x₁) = whrDetTerm x x₁
detΠRedTerm (regular x) (deepΠ y) = ⊥-elim (whnfRedTerm x Πₙ)
detΠRedTerm (deepΠ x) (regular x₁) = ⊥-elim (whnfRedTerm x₁ Πₙ)
detΠRedTerm (deepΠ x) (deepΠ y) = PE.cong _ (detΠRedTerm x y)

detΠRed : ∀ {Γ A B B′ r r′} → Γ ⊢ A ⇒Π B ^ r → Γ ⊢ A ⇒Π B′ ^ r′ → B PE.≡ B′
detΠRed (univ x) (univ y) = detΠRedTerm x y

detΠNorm* : ∀ {Γ A B B′ r r′} → ΠNorm B → ΠNorm B′ → Γ ⊢ A ⇒*Π B ^ r → Γ ⊢ A ⇒*Π B′ ^ r′ → B PE.≡ B′
detΠNorm* w w′ id id = PE.refl
detΠNorm* w w′ id (x ⇨ b) = ⊥-elim (ΠNorm-nored x w)
detΠNorm* w w′ (x ⇨ a) id = ⊥-elim (ΠNorm-nored x w′)
detΠNorm* w w′ (x ⇨ a) (x₁ ⇨ b) =
  detΠNorm* w w′ a (PE.subst (λ t → _ ⊢ t ⇒*Π _ ^ _) (detΠRed x₁ x) b)


