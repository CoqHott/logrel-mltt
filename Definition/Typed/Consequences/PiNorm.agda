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
open import Definition.Typed.Consequences.InverseUniv

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
  Πₙ : ∀ {F rF lF G lG lΠ} → ΠNorm G → ΠNorm (Π F ^ rF ° lF ▹ G ° lG ° lΠ)
  ∃ₙ : ∀ {F G} → ΠNorm (∃ F ▹ G)
  ℕₙ : ΠNorm ℕ
  Emptyₙ : ∀ {lEmpty} → ΠNorm (Empty lEmpty)
  ne   : ∀ {n} → Neutral n → ΠNorm n

ΠNorm-Π : ∀ {F rF lF G lG lΠ} → ΠNorm (Π F ^ rF ° lF ▹ G ° lG ° lΠ) → ΠNorm G
ΠNorm-Π (Πₙ x) = x
ΠNorm-Π (ne ())


data _⊢_⇒Π_∷_^_ (Γ : Con Term) : Term → Term → Term → TypeLevel → Set where
  regular : ∀ {t u A l} → Γ ⊢ t ⇒ u ∷ A ^ l → Γ ⊢ t ⇒Π u ∷ A ^ l
  deep : ∀ {F rF lF G G′ lG rG lΠ}
       → Γ ∙ F ^ [ rF , ι lF ] ⊢ G ⇒Π G′ ∷ Univ rG lG ^ next lG
       → Γ ⊢ Π F ^ rF ° lF ▹ G ° lG ° lΠ ⇒Π Π F ^ rF ° lF ▹ G′ ° lG ° lΠ ∷ Univ rG lΠ ^ next lΠ 

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
  id : ∀ {t r} → Γ ⊢ t ⇒*Π t ^ r
  _⇨_ : ∀ {t t' u r}
      → Γ ⊢ t  ⇒Π t' ^ r
      → Γ ⊢ t' ⇒*Π u ^ r
      → Γ ⊢ t  ⇒*Π u ^ r


deepstep : ∀ {Γ A B r} → Γ ⊢ A ⇒Π B ^ r → Γ ⊢ A ⇒*Π B ^ r
deepstep x = x ⇨ id

_⇨*_ : ∀ {Γ A B C r} → Γ ⊢ A ⇒*Π B ^ r → Γ ⊢ B ⇒*Π C ^ r → Γ ⊢ A ⇒*Π C ^ r
id ⇨* y = y
(x ⇨ x₁) ⇨* y = x ⇨ (x₁ ⇨* y)

regular* : ∀ {Γ t u r} → Γ ⊢ t ⇒* u ^ r → Γ ⊢ t ⇒*Π u ^ r
regular* (id x) = id
regular* (univ x ⇨ x₁) = univ (regular x) ⇨ regular* x₁

deep* : ∀ {Γ F rF lF G G′ lG rG lΠ}
      → Γ ∙ F ^ [ rF , ι lF ] ⊢ G ⇒*Π G′ ^ [ rG , ι lG ]
      → Γ ⊢ Π F ^ rF ° lF ▹ G ° lG ° lΠ ⇒*Π Π F ^ rF ° lF ▹ G′ ° lG ° lΠ ^ [ rG , ι lΠ ]
deep* id = id
deep* (univ (regular x) ⇨ x₁) = univ (deep (regular x)) ⇨ deep* x₁
deep* (univ (deep x) ⇨ x₁) = univ (deep (deep x)) ⇨ deep* x₁

doΠNorm′ : ∀ {A rA Γ l} ([A] : Γ ⊩⟨ l ⟩ A ^ rA)
         → ∃ λ B → ΠNorm B × Γ ⊢ B ^ rA × Γ ⊢ A ⇒*Π B ^ rA
doΠNorm′ (Uᵣ (Uᵣ r l′ l< PE.refl [[ A , U , d ]])) = Univ r l′ , Uₙ , Ugenⱼ (wf A) , regular* d
doΠNorm′ (ℕᵣ [[ ⊢A , ⊢B , D ]]) = ℕ , ℕₙ , ⊢B , regular* D
doΠNorm′ (Emptyᵣ {l = l} [[ ⊢A , ⊢B , D ]]) = Empty l , Emptyₙ , ⊢B , regular* D
doΠNorm′ (ne′ K [[ ⊢A , ⊢B , D ]] neK K≡K) = K , ne neK , ⊢B , regular* D
doΠNorm′ (Πᵣ′ rF lF lG lF≤ lG≤ F G [[ ⊢A , ⊢B , D ]] ⊢F ⊢G A≡A [F] [G] G-ext) =
  let redF₀ , red₀ = reducibleTerm (var (wf ⊢G) here)
      [F]′ = irrelevanceTerm redF₀ ([F] (step id) (wf ⊢G)) red₀
      G′ , nG′ , ⊢G′ , D′ = PE.subst (λ G′ → ∃ λ B → ΠNorm B × _ ⊢ B ^ _ × _ ⊢ G′ ⇒*Π B ^ _)
                              (wkSingleSubstId _)
                              (doΠNorm′ ([G] (step id) (wf ⊢G) [F]′))
  in Π F ^ rF ° lF ▹ G′ ° lG ° _ , Πₙ nG′ , univ (Πⱼ lF≤ ▹ lG≤ ▹ (un-univ ⊢F) ▹ (un-univ ⊢G′)) , regular* D ⇨* deep* D′
doΠNorm′ (∃ᵣ′ F G D ⊢F ⊢G A≡A [F] [G] G-ext) = ∃ F ▹ G , ∃ₙ , univ (∃ⱼ un-univ ⊢F ▹ un-univ ⊢G) , regular* (red D)
doΠNorm′ (emb emb< [A]) = doΠNorm′ [A]
doΠNorm′ (emb ∞< [A]) = doΠNorm′ [A]

doΠNorm : ∀ {A rA Γ} → Γ ⊢ A ^ rA
        → ∃ λ B → ΠNorm B × Γ ⊢ B ^ rA × Γ ⊢ A ⇒*Π B ^ rA
doΠNorm ⊢A = doΠNorm′ (reducible ⊢A)


ΠNorm-whnf : ∀ {A} → ΠNorm A → Whnf A
ΠNorm-whnf Uₙ = Uₙ
ΠNorm-whnf (Πₙ x) = Πₙ
ΠNorm-whnf ∃ₙ = ∃ₙ
ΠNorm-whnf ℕₙ = ℕₙ
ΠNorm-whnf Emptyₙ = Emptyₙ
ΠNorm-whnf (ne x) = ne x

ΠNorm-noredTerm : ∀ {Γ A B T r} → Γ ⊢ A ⇒Π B ∷ T ^ r  → ΠNorm A → ⊥
ΠNorm-noredTerm (regular x) w = whnfRedTerm x (ΠNorm-whnf w)
ΠNorm-noredTerm (deep x) (Πₙ w) = ΠNorm-noredTerm x w
ΠNorm-noredTerm (deep x) (ne ())



ΠNorm-nored : ∀ {Γ A B r} → Γ ⊢ A ⇒Π B ^ r → ΠNorm A → ⊥
ΠNorm-nored (univ x) w = ΠNorm-noredTerm x w

detΠRedTerm : ∀ {Γ A B B′ T T′ r r'} → Γ ⊢ A ⇒Π B ∷ T ^ r  → Γ ⊢ A ⇒Π B′ ∷ T′ ^ r' → B PE.≡ B′
detΠRedTerm (regular x) (regular x₁) = whrDetTerm x x₁
detΠRedTerm (regular x) (deep y) = ⊥-elim (whnfRedTerm x Πₙ)
detΠRedTerm (deep x) (regular x₁) = ⊥-elim (whnfRedTerm x₁ Πₙ)
detΠRedTerm (deep x) (deep y) = PE.cong _ (detΠRedTerm x y)

detΠRed : ∀ {Γ A B B′ r r′} → Γ ⊢ A ⇒Π B ^ r → Γ ⊢ A ⇒Π B′ ^ r′ → B PE.≡ B′
detΠRed (univ x) (univ y) = detΠRedTerm x y

detΠNorm* : ∀ {Γ A B B′ r r′} → ΠNorm B → ΠNorm B′ → Γ ⊢ A ⇒*Π B ^ r → Γ ⊢ A ⇒*Π B′ ^ r′ → B PE.≡ B′
detΠNorm* w w′ id id = PE.refl
detΠNorm* w w′ id (x ⇨ b) = ⊥-elim (ΠNorm-nored x w)
detΠNorm* w w′ (x ⇨ a) id = ⊥-elim (ΠNorm-nored x w′)
detΠNorm* w w′ (x ⇨ a) (x₁ ⇨ b) =
  detΠNorm* w w′ a (PE.subst (λ t → _ ⊢ t ⇒*Π _ ^ _) (detΠRed x₁ x) b)
