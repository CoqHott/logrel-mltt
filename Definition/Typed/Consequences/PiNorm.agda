{-# OPTIONS --without-K  #-}

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

-- there are 2 kinds of fat arrows𝕥y𝕥y𝕥y
-- the constructor for transitivity closure is closed on the left ⇨
-- the ones in types aren't ⇒

data ΠNorm : Term → Set where
  Uₙ : ∀ {s} → ΠNorm (Univ s)
  Πₙ : ∀ {A s B} → ΠNorm B → ΠNorm (Π A ⦂ s ▹ B)
  ℕₙ : ΠNorm ℕ
  Emptyₙ : ΠNorm Empty
  ne   : ∀ {n} → Neutral n → ΠNorm n

ΠNorm-Π : ∀ {A sA B} → ΠNorm (Π A ⦂ sA ▹ B) → ΠNorm B
ΠNorm-Π (Πₙ x) = x
ΠNorm-Π (ne ())

data _⊢_⇒Π_∷_⦂_ (Γ : Con Term) : Term → Term → Term → 𝕊 → Set where
  regular : ∀ {t u A s} → Γ ⊢ t ⇒ u ∷ A ⦂ s → Γ ⊢ t ⇒Π u ∷ A ⦂ s
  deep : ∀ {A sA B B′ sB}
       → Γ ∙ A ⦂ sA ⊢ B ⇒Π B′ ∷ Univ sB ⦂ 𝕥y
       → Γ ⊢ Π A ⦂ sA ▹ B ⇒Π Π A ⦂ sA ▹ B′ ∷ Univ sB ⦂ 𝕥y

data _⊢_⇒Π_⦂_ (Γ : Con Term) : Term → Term → 𝕊 → Set where
  univ : ∀ {A B s}
       → Γ ⊢ A ⇒Π B ∷ (Univ s) ⦂ 𝕥y
       → Γ ⊢ A ⇒Π B ⦂ s

data _⊢_⇒*Π_∷_⦂_ (Γ : Con Term) : Term → Term → Term → 𝕊 → Set where
  id : ∀ {t T s} → Γ ⊢ t ⇒*Π t ∷ T ⦂ s
  _⇨_ : ∀ {t t' u T s}
      → Γ ⊢ t  ⇒Π t' ∷ T ⦂ s
      → Γ ⊢ t' ⇒*Π u ∷ T ⦂ s
      → Γ ⊢ t  ⇒*Π u ∷ T ⦂ s

data _⊢_⇒*Π_⦂_ (Γ : Con Term) : Term → Term → 𝕊 → Set where
  id : ∀ {t s} → Γ ⊢ t ⇒*Π t ⦂ s
  _⇨_ : ∀ {t t' u s}
      → Γ ⊢ t  ⇒Π t' ⦂ s
      → Γ ⊢ t' ⇒*Π u ⦂ s
      → Γ ⊢ t  ⇒*Π u ⦂ s

deepstep : ∀ {Γ A B s} → Γ ⊢ A ⇒Π B ⦂ s → Γ ⊢ A ⇒*Π B ⦂ s
deepstep x = x ⇨ id

_⇨*_ : ∀ {Γ A B C s} → Γ ⊢ A ⇒*Π B ⦂ s → Γ ⊢ B ⇒*Π C ⦂ s → Γ ⊢ A ⇒*Π C ⦂ s
id ⇨* y = y
(x ⇨ x₁) ⇨* y = x ⇨ (x₁ ⇨* y)

regular* : ∀ {Γ t u s} → Γ ⊢ t ⇒* u ⦂ s → Γ ⊢ t ⇒*Π u ⦂ s
regular* (id x) = id
regular* (univ x ⇨ x₁) = univ (regular x) ⇨ regular* x₁

deep* : ∀ {Γ A sA B B′ sB}
      → Γ ∙ A ⦂ sA ⊢ B ⇒*Π B′ ⦂ sB
      → Γ ⊢ Π A ⦂ sA ▹ B ⇒*Π Π A ⦂ sA ▹ B′ ⦂ sB
deep* id = id
deep* (univ (regular x) ⇨ x₁) = univ (deep (regular x)) ⇨ deep* x₁
deep* (univ (deep x) ⇨ x₁) = univ (deep (deep x)) ⇨ deep* x₁

doΠNorm′ : ∀ {A sA Γ l} ([A] : Γ ⊩⟨ l ⟩ A ⦂ sA)
         → ∃ λ B → ΠNorm B × Γ ⊢ B ⦂ sA × Γ ⊢ A ⇒*Π B ⦂ sA
doΠNorm′ (Uᵣ′ sU .⁰ 0<1 ⊢Γ) = Univ sU , Uₙ , Uⱼ ⊢Γ , id
doΠNorm′ (ℕᵣ [ _ , ⊢B , D ]) = ℕ , ℕₙ , ⊢B , regular* D
doΠNorm′ (Emptyᵣ [ _ , ⊢B , D ]) = Empty , Emptyₙ , ⊢B , regular* D
doΠNorm′ (ne′ K [ _ , ⊢B , D ] neK K≡K) = K , ne neK , ⊢B , regular* D
doΠNorm′ (Πᵣ′ sF F G [ _ , ⊢B , D ] ⊢F ⊢G A≡A [F] [G] G-ext) =
  let redF₀ , red₀ = reducibleTerm (var (wf ⊢G) here)
      [F]′ = irrelevanceTerm redF₀ ([F] (step id) (wf ⊢G)) red₀
      G′ , nG′ , ⊢G′ , D′ = PE.subst (λ G′ → ∃ λ B → ΠNorm B × _ ⊢ B ⦂ _ × _ ⊢ G′ ⇒*Π B ⦂ _)
                              (wkSingleSubstId _)
                              (doΠNorm′ ([G] (step id) (wf ⊢G) [F]′))
  in Π F ⦂ sF ▹ G′ , Πₙ nG′ , Πⱼ ⊢F ▹ ⊢G′ , regular* D ⇨* deep* D′
doΠNorm′ (emb 0<1 [A]) = doΠNorm′ [A]

doΠNorm : ∀ {A sA Γ} → Γ ⊢ A ⦂ sA
        → ∃ λ B → ΠNorm B × Γ ⊢ B ⦂ sA × Γ ⊢ A ⇒*Π B ⦂ sA
doΠNorm ⊢A = doΠNorm′ (reducible ⊢A)

ΠNorm-whnf : ∀ {A} → ΠNorm A → Whnf A
ΠNorm-whnf Uₙ = Uₙ
ΠNorm-whnf (Πₙ x) = Πₙ
ΠNorm-whnf ℕₙ = ℕₙ
ΠNorm-whnf Emptyₙ = Emptyₙ
ΠNorm-whnf (ne x) = ne x

ΠNorm-noredTerm : ∀ {Γ A B T s} → Γ ⊢ A ⇒Π B ∷ T ⦂ s → ΠNorm A → ⊥
ΠNorm-noredTerm (regular x) w = whnfRedTerm x (ΠNorm-whnf w)
ΠNorm-noredTerm (deep x) (Πₙ w) = ΠNorm-noredTerm x w
ΠNorm-noredTerm (deep x) (ne ())

ΠNorm-nored : ∀ {Γ A B s} → Γ ⊢ A ⇒Π B ⦂ s → ΠNorm A → ⊥
ΠNorm-nored (univ x) w = ΠNorm-noredTerm x w

detΠRedTerm : ∀ {Γ A B B′ T T′ s s′} → Γ ⊢ A ⇒Π B ∷ T ⦂ s → Γ ⊢ A ⇒Π B′ ∷ T′ ⦂ s′ → B PE.≡ B′
detΠRedTerm (regular x) (regular x₁) = whrDetTerm x x₁
detΠRedTerm (regular x) (deep y) = ⊥-elim (whnfRedTerm x Πₙ)
detΠRedTerm (deep x) (regular x₁) = ⊥-elim (whnfRedTerm x₁ Πₙ)
detΠRedTerm (deep x) (deep y) = PE.cong _ (detΠRedTerm x y)

detΠRed : ∀ {Γ A B B′ s s′} → Γ ⊢ A ⇒Π B ⦂ s → Γ ⊢ A ⇒Π B′ ⦂ s′ → B PE.≡ B′
detΠRed (univ x) (univ y) = detΠRedTerm x y

detΠNorm* : ∀ {Γ A B B′ s s′} → ΠNorm B → ΠNorm B′ → Γ ⊢ A ⇒*Π B ⦂ s → Γ ⊢ A ⇒*Π B′ ⦂ s′ → B PE.≡ B′
detΠNorm* w w′ id id = PE.refl
detΠNorm* w w′ id (x ⇨ b) = ⊥-elim (ΠNorm-nored x w)
detΠNorm* w w′ (x ⇨ a) id = ⊥-elim (ΠNorm-nored x w′)
detΠNorm* w w′ (x ⇨ a) (x₁ ⇨ b) =
  detΠNorm* w w′ a (PE.subst (λ t → _ ⊢ t ⇒*Π _ ⦂ _) (detΠRed x₁ x) b)
