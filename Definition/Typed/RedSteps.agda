{-# OPTIONS --safe #-}

module Definition.Typed.RedSteps where

open import Definition.Untyped
open import Definition.Typed
open import Tools.Empty using (⊥; ⊥-elim)
open import Tools.Product

-- Concatenation of type reduction closures
_⇨*_ : ∀ {Γ A B C r} → Γ ⊢ A ⇒* B ^ r → Γ ⊢ B ⇒* C ^ r → Γ ⊢ A ⇒* C ^ r
id ⊢B ⇨* B⇒C = B⇒C
(A⇒A′ ⇨ A′⇒B) ⇨* B⇒C = A⇒A′ ⇨ (A′⇒B ⇨* B⇒C)

-- Concatenation of term reduction closures
_⇨∷*_ : ∀ {Γ A t u v l} → Γ ⊢ t ⇒* u ∷ A ^ l → Γ ⊢ u ⇒* v ∷ A ^ l → Γ ⊢ t ⇒* v ∷ A ^ l
id ⊢u ⇨∷* u⇒v = u⇒v
(t⇒t′ ⇨ t′⇒u) ⇨∷* u⇒v = t⇒t′ ⇨ (t′⇒u ⇨∷* u⇒v)

-- Conversion of reduction closures
conv* : ∀ {Γ A B t u l } → Γ ⊢ t ⇒* u ∷ A ^ l → Γ ⊢ A ≡ B ^ [ ! , l ] → Γ ⊢ t ⇒* u ∷ B ^ l
conv* (id x) A≡B = id (conv x A≡B)
conv* (x ⇨ d) A≡B = conv x A≡B ⇨ conv* d A≡B

conv:* : ∀ {Γ A B t u l } → Γ ⊢ t :⇒*: u ∷ A ^ l → Γ ⊢ A ≡ B ^ [ ! , l ] → Γ ⊢ t :⇒*: u ∷ B ^ l
conv:* [[ ⊢t , ⊢u , d ]] e = [[ (conv ⊢t e) , (conv ⊢u e) , conv* d e ]]
