{-# OPTIONS --without-K --safe #-}

module Definition.Typed.RedSteps where

open import Definition.Untyped
open import Definition.Typed


-- Concatenation of type reduction closures
_⇨*_ : ∀ {Γ A B C r} → Γ ⊢ A ⇒* B ^ r → Γ ⊢ B ⇒* C ^ r → Γ ⊢ A ⇒* C ^ r
id ⊢B ⇨* B⇒C = B⇒C
(A⇒A′ ⇨ A′⇒B) ⇨* B⇒C = A⇒A′ ⇨ (A′⇒B ⇨* B⇒C)

-- Concatenation of term reduction closures
_⇨∷*_ : ∀ {Γ A t u v} → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ u ⇒* v ∷ A → Γ ⊢ t ⇒* v ∷ A
id ⊢u ⇨∷* u⇒v = u⇒v
(t⇒t′ ⇨ t′⇒u) ⇨∷* u⇒v = t⇒t′ ⇨ (t′⇒u ⇨∷* u⇒v)

-- Conversion of reduction closures
conv* : ∀ {Γ A B t u} → Γ ⊢ t ⇒* u ∷ A → Γ ⊢ A ≡ B ^ ! → Γ ⊢ t ⇒* u ∷ B 
conv* (id x) A≡B = id (conv x A≡B)
conv* (x ⇨ d) A≡B = conv x A≡B ⇨ conv* d A≡B

-- Universe of reduction closures
univ* : ∀ {Γ A B r l} → Γ ⊢ A ⇒* B ∷ (Univ r l) → Γ ⊢ A ⇒* B ^ r
univ* (id x) = id (univ x)
univ* (x ⇨ A⇒B) = univ x ⇨ univ* A⇒B

-- Application substitution of reduction closures
app-subst* : ∀ {Γ A B t t′ a rA} → Γ ⊢ t ⇒* t′ ∷ Π A ^ rA ▹ B → Γ ⊢ a ∷ A ^ rA
           → Γ ⊢ t ∘ a ⇒* t′ ∘ a ∷ B [ a ] 
app-subst* (id x) a₁ = id (x ∘ⱼ a₁)
app-subst* (x ⇨ t⇒t′) a₁ = app-subst x a₁ ⇨ app-subst* t⇒t′ a₁
