{-# OPTIONS --without-K  #-}

module Definition.Typed.RedSteps where

open import Definition.Untyped
open import Definition.Typed


-- Concatenation of type reduction closures
_⇨*_ : ∀ {Γ A B C s} → Γ ⊢ A ⇒* B ⦂ s → Γ ⊢ B ⇒* C ⦂ s → Γ ⊢ A ⇒* C ⦂ s
id ⊢B ⇨* B⇒C = B⇒C
(A⇒A′ ⇨ A′⇒B) ⇨* B⇒C = A⇒A′ ⇨ (A′⇒B ⇨* B⇒C)

-- Concatenation of term reduction closures
_⇨∷*_ : ∀ {Γ A t u v s} → Γ ⊢ t ⇒* u ∷ A ⦂ s → Γ ⊢ u ⇒* v ∷ A ⦂ s → Γ ⊢ t ⇒* v ∷ A ⦂ s
id ⊢u ⇨∷* u⇒v = u⇒v
(t⇒t′ ⇨ t′⇒u) ⇨∷* u⇒v = t⇒t′ ⇨ (t′⇒u ⇨∷* u⇒v)

-- Conversion of reduction closures
conv* : ∀ {Γ A B t u s} → Γ ⊢ t ⇒* u ∷ A ⦂ s → Γ ⊢ A ≡ B ⦂ s → Γ ⊢ t ⇒* u ∷ B ⦂ s
conv* (id x) A≡B = id (conv x A≡B)
conv* (x ⇨ d) A≡B = conv x A≡B ⇨ conv* d A≡B

-- Universe of reduction closures
univ* : ∀ {Γ A B s} → Γ ⊢ A ⇒* B ∷ (Univ s) ⦂ 𝕥y → Γ ⊢ A ⇒* B ⦂ s
univ* (id x) = id (univ x)
univ* (x ⇨ A⇒B) = univ x ⇨ univ* A⇒B

-- Application substitution of reduction closures
app-subst* : ∀ {Γ A B t t′ a sA sB} → Γ ⊢ t ⇒* t′ ∷ Π A ⦂ sA ▹ B ⦂ sB → Γ ⊢ a ∷ A ⦂ sA
           → Γ ⊢ t ∘ a ⇒* t′ ∘ a ∷ B [ a ] ⦂ sB
app-subst* (id x) a₁ = id (x ∘ⱼ a₁)
app-subst* (x ⇨ t⇒t′) a₁ = app-subst x a₁ ⇨ app-subst* t⇒t′ a₁
