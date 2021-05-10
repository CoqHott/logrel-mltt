{-# OPTIONS --without-K --safe #-}

module Definition.Typed.RedSteps where

open import Definition.Untyped
open import Definition.Typed


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

-- Universe of reduction closures
univ* : ∀ {Γ A B r l} → Γ ⊢ A ⇒* B ∷ (Univ r l) ^ next l → Γ ⊢ A ⇒* B ^ [ r , ι l ]
univ* (id x) = id (univ x)
univ* (x ⇨ A⇒B) = univ x ⇨ univ* A⇒B

-- Application substitution of reduction closures
app-subst* : ∀ {Γ A B t t′ a rA lA lB l} → Γ ⊢ t ⇒* t′ ∷ Π A ^ rA ° lA ▹ B ° lB ^ l → Γ ⊢ a ∷ A ^ [ rA , ι lA ]
           → Γ ⊢ t ∘ a ⇒* t′ ∘ a ∷ B [ a ] ^ ι lB
app-subst* (id x) a₁ = id (x ∘ⱼ a₁)
app-subst* (x ⇨ t⇒t′) a₁ = app-subst x a₁ ⇨ app-subst* t⇒t′ a₁
