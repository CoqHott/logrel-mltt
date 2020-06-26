{-# OPTIONS --without-K --safe #-}

module Definition.Typed.Reduction where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties


-- Weak head expansion of type equality
reduction : ∀ {A A′ B B′ r Γ}
          → Γ ⊢ A ⇒* A′ ^ r
          → Γ ⊢ B ⇒* B′ ^ r
          → whNf A′
          → whNf B′
          → Γ ⊢ A′ ≡ B′ ^ r
          → Γ ⊢ A ≡ B ^ r
reduction D D′ whnfA′ whnfB′ A′≡B′ =
  trans (subset* D) (trans A′≡B′ (sym (subset* D′)))

reduction′ : ∀ {A A′ B B′ r Γ}
          → Γ ⊢ A ⇒* A′ ^ r
          → Γ ⊢ B ⇒* B′ ^ r
          → whNf A′
          → whNf B′
          → Γ ⊢ A ≡ B ^ r
          → Γ ⊢ A′ ≡ B′ ^ r
reduction′ D D′ whnfA′ whnfB′ A≡B =
  trans (sym (subset* D)) (trans A≡B (subset* D′))

-- Weak head expansion of term equality
reductionₜ : ∀ {a a′ b b′ A B r Γ}
           → Γ ⊢ A ⇒* B ^ r
           → Γ ⊢ a ⇒* a′ ∷ B ^ r
           → Γ ⊢ b ⇒* b′ ∷ B ^ r
           → whNf B
           → whNf a′
           → whNf b′
           → Γ ⊢ a′ ≡ b′ ∷ B ^ r
           → Γ ⊢ a ≡ b ∷ A ^ r
reductionₜ D d d′ whnfB whnfA′ whnfB′ a′≡b′ =
  conv (trans (subset*Term d)
              (trans a′≡b′ (sym (subset*Term d′))))
       (sym (subset* D))

reductionₜ′ : ∀ {a a′ b b′ A B r Γ}
           → Γ ⊢ A ⇒* B ^ r
           → Γ ⊢ a ⇒* a′ ∷ B ^ r
           → Γ ⊢ b ⇒* b′ ∷ B ^ r
           → whNf B
           → whNf a′
           → whNf b′
           → Γ ⊢ a ≡ b ∷ A ^ r
           → Γ ⊢ a′ ≡ b′ ∷ B ^ r
reductionₜ′ D d d′ whnfB whnfA′ whnfB′ a≡b =
  trans (sym (subset*Term d))
        (trans (conv a≡b (subset* D)) (subset*Term d′))
