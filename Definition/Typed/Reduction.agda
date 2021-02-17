{-# OPTIONS  --safe #-}

module Definition.Typed.Reduction where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties


-- Weak head expansion of type equality
reduction : ∀ {A A′ B B′ r Γ}
          → Γ ⊢ A ⇒* A′ ^ r
          → Γ ⊢ B ⇒* B′ ^ r
          → Whnf A′
          → Whnf B′
          → Γ ⊢ A′ ≡ B′ ^ r
          → Γ ⊢ A ≡ B ^ r
reduction D D′ whnfA′ whnfB′ A′≡B′ =
  trans (subset* D) (trans A′≡B′ (sym (subset* D′)))

reduction′ : ∀ {A A′ B B′ r Γ}
          → Γ ⊢ A ⇒* A′ ^ r
          → Γ ⊢ B ⇒* B′ ^ r
          → Whnf A′
          → Whnf B′
          → Γ ⊢ A ≡ B ^ r
          → Γ ⊢ A′ ≡ B′ ^ r
reduction′ D D′ whnfA′ whnfB′ A≡B =
  trans (sym (subset* D)) (trans A≡B (subset* D′))

-- Weak head expansion of term equality
reductionₜ : ∀ {a a′ b b′ A B l Γ}
           → Γ ⊢ A ⇒* B ^ [ ! , l ]
           → Γ ⊢ a ⇒* a′ ∷ B ^ l
           → Γ ⊢ b ⇒* b′ ∷ B ^ l
           → Whnf B
           → Whnf a′
           → Whnf b′
           → Γ ⊢ a′ ≡ b′ ∷ B ^ [ ! , l ]
           → Γ ⊢ a ≡ b ∷ A ^ [ ! , l ]
reductionₜ D d d′ whnfB whnfA′ whnfB′ a′≡b′ =
  conv (trans (subset*Term d)
              (trans a′≡b′ (sym (subset*Term d′))))
       (sym (subset* D))

reductionₜ′ : ∀ {a a′ b b′ A B l Γ}
           → Γ ⊢ A ⇒* B ^ [ ! , l ]
           → Γ ⊢ a ⇒* a′ ∷ B ^ l
           → Γ ⊢ b ⇒* b′ ∷ B ^ l
           → Whnf B
           → Whnf a′
           → Whnf b′
           → Γ ⊢ a ≡ b ∷ A ^ [ ! , l ]
           → Γ ⊢ a′ ≡ b′ ∷ B ^ [ ! , l ]
reductionₜ′ D d d′ whnfB whnfA′ whnfB′ a≡b =
  trans (sym (subset*Term d))
        (trans (conv a≡b (subset* D)) (subset*Term d′))
