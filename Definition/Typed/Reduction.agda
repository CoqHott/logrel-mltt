{-# OPTIONS --without-K  #-}

module Definition.Typed.Reduction where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties


-- Weak head expansion of type equality
reduction : ∀ {A A′ B B′ s Γ}
          → Γ ⊢ A ⇒* A′ ⦂ s
          → Γ ⊢ B ⇒* B′ ⦂ s
          → Whnf A′
          → Whnf B′
          → Γ ⊢ A′ ≡ B′ ⦂ s
          → Γ ⊢ A ≡ B ⦂ s
reduction D D′ whnfA′ whnfB′ A′≡B′ =
  trans (subset* D) (trans A′≡B′ (sym (subset* D′)))

reduction′ : ∀ {A A′ B B′ s Γ}
          → Γ ⊢ A ⇒* A′ ⦂ s
          → Γ ⊢ B ⇒* B′ ⦂ s
          → Whnf A′
          → Whnf B′
          → Γ ⊢ A ≡ B ⦂ s
          → Γ ⊢ A′ ≡ B′ ⦂ s
reduction′ D D′ whnfA′ whnfB′ A≡B =
  trans (sym (subset* D)) (trans A≡B (subset* D′))

-- Weak head expansion of term equality
reductionₜ : ∀ {a a′ b b′ A B s Γ}
           → Γ ⊢ A ⇒* B ⦂ s
           → Γ ⊢ a ⇒* a′ ∷ B ⦂ s
           → Γ ⊢ b ⇒* b′ ∷ B ⦂ s
           → Whnf B
           → Whnf a′
           → Whnf b′
           → Γ ⊢ a′ ≡ b′ ∷ B ⦂ s
           → Γ ⊢ a ≡ b ∷ A ⦂ s
reductionₜ D d d′ whnfB whnfA′ whnfB′ a′≡b′ =
  conv (trans (subset*Term d)
              (trans a′≡b′ (sym (subset*Term d′))))
       (sym (subset* D))

reductionₜ′ : ∀ {a a′ b b′ A B s Γ}
           → Γ ⊢ A ⇒* B ⦂ s
           → Γ ⊢ a ⇒* a′ ∷ B ⦂ s
           → Γ ⊢ b ⇒* b′ ∷ B ⦂ s
           → Whnf B
           → Whnf a′
           → Whnf b′
           → Γ ⊢ a ≡ b ∷ A ⦂ s
           → Γ ⊢ a′ ≡ b′ ∷ B ⦂ s
reductionₜ′ D d d′ whnfB whnfA′ whnfB′ a≡b =
  trans (sym (subset*Term d))
        (trans (conv a≡b (subset* D)) (subset*Term d′))
