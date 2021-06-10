{-# OPTIONS --without-K  #-}

module Definition.Typed.Consequences.Inversion where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties

open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Inversion of natural number type.
inversion-ℕ : ∀ {Γ C s} → Γ ⊢ ℕ ∷ C ⦂ s → Γ ⊢ C ≡ Univ 𝕥y ⦂ 𝕥y × s PE.≡ 𝕥y
inversion-ℕ (ℕⱼ x) = refl (Uⱼ x) , PE.refl
inversion-ℕ (conv x x₁) with inversion-ℕ x
... | [C≡U] , PE.refl = trans (sym x₁) [C≡U] , PE.refl

-- Inversion of Π-types.
inversion-Π : ∀ {F sF G s Γ C}
            → Γ ⊢ Π F ⦂ sF ▹ G ∷ C ⦂ s
            → ∃ λ sG
              → Γ ⊢ F ∷ Univ sF ⦂ 𝕥y
              × Γ ∙ F ⦂ sF ⊢ G ∷ Univ sG ⦂ 𝕥y
              × Γ ⊢ C ≡ Univ sG ⦂ 𝕥y
              × s PE.≡ 𝕥y
inversion-Π (Πⱼ_▹_ {sF = sF} {sG = sG} x x₁) = sG , x , x₁ , refl (Uⱼ (wfTerm x)) , PE.refl
inversion-Π (conv x x₁) = let sG , a , b , c , s≡𝕥y = inversion-Π x
                          in sG , a , b
                            , trans (sym (PE.subst (λ rx → _ ⊢ _ ≡ _ ⦂ sx) s≡𝕥y x₁)) c
                            , s≡𝕥y

inversion-Empty : ∀ {Γ C s} → Γ ⊢ Empty ∷ C ⦂ s → Γ ⊢ C ≡ Univ 𝕥y ⦂ 𝕥y × s PE.≡ 𝕥y
inversion-Empty (Emptyⱼ x) = refl (Uⱼ x) , PE.refl
inversion-Empty (conv x x₁) with inversion-Empty x
... | [C≡U] , PE.refl = trans (sym x₁) [C≡U] , PE.refl

-- Inversion of zero.
inversion-zero : ∀ {Γ C s} → Γ ⊢ zero ∷ C ⦂ s → Γ ⊢ C ≡ ℕ ⦂ 𝕥y × s PE.≡ 𝕥y
inversion-zero (zeroⱼ x) = refl (ℕⱼ x) , PE.refl
inversion-zero (conv x x₁) with inversion-zero x
... | [C≡ℕ] , PE.refl = trans (sym x₁) [C≡ℕ] , PE.refl

-- Inversion of successor.
inversion-suc : ∀ {Γ t C s} → Γ ⊢ suc t ∷ C ⦂ s → Γ ⊢ t ∷ ℕ ⦂ 𝕥y × Γ ⊢ C ≡ ℕ ⦂ 𝕥y × s PE.≡ 𝕥y
inversion-suc (sucⱼ x) = x , refl (ℕⱼ (wfTerm x)) , PE.refl
inversion-suc (conv x x₁) with inversion-suc x
... | a , b , PE.refl = a , trans (sym x₁) b , PE.refl

-- Inversion of natural recursion.
inversion-natrec : ∀ {Γ c g n A C sC} → Γ ⊢ natrec C c g n ∷ A ⦂ sC
  → (Γ ∙ ℕ ⦂ 𝕥y ⊢ C ⦂ sC)
  × Γ ⊢ c ∷ C [ zero ] ⦂ sC
  × Γ ⊢ g ∷ Π ℕ ⦂ 𝕥y ▹ (C ⦂ sC ▹▹ C [ suc (var 0) ]↑) ⦂ sC
  × Γ ⊢ n ∷ ℕ ⦂ 𝕥y
  × Γ ⊢ A ≡ C [ n ] ⦂ sC
inversion-natrec (natrecⱼ x d d₁ n) = x , d , d₁ , n , refl (substType x n)
inversion-natrec (conv d x) = let a , b , c , d , e = inversion-natrec d
                              in  a , b , c , d , trans (sym x) e

inversion-Emptyrec : ∀ {Γ e A C sC} → Γ ⊢ Emptyrec C e ∷ A ⦂ sC
  → Γ ⊢ C ⦂ sC
  × Γ ⊢ e ∷ Empty ⦂ 𝕥y
  × Γ ⊢ A ≡ C ⦂ sC
inversion-Emptyrec (Emptyrecⱼ [C] [e]) = [C] , [e] , refl [C]
inversion-Emptyrec (conv d x) = let a , b , c = inversion-Emptyrec d
                                in a , b , trans (sym x) c

-- Inversion of application.
inversion-app :  ∀ {Γ f a A s} → Γ ⊢ (f ∘ a) ∷ A ⦂ s →
  ∃₂ λ F sF → ∃ λ G → Γ ⊢ f ∷ Π F ⦂ sF ▹ G ⦂ s
  × Γ ⊢ a ∷ F ⦂ sF
  × Γ ⊢ A ≡ G [ a ] ⦂ s
inversion-app (d ∘ⱼ d₁) = _ , _ , _ , d , d₁ , refl (substTypeΠ (syntacticTerm d) d₁)
inversion-app (conv d x) = let a , b , c , d , e , f = inversion-app d
                           in  a , b , c , d , e , trans (sym x) f

-- Inversion of lambda.
inversion-lam : ∀ {t F A s Γ} → Γ ⊢ lam F ▹ t ∷ A ⦂ s →
  ∃ λ sF → ∃ λ G → Γ ⊢ F ⦂ sF
  × (Γ ∙ F ⦂ sF ⊢ t ∷ G ⦂ s
  × Γ ⊢ A ≡ Π F ⦂ sF ▹ G ⦂ s)
inversion-lam (lamⱼ x x₁) = _ , _ , x , x₁ , refl (Πⱼ x ▹ (syntacticTerm x₁))
inversion-lam (conv x x₁) = let a , b , c , d , e = inversion-lam x
                            in  a , b , c , d , trans (sym x₁) e
