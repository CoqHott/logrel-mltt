{-# OPTIONS --without-K --safe #-}

module Definition.Typed.Consequences.Inversion where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties

open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Inversion of natural number type.
inversion-ℕ : ∀ {Γ C r} → Γ ⊢ ℕ ∷ C ^ r → Γ ⊢ C ≡ Univ ! ^ ! × r PE.≡ !
inversion-ℕ (ℕⱼ x) = refl (Uⱼ x) , PE.refl
inversion-ℕ (conv x x₁) with inversion-ℕ x
... | [C≡U] , PE.refl = trans (sym x₁) [C≡U] , PE.refl

-- Inversion of Π-types.
inversion-Π : ∀ {F rF G r Γ C}
            → Γ ⊢ Π F ^ rF ▹ G ∷ C ^ r
            → ∃ λ rG
              → Γ ⊢ F ∷ Univ rF ^ !
              × Γ ∙ F ^ rF ⊢ G ∷ Univ rG ^ !
              × Γ ⊢ C ≡ Univ rG ^ !
              × r PE.≡ !
inversion-Π (Πⱼ_▹_ {rF = rF} {rG = rG} x x₁) = rG , x , x₁ , refl (Uⱼ (wfTerm x)) , PE.refl
inversion-Π (conv x x₁) = let rG , a , b , c , r≡! = inversion-Π x
                          in rG , a , b
                            , trans (sym (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ rx) r≡! x₁)) c
                            , r≡!

inversion-Empty : ∀ {Γ C r} → Γ ⊢ Empty ∷ C ^ r → Γ ⊢ C ≡ Univ % ^ ! × r PE.≡ !
inversion-Empty (Emptyⱼ x) = refl (Uⱼ x) , PE.refl
inversion-Empty (conv x x₁) with inversion-Empty x
... | [C≡U] , PE.refl = trans (sym x₁) [C≡U] , PE.refl

-- Inversion of zero.
inversion-zero : ∀ {Γ C r} → Γ ⊢ zero ∷ C ^ r → Γ ⊢ C ≡ ℕ ^ ! × r PE.≡ !
inversion-zero (zeroⱼ x) = refl (ℕⱼ x) , PE.refl
inversion-zero (conv x x₁) with inversion-zero x
... | [C≡ℕ] , PE.refl = trans (sym x₁) [C≡ℕ] , PE.refl

-- Inversion of successor.
inversion-suc : ∀ {Γ t C r} → Γ ⊢ suc t ∷ C ^ r → Γ ⊢ t ∷ ℕ ^ ! × Γ ⊢ C ≡ ℕ ^ ! × r PE.≡ !
inversion-suc (sucⱼ x) = x , refl (ℕⱼ (wfTerm x)) , PE.refl
inversion-suc (conv x x₁) with inversion-suc x
... | a , b , PE.refl = a , trans (sym x₁) b , PE.refl

-- Inversion of natural recursion.
inversion-natrec : ∀ {Γ c g n A C rC} → Γ ⊢ natrec C c g n ∷ A ^ rC
  → (Γ ∙ ℕ ^ ! ⊢ C ^ rC)
  × Γ ⊢ c ∷ C [ zero ] ^ rC
  × Γ ⊢ g ∷ Π ℕ ^ ! ▹ (C ^ rC ▹▹ C [ suc (var 0) ]↑) ^ rC
  × Γ ⊢ n ∷ ℕ ^ !
  × Γ ⊢ A ≡ C [ n ] ^ rC
inversion-natrec (natrecⱼ x d d₁ n) = x , d , d₁ , n , refl (substType x n)
inversion-natrec (conv d x) = let a , b , c , d , e = inversion-natrec d
                              in  a , b , c , d , trans (sym x) e

inversion-Emptyrec : ∀ {Γ e A C rC} → Γ ⊢ Emptyrec C e ∷ A ^ rC
  → Γ ⊢ C ^ rC
  × Γ ⊢ e ∷ Empty ^ %
  × Γ ⊢ A ≡ C ^ rC
inversion-Emptyrec (Emptyrecⱼ [C] [e]) = [C] , [e] , refl [C]
inversion-Emptyrec (conv d x) = let a , b , c = inversion-Emptyrec d
                                in a , b , trans (sym x) c

-- Inversion of application.
inversion-app :  ∀ {Γ f a A r} → Γ ⊢ (f ∘ a) ∷ A ^ r →
  ∃₂ λ F rF → ∃ λ G → Γ ⊢ f ∷ Π F ^ rF ▹ G ^ r
  × Γ ⊢ a ∷ F ^ rF
  × Γ ⊢ A ≡ G [ a ] ^ r
inversion-app (d ∘ⱼ d₁) = _ , _ , _ , d , d₁ , refl (substTypeΠ (syntacticTerm d) d₁)
inversion-app (conv d x) = let a , b , c , d , e , f = inversion-app d
                           in  a , b , c , d , e , trans (sym x) f

-- Inversion of lambda.
inversion-lam : ∀ {t F A r Γ} → Γ ⊢ lam F ▹ t ∷ A ^ r →
  ∃ λ rF → ∃ λ G → Γ ⊢ F ^ rF
  × (Γ ∙ F ^ rF ⊢ t ∷ G ^ r
  × Γ ⊢ A ≡ Π F ^ rF ▹ G ^ r)
inversion-lam (lamⱼ x x₁) = _ , _ , x , x₁ , refl (Πⱼ x ▹ (syntacticTerm x₁))
inversion-lam (conv x x₁) = let a , b , c , d , e = inversion-lam x
                            in  a , b , c , d , trans (sym x₁) e
