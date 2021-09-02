{-# OPTIONS --safe #-}

module Definition.Typed.Consequences.Inversion where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties

open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Inversion of natural number type.
inversion-U : ∀ {Γ C rU lU r} → Γ ⊢ Univ rU lU ∷ C ^ r → Γ ⊢ C ≡ U ¹ ^ [ ! , next ¹ ] × r PE.≡ [ ! , next ¹ ] × lU PE.≡ ⁰
inversion-U (univ 0<1 x) = refl (Ugenⱼ x) , PE.refl , PE.refl
inversion-U (conv x x₁) with inversion-U x
... | [C≡U] , PE.refl , PE.refl  = trans (sym x₁) [C≡U] , PE.refl , PE.refl


-- Inversion of natural number type.
inversion-ℕ : ∀ {Γ C r} → Γ ⊢ ℕ ∷ C ^ r → Γ ⊢ C ≡ U ⁰ ^ r × r PE.≡ [ ! , next ⁰ ]
inversion-ℕ (ℕⱼ x) = refl (Ugenⱼ x) , PE.refl
inversion-ℕ (conv x x₁) with inversion-ℕ x
... | [C≡U] , PE.refl = trans (sym x₁) [C≡U] , PE.refl

-- Inversion of Π-types.
inversion-Π : ∀ {F rF G r Γ C lF lG lΠ}
            → Γ ⊢ Π F ^ rF ° lF ▹ G ° lG ° lΠ  ∷ C ^ r
            → ∃ λ rG
            → lF ≤ lΠ
              × lG ≤ lΠ
              × Γ ⊢ F ∷ Univ rF lF ^ [ ! , next lF ]
              × Γ ∙ F ^ [ rF , ι lF ] ⊢ G ∷ Univ rG lG ^ [ ! , next lG ]
              × Γ ⊢ C ≡ Univ rG lΠ ^ [ ! , next lΠ ]
              × r PE.≡ [ ! , next lΠ ]
inversion-Π (Πⱼ_▹_▹_▹_ {rF = rF} {r = rG} l< l<' x x₁) = rG , l< , l<' , x , x₁ , refl (Ugenⱼ (wfTerm x)) , PE.refl
inversion-Π (conv x x₁) = let rG , l< , l<' , a , b , c , r≡! = inversion-Π x
                          in rG , l< , l<' , a , b
                            , trans (sym (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ rx) r≡! x₁)) c
                            , r≡!

-- Inversion of Π-types.
inversion-∃ : ∀ {F G Γ C  r}
            → Γ ⊢ ∃ F ▹ G ∷ C ^ r
            → ∃ λ l∃
              → Γ ⊢ F ∷ Univ % l∃ ^ [ ! , next l∃ ]
              × Γ ∙ F ^ [ % , ι l∃ ] ⊢ G ∷ Univ % l∃ ^ [ ! , next l∃ ]
              × Γ ⊢ C ≡ Univ % l∃ ^ [ ! , next l∃ ]
              × r PE.≡ [ ! , next l∃ ]
inversion-∃ (∃ⱼ_▹_ {l = l∃} x x₁) = l∃ , x , x₁ , refl (Ugenⱼ (wfTerm x)) , PE.refl
inversion-∃ (conv x x₁) = let l∃ , a , b , c , r≡! = inversion-∃ x
                          in l∃ , a , b , trans (sym (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ rx) r≡! x₁)) c , r≡!
                            
inversion-Empty : ∀ {Γ C r l} → Γ ⊢ Empty l ∷ C ^ r → Γ ⊢ C ≡ SProp l ^ r × r PE.≡ [ ! , next l ]
inversion-Empty (Emptyⱼ x) = refl (Ugenⱼ x) , PE.refl
inversion-Empty (conv x x₁) =
  let C≡SProp , r = inversion-Empty x
  in trans (sym x₁) C≡SProp , r 

-- Inversion of zero.
inversion-zero : ∀ {Γ C r} → Γ ⊢ zero ∷ C ^ r → Γ ⊢ C ≡ ℕ ^ [ ! , ι ⁰ ] × r PE.≡ [ ! , ι ⁰ ]
inversion-zero (zeroⱼ x) = univ (refl (ℕⱼ x)) , PE.refl
inversion-zero (conv x x₁) with inversion-zero x
... | [C≡ℕ] , PE.refl = trans (sym x₁) [C≡ℕ] , PE.refl

-- Inversion of successor.
inversion-suc : ∀ {Γ t C r} → Γ ⊢ suc t ∷ C ^ r → Γ ⊢ t ∷ ℕ ^ [ ! , ι ⁰ ] × Γ ⊢ C ≡ ℕ ^ [ ! , ι ⁰ ] × r PE.≡ [ ! , ι ⁰ ]
inversion-suc (sucⱼ x) = x , refl (univ (ℕⱼ (wfTerm x))) , PE.refl
inversion-suc (conv x x₁) with inversion-suc x
... | a , b , PE.refl = a , trans (sym x₁) b , PE.refl

-- Inversion of natural recursion.
inversion-natrec : ∀ {Γ c g n A C rlC lC} → Γ ⊢ natrec lC C c g n ∷ A ^ rlC
  →  ∃ λ rC → (Γ ∙ ℕ ^ [ ! , ι ⁰ ]) ⊢ C ^ [ rC , ι lC ]
  × Γ ⊢ c ∷ C [ zero ] ^ [ rC , ι lC ]
  × Γ ⊢ g ∷ Π ℕ ^ ! ° ⁰ ▹ (C ^ rC ° lC ▹▹ C [ suc (var 0) ]↑ ° lC ° lC) ° lC ° lC ^ [ rC , ι lC ]
  × Γ ⊢ n ∷ ℕ ^ [ ! , ι ⁰ ]
  × Γ ⊢ A ≡ C [ n ] ^ [ rC , ι lC ]
  × rlC PE.≡ [ rC , ι lC ]
inversion-natrec (natrecⱼ x d d₁ n) = _ , x , d , d₁ , n , refl (substType x n) , PE.refl
inversion-natrec (conv d x) = let a' , a , b , c , d , e , e' = inversion-natrec d
                              in  a' , a , b , c , d , trans (sym (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ rx) e' x)) e , e'

inversion-Emptyrec : ∀ {Γ e A C rC lC} → Γ ⊢ Emptyrec lC C e ∷ A ^ [ rC , ι lC ]
  → ∃ λ lEmpty → Γ ⊢ C ^ [ rC , ι lC ]
  × Γ ⊢ e ∷ Empty lEmpty ^ [ % , ι lEmpty ]
  × Γ ⊢ A ≡ C ^ [ rC , ι lC ]
inversion-Emptyrec (Emptyrecⱼ {l = lEmpty} [C] [e]) = lEmpty , [C] , [e] , refl [C]
inversion-Emptyrec (conv d x) = let lEmpty , a , b , c = inversion-Emptyrec d
                                in lEmpty , a , b , trans (sym x) c

-- Inversion of application.
inversion-app :  ∀ {Γ f a A r lΠ} → Γ ⊢ (f ∘ a ^ lΠ) ∷ A ^ r →
  ∃₂ λ F rF → ∃₂ λ lF G → ∃₂ λ lG rG → Γ ⊢ f ∷ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ [ rG , ι lΠ ]
  × Γ ⊢ a ∷ F ^ [ rF , ι lF ]
  × Γ ⊢ A ≡ G [ a ] ^ [ rG , ι lG ]
  × r PE.≡ [ rG , ι lG ]
inversion-app (d ∘ⱼ d₁) = _ , _ , _ , _ , _ , _ , d , d₁ , refl (substTypeΠ (syntacticTerm d) d₁) , PE.refl
inversion-app (conv d x) = let a , b , c , d , e , f , g , h , i , j = inversion-app d
                           in  a , b , c , d , e , f , g , h , trans (sym (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ rx) j x)) i , j


-- Inversion of lambda.
inversion-lam : ∀ {t F A r lΠ Γ} → Γ ⊢ lam F ▹ t ^ lΠ ∷ A ^ r →
  ∃₂ λ rF lF → ∃₂ λ G rG → ∃ λ lG → Γ ⊢ F ^ [ rF , ι lF ]
  × Γ ∙ F ^ [ rF , ι lF ] ⊢ t ∷ G ^ [ rG , ι lG ]
  × Γ ⊢ A ≡ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ [ rG , ι lΠ ]
  × r PE.≡ [ rG , ι lΠ ]
inversion-lam (lamⱼ l< l<' x x₁) = _ , _ , _ , _ , _ , x , x₁ ,
                                   refl (univ (Πⱼ l< ▹ l<' ▹ (un-univ x) ▹ un-univ (syntacticTerm x₁))) , PE.refl
inversion-lam (conv x x₁) = let a , b , c , d , e , f , g , h , i = inversion-lam x
                            in  a , b , c , d , e , f , g , trans (sym (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ rx) i x₁)) h , i
