{-# OPTIONS --safe #-}

module Definition.Typed.Consequences.Inversion where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.EqRelInstance

open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Fundamental.Reducibility

open import Tools.Product
import Tools.PropositionalEquality as PE


abstract 

  -- Inversion of contexts
  inversion-ctx : ∀ {Γ A r} → ⊢ Γ ∙ A ^ r → ⊢ Γ  × Γ ⊢ A ^ r
  inversion-ctx (X ∙ x) = X , x

  -- Inversion of Universes
  inversion-U : ∀ {Γ C rU lU r} → Γ ⊢ Univ rU lU ∷ C ^ r → Γ ⊢ C ≡ U ¹ ^ [ ! , next ¹ ] × r PE.≡ [ ! , next ¹ ] × lU PE.≡ ⁰
  inversion-U (univ 0<1 x) = refl (Ugenⱼ x) , PE.refl , PE.refl
  inversion-U (conv x x₁) with inversion-U x
  ... | [C≡U] , PE.refl , PE.refl  = trans (sym x₁) [C≡U] , PE.refl , PE.refl

  typeinfo-PE-injectivity : ∀ {r r' l l'} → [ r , l ] PE.≡ [ r' , l' ] → r PE.≡ r' × l PE.≡ l'
  typeinfo-PE-injectivity PE.refl = PE.refl , PE.refl


  -- Inversion of contexts

  inversion-ne' : ∀ {Γ t A ll l} → Neutral A
                  → ([A] : Γ ⊩⟨ l ⟩ A ^ [ ! , ll ])
                  → Γ ⊩⟨ l ⟩ t ∷ A ^ [ ! , ll ] / [A]
                  → Whnf t → Neutral t
  inversion-ne' neA (Uᵣ (Uᵣ r l′ l< eq d)) [t] whnft with whnfRed* (red d) (ne neA) 
  inversion-ne' () (Uᵣ (Uᵣ r l′ l< eq d)) [t] whnft | PE.refl 
  inversion-ne' neA (ℕᵣ d) [t] whnft with whnfRed* (red d) (ne neA) 
  inversion-ne' () (ℕᵣ d) [t] whnft | PE.refl
  inversion-ne' neA (ne′ K D neK K≡K) (neₜ k d (neNfₜ neK₁ ⊢k k≡k)) whnft =
    let eq = whnfRed*Term (redₜ d) whnft
    in PE.subst Neutral (PE.sym eq) neK₁  
  inversion-ne' neA (Πᵣ′ rF lF lG l≤F l≤G F G D ⊢F ⊢G A≡A [F] [G] G-ext) [t] whnft with whnfRed* (red D) (ne neA) 
  inversion-ne' () (Πᵣ′ rF lF lG l≤F l≤G F G D ⊢F ⊢G A≡A [F] [G] G-ext) [t] whnft | PE.refl
  inversion-ne' neA (emb emb< [A]) [t] whnft = inversion-ne' neA [A] [t] whnft
  inversion-ne' neA (emb ∞< [A]) [t] whnft = inversion-ne' neA [A] [t] whnft
  
  inversion-ne : ∀ {Γ t A l} → Neutral A → Whnf t → Γ ⊢ t ∷ A ^ [ ! , l ] → Neutral t
  inversion-ne neA whnft ⊢t =  let [A] , [t] = reducibleTerm ⊢t in inversion-ne' neA [A] [t] whnft

  
  -- Inversion of natural number type.
  inversion-ℕ : ∀ {Γ C r} → Γ ⊢ ℕ ∷ C ^ r → Γ ⊢ C ≡ U ⁰ ^ r × r PE.≡ [ ! , next ⁰ ]
  inversion-ℕ (ℕⱼ x) = refl (Ugenⱼ x) , PE.refl
  inversion-ℕ (conv x x₁) with inversion-ℕ x
  ... | [C≡U] , PE.refl = trans (sym x₁) [C≡U] , PE.refl
  
  -- Inversion of Π-types.
  inversion-Π : ∀ {F rF G r rΠ Γ C lF lG lΠ}
              → Γ ⊢ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ rΠ ∷ C ^ r
              → ∃ λ rG
              → (rG PE.≡ ! → lF ≤ lΠ × lG ≤ lΠ)
                  × (rG PE.≡ % → lG PE.≡ ⁰ × lΠ PE.≡ ⁰)
                × Γ ⊢ F ∷ Univ rF lF ^ [ ! , next lF ]
                × Γ ∙ F ^ [ rF , ι lF ] ⊢ G ∷ Univ rG lG ^ [ ! , next lG ]
                × Γ ⊢ C ≡ Univ rG lΠ ^ [ ! , next lΠ ]
                × rG PE.≡ rΠ
                × r PE.≡ [ ! , next lΠ ]
  inversion-Π (Πⱼ_▹_▹_▹_ {rF = rF} {r = rG} l! l% x x₁) = rG , l! , l% , x , x₁ , refl (Ugenⱼ (wfTerm x)) , PE.refl , PE.refl
  inversion-Π (conv x x₁) = let rG , l< , l<' , a , b , c , rG≡ , r≡! = inversion-Π x
                            in rG , l< , l<' , a , b
                              , trans (sym (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ rx) r≡! x₁)) c , rG≡
                              , r≡!
  
  inversion-Empty : ∀ {Γ C r l} → Γ ⊢ Empty l ∷ C ^ r → Γ ⊢ C ≡ SProp ^ r × r PE.≡ [ ! , next ⁰ ]
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
    →  ∃ λ rC →
      (rC PE.≡ % → lC PE.≡ ⁰)
    × (Γ ∙ ℕ ^ [ ! , ι ⁰ ]) ⊢ C ^ [ rC , ι lC ]
    × Γ ⊢ c ∷ C [ zero ] ^ [ rC , ι lC ]
    × Γ ⊢ g ∷ Π ℕ ^ ! ° ⁰ ▹ (C ^ rC ° lC ▹▹ C [ suc (var 0) ]↑ ° lC ° lC ^ rC) ° lC ° lC ^ rC ^ [ rC , ι lC ]
    × Γ ⊢ n ∷ ℕ ^ [ ! , ι ⁰ ]
    × Γ ⊢ A ≡ C [ n ] ^ [ rC , ι lC ]
    × rlC PE.≡ [ rC , ι lC ]
  inversion-natrec (natrecⱼ r% x d d₁ n) = _ , r% , x , d , d₁ , n , refl (substType x n) , PE.refl
  inversion-natrec (conv d x) = let r% , a' , a , b , c , d , e , e' = inversion-natrec d
                                in  r% , a' , a , b , c , d , trans (sym (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ rx) e' x)) e , e'
  
  inversion-Emptyrec : ∀ {Γ e A C rlC lEmpty lC} → Γ ⊢ Emptyrec lC lEmpty C e ∷ A ^ rlC
    → ∃ λ rC → Γ ⊢ C ^ [ rC , ι lC ]
    × Γ ⊢ e ∷ Empty lEmpty ^ [ % , ι lEmpty ]
    × Γ ⊢ A ≡ C ^ [ rC , ι lC ]
    × rlC PE.≡ [ rC , ι lC ]
  inversion-Emptyrec (Emptyrecⱼ [C] [e]) = _ , [C] , [e] , refl [C] , PE.refl
  inversion-Emptyrec (conv d x) = let r , a , b , c , e = inversion-Emptyrec d
                                  in r , a , b , trans (sym (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ rx) e x)) c , e
  
  -- Inversion of application.
  inversion-app :  ∀ {Γ f a A l lΠ} → Γ ⊢ (f ∘ a ^ lΠ) ∷ A ^ [ ! , l ] →
    ∃₂ λ F rF → ∃₂ λ lF G → ∃ λ lG → Γ ⊢ f ∷ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ ! ^ [ ! , ι lΠ ]
    × Γ ⊢ a ∷ F ^ [ rF , ι lF ]
    × Γ ⊢ A ≡ G [ a ] ^ [ ! , ι lG ]
    × l PE.≡ ι lG
  inversion-app (_ ▹ _ ▹ _ ▹ d ∘ⱼ d₁) = _ , _ , _ , _ , _ ,  d , d₁ , refl (substTypeΠ (syntacticTerm d) d₁) , PE.refl
  inversion-app (conv d x) = let a , b , c , d , e , g , h , i , j = inversion-app d
                             in  a , b , c , d , e , g , h , trans (sym (PE.subst (λ lx → _ ⊢ _ ≡ _ ^ [ _ , lx ]) j x)) i , j
  
  inversion-app-irr :  ∀ {Γ f a A l lΠ} → Γ ⊢ (f ∘ a ^ lΠ) ∷ A ^ [ % , l ] →
    ∃₂ λ F rF → ∃₂ λ lF G → ∃ λ lG → Γ ⊢ f ∷ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ % ^ [ % , ι lΠ ]
      × Γ ⊢ a ∷ F ^ [ rF , ι lF ]
      × lG PE.≡ ⁰
      × lΠ PE.≡ ⁰
      × l PE.≡ ι ⁰
  inversion-app-irr (l% ▹ _ ▹ _ ▹ d ∘ⱼ d₁) = let lG< , l< = l% PE.refl in  _ , _ , _ , _ , _ ,  d , d₁ , lG< , l< , PE.cong ι lG<
  inversion-app-irr (conv d x) = let a , b , c , d , e , g , h , j , k , l = inversion-app-irr d
                                 in  a , b , c , d , e , g , h , j , k , l 

  
  -- Inversion of lambda.
  inversion-lam : ∀ {t F A r lΠ Γ} → Γ ⊢ lam F ▹ t ^ lΠ ∷ A ^ r →
    ∃₂ λ rF lF → ∃₂ λ G rG → ∃ λ lG → Γ ⊢ F ^ [ rF , ι lF ]
    × Γ ∙ F ^ [ rF , ι lF ] ⊢ t ∷ G ^ [ rG , ι lG ]
    × Γ ⊢ A ≡ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ rG ^ [ rG , ι lΠ ]
    × r PE.≡ [ rG , ι lΠ ]
  inversion-lam (lamⱼ l< l<' x x₁) = _ , _ , _ , _ , _ , x , x₁ ,
                                     refl (univ (Πⱼ l< ▹ l<' ▹ (un-univ x) ▹ un-univ (syntacticTerm x₁))) , PE.refl
  inversion-lam (conv x x₁) = let a , b , c , d , e , f , g , h , i = inversion-lam x
                              in  a , b , c , d , e , f , g , trans (sym (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ rx) i x₁)) h , i
  
  
  -- Inversion of Id-types.
  inversion-Id : ∀ {A t u C r Γ}
               → Γ ⊢ Id A t u ∷ C ^ r
               → ∃ λ l
               → Γ ⊢ A ∷ U l ^ [ ! , next l ]
               × Γ ⊢ t ∷ A ^ [ ! , ι l ]
               × Γ ⊢ u ∷ A ^ [ ! , ι l ]
               × Γ ⊢ C ≡ SProp ^ [ ! , next ⁰ ]
               × r PE.≡ [ ! , next ⁰ ]
  inversion-Id (Idⱼ {l = l} A t u) = l , A , t , u , refl (Ugenⱼ (wfTerm A)) , PE.refl
  inversion-Id (conv x x₁) = let l , a , b , c , d , r≡! = inversion-Id x
                             in l , a , b , c , trans (sym (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ rx) r≡! x₁)) d , r≡!
  
  
  -- Inversion of cast-types.
  inversion-cast : ∀ {A B e t l C r Γ}
                 → Γ ⊢ cast l A B e t ∷ C ^ r
                 → ∃ λ rA
                 → Γ ⊢ A ∷ Univ rA l ^ [ ! , next ⁰ ]
                 × Γ ⊢ B ∷ Univ rA l ^ [ ! , next ⁰ ]
                 × Γ ⊢ e ∷ Id (Univ rA l) A B ^ [ % , ι ⁰ ]
                 × Γ ⊢ t ∷ A ^ [ rA , ι ⁰ ]
              × Γ ⊢ C ≡ B ^ [ rA , ι ⁰ ]
                × r PE.≡ [ rA , ι ⁰ ]
                × l PE.≡ ⁰
  inversion-cast (castⱼ X X₁ X₂ X₃) = _ , X , X₁ , X₂ , X₃ , refl (univ X₁) , PE.refl , PE.refl
  inversion-cast (conv x x₁) = let r , a , b , c , d , e , r≡! , el = inversion-cast x
                               in r , a , b , c , d , trans (sym (PE.subst (λ rx → _ ⊢ _ ≡ _ ^ rx) r≡! x₁)) e , r≡! , el
