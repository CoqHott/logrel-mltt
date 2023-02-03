{-# OPTIONS --safe #-}

module Definition.Conversion.FullReduction where

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Typed.EqRelInstance
open import Definition.Typed.Weakening
open import Definition.Conversion
open import Definition.Conversion.Whnf
open import Definition.Conversion.Soundness
open import Definition.Conversion.Stability
open import Definition.Typed.Consequences.Inversion
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.NeTypeEq
open import Definition.Typed.Consequences.Equality
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Properties.Escape
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.ShapeView
open import Definition.LogicalRelation.Fundamental.Reducibility
open import Definition.Typed.Consequences.RelevanceUnicity

open import Tools.Empty using (⊥; ⊥-elim)
open import Tools.Product
import Tools.PropositionalEquality as PE


mutual
  data NfNeutral (Γ : Con Term) : Term → Set where
    var     : ∀ n                     → NfNeutral Γ (var n)
    ∘ₙ      : ∀ {k u l}     → NfNeutral Γ  k → Nf Γ u → NfNeutral Γ  (k ∘ u ^ l)
    natrecₙ : ∀ {l C c g k} →  Nf (Γ ∙ ℕ ^ [ ! , ι ⁰ ]) C → Nf Γ c → Nf Γ g → NfNeutral Γ  k → NfNeutral Γ  (natrec l C c g k)
    castₙ : ∀ {l A B e t} → NfNeutral Γ  A → NfNeutral Γ B → NfNeutral Γ t → NfNeutral Γ  (cast l A B e t)
    castℕₙ : ∀ {l B e t} → NfNeutral Γ  B → Nf Γ t → NfNeutral Γ  (cast l ℕ B e t)
    castΠₙ : ∀ {l A rA lA P lP B e t} → Nf Γ A → Nf (Γ ∙ A ^ [ rA , ι lA ]) P → NfNeutral Γ  B → Nf Γ t
                                      → NfNeutral Γ (cast l (Π A ^ rA ° lA ▹ P ° lP ° l ^ !) B e t)
    castneℕₙ : ∀ {l B e t} → NfNeutral Γ  B → Nf Γ t → NfNeutral Γ  (cast l B ℕ e t)
    castneΠₙ : ∀ {l A rA lA P lP B e t} → Nf Γ A → Nf (Γ ∙ A ^ [ rA , ι lA ]) P → NfNeutral Γ  B → Nf Γ t
                                      → NfNeutral Γ (cast l B (Π A ^ rA ° lA ▹ P ° lP ° l ^ !) e t)
    castℕℕₙ : ∀ {l e t} → NfNeutral Γ  t → NfNeutral Γ  (cast l ℕ ℕ e t)
    castℕΠₙ : ∀ {l A rA B e t} → Nf Γ A → Nf (Γ ∙ A ^ [ rA , ι ⁰ ]) B → Nf Γ t → NfNeutral Γ  (cast l ℕ (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° l ^ !) e t)
    castΠℕₙ : ∀ {l A rA B e t} → Nf Γ A → Nf (Γ ∙ A ^ [ rA , ι ⁰ ]) B → Nf Γ t → NfNeutral Γ  (cast l (Π A ^ rA ° ⁰ ▹ B ° ⁰ ° l ^ !) ℕ e t)
    castΠΠ%!ₙ : ∀ {l A B A' B' e t} → Nf Γ A → Nf (Γ ∙ A ^ [ % , ι ⁰ ]) B → Nf Γ A' → Nf (Γ ∙ A' ^ [ ! , ι ⁰ ]) B' → Nf Γ t
                                    → NfNeutral Γ  (cast l (Π A ^ % ° ⁰ ▹ B ° ⁰ ° l ^ !) (Π A' ^ ! ° ⁰ ▹ B' ° ⁰ ° l ^ !) e t)
    castΠΠ!%ₙ : ∀ {l A B A' B' e t} → Nf Γ A → Nf (Γ ∙ A ^ [ ! , ι ⁰ ]) B → Nf Γ A' → Nf (Γ ∙ A' ^ [ % , ι ⁰ ]) B' → Nf Γ t
                                    → NfNeutral Γ  (cast l (Π A ^ ! ° ⁰ ▹ B ° ⁰ ° l ^ !) (Π A' ^ % ° ⁰ ▹ B' ° ⁰ ° l ^ !) e t)
    Emptyrecₙ : ∀ {l A e} → Nf Γ A → NfNeutral Γ  (Emptyrec l ⁰ A e)

  data Nf (Γ : Con Term) : Term → Set where

    Uₙ    : ∀ {r l} → Nf Γ (Univ r l)
    Πₙ    : ∀ {A r rΠ lA B lB l} → Nf Γ A → Nf (Γ ∙ A ^ [ r , ι lA ]) B → Nf Γ (Π A ^ r ° lA ▹ B ° lB ° l ^ rΠ)
    Idₙ : ∀ {A t u} → Nf Γ  A → Nf Γ t → Nf Γ u → Nf Γ  (Id A t u)
    ℕₙ    : Nf Γ ℕ
    Emptyₙ : ∀ {l} → Nf Γ (Empty l)

    lamₙ  : ∀ {A l rF lF t} → Γ ⊢ A ^ [ rF , ι lF ] → Nf (Γ ∙ A ^ [ rF , ι lF ]) t → Nf Γ (lam A ▹ t ^ l)
    zeroₙ : Nf Γ zero
    sucₙ  : ∀ {t} → Nf Γ t → Nf Γ (suc t)

    ne   : ∀ {n} → NfNeutral Γ  n → Nf Γ n
    sprop   : ∀ {t A l} → Γ ⊢ t ∷ A ^ [ % , l ] → Nf Γ t

NfNeutralNeutral :  ∀ {t Γ} → NfNeutral Γ t → Neutral t
NfNeutralNeutral (var n) = var n
NfNeutralNeutral (∘ₙ X x) = ∘ₙ (NfNeutralNeutral X)
NfNeutralNeutral (natrecₙ x x₁ x₂ X) = natrecₙ (NfNeutralNeutral X)
NfNeutralNeutral (castₙ X x x₁) = castₙ (NfNeutralNeutral X) (NfNeutralNeutral x) (NfNeutralNeutral x₁)
NfNeutralNeutral (castℕₙ X x) = castℕₙ (NfNeutralNeutral X)
NfNeutralNeutral (castΠₙ x x₁ X x₂) = castΠₙ (NfNeutralNeutral X)
NfNeutralNeutral (castℕℕₙ X) = castℕℕₙ (NfNeutralNeutral X)
NfNeutralNeutral (castℕΠₙ x x₁ x₂) = castℕΠₙ
NfNeutralNeutral (castΠℕₙ x x₁ x₂) = castΠℕₙ
NfNeutralNeutral (castΠΠ%!ₙ x x₁ x₂ x₃ x₄) = castΠΠ%!ₙ
NfNeutralNeutral (castΠΠ!%ₙ x x₁ x₂ x₃ x₄) = castΠΠ!%ₙ
NfNeutralNeutral (Emptyrecₙ x) = Emptyrecₙ
NfNeutralNeutral (castneℕₙ X x) = castnℕₙ (NfNeutralNeutral X)
NfNeutralNeutral (castneΠₙ x x₁ X x₂) = castnΠₙ (NfNeutralNeutral X)

NfWhnf :  ∀ {Γ t A l} → Γ ⊢ t ∷ A ^ [ ! , l ] → Nf Γ t → Whnf t
NfWhnf ⊢t Uₙ = Uₙ
NfWhnf ⊢t (Πₙ X X₁) = Πₙ
NfWhnf ⊢t (Idₙ X x x₁) = Idₙ
NfWhnf ⊢t ℕₙ = ℕₙ
NfWhnf ⊢t Emptyₙ = Emptyₙ
NfWhnf ⊢t (lamₙ _ X) = lamₙ
NfWhnf ⊢t zeroₙ = zeroₙ
NfWhnf ⊢t (sucₙ X) = sucₙ
NfWhnf ⊢t (ne x) = ne (NfNeutralNeutral x)
NfWhnf ⊢t (sprop ⊢t') = let !≡% = relevance-uniq ⊢t ⊢t' in ⊥-elim (!≢% !≡%)

NfΠinversion :  ∀ {F G rF lF lG lΠ Γ} → Nf Γ (Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ !) → Nf Γ F × Nf (Γ ∙ F ^ [ rF , ι lF ]) G
NfΠinversion (Πₙ X Y) = X , Y
NfΠinversion (sprop ⊢t) =
  let _ , _ , _ , _ , _ , _ , _ , e = inversion-Π ⊢t
      %≡! , _ = typelevel-injectivity e
  in ⊥-elim (!≢% (PE.sym %≡!))

NfΠA′ : ∀ {A F G rF lF lG lΠ Γ l} ([Π] : Γ ⊩⟨ l ⟩Π Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ ! ^[ lΠ ] )
    → Γ ⊩⟨ l ⟩ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ ! ≡ A ^ [ ! ,  ι lΠ ] / (Π-intr [Π])
    → Nf Γ A
    → ∃₂ λ H E → Nf Γ H × Nf (Γ ∙ H ^ [ rF , ι lF ]) E × A PE.≡ Π H ^ rF ° lF ▹ E ° lG ° lΠ ^ !
NfΠA′ (noemb (Πᵣ rF′ lF′ lG′ lF≤ lG≤  F G D ⊢F ⊢G A≡A [F] [G] G-ext)) (Π₌ F′ G′ D′ A≡B [F≡F′] [G≡G′]) nfA =
    let _ , rF≡rF′ , lF≡lF′ , _ , lG≡lG′ , _ = Π-PE-injectivity (whnfRed* (red D) Πₙ)
        X = whnfRed* D′ (NfWhnf (un-univ (redFirst* D′)) nfA)
        NfH , NfE =  NfΠinversion (PE.subst (Nf _) X nfA)
    in F′ , G′ , NfH , PE.subst₂ (λ r l →  Nf (_ ∙ _ ^ [ r , ι l ]) _) (PE.sym rF≡rF′) (PE.sym lF≡lF′) NfE ,
       PE.subst (λ r → _ PE.≡ Π _ ^ r ° _ ▹ _ ° _ ° _ ^ _) (PE.sym rF≡rF′)
         (PE.subst (λ l → _ PE.≡ Π _ ^ _ ° l ▹ _ ° _ ° _ ^ _) (PE.sym lF≡lF′)
           (PE.subst (λ l → _ PE.≡ Π _ ^ _ ° _ ▹ _ ° l ° _ ^ _) (PE.sym lG≡lG′) X))
NfΠA′ (emb emb< [Π]) [Π≡A] nfA = NfΠA′ [Π] [Π≡A] nfA
NfΠA′ (emb ∞< [Π]) [Π≡A] nfA = NfΠA′ [Π] [Π≡A] nfA


NfΠA : ∀ {A F G rF lF lG lΠ Γ}
    → Γ ⊢ Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ ! ≡ A ^ [ ! ,  ι lΠ ]
    → Nf Γ A
    → ∃₂ λ H E → Nf Γ H × Nf (Γ ∙ H ^ [ rF , ι lF ]) E × A PE.≡ Π H ^ rF ° lF ▹ E ° lG ° lΠ ^ !
NfΠA {A} Π≡A whnfA  =
  let X = reducibleEq Π≡A
      [Π] = proj₁ X
      [A] = proj₁ (proj₂ X)
      [Π≡A] = proj₂ (proj₂ X)
  in NfΠA′ (Π-elim [Π]) (irrelevanceEq [Π] (Π-intr (Π-elim [Π])) [Π≡A]) whnfA

NeutralNfNeutral : ∀ {Γ u A l} → Neutral u → Nf Γ u → Γ ⊢ u ∷ A ^ [ ! , l ] → NfNeutral Γ u
NeutralNfNeutral neu (ne x) ⊢u = x
NeutralNfNeutral neu (sprop ⊢u') ⊢u = let !≡% = relevance-uniq ⊢u ⊢u' in ⊥-elim (!≢% !≡%)

NfNeutralNfNeutral : ∀ {Γ t u A l} → Neutral t → Neutral A → Nf Γ u → Γ ⊢ t ≡ u ∷ A ^ [ ! , l ] → NfNeutral Γ u
NfNeutralNfNeutral net neA nfu t≡u =
  let _ , _ , ⊢u = syntacticEqTerm t≡u
      neu = inversion-ne neA (NfWhnf ⊢u nfu) ⊢u
  in NeutralNfNeutral neu nfu ⊢u


mutual

  convNfNeutral :  ∀ {Γ Δ t A r} → ⊢ Γ ≡ Δ → Γ ⊢ t ∷ A ^ r → NfNeutral Γ t → NfNeutral Δ t
  convNfNeutral Γ≡Δ ⊢t (var n) = var n
  convNfNeutral {r = [ ! , l ]} Γ≡Δ ⊢t (∘ₙ X x) =
    let F , rF , lF , G , lG , ⊢k , ⊢u , _ , erl = inversion-app ⊢t
    in ∘ₙ (convNfNeutral Γ≡Δ ⊢k X) (convNf Γ≡Δ ⊢u x)
  convNfNeutral {r = [ % , l ]} Γ≡Δ ⊢t (∘ₙ X x) =
    let F , rF , lF , G , lG , ⊢k , ⊢u , _ , _ , erl = inversion-app-irr ⊢t
    in ∘ₙ (convNfNeutral Γ≡Δ ⊢k X) (convNf Γ≡Δ ⊢u x) 
  convNfNeutral Γ≡Δ ⊢t (natrecₙ x x₁ x₂ X) =
    let _ , _ , ⊢x , ⊢x₁ , ⊢x₂ , ⊢X , _ = inversion-natrec ⊢t
    in natrecₙ (convNf (Γ≡Δ ∙ refl (univ (ℕⱼ (wfTerm ⊢t)))) (un-univ ⊢x) x) (convNf Γ≡Δ ⊢x₁ x₁)
               (convNf Γ≡Δ ⊢x₂ x₂) (convNfNeutral Γ≡Δ ⊢X X)
  convNfNeutral Γ≡Δ ⊢t (castₙ X x x₁) =
    let _ , ⊢X , ⊢x , ⊢e , ⊢x₁ , _ = inversion-cast ⊢t
    in castₙ (convNfNeutral Γ≡Δ ⊢X X) (convNfNeutral Γ≡Δ ⊢x x) (convNfNeutral Γ≡Δ ⊢x₁ x₁)
  convNfNeutral Γ≡Δ ⊢t (castℕₙ X x) =
    let _ , _ , ⊢X , ⊢e , ⊢x , _ = inversion-cast ⊢t
    in castℕₙ (convNfNeutral Γ≡Δ ⊢X X) (convNf Γ≡Δ ⊢x x)
  convNfNeutral Γ≡Δ ⊢t (castΠₙ x x₁ X x₂) =
    let _ , ⊢Π , ⊢X , ⊢e , ⊢x₂ , _ = inversion-cast ⊢t
        _ , _ , _ , ⊢F , ⊢G , _ = inversion-Π ⊢Π
    in castΠₙ (convNf Γ≡Δ ⊢F x) (convNf (Γ≡Δ ∙ refl (univ ⊢F)) ⊢G x₁) (convNfNeutral Γ≡Δ ⊢X X) (convNf Γ≡Δ ⊢x₂ x₂)
  convNfNeutral Γ≡Δ ⊢t (castℕℕₙ X) =
    let _ , _ , _ , _ , ⊢X , _ = inversion-cast ⊢t
    in castℕℕₙ (convNfNeutral Γ≡Δ ⊢X X)
  convNfNeutral Γ≡Δ ⊢t (castℕΠₙ x x₁ x₂) =
    let _ , _ , ⊢Π , ⊢e , ⊢x₂ , _ = inversion-cast ⊢t
        _ , _ , _ , ⊢F , ⊢G , _ = inversion-Π ⊢Π
    in castℕΠₙ (convNf Γ≡Δ ⊢F x) (convNf (Γ≡Δ ∙ refl (univ ⊢F)) ⊢G x₁) (convNf Γ≡Δ ⊢x₂ x₂)
  convNfNeutral Γ≡Δ ⊢t (castΠℕₙ x x₁ x₂) =
    let _ , ⊢Π , _ , ⊢e , ⊢x₂ , _ = inversion-cast ⊢t
        _ , _ , _ , ⊢F , ⊢G , _ = inversion-Π ⊢Π
    in castΠℕₙ (convNf Γ≡Δ ⊢F x) (convNf (Γ≡Δ ∙ refl (univ ⊢F)) ⊢G x₁) (convNf Γ≡Δ ⊢x₂ x₂)
  convNfNeutral Γ≡Δ ⊢t (castΠΠ%!ₙ x x₁ x₂ x₃ x₄) =
    let _ , ⊢Π , ⊢Π' , ⊢e , ⊢x₄ , _ = inversion-cast ⊢t
        _ , _ , _ , ⊢F , ⊢G , _ = inversion-Π ⊢Π
        _ , _ , _ , ⊢F' , ⊢G' , _ = inversion-Π ⊢Π'
    in castΠΠ%!ₙ (convNf Γ≡Δ ⊢F x) (convNf (Γ≡Δ ∙ refl (univ ⊢F)) ⊢G x₁)
               (convNf Γ≡Δ ⊢F' x₂) (convNf (Γ≡Δ ∙ refl (univ ⊢F')) ⊢G' x₃) (convNf Γ≡Δ ⊢x₄ x₄)
  convNfNeutral Γ≡Δ ⊢t (castΠΠ!%ₙ x x₁ x₂ x₃ x₄) =
    let _ , ⊢Π , ⊢Π' , ⊢e , ⊢x₄ , _ = inversion-cast ⊢t
        _ , _ , _ , ⊢F , ⊢G , _ = inversion-Π ⊢Π
        _ , _ , _ , ⊢F' , ⊢G' , _ = inversion-Π ⊢Π'
    in castΠΠ!%ₙ (convNf Γ≡Δ ⊢F x) (convNf (Γ≡Δ ∙ refl (univ ⊢F)) ⊢G x₁)
               (convNf Γ≡Δ ⊢F' x₂) (convNf (Γ≡Δ ∙ refl (univ ⊢F')) ⊢G' x₃) (convNf Γ≡Δ ⊢x₄ x₄)
  convNfNeutral Γ≡Δ ⊢t (Emptyrecₙ x) =
    let _ , ⊢x , _ = inversion-Emptyrec ⊢t
    in Emptyrecₙ (convNf Γ≡Δ (un-univ ⊢x) x)
  convNfNeutral Γ≡Δ ⊢t (castneℕₙ X x) =
    let _ , ⊢A , ⊢B , ⊢e , ⊢x₄ , _ = inversion-cast ⊢t
    in castneℕₙ (convNfNeutral Γ≡Δ ⊢A X) (convNf Γ≡Δ ⊢x₄ x)
  convNfNeutral Γ≡Δ ⊢t (castneΠₙ x x₁ X x₂) =
    let _ , ⊢A , ⊢Π , ⊢e , ⊢x₄ , _ = inversion-cast ⊢t
        _ , _ , _ , ⊢F , ⊢G , _ = inversion-Π ⊢Π
    in castneΠₙ (convNf Γ≡Δ ⊢F x) (convNf (Γ≡Δ ∙ refl (univ ⊢F)) ⊢G x₁) (convNfNeutral Γ≡Δ ⊢A X) (convNf Γ≡Δ ⊢x₄ x₂)



  convNf :  ∀ {Γ Δ t A r} → ⊢ Γ ≡ Δ → Γ ⊢ t ∷ A ^ r → Nf Γ t → Nf Δ t
  convNf Γ≡Δ ⊢t Uₙ = Uₙ
  convNf Γ≡Δ ⊢t (Πₙ X X₁) =
    let _ , _ , _ , ⊢F , ⊢G , _ , _ = inversion-Π ⊢t
    in Πₙ (convNf Γ≡Δ ⊢F X) (convNf (Γ≡Δ ∙ refl (univ ⊢F)) ⊢G X₁)
  convNf Γ≡Δ ⊢t (Idₙ X x x₁) =
    let _ , ⊢X , ⊢x , ⊢x₁ , _ = inversion-Id ⊢t
    in Idₙ (convNf Γ≡Δ ⊢X X) (convNf Γ≡Δ ⊢x x) (convNf Γ≡Δ ⊢x₁ x₁)
  convNf Γ≡Δ ⊢t ℕₙ = ℕₙ
  convNf Γ≡Δ ⊢t Emptyₙ = Emptyₙ
  convNf Γ≡Δ ⊢t (lamₙ ⊢F X) =
    let rF , lF , G , rG , lG , ⊢F' , ⊢t' , _ , erl = inversion-lam ⊢t
        er , el = typelevel-injectivity erl
        erF , elF = relevance-unicity ⊢F ⊢F'
    in lamₙ (stability Γ≡Δ  ⊢F) (convNf (Γ≡Δ ∙ refl ⊢F) 
            (PE.subst₂ (λ r l → _ ∙ _ ^ [ r , ι l ] ⊢ _ ∷ G ^ [ rG , ι lG ]) (PE.sym erF) (PE.sym (ιinj elF)) ⊢t')  X)
  convNf Γ≡Δ ⊢t zeroₙ = zeroₙ
  convNf Γ≡Δ ⊢t (sucₙ X) = sucₙ (convNf Γ≡Δ (proj₁ (inversion-suc ⊢t)) X )
  convNf Γ≡Δ ⊢t (ne x) = ne (convNfNeutral Γ≡Δ ⊢t x)
  convNf Γ≡Δ ⊢t (sprop x) = sprop (stabilityTerm Γ≡Δ x)

mutual
  fullRedNe : ∀ {t t' A l Γ} → Γ ⊢ t ~ t' ↑! A ^ l → ∃ λ u → NfNeutral Γ u × Γ ⊢ t ≡ u ∷ A ^ [ ! , l ]
  fullRedNe (var-refl x _) = var _ , var _ , refl x
  fullRedNe (app-cong {rF = !} {lΠ = lΠ} t u) =
    let t′ , nfT′ , t≡t′ = fullRedNe′ t
        u′ , nfU′ , u≡u′ = fullRedTerm u
    in  (t′ ∘ u′ ^ lΠ) ,
        ∘ₙ nfT′ nfU′ ,
        app-cong t≡t′ u≡u′
  fullRedNe (app-cong {t = a} {rF = %} {lΠ = lΠ} t (%~↑ ⊢a ⊢a')) =
    let t′ , nfT′ , t≡t′ = fullRedNe′ t
    in  (t′ ∘ a ^ lΠ) ,
        ∘ₙ nfT′ (sprop ⊢a) ,
        app-cong t≡t′ (proof-irrelevance ⊢a ⊢a)
  fullRedNe (natrec-cong {lF = l} C z s n) =
    let C′ , nfC′ , C≡C′ = fullRed C
        z′ , nfZ′ , z≡z′ = fullRedTerm z
        s′ , nfS′ , s≡s′ = fullRedTerm s
        n′ , nfN′ , n≡n′ = fullRedNe′ n
    in  natrec l C′ z′ s′ n′
     , natrecₙ nfC′ nfZ′ nfS′ nfN′
     ,  natrec-cong C≡C′ z≡z′ s≡s′ n≡n′
  fullRedNe (Emptyrec-cong {k = k} {ll = l} C (%~↑ ⊢e ⊢e')) =
    let C′ , nfC′ , C≡C′ = fullRed C
    in  Emptyrec l ⁰ C′ k , Emptyrecₙ nfC′
     ,  Emptyrec-cong C≡C′ ⊢e ⊢e
  fullRedNe (cast-cong {e = e} {e' = e'} x x₁ x₂ ⊢e ⊢e') =
    let A′ , nfA′ , A≡A′ = fullRedNe′ x
        B′ , nfB′ , B≡B′ = fullRedNe′ x₁
        t′ , nft′ , t≡t′ = fullRedTerm′ x₂
        _ , nft , nft' = whnfConv↓Term x₂
        _ , ⊢t , _ = syntacticEqTerm (soundnessConv↓Term x₂)
        _ , nX , nX' = ne~↓! x
        nt = inversion-ne nX nft ⊢t
        B≡B = trans (sym (soundness~↓! x₁)) B≡B′
    in cast ⁰ A′ B′ e t′ , castₙ nfA′ nfB′ (NfNeutralNfNeutral nt nX nft′ t≡t′) ,
       cast-cong A≡A′ B≡B t≡t′ ⊢e (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢e)) ) A≡A′ B≡B))) 
  fullRedNe (cast-ℕ {e = e} {e' = e'} x x₁ ⊢e ⊢e') =
    let A′ , nfA′ , A≡A′ = fullRedNe′ x
        t′ , nft′ , t≡t′ = fullRedTerm x₁
    in cast ⁰ _ A′ e t′ , castℕₙ nfA′ nft′ ,
       cast-cong (refl (ℕⱼ (wfTerm ⊢e)) ) A≡A′ t≡t′ ⊢e
                 (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢e)) ) (refl (ℕⱼ (wfTerm ⊢e))) A≡A′)))
  fullRedNe {Γ = Γ} (cast-Π {e = e} {e' = e'} x x₁ x₂ ⊢e ⊢e') =
    let A′ , nfA′ , A≡A′ = fullRedTerm x
        B′ , nfB′ , B≡B′ = fullRedNe′ x₁
        t′ , nft′ , t≡t′ = fullRedTerm x₂
        H , E , NfH , NfE , Π≡HE = NfΠA (univ A≡A′) nfA′
        nfCast = castΠₙ NfH NfE nfB′ nft′
    in cast ⁰ A′ B′ e t′ , PE.subst (λ A →  NfNeutral Γ (cast ⁰ A B′ e t′)) (PE.sym Π≡HE) nfCast ,
       cast-cong A≡A′ B≡B′ t≡t′ ⊢e (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢e)) ) A≡A′ B≡B′)))
  fullRedNe {Γ = Γ} (cast-Πℕ {e = e} {e' = e'} x x₁ ⊢e ⊢e') =
    let A′ , nfA′ , A≡A′ = fullRedTerm x
        t′ , nft′ , t≡t′ = fullRedTerm x₁
        H , E , NfH , NfE , Π≡HE = NfΠA (univ A≡A′) nfA′
        nfCast = castΠℕₙ NfH NfE nft′
    in cast ⁰ A′ ℕ e t′ , PE.subst (λ A → NfNeutral  Γ (cast ⁰ A ℕ e t′)) (PE.sym Π≡HE) nfCast ,
       cast-cong A≡A′ (refl (ℕⱼ (wfTerm ⊢e))) t≡t′ ⊢e (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢e)) ) A≡A′ (refl (ℕⱼ (wfTerm ⊢e))))))
  fullRedNe {Γ = Γ} (cast-ℕΠ {e = e} {e' = e'} x x₁ ⊢e ⊢e') =
    let A′ , nfA′ , A≡A′ = fullRedTerm x
        t′ , nft′ , t≡t′ = fullRedTerm x₁
        H , E , NfH , NfE , Π≡HE = NfΠA (univ A≡A′) nfA′
        nfCast = castℕΠₙ NfH NfE nft′
    in cast ⁰ ℕ A′ e t′ , PE.subst (λ A →  NfNeutral Γ (cast ⁰ ℕ A e t′)) (PE.sym Π≡HE) nfCast ,
       cast-cong (refl (ℕⱼ (wfTerm ⊢e))) A≡A′ t≡t′ ⊢e (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢e)) ) (refl (ℕⱼ (wfTerm ⊢e))) A≡A′ )))
  fullRedNe {Γ = Γ} (cast-ΠΠ%! {e = e} {e' = e'} x x₁ x₂ ⊢e ⊢e') =
    let A′ , nfA′ , A≡A′ = fullRedTerm x
        B′ , nfB′ , B≡B′ = fullRedTerm x₁
        t′ , nft′ , t≡t′ = fullRedTerm x₂
        H , E , NfH , NfE , Π≡HE = NfΠA (univ A≡A′) nfA′
        H' , E' , NfH' , NfE' , Π≡HE' = NfΠA (univ B≡B′) nfB′
        nfCast = castΠΠ%!ₙ NfH NfE NfH' NfE' nft′
    in cast ⁰ A′ B′ e t′ , PE.subst₂ (λ A B →  NfNeutral Γ (cast ⁰ A B e t′)) (PE.sym Π≡HE) (PE.sym Π≡HE') nfCast ,
       cast-cong A≡A′ B≡B′ t≡t′ ⊢e (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢e)) ) A≡A′ B≡B′ )))
  fullRedNe {Γ = Γ} (cast-ΠΠ!% {e = e} {e' = e'} x x₁ x₂ ⊢e ⊢e') =
    let A′ , nfA′ , A≡A′ = fullRedTerm x
        B′ , nfB′ , B≡B′ = fullRedTerm x₁
        t′ , nft′ , t≡t′ = fullRedTerm x₂
        H , E , NfH , NfE , Π≡HE = NfΠA (univ A≡A′) nfA′
        H' , E' , NfH' , NfE' , Π≡HE' = NfΠA (univ B≡B′) nfB′
        nfCast = castΠΠ!%ₙ NfH NfE NfH' NfE' nft′
    in cast ⁰ A′ B′ e t′ , PE.subst₂ (λ A B →  NfNeutral Γ (cast ⁰ A B e t′)) (PE.sym Π≡HE) (PE.sym Π≡HE') nfCast ,
       cast-cong A≡A′ B≡B′ t≡t′ ⊢e (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢e)) ) A≡A′ B≡B′ )))
  fullRedNe (cast-neℕ {e = e} x x₁ ⊢e _) =
    let A′ , nfA′ , A≡A′ = fullRedNe′ x
        t′ , nft′ , t≡t′ = fullRedTerm x₁
    in cast ⁰ A′ ℕ e t′ , castneℕₙ nfA′ nft′ ,
       cast-cong A≡A′ (refl (ℕⱼ (wfTerm ⊢e))) t≡t′ ⊢e (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢e)) ) A≡A′ (refl (ℕⱼ (wfTerm ⊢e))) )))
  fullRedNe {Γ = Γ} (cast-neΠ {e = e} X x x₁ ⊢e _) =
    let A′ , nfA′ , A≡A′ = fullRedNe′ x
        t′ , nft′ , t≡t′ = fullRedTerm x₁
        Π′ , nfΠ′ , Π≡Π′ = fullRedTerm X
        H , E , NfH , NfE , Π≡HE = NfΠA (univ Π≡Π′) nfΠ′
        nfCast = castneΠₙ NfH NfE nfA′ nft′ 
    in cast ⁰ A′ Π′ e t′ , PE.subst (λ B →  NfNeutral Γ (cast ⁰ A′ B e t′)) (PE.sym Π≡HE) nfCast ,
      cast-cong A≡A′ Π≡Π′ t≡t′ ⊢e (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢e)) ) A≡A′ Π≡Π′)))
  fullRedNe (cast-refl {e = e} x x₁ ⊢e) =
    let A′ , nfA′ , A≡A′ = fullRedNe′ x
        _ , neA , _ = ne~↓! x
        t′ , nft′ , t≡t′ = fullRedTerm′ x₁
        _ , ⊢t , ⊢t′ = syntacticEqTerm t≡t′
        A≡A = soundness~↓! x        
    in cast ⁰ A′ A′ e t′ ,
       castₙ nfA′ nfA′ (NeutralNfNeutral (inversion-ne neA (NfWhnf ⊢t′ nft′) ⊢t′) nft′ ⊢t′) ,
       cast-cong A≡A′ (trans (sym A≡A) A≡A′) t≡t′ ⊢e (conv ⊢e (univ (Id-cong (refl (univ 0<1 (wfTerm ⊢e)) ) A≡A′ (trans (sym A≡A) A≡A′)))) 
  fullRedNe (castℕ-refl {e = e} x ⊢e) =
    let t′ , net′ , t≡t′ = fullRedNe′ x
        _ , ⊢t , ⊢t′ = syntacticEqTerm t≡t′
        ℕ≡ℕ = refl (ℕⱼ (wfTerm ⊢e))
    in cast ⁰ ℕ ℕ e t′ ,
       castℕℕₙ net′ ,
       cast-cong ℕ≡ℕ ℕ≡ℕ t≡t′ ⊢e ⊢e
    
  fullRedNe (cast-refl' x x₁ x₂) =
    let A′ , nfA′ , A≡A′ = fullRedNe′ x
        _ , _ , neA = ne~↓! x
        t′ , nft′ , t≡t′ = fullRedTerm′ x₁
        _ , ⊢t , ⊢t′ = syntacticEqTerm t≡t′
        A≡A = soundness~↓! x        
    in t′ ,
       NeutralNfNeutral (inversion-ne neA (NfWhnf ⊢t′ nft′) ⊢t′) nft′ ⊢t′ , 
       t≡t′ 
  fullRedNe (castℕ-refl' x x₁) = fullRedNe′ x


  fullRedNe′ : ∀ {t t' A rA Γ} → Γ ⊢ t ~ t' ↓! A ^ rA → ∃ λ u → NfNeutral Γ u × Γ ⊢ t ≡ u ∷ A ^ [ ! , rA ]
  fullRedNe′ ([~] A D whnfB k~l) =
    let u , nf , t≡u = fullRedNe k~l
    in u , nf , conv t≡u (subset* D)

  fullRed : ∀ {A A' rA Γ} → Γ ⊢ A [conv↑] A' ^ rA → ∃ λ B → Nf Γ B × Γ ⊢ A ≡ B ^ rA
  fullRed ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) =
    let B″ , nf , B′≡B″ = fullRed′ A′<>B′
    in  B″ , nf , trans (subset* D) B′≡B″

  fullRed′ : ∀ {A B rA Γ} → Γ ⊢ A [conv↓] B ^ rA → ∃ λ B → Nf Γ B × Γ ⊢ A ≡ B ^ rA
  fullRed′ (U-refl {r = r} _ ⊢Γ) = Univ r ¹  , Uₙ , refl (Uⱼ ⊢Γ)
  fullRed′ (univ x) =
    let u , Nfu , u≡u = fullRedTerm′ x
    in u , Nfu , univ u≡u

  fullRedTerm : ∀ {t t' A l Γ} → Γ ⊢ t [conv↑] t' ∷ A ^ l → ∃ λ u → Nf Γ u × Γ ⊢ t ≡ u ∷ A ^ [ ! , l ]
  fullRedTerm ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) =
    let u″ , nf , u′≡u″ = fullRedTerm′ t<>u
    in  u″ , nf , conv (trans (subset*Term d) u′≡u″) (sym (subset* D))

  fullRedTerm′ : ∀ {t t' A l Γ} → Γ ⊢ t [conv↓] t' ∷ A ^ l → ∃ λ u → Nf Γ u × Γ ⊢ t ≡ u ∷ A ^ [ ! , l ]
  fullRedTerm′ (U-refl {r = r} _ ⊢Γ) = Univ r ⁰ , Uₙ , refl (univ 0<1 ⊢Γ)
  fullRedTerm′ (ne A) =
    let B , nf , A≡B = fullRedNe′ A
    in  B , ne nf , A≡B
  fullRedTerm′ (ℕ-refl ⊢Γ) = ℕ , ℕₙ , refl (ℕⱼ ⊢Γ)
  fullRedTerm′ (Empty-refl ⊢Γ) = Empty _ , Emptyₙ , refl (Emptyⱼ ⊢Γ)
  fullRedTerm′ (Π-cong {rF = rF} PE.refl PE.refl PE.refl PE.refl l< l<' ⊢F F G) =
    let F′ , nfF′ , F≡F′ = fullRedTerm F
        G′ , nfG′ , G≡G′ = fullRedTerm G
    in Π F′ ^ rF ° _ ▹ G′ ° _ ° _  ^ _
    , Πₙ nfF′ (convNf (reflConEq (wf ⊢F) ∙ univ F≡F′) (proj₂ (proj₂ (syntacticEqTerm G≡G′))) nfG′)
    , Π-cong l< l<' ⊢F F≡F′ G≡G′
  fullRedTerm′ (Id-cong A t u) =
    let A′ , nfA′ , A≡A′ = fullRedTerm A
        t′ , nfT′ , t≡t′ = fullRedTerm t
        u′ , nfU′ , u≡u′ = fullRedTerm u
    in Id A′ t′ u′ , Idₙ nfA′ nfT′ nfU′ , Id-cong A≡A′ t≡t′ u≡u′
  fullRedTerm′  (ℕ-ins t) =
    let u , nf , t≡u = fullRedNe′ t
    in  u , ne nf , t≡u
  fullRedTerm′ (ne-ins ⊢t _ _ t) =
    let u , nfU , t≡u = fullRedNe′ t
        _ , ⊢t∷M , _ = syntacticEqTerm t≡u
        _ , neT , _ = ne~↓! t
    in  u , ne nfU , conv t≡u (proj₂ (neTypeEq neT ⊢t∷M ⊢t))
  fullRedTerm′ (zero-refl ⊢Γ) = zero , zeroₙ , refl (zeroⱼ ⊢Γ)
  fullRedTerm′ (suc-cong t) =
    let u , nf , t≡u = fullRedTerm t
    in  suc u , sucₙ nf , suc-cong t≡u
  fullRedTerm′ {Γ = Γ} (η-eq {f} {g} {F} {G} {rF} {lF} {lG} {l} l< l<' ⊢F ⊢t _ _ _ t∘0) =
    let u , nf , t∘0≡u = fullRedTerm t∘0
        _ , _ , ⊢u = syntacticEqTerm t∘0≡u
        ΓF⊢ = wf ⊢F ∙ ⊢F
        wk⊢F = wk (step id) ΓF⊢ ⊢F
        ΓFF'⊢ = ΓF⊢ ∙ wk⊢F
        wk⊢u = wkTerm (lift (step id)) ΓFF'⊢ ⊢u
        λu∘0 = (lam _ ▹ (U.wk (lift (step id)) u) ^ _) ∘ var 0 ^ l
    in  lam _ ▹ u ^ _ ,
        lamₙ ⊢F nf
     ,  η-eq l< l<' ⊢F ⊢t (lamⱼ (λ _ → l< , l<') (λ abs → ⊥-elim (!≢% abs)) ⊢F ⊢u)
             (trans t∘0≡u (PE.subst₂ (λ x y → Γ ∙ F ^ [ rF , ι lF ] ⊢ x ≡ λu∘0 ∷ y ^ [ ! , ι lG ])
                                     (wkSingleSubstId u) (wkSingleSubstId _)
                                     (sym (β-red l< l<' wk⊢F wk⊢u (var ΓF⊢ here)))))

