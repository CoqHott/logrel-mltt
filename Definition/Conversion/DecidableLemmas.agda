{-# OPTIONS --safe #-}

module Definition.Conversion.DecidableLemmas where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed as T
open import Definition.Typed.Properties
open import Definition.Conversion
open import Definition.Conversion.Whnf
open import Definition.Conversion.Soundness
open import Definition.Conversion.Symmetry
open import Definition.Conversion.Transitivity
open import Definition.Conversion.SymmetrySize
open import Definition.Conversion.Stability
open import Definition.Conversion.Conversion
open import Definition.Conversion.Lift
open import Definition.Conversion.Inversion
open import Definition.Conversion.ConvSize
open import Definition.Conversion.ConversionProp
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.Reduction
open import Definition.Typed.Consequences.Equality
open import Definition.Typed.Consequences.Inequality as IE
open import Definition.Typed.Consequences.NeTypeEq
open import Definition.Typed.Consequences.SucCong
open import Definition.Typed.Consequences.Inversion
open import Definition.Typed.Consequences.TypeUnicity
open import Definition.Conversion.Consequences.Completeness
open import Definition.Conversion.EqRelInstance

open import Definition.Conversion.HelperDecidable


open import Tools.Nat
open import Tools.Product
open import Tools.Empty
open import Tools.Nullary
import Tools.PropositionalEquality as PE

abstract
  ~atU' : ∀ {Γ t v u r lU l}
    → Γ ⊢ t ~ v ↓! Univ r lU ^ l
    → (∃ λ A → ∃ λ lA → Γ ⊢ t ~ u ↓! A ^ lA)
    → Γ ⊢ t ~ u ↓! Univ r lU ^ l
  ~atU' t~v t~u = let _ , ⊢t , _ = syntacticEqTerm (soundness~↓! t~v) in ~atU ⊢t t~u

  ~atU-' : ∀ {Γ t v u r lU l}
    → Γ ⊢ v ~ t ↓! Univ r lU ^ l
    → (∃ λ A → ∃ λ lA → Γ ⊢ u ~ t ↓! A ^ lA)
    → Γ ⊢ u ~ t ↓! Univ r lU ^ l
  ~atU-' v~t u~t = let _ , _ , ⊢t = syntacticEqTerm (soundness~↓! v~t) in ~atU- ⊢t u~t

  sym~↓!U : ∀ {Γ A B r lU l}
    → Γ ⊢ A ~ B ↓! Univ r lU ^ l
    → Γ ⊢ B ~ A ↓! Univ r lU ^ l
  sym~↓!U A~B = let _ , _ , ⊢B = syntacticEqTerm (soundness~↓! A~B)
                    _ , _ , _ , B~A = sym~↓! (reflConEq (wfTerm ⊢B)) A~B
                in ~atU ⊢B (_ , _ , B~A)

  sym~↓!Usize : ∀ {Γ A B r lU l}
    → (A~B : Γ ⊢ A ~ B ↓! Univ r lU ^ l)
    → size~↓! (sym~↓!U A~B) PE.≡ size~↓! A~B
  sym~↓!Usize A~B =
    let _ , _ , ⊢B = syntacticEqTerm (soundness~↓! A~B)
        _ , _ , _ , B~A = sym~↓! (reflConEq (wfTerm ⊢B)) A~B
    in PE.trans (~atUsize ⊢B (_ , _ , B~A)) (size-sym~↓! (reflConEq (wfTerm ⊢B)) A~B)

  reflℕ :  ∀ {Γ t u}
    → Γ ⊢ t ~ u ↓! ℕ ^ ι ⁰
    → Γ ⊢ t ~ t ↓! ℕ ^ ι ⁰
  reflℕ t~u =
    let _ , _ , ⊢u = syntacticEqTerm (soundness~↓! t~u)
        _ , _ , _ , u~t = sym~↓! (reflConEq (wfTerm ⊢u)) t~u
        C , wC , t~t , eqC = trans~↓!-simpl t~u u~t
        eqℕ = ℕ≡A eqC wC        
    in PE.subst (λ X →  _ ⊢ _ ~ _ ↓! X ^ ι ⁰) eqℕ t~t 

  cast-ℕℕ : ∀ {Γ t t' e e'}
              → Γ ⊢ t ~ t' ↓! ℕ ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) ℕ ℕ) ^ [ % , ι ⁰ ]
              → Γ ⊢ e' ∷ (Id (U ⁰) ℕ ℕ) ^ [ % , ι ⁰ ]
              → Γ ⊢ cast ⁰ ℕ ℕ e t ~ cast ⁰ ℕ ℕ e' t' ↑! ℕ ^ ι ⁰
  cast-ℕℕ t~t ⊢e ⊢e' = castℕ-refl ([~] _ (id (univ (ℕⱼ (wfTerm ⊢e)))) ℕₙ (castℕ-refl' t~t ⊢e')) ⊢e

abstract
  cast-refl-dec : ∀ {Γ A B t e u}
              → Neutral A
              → Neutral B
              → Γ ⊢ A ∷ Univ ! ⁰ ^ [ ! , ι ¹ ]
              → Γ ⊢ t ∷ A ^ [ ! , ι ⁰ ]
              → (⊢e : Γ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ])
              → (decAB : Dec (∃ λ U → ∃ λ lA → Γ ⊢ A ~ B ↓! U ^ lA))
              → (dectu : Dec (∃ λ U → ∃ λ lA → Γ ⊢ t ~ u ↑! U ^ lA))
              → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
              → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ A B e t ~ u ↑! U ^ lA)
  cast-refl-dec neA neB ⊢A ⊢tA ⊢e (yes (_ , _ , A~B)) (yes (_ , _ , p)) _ _ =
    let _ , neA , _ = ne~↓! A~B
        var≡t = soundness~↑! p
        ⊢K , ⊢t , ⊢u = syntacticEqTerm var≡t
        el , eA = type-uniq ⊢t ⊢tA
        _ , whnfD , dd = whNormTerm (un-univ (PE.subst (λ X →  _ ⊢ _ ^ [ ! , X ]) el ⊢K)) 
    in yes ( _ , _ , cast-refl (~atU ⊢A (_ , _ , A~B))
                               (ne-ins ⊢tA (conv (PE.subst (λ X → _ ⊢ _ ∷ _ ^ [ ! , X ]) el ⊢u )
                                               (PE.subst (λ X → _ ⊢ _ ≡ _ ^ [ ! , X ]) el eA))
                                       neA ([~] _ (red (univ:⇒*: dd)) whnfD (PE.subst (λ X → _ ⊢ _ ~ _ ↑! _ ^  X) el p)))
                                                                         ⊢e)
  cast-refl-dec neA neB ⊢A _ ⊢e (yes (_ , _ , A~B)) (no ¬p) noeqNe noeqℕ =
    no (λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ⊥-elim (let _ , _ , neA' = ne~↓! x
                                                            _ , neB' , _ = ne~↓! x₁
                                                        in noeqNe neA' neB' PE.refl) ;
            (_ , _ , cast-refl x x₁ x₂) → ¬p (_ , _ , let _ , neA , _ = ne~↓! A~B
                                                          _ , var~t' , _ = [conv↓]ne neA x₁
                                                          _ , var~t = neutral↓↑ var~t'
                                                      in var~t) ;
            (_ , _ , cast-refl' x x₁ x₂) → ⊥-elim (let _ , neB' , neA' = ne~↓! x
                                                   in noeqNe neA' neB' PE.refl) ;
            (_ , _ , castℕ-refl' x x₁) → ⊥-elim (noeqℕ PE.refl) })
  cast-refl-dec neA neB ⊢A _ ⊢e (no ¬AB) _ noeqNe noeqℕ =
    no (λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ⊥-elim (let _ , _ , neA' = ne~↓! x
                                                            _ , neB' , _ = ne~↓! x₁
                                                        in noeqNe neA' neB' PE.refl) ;
            (_ , _ , cast-refl x x₁ x₂) → ¬AB (_ , _ , x) ;
            (_ , _ , cast-refl' x x₁ x₂) → ⊥-elim (let _ , neB' , neA' = ne~↓! x
                                                   in noeqNe neA' neB' PE.refl) ;
            (_ , _ , castℕ-refl' x x₁) → ⊥-elim (noeqℕ PE.refl) })

abstract
  cast-refl'-dec : ∀ {Γ A B t e u}
                 → Neutral A
                 → Neutral B
                 → Γ ⊢ B ∷ Univ ! ⁰ ^ [ ! , ι ¹ ]
                 → Γ ⊢ t ∷ A ^ [ ! , ι ⁰ ]
                 → (⊢e : Γ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ])
                 → (decAB : Dec (∃ λ U → ∃ λ lA → Γ ⊢ B ~ A ↓! U ^ lA))
                 → (dectu : Dec (∃ λ U → ∃ λ lA → Γ ⊢ u ~ t ↑! U ^ lA))
                 → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
                 → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
                 → Dec (∃ λ U → ∃ λ lA → Γ ⊢ u ~ cast ⁰ A B e t ↑! U ^ lA)
  cast-refl'-dec neA neB ⊢B ⊢tA ⊢e (yes (_ , _ , B~A)) (yes (_ , _ , p)) _ _ =
    let _ , _ , neA = ne~↓! B~A
        var≡t = soundness~↑! p
        ⊢K , ⊢u , ⊢t  = syntacticEqTerm var≡t
        el , eA = type-uniq ⊢t ⊢tA
        _ , whnfD , dd = whNormTerm (un-univ (PE.subst (λ X →  _ ⊢ _ ^ [ ! , X ]) el ⊢K)) 
    in yes ( _ , _ , cast-refl' (~atU ⊢B (_ , _ , B~A))
                                (ne-ins (conv (PE.subst (λ X → _ ⊢ _ ∷ _ ^ [ ! , X ]) el ⊢u )
                                              (PE.subst (λ X → _ ⊢ _ ≡ _ ^ [ ! , X ]) el eA))
                                        ⊢tA
                                        neA ([~] _ (red (univ:⇒*: dd)) whnfD (PE.subst (λ X → _ ⊢ _ ~ _ ↑! _ ^  X) el p)))
                                        ⊢e)
  cast-refl'-dec neA neB _ _ ⊢e (yes (_ , _ , A~B)) (no ¬p) noeqNe noeqℕ =
    no (λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ⊥-elim (let _ , neA' , _ = ne~↓! x
                                                            _ , _ , neB' = ne~↓! x₁
                                                        in noeqNe neA' neB' PE.refl) ;
            (_ , _ , cast-refl' x x₁ x₂) → ¬p (_ , _ , let _ , _ , neA = ne~↓! A~B
                                                           _ , var~t' , _ = [conv↓]ne neA x₁  
                                                           _ , var~t = neutral↓↑ var~t'
                                                       in var~t) ;
            (_ , _ , cast-refl x x₁ x₂) → ⊥-elim (let _ , neA' , neB' = ne~↓! x
                                                  in noeqNe neA' neB' PE.refl) ;
            (_ , _ , castℕ-refl x x₁) → ⊥-elim (noeqℕ PE.refl) })
  cast-refl'-dec neA neB _ _ ⊢e (no ¬AB) _ noeqNe noeqℕ =
    no (λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ⊥-elim (let _ , neA' , _ = ne~↓! x
                                                            _ , _ , neB' = ne~↓! x₁
                                                        in noeqNe neA' neB' PE.refl) ;
            (_ , _ , cast-refl' x x₁ x₂) → ¬AB (_ , _ , x) ;
            (_ , _ , cast-refl x x₁ x₂) → ⊥-elim (let _ , neA' , neB' = ne~↓! x
                                                  in noeqNe neA' neB' PE.refl) ;
            (_ , _ , castℕ-refl x x₁) → ⊥-elim (noeqℕ PE.refl) })

abstract
  castℕ-refl-dec : ∀ {Γ A t e u}
              → Neutral A
              → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
              → (noeqNeℕ : ∀ {A' t' e'} → Neutral A' → u PE.≡ cast ⁰ ℕ A' e' t' → ⊥)
              → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ u ~ cast ⁰ ℕ A e t ↑! U ^ lA)
  castℕ-refl-dec _ noeqNe noeqNeℕ noeqℕ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neA , neB = ne~↓! x in noeqNe neA neB PE.refl ;
                                                  (_ , _ , castℕ-refl x x₁) → noeqℕ PE.refl ;
                                                  (_ , _ , cast-ℕ x x₁ x₂ x₃) → let _ , _ , neA = ne~↓! x in noeqNeℕ neA PE.refl } )

  castℕ-refl'-dec : ∀ {Γ A t e u}
              → Neutral A
              → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
              → (noeqNeℕ : ∀ {A' t' e'} → Neutral A' → u PE.≡ cast ⁰ ℕ A' e' t' → ⊥)
              → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ ℕ A e t ~ u ↑! U ^ lA)
  castℕ-refl'-dec _ noeqNe noeqNeℕ noeqℕ = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neB , neA = ne~↓! x in noeqNe neA neB PE.refl ;
                                                   (_ , _ , castℕ-refl' x x₁) → noeqℕ PE.refl ;
                                                   (_ , _ , cast-ℕ x x₁ x₂ x₃) → let _ , neA , _ = ne~↓! x in noeqNeℕ neA PE.refl } )

  castneℕ-refl-dec : ∀ {Γ A t e u}
              → Neutral A
              → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
              → (noeqNeℕ : ∀ {A' t' e'} → Neutral A' → u PE.≡ cast ⁰ A' ℕ e' t' → ⊥)
              → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ u ~ cast ⁰ A ℕ e t ↑! U ^ lA)
  castneℕ-refl-dec _ noeqNe noeqNeℕ noeqℕ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neA , neB = ne~↓! x in noeqNe neA neB PE.refl ;
                                                  (_ , _ , castℕ-refl x x₁) → noeqℕ PE.refl ;
                                                  (_ , _ , cast-neℕ x x₁ x₂ x₃) → let _ , neA , _ = ne~↓! x in noeqNeℕ neA PE.refl } )

  castneℕ-refl'-dec : ∀ {Γ A t e u}
              → Neutral A
              → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
              → (noeqNeℕ : ∀ {A' t' e'} → Neutral A' → u PE.≡ cast ⁰ A' ℕ e' t' → ⊥)
              → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ A ℕ e t ~ u ↑! U ^ lA)
  castneℕ-refl'-dec _ noeqNe noeqNeℕ noeqℕ = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neB , neA = ne~↓! x in noeqNe neA neB PE.refl ;
                                                   (_ , _ , castℕ-refl' x x₁) → noeqℕ PE.refl ;
                                                   (_ , _ , cast-neℕ x x₁ x₂ x₃) → let _ , _ , neA = ne~↓! x in noeqNeℕ neA PE.refl } )


  castneΠ-refl-dec : ∀ {Γ A X Y rX t e u}
              → Neutral A
              → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
              → (noeqNeΠ : ∀ {A' X' Y' rX' t' e'} → Neutral A' → u PE.≡ cast ⁰ A' (Π X' ^ rX' ° ⁰ ▹ Y' ° ⁰ ° ⁰ ^ ! ) e' t' → ⊥)
              → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ u ~ cast ⁰ A (Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! ) e t ↑! U ^ lA)
  castneΠ-refl-dec _ noeqNe noeqNeΠ noeqℕ = no (λ { (_ , _ , cast-refl x x₁ x₂) → let _ , neA , neB = ne~↓! x in noeqNe neA neB PE.refl ;
                                                    (_ , _ , castℕ-refl x x₁) → noeqℕ PE.refl ;
                                                    (_ , _ , cast-neΠ x x₁ x₂ x₃ x₄) → let _ , neA , _ = ne~↓! x₁ in noeqNeΠ neA PE.refl } )

  castneΠ-refl'-dec : ∀ {Γ A X Y rX t e u}
              → Neutral A
              → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
              → (noeqNeΠ : ∀ {A' X' Y' rX' t' e'} → Neutral A' → u PE.≡ cast ⁰ A' (Π X' ^ rX' ° ⁰ ▹ Y' ° ⁰ ° ⁰ ^ ! ) e' t' → ⊥)
              → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ A (Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! ) e t ~ u ↑! U ^ lA)
  castneΠ-refl'-dec _ noeqNe noeqNeΠ noeqℕ = no (λ { (_ , _ , cast-refl' x x₁ x₂) → let _ , neB , neA = ne~↓! x in noeqNe neA neB PE.refl ;
                                                    (_ , _ , castℕ-refl' x x₁) → noeqℕ PE.refl ;
                                                    (_ , _ , cast-neΠ x x₁ x₂ x₃ x₄) → let _ , _ , neA = ne~↓! x₁ in noeqNeΠ neA PE.refl } )


abstract
  cast-cast-≡ : ∀ {Γ A A' B B' t t' e e' X lX}
                 → Γ ⊢ cast ⁰ A B e t ~ cast ⁰ A' B' e' t' ↑! X ^ lX
                 → Γ ⊢ B ≡ B' ^ [ ! , ι ⁰ ]
  cast-cast-≡ X =
    let cast≡cast = soundness~↑! X
        _ , ⊢cast , ⊢cast' = syntacticEqTerm cast≡cast
        _ , _ , _ , _ , ⊢t , R≡R , eqR , _ = inversion-cast ⊢cast
        _ , _ , _ , _ , _ , T≡T , eqT , _ = inversion-cast ⊢cast'
        eqR , el = typeinfo-PE-injectivity eqR
        eqT , _ = typeinfo-PE-injectivity eqT
        T≡T' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqT) T≡T
        R≡R' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqR) R≡R
    in T.trans (T.sym R≡R') T≡T'

abstract
  castℕℕ-refl-dec : ∀ {Γ t e u}
              → Γ ⊢ t ∷ ℕ ^ [ ! , ι ⁰ ]
              → (⊢e : Γ ⊢ e ∷ (Id (U ⁰) ℕ ℕ) ^ [ % , ι ⁰ ])
              → (dectu : Dec (∃ λ U → ∃ λ lA → Γ ⊢ t ~ u ↑! U ^ lA))
              → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
              → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ ℕ ℕ e t ~ u ↑! U ^ lA)
  castℕℕ-refl-dec x ⊢e (yes (_ , _ , p)) _ _ =
    let var≡t = soundness~↑! p
        ⊢K , ⊢t , ⊢u = syntacticEqTerm var≡t
        el , eA = type-uniq ⊢t x
        _ , whnfD , dd = whNormTerm (un-univ (PE.subst (λ X →  _ ⊢ _ ^ [ ! , X ]) el ⊢K))
        eA' = ℕ≡A (trans (sym (PE.subst (λ X →  _ ⊢ _ ≡  _ ^ [ ! , X ]) el eA)) (subset* (univ⇒* (redₜ dd)))) whnfD
    in yes ( _ , _ , castℕ-refl ([~] _ (univ⇒* (PE.subst (λ X → _ ⊢ _ ⇒* X ∷ Univ ! ⁰ ^ ι ¹) eA' (redₜ dd))) ℕₙ (PE.subst (λ X → _ ⊢ _ ~ _ ↑! _ ^  X) el p)) ⊢e)
  castℕℕ-refl-dec t~t' ⊢e (no ¬p) noeqNe noeqℕ =
    no (λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ⊥-elim (let _ , _ , neA' = ne~↓! x
                                                            _ , neB' , _ = ne~↓! x₁
                                                        in noeqNe neA' neB' PE.refl) ;
            (_ , _ , cast-refl () x₁ x₂) ;
            (_ , _ , cast-refl' x x₁ x₂) → ⊥-elim (let _ , neB' , neA' = ne~↓! x
                                                   in noeqNe neA' neB' PE.refl) ;
            (_ , _ , castℕ-refl ([~] A D whnfB k~l) x₁) → ¬p (_ , _ , k~l) ;
            (_ , _ , castℕ-refl' x x₁) → ⊥-elim (noeqℕ PE.refl) })

  castℕℕ-refl'-dec : ∀ {Γ t e u}
                 → Γ ⊢ t ∷ ℕ ^ [ ! , ι ⁰ ]
                 → (⊢e : Γ ⊢ e ∷ (Id (U ⁰) ℕ ℕ) ^ [ % , ι ⁰ ])
                 → (dectu : Dec (∃ λ U → ∃ λ lA → Γ ⊢ u ~ t ↑! U ^ lA))
                 → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
                 → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
                 → Dec (∃ λ U → ∃ λ lA → Γ ⊢ u ~ cast ⁰ ℕ ℕ e t ↑! U ^ lA)
  castℕℕ-refl'-dec x ⊢e (yes (_ , _ , p)) _ _ =
    let var≡t = soundness~↑! p
        ⊢K , ⊢u , ⊢t = syntacticEqTerm var≡t
        el , eA = type-uniq ⊢t x
        _ , whnfD , dd = whNormTerm (un-univ (PE.subst (λ X →  _ ⊢ _ ^ [ ! , X ]) el ⊢K))
        eA' = ℕ≡A (trans (sym (PE.subst (λ X →  _ ⊢ _ ≡  _ ^ [ ! , X ]) el eA)) (subset* (univ⇒* (redₜ dd)))) whnfD
    in yes ( _ , _ , castℕ-refl' ([~] _ (univ⇒* (PE.subst (λ X → _ ⊢ _ ⇒* X ∷ Univ ! ⁰ ^ ι ¹) eA' (redₜ dd))) ℕₙ (PE.subst (λ X → _ ⊢ _ ~ _ ↑! _ ^  X) el p)) ⊢e)

  castℕℕ-refl'-dec t~t' ⊢e (no ¬p) noeqNe noeqℕ =
    no (λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ⊥-elim (let _ , neA' , _ = ne~↓! x
                                                            _ , _ , neB' = ne~↓! x₁
                                                        in noeqNe neA' neB' PE.refl) ;
            (_ , _ , cast-refl' () x₁ x₂) ;
            (_ , _ , cast-refl x x₁ x₂) → ⊥-elim (let _ , neA' , neB' = ne~↓! x
                                                  in noeqNe neA' neB' PE.refl) ;
            (_ , _ , castℕ-refl' ([~] A D whnfB k~l) x₁) → ¬p (_ , _ , k~l) ;
            (_ , _ , castℕ-refl x x₁) → ⊥-elim (noeqℕ PE.refl) })

abstract
  cast-refl'-dec~ : ∀ {Γ A A' B B' t t' e u}
                 → Γ ⊢ A ~ A' ↓! U ⁰ ^ next ⁰
                 → Γ ⊢ B ~ B' ↓! U ⁰ ^ ι ¹
                 → Γ ⊢ t [conv↓] t' ∷ A ^ ι ⁰
                 → (⊢e : Γ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ])
                 → (decAB : Dec (∃ λ U → ∃ λ lA → Γ ⊢ B ~ A ↓! U ^ lA))
                 → (dectu : Dec (∃ λ U → ∃ λ lA → Γ ⊢ u ~ t ↑! U ^ lA))
                 → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
                 → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
                 → Dec (∃ λ U → ∃ λ lA → Γ ⊢ u ~ cast ⁰ A B e t ↑! U ^ lA)
  cast-refl'-dec~ A B t ⊢e decAB dectu noeqNe noeqℕ =
    let _ , neA , _ = ne~↓! A
        _ , neB , _ = ne~↓! B
        _ , ⊢B , _ = syntacticEqTerm (soundness~↓! B)
        _ , ⊢t , _ = syntacticEqTerm (soundnessConv↓Term t)
    in cast-refl'-dec neA neB ⊢B ⊢t ⊢e decAB dectu noeqNe noeqℕ

  cast-refl-dec~ : ∀ {Γ A A' B B' t t' e u}
                 → Γ ⊢ A ~ A' ↓! U ⁰ ^ next ⁰
                 → Γ ⊢ B ~ B' ↓! U ⁰ ^ ι ¹
                 → Γ ⊢ t [conv↓] t' ∷ A ^ ι ⁰
                 → (⊢e : Γ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ])
                 → (decAB : Dec (∃ λ U → ∃ λ lA → Γ ⊢ A ~ B ↓! U ^ lA))
                 → (dectu : Dec (∃ λ U → ∃ λ lA → Γ ⊢ t ~ u ↑! U ^ lA))
                 → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
                 → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
                 → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ A B e t ~ u ↑! U ^ lA)
  cast-refl-dec~ A B t ⊢e decAB dectu noeqNe noeqℕ =
    let _ , neA , _ = ne~↓! A
        _ , neB , _ = ne~↓! B
        _ , ⊢A , _ = syntacticEqTerm (soundness~↓! A)
        _ , ⊢t , _ = syntacticEqTerm (soundnessConv↓Term t)
    in cast-refl-dec neA neB ⊢A ⊢t ⊢e decAB dectu noeqNe noeqℕ

  castℕ-refl-dec~ : ∀ {Γ A A' t e u}
              → Γ ⊢ A ~ A' ↓! U ⁰ ^ next ⁰
              → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
              → (noeqNeℕ : ∀ {A' t' e'} → Neutral A' → u PE.≡ cast ⁰ ℕ A' e' t' → ⊥)
              → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ u ~ cast ⁰ ℕ A e t ↑! U ^ lA)
  castℕ-refl-dec~ A noeqNe noeqNeℕ noeqℕ = let _ , neA , _ = ne~↓! A in castℕ-refl-dec neA noeqNe noeqNeℕ noeqℕ

  castℕ-refl'-dec~ : ∀ {Γ A A' t e u}
              → Γ ⊢ A ~ A' ↓! U ⁰ ^ next ⁰
              → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
              → (noeqNeℕ : ∀ {A' t' e'} → Neutral A' → u PE.≡ cast ⁰ ℕ A' e' t' → ⊥)
              → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ ℕ A e t ~ u ↑! U ^ lA)
  castℕ-refl'-dec~ A noeqNe noeqNeℕ noeqℕ = let _ , neA , _ = ne~↓! A in castℕ-refl'-dec neA noeqNe noeqNeℕ noeqℕ

  castneℕ-refl-dec~ : ∀ {Γ A A' t e u}
              → Γ ⊢ A ~ A' ↓! U ⁰ ^ next ⁰
              → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
              → (noeqNeℕ : ∀ {A' t' e'} → Neutral A' → u PE.≡ cast ⁰ A' ℕ e' t' → ⊥)
              → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ u ~ cast ⁰ A ℕ e t ↑! U ^ lA)
  castneℕ-refl-dec~ A noeqNe noeqNeℕ noeqℕ = let _ , neA , _ = ne~↓! A in castneℕ-refl-dec neA noeqNe noeqNeℕ noeqℕ

  castneℕ-refl'-dec~ : ∀ {Γ A A' t e u}
              → Γ ⊢ A ~ A' ↓! U ⁰ ^ next ⁰
              → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
              → (noeqNeℕ : ∀ {A' t' e'} → Neutral A' → u PE.≡ cast ⁰ A' ℕ e' t' → ⊥)
              → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ A ℕ e t ~ u ↑! U ^ lA)
  castneℕ-refl'-dec~ A noeqNe noeqNeℕ noeqℕ = let _ , neA , _ = ne~↓! A in castneℕ-refl'-dec neA noeqNe noeqNeℕ noeqℕ

  castneΠ-refl-dec~ : ∀ {Γ A A' X Y rX t e u}
              → Γ ⊢ A ~ A' ↓! U ⁰ ^ next ⁰
              → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
              → (noeqNeΠ : ∀ {A' X' Y' rX' t' e'} → Neutral A' → u PE.≡ cast ⁰ A' (Π X' ^ rX' ° ⁰ ▹ Y' ° ⁰ ° ⁰ ^ ! ) e' t' → ⊥)
              → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ u ~ cast ⁰ A (Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! ) e t ↑! U ^ lA)
  castneΠ-refl-dec~ A noeqNe noeqNeΠ noeqℕ = let _ , neA , _ = ne~↓! A in castneΠ-refl-dec neA noeqNe noeqNeΠ noeqℕ 

  castneΠ-refl'-dec~ : ∀ {Γ A A' X Y rX t e u}
              → Γ ⊢ A ~ A' ↓! U ⁰ ^ next ⁰
              → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
              → (noeqNeΠ : ∀ {A' X' Y' rX' t' e'} → Neutral A' → u PE.≡ cast ⁰ A' (Π X' ^ rX' ° ⁰ ▹ Y' ° ⁰ ° ⁰ ^ ! ) e' t' → ⊥)
              → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ A (Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! ) e t ~ u ↑! U ^ lA)
  castneΠ-refl'-dec~ A noeqNe noeqNeΠ noeqℕ = let _ , neA , _ = ne~↓! A in castneΠ-refl'-dec neA noeqNe noeqNeΠ noeqℕ 


  castℕℕ-refl-dec~ : ∀ {Γ t t' e u}
              → Γ ⊢ t ~ t' ↓! ℕ ^ ι ⁰
              → (⊢e : Γ ⊢ e ∷ (Id (U ⁰) ℕ ℕ) ^ [ % , ι ⁰ ])
              → (dectu : Dec (∃ λ U → ∃ λ lA → Γ ⊢ t ~ u ↑! U ^ lA))
              → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
              → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ ℕ ℕ e t ~ u ↑! U ^ lA)
  castℕℕ-refl-dec~ X ⊢e dectu noeqNe noeqℕ = let _ , x , _ = syntacticEqTerm (soundness~↓! X) in castℕℕ-refl-dec x ⊢e dectu noeqNe noeqℕ

  castℕℕ-refl'-dec~ : ∀ {Γ t t' e u}
              → Γ ⊢ t ~ t' ↓! ℕ ^ ι ⁰
              → (⊢e : Γ ⊢ e ∷ (Id (U ⁰) ℕ ℕ) ^ [ % , ι ⁰ ])
              → (dectu : Dec (∃ λ U → ∃ λ lA → Γ ⊢ u ~ t ↑! U ^ lA))
              → (noeqNe : ∀ {A' B' t' e'} → Neutral A' → Neutral B' → u PE.≡ cast ⁰ A' B' e' t' → ⊥)
              → (noeqℕ : ∀ {t' e'} → u PE.≡ cast ⁰ ℕ ℕ e' t' → ⊥)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ u ~ cast ⁰ ℕ ℕ e t ↑! U ^ lA)
  castℕℕ-refl'-dec~ X ⊢e dectu noeqNe noeqℕ = let _ , x , _ = syntacticEqTerm (soundness~↓! X) in castℕℕ-refl'-dec x ⊢e dectu noeqNe noeqℕ


  cast-cast-dec : ∀ {Γ Δ A B t e C D u e'}
              → ⊢ Γ ≡ Δ
              → Neutral A
              → Neutral B
              → Neutral C
              → Neutral D
              → Γ ⊢ A ∷ Univ ! ⁰ ^ [ ! , ι ¹ ]
              → Γ ⊢ B ∷ Univ ! ⁰ ^ [ ! , ι ¹ ]
              → Δ ⊢ C ∷ Univ ! ⁰ ^ [ ! , ι ¹ ]
              → Δ ⊢ D ∷ Univ ! ⁰ ^ [ ! , ι ¹ ]
              → Γ ⊢ t ∷ A ^ [ ! , ι ⁰ ]
              → Δ ⊢ u ∷ C ^ [ ! , ι ⁰ ]
              → (⊢e : Γ ⊢ e ∷ (Id (U ⁰) A B) ^ [ % , ι ⁰ ])
              → (⊢e' : Δ ⊢ e' ∷ (Id (U ⁰) C D) ^ [ % , ι ⁰ ])
              → (decAB : Dec (∃ λ U → ∃ λ lA → Γ ⊢ A ~ C ↓! U ^ lA))
              → (decDB : Dec (∃ λ U → ∃ λ lA → Δ ⊢ D ~ B ↓! U ^ lA))
              → (decAC : Dec (∃ λ U → ∃ λ lA → Γ ⊢ A ~ B ↓! U ^ lA))
              → (decCD : Dec (∃ λ U → ∃ λ lA → Δ ⊢ C ~ D ↓! U ^ lA))
              → (dectu : (∃ λ U → ∃ λ lA → Γ ⊢ A ~ C ↓! U ^ lA) → Dec (Γ ⊢ t [conv↓] u ∷ A ^ ι ⁰))
              → (dectcast : Dec (∃ λ U → ∃ λ lA → Γ ⊢ t ~ cast ⁰ C D e' u ↑! U ^ lA))
              → (deccastu : Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ A B e t ~ u ↑! U ^ lA))
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ A B e t ~ cast ⁰ C D e' u ↑! U ^ lA)
  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u ⊢e ⊢e' _ (no ¬BD) _ _ _ _ _ =
    no λ { (_ , _ , X) → ¬BD (U ⁰ , ι ¹ , ~atU ⊢D
                                               let T≡R = sym (cast-cast-≡ X)
                                                   eq = completeEqNeutral neD neB (un-univ≡ (stabilityEq Γ≡Δ T≡R))
                                               in  _ , _ , eq) } 
  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u ⊢e ⊢e' (yes (_ , _ , A~C)) (yes (_ , _ , B~D)) (yes (_ , _ , A~B)) _ dectu _ _
    with dectu (_ , _ , A~C)
  ... | yes p = yes (_ , _ , cast-cong (~atU ⊢A (_ , _ , A~C)) (~atU (stabilityTerm (symConEq Γ≡Δ) ⊢D) (_ , _ , stability~↓! (symConEq Γ≡Δ) B~D)) p ⊢e (stabilityTerm (symConEq Γ≡Δ) ⊢e'))
  ... | no ¬p = no λ { (_ , _ , X) → let whnfcast , whnfcast' = ne~↑! X
                                         cast≡cast = soundness~↑! X
                                         A≡B = soundness~↓! (~atU ⊢A (_ , _ , A~B))
                                         A≡C = soundness~↓! (~atU ⊢A (_ , _ , A~C))
                                         B≡D = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! (~atU ⊢D (_ , _ , B~D))))
                                         C≡D = trans (sym (univ A≡C)) (trans (univ A≡B) (sym B≡D))
                                         _ , ⊢cast , ⊢cast' = syntacticEqTerm cast≡cast
                                         _ , _ , _ , _ , ⊢t , R≡R , eqR , _ = inversion-cast ⊢cast
                                         eqR , el = typeinfo-PE-injectivity eqR
                                         R≡R' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqR) R≡R
                                         cast≡cast' = PE.subst (λ X →  _ ⊢ _ ≡ _ ∷ _ ^ [ ! , X ]) el cast≡cast
                                         ⊢t' = PE.subst (λ X →  _ ⊢ _ ∷ _ ^ [ X , _ ]) (PE.sym eqR) ⊢t
                                         net = castNeutralInv neA neB whnfcast
                                         neu = castNeutralInv neC neD whnfcast'                                        
                                     in ¬p (completeEqTerm↓ (ne neA) (ne net) (ne neu)
                                                            (trans (sym (conv (T.cast-refl A≡B ⊢e ⊢t') (sym (univ A≡B))))
                                                            (trans (conv cast≡cast' (trans R≡R' (sym (univ A≡B))))
                                                            (conv (T.cast-refl (un-univ≡ C≡D) (stabilityTerm (symConEq Γ≡Δ) ⊢e') (stabilityTerm (symConEq Γ≡Δ) ⊢u))
                                                                  (trans B≡D (sym (univ A≡B))))))) }
  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u eAB eCD (no ¬AC) (yes B~D) (yes A~B) (yes C~D) _ _ _ =
    no λ { (_ , _ , X) → ¬AC (let _ , _ , _ , D~B = sym~↓! (reflConEq (wfTerm eCD)) (~atU ⊢D B~D)
                                  _ , _ , A~D , _ = trans~↓!-simpl (~atU ⊢A A~B) (stability~↓! (symConEq Γ≡Δ) D~B)
                                  _ , _ , _ , D~C = sym~↓! (reflConEq (wfTerm eCD)) (~atU ⊢C C~D)
                                  _ , _ , A~C , _ = trans~↓!-simpl A~D (stability~↓! (symConEq Γ≡Δ) D~C)
                              in _ , _ , A~C )}

  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u eAB eCD (yes A~C) (yes B~D) (no ¬AB) (yes C~D) _ _ _ =
    no λ { (_ , _ , X) → ¬AB (let _ , _ , A~D , _ = trans~↓!-simpl (~atU ⊢A A~C) (stability~↓! (symConEq Γ≡Δ) (~atU ⊢C C~D))
                                  _ , _ , A~B , _ = trans~↓!-simpl A~D (stability~↓! (symConEq Γ≡Δ) (~atU ⊢D B~D))
                              in _ , _ , A~B )}

  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u eAB eCD (no ¬AC) (yes B~D) (no ¬AB) (no ¬CD) _ _ _ =
    no λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ¬AC (_ , _ , x) ;
           (_ , _ , cast-refl x x₁ x₂) → ¬AB (_ , _ , x) ;
           (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , _ , D~B = sym~↓! Γ≡Δ (~atU (stabilityTerm (symConEq Γ≡Δ) ⊢D) (_ , _ , x))
                                          in ¬CD (_ , _ , D~B)}

  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u eAB eCD (no ¬AC) (yes B~D) (yes A~B) (no ¬CD) _ (yes (_ , _ , tu)) _ =
    yes (_ , _ , let t≡cast = soundness~↑! tu
                     ⊢K , _ , ⊢cast' = syntacticEqTerm t≡cast
                     _ , ⊢A' , ⊢B' , _ , ⊢t' , T≡T , eqT , _ = inversion-cast ⊢cast'
                     eqT , el = typeinfo-PE-injectivity eqT
                     _ , whnfD , dd = whNormTerm (un-univ (PE.subst (λ X →  _ ⊢ _ ^ [ ! , X ]) el ⊢K)) 
                     A≡B = soundness~↓! (~atU ⊢A A~B)
                     B≡D = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! (~atU ⊢D B~D)))
                  in cast-refl (~atU ⊢A A~B) (ne-ins ⊢t (conv (T.castⱼ (PE.subst (λ X →  _ ⊢ _ ∷ Univ X _ ^ _) (PE.sym eqT) ⊢A')
                                                                                                (PE.subst (λ X →  _ ⊢ _ ∷ Univ X _ ^ _) (PE.sym eqT) ⊢B')
                                                                                                (stabilityTerm (symConEq Γ≡Δ) eCD)
                                                                                                (PE.subst (λ X →  _ ⊢ _ ∷ _ ^ [ X , _ ]) (PE.sym eqT) ⊢t'))
                                                                                       (trans B≡D (sym (univ A≡B))))
                                                                          neA ([~] _ (red (univ:⇒*: dd)) whnfD (PE.subst (λ X →  _ ⊢ _ ~ _ ↑! _ ^ X) el tu)))
                                                     eAB)

  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u eAB eCD (no ¬AC) (yes B~D) (yes A~B) (no ¬CD) _ (no ¬tu) _ =
                 no λ { (_ , _ , X) → let whnfcast , whnfcast' = ne~↑! X
                                          cast≡cast = soundness~↑! X
                                          A≡B = soundness~↓! (~atU ⊢A A~B)
                                          B≡D = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! (~atU ⊢D B~D)))
                                          _ , ⊢cast , ⊢cast' = syntacticEqTerm cast≡cast
                                          _ , _ , _ , _ , ⊢t , R≡R , eqR , _ = inversion-cast ⊢cast
                                          _ , _ , _ , _ , _ , T≡T , eqT , _ = inversion-cast ⊢cast'
                                          eqR , el = typeinfo-PE-injectivity eqR
                                          eqT , _ = typeinfo-PE-injectivity eqT
                                          T≡T' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqT) T≡T
                                          R≡R' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqR) R≡R
                                          cast≡cast' = PE.subst (λ X →  _ ⊢ _ ≡ _ ∷ _ ^ [ ! , X ]) el cast≡cast
                                          ⊢t' = PE.subst (λ X →  _ ⊢ _ ∷ _ ^ [ X , _ ]) (PE.sym eqR) ⊢t
                                          net = castNeutralInv neA neB whnfcast
                                          neu = castNeutralInv neC neD whnfcast'                                        
                                       in ¬tu (let _ , e' , _ = [conv↓]ne neA (completeEqTerm↓ (ne neA) (ne net) (ne (castₙ neC neD neu))
                                                                                               (trans (sym (conv (T.cast-refl A≡B eAB ⊢t') (sym (univ A≡B)) ))
                                                                                                      (conv cast≡cast' (trans R≡R' (sym (univ A≡B))))))
                                                   _ , e = neutral↓↑ e' in _ , _ , e) }

  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u eAB eCD (no ¬AC) (yes B~D) (no ¬AB) (yes C~D) _ _ (yes (_ , _ , tu)) =
                           yes (_ , _ , let t≡cast = soundness~↑! tu
                                            ⊢K , ⊢cast , _ = syntacticEqTerm t≡cast
                                            _ , ⊢A' , ⊢B' , _ , ⊢t' , T≡T , eqT , _ = inversion-cast ⊢cast
                                            eqT , el = typeinfo-PE-injectivity eqT
                                            _ , _ , _ , D~C = sym~↓! (symConEq Γ≡Δ) (~atU ⊢C C~D)
                                            _ , whnfD , dd = whNormTerm (un-univ (PE.subst (λ X →  _ ⊢ _ ^ [ ! , X ]) el ⊢K)) 
                                            C≡D = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! (~atU ⊢C C~D)))
                                            B≡D = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! (~atU ⊢D B~D)))
                                            in cast-refl' (~atU (stabilityTerm (symConEq Γ≡Δ) ⊢D) (_ , _ , D~C))
                                                          (ne-ins (conv (T.castⱼ (PE.subst (λ X →  _ ⊢ _ ∷ Univ X _ ^ _) (PE.sym eqT) ⊢A')
                                                                                 (PE.subst (λ X →  _ ⊢ _ ∷ Univ X _ ^ _) (PE.sym eqT) ⊢B')
                                                                                 eAB
                                                                                 (PE.subst (λ X →  _ ⊢ _ ∷ _ ^ [ X , _ ]) (PE.sym eqT) ⊢t'))
                                                                        (trans (sym B≡D) (sym C≡D)))
                                                                  (stabilityTerm (symConEq Γ≡Δ) ⊢u)
                                                                  neC ([~] _ (red (univ:⇒*: dd)) whnfD (PE.subst (λ X →  _ ⊢ _ ~ _ ↑! _ ^ X) el tu)))
                                                          (stabilityTerm (symConEq Γ≡Δ) eCD))

  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u eAB eCD (no ¬AC) (yes B~D) (no ¬AB) (yes C~D) _ _ (no ¬tu) =
                 no λ { (_ , _ , X) → let whnfcast , whnfcast' = ne~↑! X
                                          cast≡cast = soundness~↑! X
                                          C≡D = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! (~atU ⊢C C~D)))
                                          B≡D = stabilityEq (symConEq Γ≡Δ) (univ (soundness~↓! (~atU ⊢D B~D)))
                                          _ , ⊢cast , ⊢cast' = syntacticEqTerm cast≡cast
                                          _ , _ , _ , _ , ⊢t , R≡R , eqR , _ = inversion-cast ⊢cast
                                          _ , _ , _ , _ , _ , T≡T , eqT , _ = inversion-cast ⊢cast'
                                          eqR , el = typeinfo-PE-injectivity eqR
                                          eqT , _ = typeinfo-PE-injectivity eqT
                                          T≡T' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqT) T≡T
                                          R≡R' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqR) R≡R
                                          cast≡cast' = PE.subst (λ X →  _ ⊢ _ ≡ _ ∷ _ ^ [ ! , X ]) el cast≡cast
                                          ⊢t' = PE.subst (λ X →  _ ⊢ _ ∷ _ ^ [ X , _ ]) (PE.sym eqR) ⊢t
                                          net = castNeutralInv neA neB whnfcast
                                          neu = castNeutralInv neC neD whnfcast'                                        
                                       in ¬tu (let _ , e' , _ = [conv↓]ne neB (completeEqTerm↓ (ne neB) (ne (castₙ neA neB net)) (ne neu)
                                                                                               (trans (conv cast≡cast' R≡R')
                                                                                                      (conv (T.cast-refl (un-univ≡ C≡D) (stabilityTerm (symConEq Γ≡Δ) eCD)
                                                                                                                         (stabilityTerm (symConEq Γ≡Δ) ⊢u))
                                                                                                            (trans (sym T≡T') R≡R'))))
                                                   _ , e = neutral↓↑ e' in _ , _ , e) } 

  cast-cast-dec Γ≡Δ neA neB neC neD ⊢A ⊢B ⊢C ⊢D ⊢t ⊢u ⊢e ⊢e' (yes (_ , _ , A~C)) (yes (_ , _ , B~D)) (no ¬AB) (no ¬CD) dectu _ _
    with dectu (_ , _ , A~C)
  ... | yes p = yes (_ , _ , cast-cong (~atU ⊢A (_ , _ , A~C)) (~atU (stabilityTerm (symConEq Γ≡Δ) ⊢D) (_ , _ , stability~↓! (symConEq Γ≡Δ) B~D)) p ⊢e (stabilityTerm (symConEq Γ≡Δ) ⊢e'))
  ... | no ¬p = no λ { (_ , _ , cast-cong x x₁ x₂ x₃ x₄) → ¬p x₂ ;
                       (_ , _ , cast-refl x x₁ x₂) → ¬AB (_ , _ , x) ;
                       (_ , _ , cast-refl' x x₁ x₂) → let _ , _ , _ , D~B = sym~↓! Γ≡Δ (~atU (stabilityTerm (symConEq Γ≡Δ) ⊢D) (_ , _ , x))
                                                      in ¬CD (_ , _ , D~B) }



abstract

  dec-var-var : ∀ {Γ Δ A A' x y x' y' l l'}
              → ⊢ Γ ≡ Δ
              → (⊢x : Γ ⊢ var x ∷ A ^ [ ! , l ])
              → (e : x PE.≡ y)
              → (⊢x' : Δ ⊢ var x' ∷ A' ^ [ ! , l' ])
              → (e' : x' PE.≡ y')
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ var x ~ var x' ↑! U ^ lA)
  dec-var-var {x = x} {x' = x'} Γ≡Δ ⊢x PE.refl ⊢y m≡m with x ≟ x'
  ... | yes PE.refl =  yes (_ , (_ , var-refl ⊢x PE.refl))
  ... | no ¬p = no λ (_ , (_ , eq)) → ¬p (strongVarEq eq)

  dec-castℕ-castℕ : ∀ {Γ Δ A A' t t' u u' B B' e e'}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ A' ~ A ↓! U ⁰ ^ next ⁰
              → Γ ⊢ t [conv↑] t' ∷ ℕ ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) ℕ A) ^ [ % , ι ⁰ ]
              → Δ ⊢ B' ~ B ↓! U ⁰ ^ next ⁰
              → Δ ⊢ u [conv↑] u' ∷ ℕ ^ ι ⁰
              → Δ ⊢ e' ∷ (Id (U ⁰) ℕ B) ^ [ % , ι ⁰ ]
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ B ~ A ↓! U ^ lA)
              → Dec (Γ ⊢ t [conv↑] u ∷ ℕ ^ ι ⁰)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ ℕ A e t ~ cast ⁰ ℕ B e' u ↑! U ^ lA)
  dec-castℕ-castℕ Γ≡Δ A t eℕA B u eℕB decAB dectu with decAB | dectu
  ... | yes AB | yes tu = yes (_ , _ , cast-ℕ (~atU-' A AB) tu eℕA (stabilityTerm (symConEq Γ≡Δ) eℕB))
  ... | yes AB | no ¬tu = no λ { (_ , _ , cast-ℕ x x₁ x₂ x₃) → ¬tu x₁ }
  ... | no ¬AB | _ = no λ { (_ , _ , cast-ℕ x x₁ x₂ x₃) → ¬AB (_ , _ , x) }


  dec-castΠ-castΠ : ∀ {Γ Δ A A' X rX Y X' Y' t t' u u' B B' Z rZ W Z' W' e e'}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ ! [conv↑] Π X' ^ rX ° ⁰ ▹ Y' ° ⁰ ° ⁰  ^ ! ∷ U ⁰ ^ next ⁰
              → Γ ⊢ A' ~ A ↓! U ⁰ ^ next ⁰
              → Γ ⊢ t [conv↑] t' ∷ Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ ! ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) (Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ !) A) ^ [ % , ι ⁰ ]
              → Δ ⊢ Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰  ^ ! [conv↑] Π Z' ^ rZ ° ⁰ ▹ W' ° ⁰ ° ⁰  ^ ! ∷ U ⁰ ^ next ⁰
              → Δ ⊢ B' ~ B ↓! U ⁰ ^ next ⁰
              → Δ ⊢ u [conv↑] u' ∷ Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰  ^ ! ^ ι ⁰
              → Δ ⊢ e' ∷ (Id (U ⁰) (Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰  ^ !) B) ^ [ % , ι ⁰ ]
              → Dec (Γ ⊢ Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! [conv↑] Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ ι ¹)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ B ~ A ↓! U ^ lA)
              → ((Γ ⊢ Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! [conv↑] Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ ι ¹) → Dec (Γ ⊢ t [conv↑] u ∷ Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ ! ^ ι ⁰))
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ (Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ !) A e t ~ cast ⁰ (Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰  ^ !) B e' u ↑! U ^ lA)
  dec-castΠ-castΠ {rX = rX} {rZ = rZ} Γ≡Δ Π A t eΠA Π' B u eΠB decΠΠ decAB dectu with dec-relevance rX rZ | decΠΠ | decAB
  ... | no ¬p | _ | _ = no λ { (_ , _ , cast-Π x x₁ x₂ x₃ x₄) → ¬p PE.refl }
  ... | yes PE.refl | no ¬ΠΠ′ | _ = no λ { (_ , _ , cast-Π x x₁ x₂ x₃ x₄) → ¬ΠΠ′ x }
  ... | yes PE.refl | yes ΠΠ′ | no ¬AB = no λ { (_ , _ , cast-Π x x₁ x₂ x₃ x₄) → ¬AB (_ , _ , x₁) }
  ... | yes PE.refl | yes ΠΠ′ | yes AB with dectu ΠΠ′
  ... | yes p = yes (_ , _ , cast-Π ΠΠ′ (~atU-' A AB) p eΠA (stabilityTerm (symConEq Γ≡Δ) eΠB))
  ... | no ¬p = no λ { (_ , _ , cast-Π x x₁ x₂ x₃ x₄) → ¬p x₂ }

  dec-castΠℕ-castΠℕ : ∀ {Γ Δ X rX Y X' Y' t t' u u' Z rZ W Z' W' e e'}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ ! [conv↑] Π X' ^ rX ° ⁰ ▹ Y' ° ⁰ ° ⁰  ^ ! ∷ U ⁰ ^ next ⁰
              → Γ ⊢ t [conv↑] t' ∷ Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ ! ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) (Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ !) ℕ) ^ [ % , ι ⁰ ]
              → Δ ⊢ Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰  ^ ! [conv↑] Π Z' ^ rZ ° ⁰ ▹ W' ° ⁰ ° ⁰  ^ ! ∷ U ⁰ ^ next ⁰
              → Δ ⊢ u [conv↑] u' ∷ Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰  ^ ! ^ ι ⁰
              → Δ ⊢ e' ∷ (Id (U ⁰) (Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰  ^ !) ℕ) ^ [ % , ι ⁰ ]
              → Dec (Γ ⊢ Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! [conv↑] Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ ι ¹)
              → ((Γ ⊢ Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! [conv↑] Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ ι ¹) → Dec (Γ ⊢ t [conv↑] u ∷ Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ ! ^ ι ⁰))
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ (Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ !) ℕ e t ~ cast ⁰ (Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰  ^ !) ℕ e' u ↑! U ^ lA)
  dec-castΠℕ-castΠℕ {rX = rX} {rZ = rZ} Γ≡Δ Π t eΠℕ Π' u eΠℕ′ decΠΠ dectu with dec-relevance rX rZ | decΠΠ 
  ... | no ¬p | _ = no λ { (_ , _ , cast-Πℕ x x₁ x₂ x₃) → ¬p PE.refl }
  ... | yes PE.refl | no ¬ΠΠ′ = no λ { (_ , _ , cast-Πℕ x x₁ x₂ x₃) → ¬ΠΠ′ x }
  ... | yes PE.refl | yes ΠΠ′ with dectu ΠΠ′
  ... | yes p = yes (_ , _ , cast-Πℕ ΠΠ′ p eΠℕ (stabilityTerm (symConEq Γ≡Δ) eΠℕ′))
  ... | no ¬p = no λ { (_ , _ , cast-Πℕ x x₁ x₂ x₃) → ¬p x₁ }

  dec-castℕΠ-castℕΠ : ∀ {Γ Δ X rX Y X' Y' t t' u u' Z rZ W Z' W' e e'}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ ! [conv↑] Π X' ^ rX ° ⁰ ▹ Y' ° ⁰ ° ⁰  ^ ! ∷ U ⁰ ^ next ⁰
              → Γ ⊢ t [conv↑] t' ∷ ℕ ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) ℕ (Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ !)) ^ [ % , ι ⁰ ]
              → Δ ⊢ Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰  ^ ! [conv↑] Π Z' ^ rZ ° ⁰ ▹ W' ° ⁰ ° ⁰  ^ ! ∷ U ⁰ ^ next ⁰
              → Δ ⊢ u [conv↑] u' ∷ ℕ ^ ι ⁰
              → Δ ⊢ e' ∷ (Id (U ⁰) ℕ (Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰  ^ !)) ^ [ % , ι ⁰ ]
              → Dec (Γ ⊢ Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰ ^ ! [conv↑] Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ ι ¹)
              → Dec (Γ ⊢ t [conv↑] u ∷ ℕ ^ ι ⁰)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ ℕ (Π X ^ rX ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ !) e t ~ cast ⁰ ℕ (Π Z ^ rZ ° ⁰ ▹ W ° ⁰ ° ⁰  ^ !) e' u ↑! U ^ lA)
  dec-castℕΠ-castℕΠ {rX = rX} {rZ = rZ} Γ≡Δ Π t eΠℕ Π' u eΠℕ′ decΠΠ dectu with dec-relevance rX rZ | decΠΠ | dectu
  ... | no ¬p | _ | _ = no λ { (_ , _ , cast-ℕΠ x x₁ x₂ x₃) → ¬p PE.refl }
  ... | yes PE.refl | no ¬ΠΠ′ | _ = no λ { (_ , _ , cast-ℕΠ x x₁ x₂ x₃) → ¬ΠΠ′ x }
  ... | yes PE.refl | yes ΠΠ′ | no ¬p = no λ { (_ , _ , cast-ℕΠ x x₁ x₂ x₃) → ¬p x₁ }
  ... | yes PE.refl | yes ΠΠ′ | yes p = yes (_ , _ , cast-ℕΠ ΠΠ′ p eΠℕ (stabilityTerm (symConEq Γ≡Δ) eΠℕ′))

  dec-castΠΠ%!-castΠΠ%! : ∀ {Γ Δ X Y A B t t' u u' Z W C D e e'}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ t [conv↑] t' ∷ Π X ^ % ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ ! ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) (Π X ^ % ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ !) (Π A ^ ! ° ⁰ ▹ B ° ⁰ ° ⁰  ^ !)) ^ [ % , ι ⁰ ]
              → Δ ⊢ u [conv↑] u' ∷ Π Z ^ % ° ⁰ ▹ W ° ⁰ ° ⁰  ^ ! ^ ι ⁰
              → Δ ⊢ e' ∷ (Id (U ⁰) (Π Z ^ % ° ⁰ ▹ W ° ⁰ ° ⁰  ^ !) (Π C ^ ! ° ⁰ ▹ D ° ⁰ ° ⁰  ^ !)) ^ [ % , ι ⁰ ]
              → Dec (Γ ⊢ Π X ^ % ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! [conv↑] Π Z ^ % ° ⁰ ▹ W ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ ι ¹)
              → Dec (Γ ⊢ Π C ^ ! ° ⁰ ▹ D ° ⁰ ° ⁰  ^ ! [conv↑] Π A ^ ! ° ⁰ ▹ B ° ⁰ ° ⁰  ^ ! ∷ U ⁰ ^ ι ¹)
              → ((Γ ⊢ Π X ^ % ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! [conv↑] Π Z ^ % ° ⁰ ▹ W ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ ι ¹) → Dec (Γ ⊢ t [conv↑] u ∷ Π X ^ % ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ ! ^ ι ⁰))
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ (Π X ^ % ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ !) (Π A ^ ! ° ⁰ ▹ B ° ⁰ ° ⁰  ^ !) e t ~ cast ⁰ (Π Z ^ % ° ⁰ ▹ W ° ⁰ ° ⁰  ^ !) (Π C ^ ! ° ⁰ ▹ D ° ⁰ ° ⁰  ^ !) e' u ↑! U ^ lA)
  dec-castΠΠ%!-castΠΠ%! Γ≡Δ t eAB u eCD decΠΠ decΠΠ' dectu with decΠΠ | decΠΠ' 
  ... | no ¬AC | _ = no λ { (_ , _ , cast-ΠΠ%! x x₁ x₂ x₃ x₄) → ¬AC x }
  ... | yes AC | no ¬BD = no λ { (_ , _ , cast-ΠΠ%! x x₁ x₂ x₃ x₄) → ¬BD x₁ }
  ... | yes AC | yes BD with dectu AC
  ... | yes p = yes (_ , _ , cast-ΠΠ%! AC BD p eAB (stabilityTerm (symConEq Γ≡Δ) eCD))
  ... | no ¬p = no λ { (_ , _ , cast-ΠΠ%! x x₁ x₂ x₃ x₄) → ¬p x₂ }

  dec-castΠΠ!%-castΠΠ!% : ∀ {Γ Δ X Y A B t t' u u' Z W C D e e'}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ t [conv↑] t' ∷ Π X ^ ! ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ ! ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) (Π X ^ ! ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ !) (Π A ^ % ° ⁰ ▹ B ° ⁰ ° ⁰  ^ !)) ^ [ % , ι ⁰ ]
              → Δ ⊢ u [conv↑] u' ∷ Π Z ^ ! ° ⁰ ▹ W ° ⁰ ° ⁰  ^ ! ^ ι ⁰
              → Δ ⊢ e' ∷ (Id (U ⁰) (Π Z ^ ! ° ⁰ ▹ W ° ⁰ ° ⁰  ^ !) (Π C ^ % ° ⁰ ▹ D ° ⁰ ° ⁰  ^ !)) ^ [ % , ι ⁰ ]
              → Dec (Γ ⊢ Π X ^ ! ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! [conv↑] Π Z ^ ! ° ⁰ ▹ W ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ ι ¹)
              → Dec (Γ ⊢ Π C ^ % ° ⁰ ▹ D ° ⁰ ° ⁰  ^ ! [conv↑] Π A ^ % ° ⁰ ▹ B ° ⁰ ° ⁰  ^ ! ∷ U ⁰ ^ ι ¹)
              → ((Γ ⊢ Π X ^ ! ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! [conv↑] Π Z ^ ! ° ⁰ ▹ W ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ ι ¹) → Dec (Γ ⊢ t [conv↑] u ∷ Π X ^ ! ° ⁰ ▹ Y ° ⁰ ° ⁰  ^ ! ^ ι ⁰))
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ (Π X ^ ! ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ !) (Π A ^ % ° ⁰ ▹ B ° ⁰ ° ⁰  ^ !) e t ~ cast ⁰ (Π Z ^ ! ° ⁰ ▹ W ° ⁰ ° ⁰  ^ !) (Π C ^ % ° ⁰ ▹ D ° ⁰ ° ⁰  ^ !) e' u ↑! U ^ lA)
  dec-castΠΠ!%-castΠΠ!% Γ≡Δ t eAB u eCD decΠΠ decΠΠ' dectu with decΠΠ | decΠΠ' 
  ... | no ¬AC | _ = no λ { (_ , _ , cast-ΠΠ!% x x₁ x₂ x₃ x₄) → ¬AC x }
  ... | yes AC | no ¬BD = no λ { (_ , _ , cast-ΠΠ!% x x₁ x₂ x₃ x₄) → ¬BD x₁ }
  ... | yes AC | yes BD with dectu AC
  ... | yes p = yes (_ , _ , cast-ΠΠ!% AC BD p eAB (stabilityTerm (symConEq Γ≡Δ) eCD))
  ... | no ¬p = no λ { (_ , _ , cast-ΠΠ!% x x₁ x₂ x₃ x₄) → ¬p x₂ }

  dec-castℕrefl-castℕrefl : ∀ {Γ Δ t t' v v' e e'}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ t ~ t' ↓! ℕ ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) ℕ ℕ) ^ [ % , ι ⁰ ]
              → Δ ⊢ v ~ v' ↓! ℕ ^ ι ⁰
              → Δ ⊢ e' ∷ (Id (U ⁰) ℕ ℕ) ^ [ % , ι ⁰ ]
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ t ~ v ↓! U ^ lA)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ ℕ ℕ e t ~ cast ⁰ ℕ ℕ e' v ↑! U ^ lA)
  dec-castℕrefl-castℕrefl Γ≡Δ t eℕℕ u eℕℕ′ dectu with dectu
  ... | yes tu = yes (_ , _ , let _ , ⊢t , _ = syntacticEqTerm (soundness~↓! t) in cast-ℕℕ (~atℕ ⊢t tu) eℕℕ (stabilityTerm (symConEq Γ≡Δ) eℕℕ′))
  ... | no ¬tu = no λ { (_ , _ , X) → let whnfcast , whnfcast' = ne~↑! X
                                          cast≡cast = soundness~↑! X
                                          _ , ⊢cast , ⊢cast' = syntacticEqTerm cast≡cast
                                          _ , _ , _ , _ , ⊢t , R≡R , eqR , _ = inversion-cast ⊢cast
                                          eqR , el = typeinfo-PE-injectivity eqR
                                          R≡R' = PE.subst (λ X →  _ ⊢ _ ≡ _ ^ [ X , ι _ ]) (PE.sym eqR) R≡R
                                          cast≡cast' = PE.subst (λ X →  _ ⊢ _ ≡ _ ∷ _ ^ [ ! , X ]) el cast≡cast
                                          ⊢t' = PE.subst (λ X →  _ ⊢ _ ∷ _ ^ [ X , _ ]) (PE.sym eqR) ⊢t
                                          net = castℕInv whnfcast
                                          neu = castℕInv whnfcast'                                        
                                          _ , ⊢u , _ = syntacticEqTerm (soundness~↓! u)
                                      in ¬tu (_ , _ , completeEqℕ net neu
                                                         (trans (sym (T.cast-refl (refl (ℕⱼ (wfTerm ⊢t))) eℕℕ ⊢t'))
                                                         (trans (conv cast≡cast' R≡R')
                                                                (T.cast-refl (refl (ℕⱼ (wfTerm ⊢t))) (stabilityTerm (symConEq Γ≡Δ) eℕℕ′) (stabilityTerm (symConEq Γ≡Δ) ⊢u))))) }

  dec-castneℕ-castneℕ : ∀ {Γ Δ A A' t t' e B B' v v' e'}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ A ~ A' ↓! U ⁰ ^ next ⁰
              → Γ ⊢ t [conv↑] t' ∷ A ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) A ℕ) ^ [ % , ι ⁰ ]
              → Δ ⊢ B ~ B' ↓! U ⁰ ^ next ⁰
              → Δ ⊢ v [conv↑] v' ∷ B ^ ι ⁰
              → Δ ⊢ e' ∷ (Id (U ⁰) B ℕ) ^ [ % , ι ⁰ ]
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ A ~ B ↓! U ^ lA)
              → ((∃ λ U → ∃ λ lA → Γ ⊢ A ~ B ↓! U ^ lA) → Dec (Γ ⊢ t [conv↑] v ∷ A ^ ι ⁰))
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ A ℕ e t ~ cast ⁰ B ℕ e' v ↑! U ^ lA)
  dec-castneℕ-castneℕ Γ≡Δ A t eℕA B u eℕB decAB dectu with decAB
  ... | no ¬AB = no λ { (_ , _ , cast-neℕ x x₁ x₂ x₃) → ¬AB (_ , _ , x) }
  ... | yes AB with dectu AB
  ... | yes tu = yes (_ , _ , cast-neℕ (~atU' A AB) tu eℕA (stabilityTerm (symConEq Γ≡Δ) eℕB))
  ... | no ¬tu = no λ { (_ , _ , cast-neℕ x x₁ x₂ x₃) → ¬tu x₁ }

  dec-castneΠ-castneΠ : ∀ {Γ Δ A A' X Y r t t' e B B' Z W r' v v' e'}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ A ~ A' ↓! U ⁰ ^ next ⁰
              → Γ ⊢ t [conv↑] t' ∷ A ^ ι ⁰
              → Γ ⊢ e ∷ (Id (U ⁰) A (Π X ^ r ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ !)) ^ [ % , ι ⁰ ]
              → Δ ⊢ B ~ B' ↓! U ⁰ ^ next ⁰
              → Δ ⊢ v [conv↑] v' ∷ B ^ ι ⁰
              → Δ ⊢ e' ∷ (Id (U ⁰) B ( Π Z ^ r' ° ⁰ ▹ W ° ⁰ ° ⁰ ^ !)) ^ [ % , ι ⁰ ]
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ A ~ B ↓! U ^ lA)
              → Dec (Γ ⊢ Π Z ^ r' ° ⁰ ▹ W ° ⁰ ° ⁰ ^ ! [conv↑] Π X ^ r ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ ! ∷ U ⁰ ^ ι ¹)
              → ((∃ λ U → ∃ λ lA → Γ ⊢ A ~ B ↓! U ^ lA) → Dec (Γ ⊢ t [conv↑] v ∷ A ^ ι ⁰))
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ cast ⁰ A (Π X ^ r ° ⁰ ▹ Y ° ⁰ ° ⁰ ^ !) e t ~ cast ⁰ B ( Π Z ^ r' ° ⁰ ▹ W ° ⁰ ° ⁰ ^ !) e' v ↑! U ^ lA)
  dec-castneΠ-castneΠ {r = r} {r' = r'} Γ≡Δ A t eℕA B u eℕB decAB decΠΠ dectu with dec-relevance r r' | decΠΠ | decAB
  ... | no ¬p | _ | _ = no λ { (_ , _ , cast-neΠ x x₁ x₂ x₃ x₄) → ¬p PE.refl }
  ... | yes PE.refl | no ¬ΠΠ′ | _ = no λ { (_ , _ , cast-neΠ x x₁ x₂ x₃ x₄) → ¬ΠΠ′ x }
  ... | yes PE.refl | yes ΠΠ′ | no ¬AB = no λ { (_ , _ , cast-neΠ x x₁ x₂ x₃ x₄) → ¬AB (_ , _ , x₁) }
  ... | yes PE.refl | yes ΠΠ′ | yes (_ , _ , AB) with dectu (_ , _ , AB)
  ... | yes tu = yes (_ , _ , cast-neΠ ΠΠ′ (~atU' A (_ , _ , AB)) tu eℕA (stabilityTerm (symConEq Γ≡Δ) eℕB))
  ... | no ¬tu = no λ { (_ , _ , cast-neΠ _ x x₁ x₂ x₃) → ¬tu x₁ }

abstract
  dec-natrec-natrec : ∀ {Γ Δ k l h g a₀ b₀ F G lF k' l' h' g' a₀' b₀' F' G' lF'}
              → ⊢ Γ ≡ Δ
              → Γ ∙ ℕ ^ [ ! , ι ⁰ ] ⊢ F [conv↑] G ^ [ ! , ι lF ]
              → Γ ⊢ a₀ [conv↑] b₀ ∷ F [ zero ] ^ ι lF
              → Γ ⊢ h [conv↑] g ∷ Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° lF ▹▹ F [ suc (var 0) ]↑ ° lF ° lF ^ !) ° lF ° lF ^ ! ^ ι lF
              → Γ ⊢ k ~ l ↓! ℕ ^ ι ⁰
              → Δ ∙ ℕ ^ [ ! , ι ⁰ ] ⊢ F' [conv↑] G' ^ [ ! , ι lF' ]
              → Δ ⊢ a₀' [conv↑] b₀' ∷ F' [ zero ] ^ ι lF'
              → Δ ⊢ h' [conv↑] g' ∷ Π ℕ ^ ! ° ⁰ ▹ (F' ^ ! ° lF' ▹▹ F' [ suc (var 0) ]↑ ° lF' ° lF' ^ !) ° lF' ° lF' ^ ! ^ ι lF'
              → Δ ⊢ k' ~ l' ↓! ℕ ^ ι ⁰
              → ((lF PE.≡ lF') → Dec (Γ ∙ ℕ ^ [ ! , ι ⁰ ] ⊢ F [conv↑] F' ^ [ ! , ι lF ]))
              → ((lF PE.≡ lF') → (Γ ∙ ℕ ^ [ ! , ι ⁰ ] ⊢ F [conv↑] F' ^ [ ! , ι lF ]) →
                     Dec (Γ ⊢ a₀ [conv↑] a₀' ∷ F [ zero ] ^ ι lF))
              → ((lF PE.≡ lF') → (Γ ∙ ℕ ^ [ ! , ι ⁰ ] ⊢ F [conv↑] F' ^ [ ! , ι lF ]) →
                     Dec (Γ ⊢ h [conv↑] h' ∷ Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° lF ▹▹ F [ suc (var 0) ]↑ ° lF ° lF ^ !) ° lF ° lF ^ ! ^ ι lF))
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ k ~ k' ↓! U ^ lA)
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ natrec lF F a₀ h k ~ natrec lF' F' a₀' h' k' ↑! U ^ lA)

  dec-natrec-natrec {lF = lF} {lF' = lF'} Γ≡Δ F a0 aS k G b0 bS k₀ decF deca dech deck with dec-level lF lF' 
  ... | no ¬p = no (λ { (_ , .(ι lF) , natrec-cong x x₁ x₂ x₃) → ¬p PE.refl })
  ... | yes PE.refl with decF PE.refl
  ... | no ¬p = no (λ { (_ , _ , natrec-cong x x₁ x₂ x₃) → ¬p x })
  ... | yes p with deca PE.refl p | dech PE.refl p | deck
  ... | yes p0 | yes pS | yes pK = yes (_ , _ , let _ , ⊢k , _ = syntacticEqTerm (soundness~↓! k) in natrec-cong p p0 pS (~atℕ ⊢k pK))
  ... | yes p0 | yes pS | no ¬pK = no (λ { (_ , _ , natrec-cong x x₁ x₂ x₃) → ¬pK (_ , _ , x₃) })
  ... | yes p0 | no ¬pS | _ = no (λ { (_ , _ , natrec-cong x x₁ x₂ x₃) → ¬pS x₂ })
  ... | no ¬p0 | _ | _ = no (λ { (_ , _ , natrec-cong x x₁ x₂ x₃) → ¬p0 x₁ })

  dec-emptyrec-emptyrec : ∀ {Γ Δ k l F G lF k' l' F' G' lF'}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ F [conv↑] G ^ [ ! , ι lF ]
              → Γ ⊢ k ~ l ↑% sEmpty ^ ι ⁰
              → Δ ⊢ F' [conv↑] G' ^ [ ! , ι lF' ]
              → Δ ⊢ k' ~ l' ↑% sEmpty ^ ι ⁰
              → ((lF PE.≡ lF') → Dec (Γ ⊢ F [conv↑] F' ^ [ ! , ι lF ]))
              → Dec (∃ λ U → ∃ λ lA → Γ ⊢ Emptyrec lF ⁰ F k ~ Emptyrec lF' ⁰ F' k' ↑! U ^ lA)
  dec-emptyrec-emptyrec {lF = lF} {lF' = lF'} Γ≡Δ F k G k₀ decF with dec-level lF lF' 
  ... | no ¬p = no (λ { (_ , .(ι lF) , Emptyrec-cong x x₁) → ¬p PE.refl })
  ... | yes PE.refl with decF PE.refl
  ... | yes p = let ⊢k , _  = soundness~↑% k
                    ⊢k₀ , _ = soundness~↑% k₀
                    ⊢Γ = wfTerm ⊢k
                in yes (_ , _ , Emptyrec-cong p (%~↑ ⊢k (stabilityTerm (symConEq Γ≡Δ) ⊢k₀)))
  ... | no ¬p = no (λ { (_ , .(ι lF) , Emptyrec-cong x x₁) → ¬p x })
