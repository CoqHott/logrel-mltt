{-# OPTIONS --safe #-}

module Definition.Conversion.Soundness where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Properties
open import Definition.Conversion
open import Definition.Conversion.Whnf
open import Definition.Typed.Consequences.InverseUniv
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.NeTypeEq

open import Tools.Product
import Tools.PropositionalEquality as PE


mutual
  -- Algorithmic equality of neutrals is well-formed.
  soundness~↑! : ∀ {k l A lA Γ} → Γ ⊢ k ~ l ↑! A ^ lA → Γ ⊢ k ≡ l ∷ A ^ [ ! , lA ]
  soundness~↑! (var-refl x x≡y) = PE.subst (λ y → _ ⊢ _ ≡ var y ∷ _ ^ _) x≡y (refl x)
  soundness~↑! (app-cong {rF = !} k~l x₁) = app-cong (soundness~↓! k~l) (soundnessConv↑Term x₁)
  soundness~↑! (app-cong {rF = %} k~l x₁) = app-cong (soundness~↓! k~l) (let _ , _ , y = soundness~↑% x₁ in y)
  soundness~↑! (natrec-cong x₁ x₂ x₃ k~l) =
    natrec-cong (soundnessConv↑ x₁) (soundnessConv↑Term x₂)
                (soundnessConv↑Term x₃) (soundness~↓! k~l)
  soundness~↑! (Emptyrec-cong x₁ k~l) = let ⊢k , ⊢l , _ = soundness~↑% k~l in
    Emptyrec-cong (soundnessConv↑ x₁) ⊢k ⊢l
  soundness~↑! (Id-cong X x x₁) = Id-cong (soundness~↓! X) (soundnessConv↑Term x) (soundnessConv↑Term x₁)
  soundness~↑! (Id-ℕ X x) = Id-cong (refl (ℕⱼ (wfEqTerm (soundness~↓! X)))) (soundness~↓! X) (soundnessConv↑Term x)
  soundness~↑! (Id-ℕ0 X) = let XX = soundness~↓! X in Id-cong (refl (ℕⱼ (wfEqTerm XX))) (refl (zeroⱼ (wfEqTerm XX))) XX
  soundness~↑! (Id-ℕS x X) = let XX = soundness~↓! X in Id-cong (refl (ℕⱼ (wfEqTerm XX))) (suc-cong (soundnessConv↑Term x)) XX
  soundness~↑! (Id-U X x) = Id-cong (refl (univ 0<1 (wfEqTerm (soundness~↓! X)))) (soundness~↓! X) (soundnessConv↑Term x)
  soundness~↑! (Id-Uℕ X) = let XX = soundness~↓! X in Id-cong (refl (univ 0<1 (wfEqTerm XX))) (refl (ℕⱼ (wfEqTerm XX))) XX
  soundness~↑! (Id-UΠ x X) = let XX = soundness~↓! X
                                 xx = soundnessConv↑Term x
                             in Id-cong (refl (univ 0<1 (wfEqTerm XX))) xx XX
  soundness~↑! (cast-cong X x x₁ x₂ x₃) = cast-cong (soundness~↓! X) (soundnessConv↑Term x) (soundnessConv↑Term x₁) x₂ x₃
  soundness~↑! (cast-ℕ X x x₁ x₂) = let XX = soundness~↓! X in cast-cong (refl (ℕⱼ (wfEqTerm XX))) XX (soundnessConv↑Term x) x₁ x₂
  soundness~↑! (cast-ℕℕ X x x₁) = let XX = soundness~↓! X in cast-cong (refl (ℕⱼ (wfEqTerm XX))) (refl (ℕⱼ (wfEqTerm XX))) XX x x₁
  soundness~↑! (cast-Π x X x₁ x₂ x₃) = cast-cong (soundnessConv↑Term x) (soundness~↓! X) (soundnessConv↑Term x₁) x₂ x₃
  soundness~↑! (cast-Πℕ x x₁ x₂ x₃) = let XX = (soundnessConv↑Term x) in cast-cong XX (refl (ℕⱼ (wfEqTerm XX))) (soundnessConv↑Term x₁) x₂ x₃
  soundness~↑! (cast-ℕΠ x x₁ x₂ x₃) = let XX = (soundnessConv↑Term x) in cast-cong (refl (ℕⱼ (wfEqTerm XX))) XX (soundnessConv↑Term x₁) x₂ x₃
  soundness~↑! (cast-ΠΠ%! x x₁ x₂ x₃ x₄) = cast-cong (soundnessConv↑Term x) (soundnessConv↑Term x₁) (soundnessConv↑Term x₂) x₃ x₄
  soundness~↑! (cast-ΠΠ!% x x₁ x₂ x₃ x₄) = cast-cong (soundnessConv↑Term x) (soundnessConv↑Term x₁) (soundnessConv↑Term x₂) x₃ x₄

  soundness~↑% : ∀ {k l A lA Γ} → Γ ⊢ k ~ l ↑% A ^ lA  →  Γ ⊢ k ∷ A ^ [ % , lA ] × Γ ⊢ l ∷ A ^ [ % , lA ] × Γ ⊢ k ≡ l ∷ A ^ [ % , lA ]
  soundness~↑% (%~↑ ⊢k ⊢l) =  ⊢k , ⊢l , proof-irrelevance ⊢k ⊢l

  soundness~↑ : ∀ {k l A rA lA Γ} → Γ ⊢ k ~ l ↑ A ^ [ rA , lA ] → Γ ⊢ k ≡ l ∷ A ^ [ rA , lA ]
  soundness~↑ (~↑! x) = soundness~↑! x
  soundness~↑ (~↑% x) = let _ , _ , y = soundness~↑% x in y

  -- Algorithmic equality of neutrals in WHNF is well-formed.
  soundness~↓! : ∀ {k l A lA Γ} → Γ ⊢ k ~ l ↓! A ^ lA → Γ ⊢ k ≡ l ∷ A ^ [ ! , lA ]
  soundness~↓! ([~] A₁ D whnfA k~l) = conv (soundness~↑! k~l) (subset* D)

  -- Algorithmic equality of types is well-formed.
  soundnessConv↑ : ∀ {A B rA Γ} → Γ ⊢ A [conv↑] B ^ rA → Γ ⊢ A ≡ B ^ rA
  soundnessConv↑ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) =
    trans (subset* D) (trans (soundnessConv↓ A′<>B′) (sym (subset* D′)))

  -- Algorithmic equality of types in WHNF is well-formed.
  soundnessConv↓ : ∀ {A B rA Γ} → Γ ⊢ A [conv↓] B ^ rA → Γ ⊢ A ≡ B ^ rA
  soundnessConv↓ (U-refl PE.refl ⊢Γ) = refl (Uⱼ ⊢Γ)
  soundnessConv↓ (univ x₂) = univ (soundnessConv↓Term x₂)

  -- Algorithmic equality of terms is well-formed.
  soundnessConv↑Term : ∀ {a b A lA Γ} → Γ ⊢ a [conv↑] b ∷ A ^ lA → Γ ⊢ a ≡ b ∷ A ^ [ ! , lA ]
  soundnessConv↑Term ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) =
    conv (trans (subset*Term d)
                (trans (soundnessConv↓Term t<>u)
                       (sym (subset*Term d′))))
         (sym (subset* D))

  -- Algorithmic equality of terms in WHNF is well-formed.
  soundnessConv↓Term : ∀ {a b A lA Γ} → Γ ⊢ a [conv↓] b ∷ A ^ lA → Γ ⊢ a ≡ b ∷ A ^ [ ! , lA ]
  soundnessConv↓Term (ne x) = soundness~↓! x
  soundnessConv↓Term (ℕ-refl ⊢Γ) = refl (ℕⱼ ⊢Γ)
  soundnessConv↓Term (Empty-refl PE.refl ⊢Γ) = refl (Emptyⱼ ⊢Γ)
  soundnessConv↓Term (Π-cong PE.refl PE.refl PE.refl PE.refl l< l<' F c c₁) =
    Π-cong l< l<' F (soundnessConv↑Term c) (soundnessConv↑Term c₁)
  soundnessConv↓Term (∃-cong PE.refl F c c₁) =
    ∃-cong F (soundnessConv↑Term c) (soundnessConv↑Term c₁)
  soundnessConv↓Term (ℕ-ins x) = soundness~↓! x
  -- soundnessConv↓Term (Empty-ins x) = soundness~↓% x
  soundnessConv↓Term (ne-ins t u x x₁) =
    let whnfM , neA , neB = ne~↓! x₁
        X = soundness~↓! x₁
        _ , t∷M , _ = syntacticEqTerm X
        _ , M≡A' = neTypeEq neA t∷M t -- soundnessConv↑ M≡A
    in conv X M≡A'
  soundnessConv↓Term (zero-refl ⊢Γ) = refl (zeroⱼ ⊢Γ)
  soundnessConv↓Term (suc-cong c) = suc-cong (soundnessConv↑Term c)
  soundnessConv↓Term (η-eq l< l<' F x x₁ y y₁ c) = η-eq l< l<' F x x₁ (soundnessConv↑Term c)
  soundnessConv↓Term (U-refl PE.refl ⊢Γ) = refl (univ 0<1 ⊢Γ)



app-cong′ : ∀ {Γ k l t v F rF lF G lG lΠ}
          → Γ ⊢ k ~ l ↓! Π F ^ rF ° lF ▹ G ° lG ° lΠ ^ ι lΠ
          → Γ ⊢ t [genconv↑] v ∷ F ^ [ rF , ι lF ]
          → Γ ⊢ k ∘ t ^ lΠ ~ l ∘ v ^ lΠ ↑ G [ t ] ^ [ ! , ι lG ]
app-cong′ k~l t=v = ~↑! (app-cong k~l t=v)

natrec-cong′ : ∀ {Γ k l h g a b F lF G}
             → Γ ∙ ℕ ^ [ ! , ι ⁰ ]  ⊢ F [conv↑] G ^ [ ! , ι lF ]
             → Γ ⊢ a [conv↑] b ∷ F [ zero ] ^ ι lF
             → Γ ⊢ h [conv↑] g ∷ Π ℕ ^ ! ° ⁰ ▹ (F ^ ! ° lF ▹▹ F [ suc (var 0) ]↑ ° lF ° lF) ° lF ° lF ^ ι lF
             → Γ ⊢ k ~ l ↓! ℕ ^ ι ⁰
             → Γ ⊢ natrec lF F a h k ~ natrec lF G b g l ↑ F [ k ] ^ [ ! , ι lF ]
natrec-cong′ F=G a=b h=g k~l = ~↑! (natrec-cong F=G a=b h=g k~l)

Emptyrec-cong′ : ∀ {Γ k l F lF lEmpty G}
               → Γ ⊢ F [conv↑] G ^ [ ! , ι lF ]
               → Γ ⊢ k ~ l ↑% Empty lEmpty ^ ι lEmpty
               → Γ ⊢ Emptyrec lF lEmpty F k ~ Emptyrec lF lEmpty G l ↑ F ^ [ ! , ι lF ]
Emptyrec-cong′ F=G k~l = ~↑! (Emptyrec-cong F=G k~l)
