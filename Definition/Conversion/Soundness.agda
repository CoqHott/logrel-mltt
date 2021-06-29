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
  soundness~↑! : ∀ {k l A Γ} → Γ ⊢ k ~ l ↑! A → Γ ⊢ k ≡ l ∷ A ^ !
  soundness~↑! (var-refl x x≡y) = PE.subst (λ y → _ ⊢ _ ≡ var y ∷ _ ^ _) x≡y (refl x)
  soundness~↑! (app-cong {rF = !} k~l x₁) = app-cong (soundness~↓! k~l) (soundnessConv↑Term x₁)
  soundness~↑! (app-cong {rF = %} k~l x₁) = app-cong (soundness~↓! k~l) (soundness~↑% x₁)
  soundness~↑! (natrec-cong x₁ x₂ x₃ k~l) =
    natrec-cong (soundnessConv↑ x₁) (soundnessConv↑Term x₂)
                (soundnessConv↑Term x₃) (soundness~↓! k~l)
  soundness~↑! (Emptyrec-cong x₁ k~l) =
    Emptyrec-cong (soundnessConv↑ x₁) (soundness~↑% k~l)

  soundness~↑% : ∀ {k l A Γ} → Γ ⊢ k ~ l ↑% A → Γ ⊢ k ≡ l ∷ A ^ %
  soundness~↑% (%~↑ ⊢k ⊢l) = proof-irrelevance ⊢k ⊢l

  soundness~↑ : ∀ {k l A rA Γ} → Γ ⊢ k ~ l ↑ A ^ rA → Γ ⊢ k ≡ l ∷ A ^ rA
  soundness~↑ (~↑! x) = soundness~↑! x
  soundness~↑ (~↑% x) = soundness~↑% x

  -- Algorithmic equality of neutrals in WHNF is well-formed.
  soundness~↓! : ∀ {k l A Γ} → Γ ⊢ k ~ l ↓! A → Γ ⊢ k ≡ l ∷ A ^ !
  soundness~↓! ([~] A₁ D whnfA k~l) = conv (soundness~↑! k~l) (subset* D)

  -- Algorithmic equality of types is well-formed.
  soundnessConv↑ : ∀ {A B rA Γ} → Γ ⊢ A [conv↑] B ^ rA → Γ ⊢ A ≡ B ^ rA
  soundnessConv↑ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) =
    trans (subset* D) (trans (soundnessConv↓ A′<>B′) (sym (subset* D′)))

  -- Algorithmic equality of types in WHNF is well-formed.
  soundnessConv↓ : ∀ {A B rA Γ} → Γ ⊢ A [conv↓] B ^ rA → Γ ⊢ A ≡ B ^ rA
  soundnessConv↓ (U-refl PE.refl ⊢Γ) = refl (Uⱼ ⊢Γ)
  soundnessConv↓ (ℕ-refl ⊢Γ) = refl (ℕⱼ ⊢Γ)
  soundnessConv↓ (Empty-refl ⊢Γ) = refl (Emptyⱼ ⊢Γ)
  soundnessConv↓ (ne x) = univ (soundness~↓! x)
  soundnessConv↓ (Π-cong PE.refl F c c₁) =
    Π-cong F (soundnessConv↑ c) (soundnessConv↑ c₁)

  -- Algorithmic equality of terms is well-formed.
  soundnessConv↑Term : ∀ {a b A Γ} → Γ ⊢ a [conv↑] b ∷ A → Γ ⊢ a ≡ b ∷ A ^ !
  soundnessConv↑Term ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) =
    conv (trans (subset*Term d)
                (trans (soundnessConv↓Term t<>u)
                       (sym (subset*Term d′))))
         (sym (subset* D))

  -- Algorithmic equality of terms in WHNF is well-formed.
  soundnessConv↓Term : ∀ {a b A Γ} → Γ ⊢ a [conv↓] b ∷ A → Γ ⊢ a ≡ b ∷ A ^ !
  soundnessConv↓Term (ℕ-ins x) = soundness~↓! x
  -- soundnessConv↓Term (Empty-ins x) = soundness~↓% x
  soundnessConv↓Term (ne-ins t u x x₁) =
    let _ , neA , _ = ne~↓ x₁
        _ , t∷M , _ = syntacticEqTerm (soundness~↓! x₁)
        M≡A = neTypeEq neA t∷M t
    in  conv (soundness~↓! x₁) M≡A
  soundnessConv↓Term (univ x x₁ x₂) = inverseUnivEq x (soundnessConv↓ x₂)
  soundnessConv↓Term (zero-refl ⊢Γ) = refl (zeroⱼ ⊢Γ)
  soundnessConv↓Term (suc-cong c) = suc-cong (soundnessConv↑Term c)
  soundnessConv↓Term (η-eq F x x₁ y y₁ c) =
    η-eq F x x₁ (soundnessConv↑Term c)



app-cong′ : ∀ {Γ k l t v F rF G}
          → Γ ⊢ k ~ l ↓! Π F ^ rF ▹ G
          → Γ ⊢ t [genconv↑] v ∷ F ^ rF 
          → Γ ⊢ k ∘ t ~ l ∘ v ↑ G [ t ] ^ !
app-cong′ k~l t=v = ~↑! (app-cong k~l t=v)

natrec-cong′ : ∀ {Γ k l h g a b F G}
             → Γ ∙ ℕ ^ ! ⊢ F [conv↑] G ^ !
             → Γ ⊢ a [conv↑] b ∷ F [ zero ] 
             → Γ ⊢ h [conv↑] g ∷ Π ℕ ^ ! ▹ (F ^ ! ▹▹ F [ suc (var 0) ]↑) 
             → Γ ⊢ k ~ l ↓! ℕ 
             → Γ ⊢ natrec F a h k ~ natrec G b g l ↑ F [ k ] ^ !
natrec-cong′ F=G a=b h=g k~l = ~↑! (natrec-cong F=G a=b h=g k~l)

Emptyrec-cong′ : ∀ {Γ k l F G}
               → Γ ⊢ F [conv↑] G ^ !
               → Γ ⊢ k ~ l ↑% Empty 
               → Γ ⊢ Emptyrec F k ~ Emptyrec G l ↑ F ^ !
Emptyrec-cong′ F=G k~l = ~↑! (Emptyrec-cong F=G k~l)
