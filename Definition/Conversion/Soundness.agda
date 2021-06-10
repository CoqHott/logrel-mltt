{-# OPTIONS --without-K  #-}

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
  soundness~↑𝕥y : ∀ {k l A Γ} → Γ ⊢ k ~ l ↑𝕥y A → Γ ⊢ k ≡ l ∷ A ⦂ 𝕥y
  soundness~↑𝕥y (var-refl x x≡y) = PE.subst (λ y → _ ⊢ _ ≡ var y ∷ _ ⦂ _) x≡y (refl x)
  soundness~↑𝕥y (app-cong k~l x₁) = app-cong (soundness~↓𝕥y k~l) (soundnessConv↑Term x₁)
  soundness~↑𝕥y (natrec-cong x₁ x₂ x₃ k~l) =
    natrec-cong (soundnessConv↑ x₁) (soundnessConv↑Term x₂)
                (soundnessConv↑Term x₃) (soundness~↓𝕥y k~l)
  soundness~↑𝕥y (Emptyrec-cong x₁ k~l) =
    Emptyrec-cong (soundnessConv↑ x₁) (soundness~↓𝕥y k~l)

  soundness~↑𝕥y : ∀ {k l A Γ} → Γ ⊢ k ~ l ↑𝕥y A → Γ ⊢ k ≡ l ∷ A ⦂ 𝕥y
  soundness~↑𝕥y (𝕥y~↑ neK neL ⊢k ⊢l) = proof-irrelevance ⊢k ⊢l

  soundness~↑ : ∀ {k l A sA Γ} → Γ ⊢ k ~ l ↑ A ⦂ sA → Γ ⊢ k ≡ l ∷ A ⦂ sA
  soundness~↑ (~↑𝕥y x) = soundness~↑𝕥y x
  soundness~↑ (~↑𝕥y x) = soundness~↑𝕥y x

  -- Algorithmic equality of neutrals in WHNF is well-formed.
  soundness~↓𝕥y : ∀ {k l A Γ} → Γ ⊢ k ~ l ↓𝕥y A → Γ ⊢ k ≡ l ∷ A ⦂ 𝕥y
  soundness~↓𝕥y ([~] A₁ D whnfA k~l) = conv (soundness~↑𝕥y k~l) (subset* D)

  soundness~↓𝕥y : ∀ {k l A Γ} → Γ ⊢ k ~ l ↓𝕥y A → Γ ⊢ k ≡ l ∷ A ⦂ 𝕥y
  soundness~↓𝕥y ([~] A₁ D whnfA k~l) = conv (soundness~↑𝕥y k~l) (subset* D)

  soundness~↓ : ∀ {k l A sA Γ} → Γ ⊢ k ~ l ↓ A ⦂ sA → Γ ⊢ k ≡ l ∷ A ⦂ sA
  soundness~↓ (~↓𝕥y x) = soundness~↓𝕥y x
  soundness~↓ (~↓𝕥y x) = soundness~↓𝕥y x

  -- Algorithmic equality of types is well-formed.
  soundnessConv↑ : ∀ {A B sA Γ} → Γ ⊢ A [conv↑] B ⦂ sA → Γ ⊢ A ≡ B ⦂ sA
  soundnessConv↑ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) =
    trans (subset* D) (trans (soundnessConv↓ A′<>B′) (sym (subset* D′)))

  -- Algorithmic equality of types in WHNF is well-formed.
  soundnessConv↓ : ∀ {A B sA Γ} → Γ ⊢ A [conv↓] B ⦂ sA → Γ ⊢ A ≡ B ⦂ sA
  soundnessConv↓ (U-refl PE.refl ⊢Γ) = refl (Uⱼ ⊢Γ)
  soundnessConv↓ (ℕ-refl ⊢Γ) = refl (ℕⱼ ⊢Γ)
  soundnessConv↓ (Empty-refl ⊢Γ) = refl (Emptyⱼ ⊢Γ)
  soundnessConv↓ (ne x) = univ (soundness~↓𝕥y x)
  soundnessConv↓ (Π-cong PE.refl F c c₁) =
    Π-cong F (soundnessConv↑ c) (soundnessConv↑ c₁)

  -- Algorithmic equality of terms is well-formed.
  soundnessConv↑Term : ∀ {a b A sA Γ} → Γ ⊢ a [conv↑] b ∷ A ⦂ sA → Γ ⊢ a ≡ b ∷ A ⦂ sA
  soundnessConv↑Term ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) =
    conv (trans (subset*Term d)
                (trans (soundnessConv↓Term t<>u)
                       (sym (subset*Term d′))))
         (sym (subset* D))

  -- Algorithmic equality of terms in WHNF is well-formed.
  soundnessConv↓Term : ∀ {a b A sA Γ} → Γ ⊢ a [conv↓] b ∷ A ⦂ sA → Γ ⊢ a ≡ b ∷ A ⦂ sA
  soundnessConv↓Term (ℕ-ins x) = soundness~↓𝕥y x
  soundnessConv↓Term (Empty-ins x) = soundness~↓𝕥y x
  soundnessConv↓Term (ne-ins t u x x₁) =
    let _ , neA , _ = ne~↓ x₁
        _ , t∷M , _ = syntacticEqTerm (soundness~↓ x₁)
        M≡A = neTypeEq neA t∷M t
    in  conv (soundness~↓ x₁) M≡A
  soundnessConv↓Term (univ x x₁ x₂) = inverseUnivEq x (soundnessConv↓ x₂)
  soundnessConv↓Term (zero-refl ⊢Γ) = refl (zeroⱼ ⊢Γ)
  soundnessConv↓Term (suc-cong c) = suc-cong (soundnessConv↑Term c)
  soundnessConv↓Term (η-eq F x x₁ y y₁ c) =
    η-eq F x x₁ (soundnessConv↑Term c)



app-cong′ : ∀ {Γ k l t v F sF G sG}
          → Γ ⊢ k ~ l ↓ Π F ⦂ sF ▹ G ⦂ sG
          → Γ ⊢ t [conv↑] v ∷ F ⦂ sF
          → Γ ⊢ k ∘ t ~ l ∘ v ↑ G [ t ] ⦂ sG
app-cong′ (~↓𝕥y k~l) t=v = ~↑𝕥y (app-cong k~l t=v)
app-cong′ (~↓𝕥y k~l) t=v =
  let _ , neK , neL = ne~↓𝕥y k~l
      k≡l = soundness~↓𝕥y k~l
      t≡v = soundnessConv↑Term t=v
      _ , ⊢₁ , ⊢₂ = syntacticEqTerm (app-cong k≡l t≡v)
  in ~↑𝕥y (𝕥y~↑ (∘ₙ neK) (∘ₙ neL) ⊢₁ ⊢₂)

natrec-cong′ : ∀ {Γ k l h g a b F G s}
             → Γ ∙ ℕ ⦂ 𝕥y ⊢ F [conv↑] G ⦂ s
             → Γ ⊢ a [conv↑] b ∷ F [ zero ] ⦂ s
             → Γ ⊢ h [conv↑] g ∷ Π ℕ ⦂ 𝕥y ▹ (F ⦂ s ▹▹ F [ suc (var 0) ]↑) ⦂ s
             → Γ ⊢ k ~ l ↓ ℕ ⦂ 𝕥y
             → Γ ⊢ natrec F a h k ~ natrec G b g l ↑ F [ k ] ⦂ s
natrec-cong′ {s = 𝕥y} F=G a=b h=g (~↓𝕥y k~l) = ~↑𝕥y (natrec-cong F=G a=b h=g k~l)
natrec-cong′ {F = F} {G = G} {s = 𝕥y} F=G a=b h=g k~l =
  let _ , neK , neL = ne~↓ k~l
      F≡G = soundnessConv↑ F=G
      a≡b = soundnessConv↑Term a=b
      h≡g = soundnessConv↑Term h=g
      k≡l = soundness~↓ k~l
      _ , ⊢₁ , ⊢₂ = syntacticEqTerm (natrec-cong F≡G a≡b h≡g k≡l)
  in ~↑𝕥y (𝕥y~↑ (natrecₙ neK) (natrecₙ neL) ⊢₁ ⊢₂)

Emptyrec-cong′ : ∀ {Γ k l F G s}
               → Γ ⊢ F [conv↑] G ⦂ s
               → Γ ⊢ k ~ l ↓ Empty ⦂ 𝕥y
               → Γ ⊢ Emptyrec F k ~ Emptyrec G l ↑ F ⦂ s
Emptyrec-cong′ {s = 𝕥y} F=G (~↓𝕥y k~l) = ~↑𝕥y (Emptyrec-cong F=G k~l)
Emptyrec-cong′ {s = 𝕥y} F=G k~l =
  let _ , neK , neL = ne~↓ k~l
      F≡G = soundnessConv↑ F=G
      k≡l = soundness~↓ k~l
      _ , ⊢₁ , ⊢₂ = syntacticEqTerm (Emptyrec-cong F≡G k≡l)
  in ~↑𝕥y (𝕥y~↑ (Emptyrecₙ neK) (Emptyrecₙ neL) ⊢₁ ⊢₂)
