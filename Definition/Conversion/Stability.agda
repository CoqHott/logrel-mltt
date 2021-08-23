{-# OPTIONS --safe #-}

module Definition.Conversion.Stability where

open import Definition.Untyped
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Conversion
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Substitution

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Equality of contexts.
data ⊢_≡_ : (Γ Δ : Con Term) → Set where
  ε : ⊢ ε ≡ ε
  _∙_ : ∀ {Γ Δ A B r} → ⊢ Γ ≡ Δ → Γ ⊢ A ≡ B ^ r → ⊢ Γ ∙ A ^ r ≡ Δ ∙ B ^ r

mutual
  -- Syntactic validity and conversion substitution of a context equality.
  contextConvSubst : ∀ {Γ Δ} → ⊢ Γ ≡ Δ → ⊢ Γ × ⊢ Δ × Δ ⊢ˢ idSubst ∷ Γ
  contextConvSubst ε = ε , ε , id
  contextConvSubst (_∙_ {Γ} {Δ} {A} {B} Γ≡Δ A≡B) =
    let ⊢Γ , ⊢Δ , [σ] = contextConvSubst Γ≡Δ
        ⊢A , ⊢B = syntacticEq A≡B
        Δ⊢B = stability Γ≡Δ ⊢B
    in  ⊢Γ ∙ ⊢A , ⊢Δ ∙ Δ⊢B
        , (wk1Subst′ ⊢Γ ⊢Δ Δ⊢B [σ]
        , conv (var (⊢Δ ∙ Δ⊢B) here)
               (PE.subst (λ x → _ ⊢ _ ≡ x ^ _)
                         (wk1-tailId A)
                         (wkEq (step id) (⊢Δ ∙ Δ⊢B) (stabilityEq Γ≡Δ (sym A≡B)))))

  -- Stability of types under equal contexts.
  stability : ∀ {A rA Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ A ^ rA → Δ ⊢ A ^ rA
  stability Γ≡Δ A =
    let ⊢Γ , ⊢Δ , σ = contextConvSubst Γ≡Δ
        q = substitution A σ ⊢Δ
    in  PE.subst (λ x → _ ⊢ x ^ _) (subst-id _) q

  -- Stability of type equality.
  stabilityEq : ∀ {A B rA Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ A ≡ B ^ rA → Δ ⊢ A ≡ B ^ rA
  stabilityEq Γ≡Δ A≡B =
    let ⊢Γ , ⊢Δ , σ = contextConvSubst Γ≡Δ
        q = substitutionEq A≡B (substRefl σ) ⊢Δ
    in  PE.subst₂ (λ x y → _ ⊢ x ≡ y ^ _) (subst-id _) (subst-id _) q

-- Reflexivity of context equality.
reflConEq : ∀ {Γ} → ⊢ Γ → ⊢ Γ ≡ Γ
reflConEq ε = ε
reflConEq (⊢Γ ∙ ⊢A) = reflConEq ⊢Γ ∙ refl ⊢A

-- Symmetry of context equality.
symConEq : ∀ {Γ Δ} → ⊢ Γ ≡ Δ → ⊢ Δ ≡ Γ
symConEq ε = ε
symConEq (Γ≡Δ ∙ A≡B) = symConEq Γ≡Δ ∙ stabilityEq Γ≡Δ (sym A≡B)

-- Stability of terms.
stabilityTerm : ∀ {t A rA Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ t ∷ A ^ rA → Δ ⊢ t ∷ A ^ rA
stabilityTerm Γ≡Δ t =
  let ⊢Γ , ⊢Δ , σ = contextConvSubst Γ≡Δ
      q = substitutionTerm t σ ⊢Δ
  in  PE.subst₂ (λ x y → _ ⊢ x ∷ y ^ _) (subst-id _) (subst-id _) q

-- Stability of term reduction.
stabilityRedTerm : ∀ {t u A Γ Δ l} → ⊢ Γ ≡ Δ → Γ ⊢ t ⇒ u ∷ A ^ l → Δ ⊢ t ⇒ u ∷ A ^ l
stabilityRedTerm Γ≡Δ (conv d x) =
  conv (stabilityRedTerm Γ≡Δ d) (stabilityEq Γ≡Δ x)
stabilityRedTerm Γ≡Δ (app-subst d x) =
  app-subst (stabilityRedTerm Γ≡Δ d) (stabilityTerm Γ≡Δ x)
stabilityRedTerm Γ≡Δ (β-red l< l<' x x₁ x₂) =
  β-red l< l<' (stability Γ≡Δ x) (stabilityTerm (Γ≡Δ ∙ refl x) x₁)
        (stabilityTerm Γ≡Δ x₂)
stabilityRedTerm Γ≡Δ (natrec-subst x x₁ x₂ d) =
  let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
  in  natrec-subst (stability (Γ≡Δ ∙ refl (univ (ℕⱼ ⊢Γ))) x) (stabilityTerm Γ≡Δ x₁)
                   (stabilityTerm Γ≡Δ x₂) (stabilityRedTerm Γ≡Δ d)
stabilityRedTerm Γ≡Δ (natrec-zero x x₁ x₂) =
  let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
  in  natrec-zero (stability (Γ≡Δ ∙ refl (univ (ℕⱼ ⊢Γ))) x) (stabilityTerm Γ≡Δ x₁)
                  (stabilityTerm Γ≡Δ x₂)
stabilityRedTerm Γ≡Δ (natrec-suc x x₁ x₂ x₃) =
  let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
  in  natrec-suc (stabilityTerm Γ≡Δ x) (stability (Γ≡Δ ∙ refl (univ (ℕⱼ ⊢Γ))) x₁)
                 (stabilityTerm Γ≡Δ x₂) (stabilityTerm Γ≡Δ x₃)
stabilityRedTerm Γ≡Δ (Id-subst X x x₁) = Id-subst (stabilityRedTerm Γ≡Δ X) (stabilityTerm Γ≡Δ x) (stabilityTerm Γ≡Δ x₁)
stabilityRedTerm Γ≡Δ (Id-ℕ-subst X x) = Id-ℕ-subst (stabilityRedTerm Γ≡Δ X) (stabilityTerm Γ≡Δ x)
stabilityRedTerm Γ≡Δ (Id-ℕ-0-subst X) = Id-ℕ-0-subst (stabilityRedTerm Γ≡Δ X)
stabilityRedTerm Γ≡Δ (Id-ℕ-S-subst x X) = Id-ℕ-S-subst (stabilityTerm Γ≡Δ x) (stabilityRedTerm Γ≡Δ X)
stabilityRedTerm Γ≡Δ (Id-U-subst X x) = Id-U-subst (stabilityRedTerm Γ≡Δ X) (stabilityTerm Γ≡Δ x)
stabilityRedTerm Γ≡Δ (Id-U-ℕ-subst X) = Id-U-ℕ-subst (stabilityRedTerm Γ≡Δ X) 
stabilityRedTerm Γ≡Δ (Id-U-Π-subst x x₁ X) = Id-U-Π-subst (stabilityTerm Γ≡Δ x) (stabilityTerm (Γ≡Δ ∙ refl (univ x)) x₁) (stabilityRedTerm Γ≡Δ X)
stabilityRedTerm Γ≡Δ (Id-Π l< l<' x x₁ x₂ x₃) = Id-Π l< l<' (stabilityTerm Γ≡Δ x) (stabilityTerm (Γ≡Δ ∙ refl (univ x)) x₁) (stabilityTerm Γ≡Δ x₂) (stabilityTerm Γ≡Δ x₃)
stabilityRedTerm Γ≡Δ (Id-ℕ-00 x) = let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ in Id-ℕ-00 ⊢Δ
stabilityRedTerm Γ≡Δ (Id-ℕ-SS x x₁) = Id-ℕ-SS (stabilityTerm Γ≡Δ x) (stabilityTerm Γ≡Δ x₁)
stabilityRedTerm Γ≡Δ (Id-U-ΠΠ x x₁ x₂ x₃) = Id-U-ΠΠ (stabilityTerm Γ≡Δ x) (stabilityTerm (Γ≡Δ ∙ refl (univ x)) x₁) (stabilityTerm Γ≡Δ x₂) (stabilityTerm (Γ≡Δ ∙ refl (univ x₂)) x₃)
stabilityRedTerm Γ≡Δ (Id-U-ℕℕ x) = let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ in Id-U-ℕℕ ⊢Δ
stabilityRedTerm Γ≡Δ (Id-SProp x x₁) = Id-SProp (stabilityTerm Γ≡Δ x) (stabilityTerm Γ≡Δ x₁)
stabilityRedTerm Γ≡Δ (Id-ℕ-0S x) = Id-ℕ-0S (stabilityTerm Γ≡Δ x)
stabilityRedTerm Γ≡Δ (Id-ℕ-S0 x) = Id-ℕ-S0 (stabilityTerm Γ≡Δ x)
stabilityRedTerm Γ≡Δ (Id-U-ℕΠ x x₁) = Id-U-ℕΠ (stabilityTerm Γ≡Δ x) (stabilityTerm (Γ≡Δ ∙ refl (univ x)) x₁)
stabilityRedTerm Γ≡Δ (Id-U-Πℕ x x₁) = Id-U-Πℕ (stabilityTerm Γ≡Δ x) (stabilityTerm (Γ≡Δ ∙ refl (univ x)) x₁)
stabilityRedTerm Γ≡Δ (Id-U-ΠΠ!% x x₁ x₂ x₃ x₄) =
  Id-U-ΠΠ!% x (stabilityTerm Γ≡Δ x₁) (stabilityTerm (Γ≡Δ ∙ refl (univ x₁)) x₂) (stabilityTerm Γ≡Δ x₃) (stabilityTerm (Γ≡Δ ∙ refl (univ x₃)) x₄)
stabilityRedTerm Γ≡Δ (cast-subst X x x₁ x₂) = cast-subst (stabilityRedTerm Γ≡Δ X) (stabilityTerm Γ≡Δ x) (stabilityTerm Γ≡Δ x₁) (stabilityTerm Γ≡Δ x₂)
stabilityRedTerm Γ≡Δ (cast-ℕ-subst X x x₁) =
  cast-ℕ-subst (stabilityRedTerm Γ≡Δ X) (stabilityTerm Γ≡Δ x) (stabilityTerm Γ≡Δ x₁)
stabilityRedTerm Γ≡Δ (cast-Π-subst x x₁ X x₂ x₃) =
  cast-Π-subst (stabilityTerm Γ≡Δ x) (stabilityTerm (Γ≡Δ ∙ refl (univ x)) x₁) (stabilityRedTerm Γ≡Δ X) (stabilityTerm Γ≡Δ x₂) (stabilityTerm Γ≡Δ x₃)
stabilityRedTerm Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄ x₅) =
  cast-Π (stabilityTerm Γ≡Δ x) (stabilityTerm (Γ≡Δ ∙ refl (univ x)) x₁) (stabilityTerm Γ≡Δ x₂) (stabilityTerm (Γ≡Δ ∙ refl (univ x₂)) x₃) (stabilityTerm Γ≡Δ x₄) (stabilityTerm Γ≡Δ x₅)
stabilityRedTerm Γ≡Δ (cast-ℕ-0 x) = cast-ℕ-0 (stabilityTerm Γ≡Δ x)
stabilityRedTerm Γ≡Δ (cast-ℕ-S x x₁) = cast-ℕ-S (stabilityTerm Γ≡Δ x) (stabilityTerm Γ≡Δ x₁)
stabilityRedTerm Γ≡Δ (cast-ℕ-cong x X) = cast-ℕ-cong (stabilityTerm Γ≡Δ x) (stabilityRedTerm Γ≡Δ X)

-- Stability of type reductions.
stabilityRed : ∀ {A B r Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ A ⇒ B ^ r → Δ ⊢ A ⇒ B ^ r
stabilityRed Γ≡Δ (univ x) = univ (stabilityRedTerm Γ≡Δ x)

-- Stability of type reduction closures.
stabilityRed* : ∀ {A B r Γ Δ} → ⊢ Γ ≡ Δ → Γ ⊢ A ⇒* B ^ r → Δ ⊢ A ⇒* B ^ r
stabilityRed* Γ≡Δ (id x) = id (stability Γ≡Δ x)
stabilityRed* Γ≡Δ (x ⇨ D) = stabilityRed Γ≡Δ x ⇨ stabilityRed* Γ≡Δ D

-- Stability of term reduction closures.
stabilityRed*Term : ∀ {t u A Γ Δ l} → ⊢ Γ ≡ Δ → Γ ⊢ t ⇒* u ∷ A ^ l → Δ ⊢ t ⇒* u ∷ A ^ l
stabilityRed*Term Γ≡Δ (id x) = id (stabilityTerm Γ≡Δ x)
stabilityRed*Term Γ≡Δ (x ⇨ d) = stabilityRedTerm Γ≡Δ x ⇨ stabilityRed*Term Γ≡Δ d


mutual
  -- Stability of algorithmic equality of neutrals.
  stability~↑! : ∀ {k l A Γ Δ lA}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ k ~ l ↑! A ^ lA
              → Δ ⊢ k ~ l ↑! A ^ lA
  stability~↑! Γ≡Δ (var-refl x x≡y) =
    var-refl (stabilityTerm Γ≡Δ x) x≡y
  stability~↑! Γ≡Δ (app-cong {rF = ! } k~l x) =
    app-cong (stability~↓! Γ≡Δ k~l) (stabilityConv↑Term Γ≡Δ x)
  stability~↑! Γ≡Δ (app-cong {rF = %} k~l x) =
    app-cong (stability~↓! Γ≡Δ k~l) (stability~↑% Γ≡Δ x)
  stability~↑! Γ≡Δ (natrec-cong x₁ x₂ x₃ k~l) =
    let ⊢Γ , _ , _ = contextConvSubst Γ≡Δ
    in natrec-cong (stabilityConv↑ (Γ≡Δ ∙ (refl (univ (ℕⱼ ⊢Γ)))) x₁)
                   (stabilityConv↑Term Γ≡Δ x₂)
                   (stabilityConv↑Term Γ≡Δ x₃)
                   (stability~↓! Γ≡Δ k~l)
  stability~↑! Γ≡Δ (Emptyrec-cong x₁ k~l) =
    Emptyrec-cong (stabilityConv↑ Γ≡Δ x₁)
                (stability~↑% Γ≡Δ k~l)
  stability~↑! Γ≡Δ (Id-cong X x x₁) = Id-cong (stability~↓! Γ≡Δ X) (stabilityConv↑Term Γ≡Δ x) (stabilityConv↑Term Γ≡Δ x₁)
  stability~↑! Γ≡Δ (Id-ℕ X x) = Id-ℕ (stability~↓! Γ≡Δ X) (stabilityConv↑Term Γ≡Δ x)
  stability~↑! Γ≡Δ (Id-ℕ0 X) = Id-ℕ0 (stability~↓! Γ≡Δ X)
  stability~↑! Γ≡Δ (Id-ℕS x X) = Id-ℕS (stabilityConv↑Term Γ≡Δ x) (stability~↓! Γ≡Δ X)
  stability~↑! Γ≡Δ (Id-U X x) = Id-U (stability~↓! Γ≡Δ X) (stabilityConv↑Term Γ≡Δ x)
  stability~↑! Γ≡Δ (Id-Uℕ X) = Id-Uℕ (stability~↓! Γ≡Δ X)
  stability~↑! Γ≡Δ (Id-UΠ x X) = Id-UΠ (stabilityConv↑Term Γ≡Δ x) (stability~↓! Γ≡Δ X)
  stability~↑! Γ≡Δ (cast-cong X x x₁ x₂ x₃) = cast-cong (stability~↓! Γ≡Δ X) (stabilityConv↑Term Γ≡Δ x) (stabilityConv↑Term Γ≡Δ x₁) (stabilityTerm Γ≡Δ x₂) (stabilityTerm Γ≡Δ x₃)
  stability~↑! Γ≡Δ (cast-ℕ X x x₁ x₂) = cast-ℕ (stability~↓! Γ≡Δ X) (stabilityConv↑Term Γ≡Δ x) (stabilityTerm Γ≡Δ x₁) (stabilityTerm Γ≡Δ x₂) 
  stability~↑! Γ≡Δ (cast-ℕℕ X x x₁) = cast-ℕℕ (stability~↓! Γ≡Δ X) (stabilityTerm Γ≡Δ x) (stabilityTerm Γ≡Δ x₁)  
  stability~↑! Γ≡Δ (cast-Π x X x₁ x₂ x₃) = cast-Π (stabilityConv↑Term Γ≡Δ x) (stability~↓! Γ≡Δ X) (stabilityConv↑Term Γ≡Δ x₁) (stabilityTerm Γ≡Δ x₂) (stabilityTerm Γ≡Δ x₃)
  stability~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) = cast-Πℕ (stabilityConv↑Term Γ≡Δ x) (stabilityConv↑Term Γ≡Δ x₁) (stabilityTerm Γ≡Δ x₂) (stabilityTerm Γ≡Δ x₃)
  stability~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) = cast-ℕΠ (stabilityConv↑Term Γ≡Δ x) (stabilityConv↑Term Γ≡Δ x₁) (stabilityTerm Γ≡Δ x₂) (stabilityTerm Γ≡Δ x₃)
  stability~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) = cast-ΠΠ%! (stabilityConv↑Term Γ≡Δ x) (stabilityConv↑Term Γ≡Δ x₁) (stabilityConv↑Term Γ≡Δ x₂) (stabilityTerm Γ≡Δ x₃) (stabilityTerm Γ≡Δ x₄)
  stability~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) = cast-ΠΠ!% (stabilityConv↑Term Γ≡Δ x) (stabilityConv↑Term Γ≡Δ x₁) (stabilityConv↑Term Γ≡Δ x₂) (stabilityTerm Γ≡Δ x₃) (stabilityTerm Γ≡Δ x₄)

  stability~↑% : ∀ {k l A Γ Δ lA}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ k ~ l ↑% A ^ lA
              → Δ ⊢ k ~ l ↑% A ^ lA
  stability~↑% Γ≡Δ (%~↑ ⊢k ⊢l) = %~↑ (stabilityTerm Γ≡Δ ⊢k) (stabilityTerm Γ≡Δ ⊢l)

  stability~↑ : ∀ {k l A rA lA Γ Δ}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ k ~ l ↑ A ^[ rA , lA ]
              → Δ ⊢ k ~ l ↑ A ^[ rA , lA ]
  stability~↑ Γ≡Δ (~↑! x) = ~↑! (stability~↑! Γ≡Δ x)
  stability~↑ Γ≡Δ (~↑% x) = ~↑% (stability~↑% Γ≡Δ x)

  -- Stability of algorithmic equality of neutrals of types in WHNF.
  stability~↓! : ∀ {k l A lA Γ Δ}
              → ⊢ Γ ≡ Δ
              → Γ ⊢ k ~ l ↓! A ^ lA 
              → Δ ⊢ k ~ l ↓! A ^ lA
  stability~↓! Γ≡Δ ([~] A D whnfA k~l) =
    [~] A (stabilityRed* Γ≡Δ D) whnfA (stability~↑! Γ≡Δ k~l)

  -- Stability of algorithmic equality of types.
  stabilityConv↑ : ∀ {A B r Γ Δ}
                 → ⊢ Γ ≡ Δ
                 → Γ ⊢ A [conv↑] B ^ r
                 → Δ ⊢ A [conv↑] B ^ r
  stabilityConv↑ Γ≡Δ ([↑] A′ B′ D D′ whnfA′ whnfB′ A′<>B′) =
    [↑] A′ B′ (stabilityRed* Γ≡Δ D) (stabilityRed* Γ≡Δ D′) whnfA′ whnfB′
        (stabilityConv↓ Γ≡Δ A′<>B′)

  -- Stability of algorithmic equality of types in WHNF.
  stabilityConv↓ : ∀ {A B r Γ Δ}
                 → ⊢ Γ ≡ Δ
                 → Γ ⊢ A [conv↓] B ^ r
                 → Δ ⊢ A [conv↓] B ^ r
  stabilityConv↓ Γ≡Δ (U-refl PE.refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  U-refl PE.refl ⊢Δ
  stabilityConv↓ Γ≡Δ (univ x) = univ (stabilityConv↓Term Γ≡Δ x)

  -- Stability of algorithmic equality of terms.
  stabilityConv↑Term : ∀ {t u A lA Γ Δ}
                     → ⊢ Γ ≡ Δ
                     → Γ ⊢ t [conv↑] u ∷ A ^ lA 
                     → Δ ⊢ t [conv↑] u ∷ A ^ lA
  stabilityConv↑Term Γ≡Δ ([↑]ₜ B t′ u′ D d d′ whnfB whnft′ whnfu′ t<>u) =
    [↑]ₜ B t′ u′ (stabilityRed* Γ≡Δ D) (stabilityRed*Term Γ≡Δ d)
                 (stabilityRed*Term Γ≡Δ d′) whnfB whnft′ whnfu′
                 (stabilityConv↓Term Γ≡Δ t<>u)

  -- Stability of algorithmic equality of terms in WHNF.
  stabilityConv↓Term : ∀ {t u A lA Γ Δ}
                     → ⊢ Γ ≡ Δ
                     → Γ ⊢ t [conv↓] u ∷ A ^ lA
                     → Δ ⊢ t [conv↓] u ∷ A ^ lA
  stabilityConv↓Term Γ≡Δ (U-refl PE.refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  U-refl PE.refl ⊢Δ
  stabilityConv↓Term Γ≡Δ (ne x) = ne (stability~↓! Γ≡Δ x)
  stabilityConv↓Term Γ≡Δ (ℕ-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  ℕ-refl ⊢Δ
  stabilityConv↓Term Γ≡Δ (Empty-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  Empty-refl ⊢Δ
  stabilityConv↓Term Γ≡Δ (Π-cong PE.refl PE.refl PE.refl l< l<' F A<>B A<>B₁) =
    Π-cong PE.refl PE.refl PE.refl l< l<' (stability Γ≡Δ F) (stabilityConv↑Term Γ≡Δ A<>B)
           (stabilityConv↑Term (Γ≡Δ ∙ refl F) A<>B₁)
  stabilityConv↓Term Γ≡Δ (ℕ-ins x) =
    ℕ-ins (stability~↓! Γ≡Δ x)
  -- stabilityConv↓Term Γ≡Δ (Empty-ins x) =
  --   Empty-ins (stability~↓% Γ≡Δ x)
  stabilityConv↓Term Γ≡Δ (ne-ins t u neN x) = 
    ne-ins (stabilityTerm Γ≡Δ t) (stabilityTerm Γ≡Δ u) neN (stability~↓! Γ≡Δ x)
  stabilityConv↓Term Γ≡Δ (zero-refl x) =
    let _ , ⊢Δ , _ = contextConvSubst Γ≡Δ
    in  zero-refl ⊢Δ
  stabilityConv↓Term Γ≡Δ (suc-cong t<>u) = suc-cong (stabilityConv↑Term Γ≡Δ t<>u)
  stabilityConv↓Term Γ≡Δ (η-eq l< l<' F x x₁ y y₁ t<>u) =
    η-eq l< l<' (stability Γ≡Δ F) (stabilityTerm Γ≡Δ x) (stabilityTerm Γ≡Δ x₁)
         y y₁ (stabilityConv↑Term (Γ≡Δ ∙ refl F) t<>u)
