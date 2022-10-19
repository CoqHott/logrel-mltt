{-# OPTIONS --allow-unsolved-metas #-}
--{-# OPTIONS --safe #-}

module Definition.Conversion.StabilityProp where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.RedSteps
open import Definition.Typed.Properties
open import Definition.Conversion
open import Definition.Conversion.Stability
open import Definition.Conversion.Conversion
open import Definition.Conversion.ConvSize
open import Definition.Conversion.Soundness
open import Definition.Typed.Consequences.Syntactic
open import Definition.Typed.Consequences.Injectivity
open import Definition.Typed.Consequences.Equality
open import Definition.Typed.Consequences.Reduction

open import Tools.Product
import Tools.PropositionalEquality as PE
open import Tools.Nat as Nat

plus0 : ∀ {n : Nat} → (n + 0) PE.≡ n
plus0 {0} = PE.refl
plus0 {1+ n} = PE.cong 1+ plus0

mutual

  stabilitySize~↑! : ∀ {k l A Γ Δ lA}
              → (Γ≡Δ : ⊢ Γ ≡ Δ)
              → (t~u : Γ ⊢ k ~ l ↑! A ^ lA)
              → size~↑! (stability~↑! Γ≡Δ t~u) PE.≡
                size~↑! t~u

  stabilitySize~↑! Γ≡Δ (var-refl x x₁) = PE.refl
  stabilitySize~↑! Γ≡Δ (app-cong {rF = !} x x₁) rewrite stabilitySize~↑! Γ≡Δ (_⊢_~_↓!_^_.k~l x) =
    PE.cong (λ n → 1+ (size~↑! (_⊢_~_↓!_^_.k~l x) + 1+ n)) (stabilitySizeConv↓Term Γ≡Δ (_⊢_[conv↑]_∷_^_.t<>u x₁))
  stabilitySize~↑! Γ≡Δ (app-cong {rF = %} x x₁) rewrite stabilitySize~↑! Γ≡Δ (_⊢_~_↓!_^_.k~l x) = PE.refl
  stabilitySize~↑! Γ≡Δ (natrec-cong x x₁ x₂ x₃) = 
    PE.cong₄ (λ a b c d → 1+ (1+ (a + b + c + d)))
             (stabilitySizeConv↓ _ (_⊢_[conv↑]_^_.A′<>B′ x))
             (stabilitySizeConv↑Term Γ≡Δ x₁)
             (stabilitySizeConv↑Term Γ≡Δ x₂)
             (stabilitySize~↓! Γ≡Δ x₃)
  stabilitySize~↑! Γ≡Δ (Emptyrec-cong x x₁) = PE.cong (λ n → 2 + n) (stabilitySizeConv↓ Γ≡Δ (_⊢_[conv↑]_^_.A′<>B′ x))
  stabilitySize~↑! Γ≡Δ (Id-cong x x₁ x₂) = {!!}
  stabilitySize~↑! Γ≡Δ (Id-ℕ x x₁) = {!!}
  stabilitySize~↑! Γ≡Δ (Id-ℕ0 x) = {!!}
  stabilitySize~↑! Γ≡Δ (Id-ℕS x x₁) = {!!}
  stabilitySize~↑! Γ≡Δ (Id-U x x₁) = {!!}
  stabilitySize~↑! Γ≡Δ (Id-Uℕ x) = {!!}
  stabilitySize~↑! Γ≡Δ (Id-UΠ x x₁) = {!!}
  stabilitySize~↑! Γ≡Δ (cast-cong x x₁ x₂ x₃ x₄ x₅ x₆) = {!!}
  stabilitySize~↑! Γ≡Δ (cast-refl x x₁ x₂ x₃ x₄) = {!!}
  stabilitySize~↑! Γ≡Δ (castℕ-refl x x₁) = {!!}
  stabilitySize~↑! Γ≡Δ (cast-refl' x x₁ x₂ x₃ x₄) = {!!}
  stabilitySize~↑! Γ≡Δ (castℕ-refl' x x₁) = {!!}
  stabilitySize~↑! Γ≡Δ (cast-neℕ x x₁ x₂ x₃) = {!!}
  stabilitySize~↑! Γ≡Δ (cast-ℕ x x₁ x₂ x₃) = {!!}
  stabilitySize~↑! Γ≡Δ (cast-ℕℕ x x₁ x₂) = {!!}
  stabilitySize~↑! Γ≡Δ (cast-neΠ x x₁ x₂ x₃ x₄) = {!!}
  stabilitySize~↑! Γ≡Δ (cast-Π x x₁ x₂ x₃ x₄) = {!!}
  stabilitySize~↑! Γ≡Δ (cast-Πℕ x x₁ x₂ x₃) = {!!}
  stabilitySize~↑! Γ≡Δ (cast-ℕΠ x x₁ x₂ x₃) = {!!}
  stabilitySize~↑! Γ≡Δ (cast-ΠΠ%! x x₁ x₂ x₃ x₄) = {!!}
  stabilitySize~↑! Γ≡Δ (cast-ΠΠ!% x x₁ x₂ x₃ x₄) = {!!}


  stabilitySize~↓! : ∀ {k l A Γ Δ lA}
              → (Γ≡Δ : ⊢ Γ ≡ Δ)
              → (t~u : Γ ⊢ k ~ l ↓! A ^ lA)
              → size~↓! (stability~↓! Γ≡Δ t~u) PE.≡
                size~↓! t~u

  stabilitySize~↓! Γ≡Δ t~u = {!!}

  stabilitySizeConv↓Term : ∀ {k l A Γ Δ lA}
              → (Γ≡Δ : ⊢ Γ ≡ Δ)
              → (t~u : Γ ⊢ k [conv↓] l ∷ A ^ lA)
              → sizeConv↓Term (stabilityConv↓Term Γ≡Δ t~u) PE.≡
                sizeConv↓Term t~u
  stabilitySizeConv↓Term Γ≡Δ t~u = {!!} 

  stabilitySizeConv↓ : ∀ {k l Γ Δ lA}
              → (Γ≡Δ : ⊢ Γ ≡ Δ)
              → (t~u : Γ ⊢ k [conv↓] l ^ lA)
              → sizeConv↓ (stabilityConv↓ Γ≡Δ t~u) PE.≡
                sizeConv↓ t~u
  stabilitySizeConv↓ Γ≡Δ t~u = {!!} 

  stabilitySizeConv↑Term : ∀ {k l A Γ Δ lA}
              → (Γ≡Δ : ⊢ Γ ≡ Δ)
              → (t~u : Γ ⊢ k [conv↑] l ∷ A ^ lA)
              → sizeConv↑Term (stabilityConv↑Term Γ≡Δ t~u) PE.≡
                sizeConv↑Term t~u
  stabilitySizeConv↑Term Γ≡Δ t~u = {!!} 

  stabilitySizeConv↑ : ∀ {k l Γ Δ lA}
              → (Γ≡Δ : ⊢ Γ ≡ Δ)
              → (t~u : Γ ⊢ k [conv↑] l ^ lA)
              → sizeConv↑ (stabilityConv↑ Γ≡Δ t~u) PE.≡
                sizeConv↑ t~u
  stabilitySizeConv↑ Γ≡Δ t~u = {!!} 
