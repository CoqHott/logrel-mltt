{-# OPTIONS --without-K  #-}

module Definition.Typed.Consequences.InverseUniv where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Consequences.Syntactic

import Tools.Sum as Sum
open import Tools.Sum using (_⊎_; inj₁; inj₂)
open import Tools.Product
open import Tools.Empty
open import Tools.Nullary


-- Proposition for terms if they contain a U.
data UFull : Term → Set where
  ∃U  : ∀ {s} → UFull (Univ s)
  ∃Π₁ : ∀ {F sF G} → UFull F → UFull (Π F ⦂ sF ▹ G)
  ∃Π₂ : ∀ {F sF G} → UFull G → UFull (Π F ⦂ sF ▹ G)

-- Terms cannot contain U.
noU : ∀ {t A sA Γ} → Γ ⊢ t ∷ A ⦂ sA → ¬ (UFull t)
noU (ℕⱼ x) ()
noU (Emptyⱼ x) ()
noU (Πⱼ t ▹ t₁) (∃Π₁ ufull) = noU t ufull
noU (Πⱼ t ▹ t₁) (∃Π₂ ufull) = noU t₁ ufull
noU (var x₁ x₂) ()
noU (lamⱼ x t₁) ()
noU (t ∘ⱼ t₁) ()
noU (zeroⱼ x) ()
noU (sucⱼ t) ()
noU (natrecⱼ x t t₁ t₂) ()
noU (Emptyrecⱼ x t) ()
noU (conv t₁ x) ufull = noU t₁ ufull

-- Neutrals cannot contain U.
noUNe : ∀ {A} → Neutral A → ¬ (UFull A)
noUNe (var n) ()
noUNe (∘ₙ neA) ()
noUNe (natrecₙ neA) ()
noUNe (Emptyrecₙ neA) ()

-- Helper function where if at least one Π-type does not contain U,
-- one of F and H will not contain U and one of G and E will not contain U.
pilem : ∀ {F G H E sF sH}
      → (¬ UFull (Π F ⦂ sF ▹ G)) ⊎ (¬ UFull (Π H ⦂ sH ▹ E))
      → (¬ UFull F) ⊎ (¬ UFull H) × (¬ UFull G) ⊎ (¬ UFull E)
pilem (inj₁ x) = inj₁ (λ x₁ → x (∃Π₁ x₁)) , inj₁ (λ x₁ → x (∃Π₂ x₁))
pilem (inj₂ x) = inj₂ (λ x₁ → x (∃Π₁ x₁)) , inj₂ (λ x₁ → x (∃Π₂ x₁))

-- If type A does not contain U, then A can be a term of type U.
inverseUniv : ∀ {A sA Γ} → ¬ (UFull A) → Γ ⊢ A ⦂ sA → Γ ⊢ A ∷ Univ sA ⦂ 𝕥y
inverseUniv q (ℕⱼ x) = ℕⱼ x
inverseUniv q (Emptyⱼ x) = Emptyⱼ x
inverseUniv q (Uⱼ x) = ⊥-elim (q ∃U)
inverseUniv q (Πⱼ A ▹ A₁) = Πⱼ inverseUniv (λ x → q (∃Π₁ x)) A ▹ inverseUniv (λ x → q (∃Π₂ x)) A₁
inverseUniv q (univ x) = x

-- If A is a neutral type, then A can be a term of U.
inverseUnivNe : ∀ {A sA Γ} → Neutral A → Γ ⊢ A ⦂ sA → Γ ⊢ A ∷ Univ sA ⦂ 𝕥y
inverseUnivNe neA ⊢A = inverseUniv (noUNe neA) ⊢A

-- Helper function where if at least one type does not contain U, then the
-- equality of types can be an equality of term of type U.
inverseUnivEq′ : ∀ {A B sA Γ} → (¬ (UFull A)) ⊎ (¬ (UFull B))
               → Γ ⊢ A ≡ B ⦂ sA
               → Γ ⊢ A ≡ B ∷ Univ sA ⦂ 𝕥y
inverseUnivEq′ q (univ x) = x
inverseUnivEq′ q (refl x) = refl (inverseUniv (Sum.id q) x)
inverseUnivEq′ q (sym A≡B) = sym (inverseUnivEq′ (Sum.sym q) A≡B)
inverseUnivEq′ (inj₁ x) (trans A≡B A≡B₁) =
  let w = inverseUnivEq′ (inj₁ x) A≡B
      _ , _ , t = syntacticEqTerm w
      y = noU t
  in  trans w (inverseUnivEq′ (inj₁ y) A≡B₁)
inverseUnivEq′ (inj₂ x) (trans A≡B A≡B₁) =
  let w = inverseUnivEq′ (inj₂ x) A≡B₁
      _ , t , _ = syntacticEqTerm w
      y = noU t
  in  trans (inverseUnivEq′ (inj₂ y) A≡B) w
inverseUnivEq′ q (Π-cong x A≡B A≡B₁) =
  let w , e = pilem q
  in  Π-cong x (inverseUnivEq′ w A≡B) (inverseUnivEq′ e A≡B₁)

-- If A is a term of U, then the equality of types is an equality of terms of type U.
inverseUnivEq : ∀ {A B sA Γ} → Γ ⊢ A ∷ Univ sA ⦂ 𝕥y → Γ ⊢ A ≡ B ⦂ sA → Γ ⊢ A ≡ B ∷ Univ sA ⦂ 𝕥y
inverseUnivEq A A≡B = inverseUnivEq′ (inj₁ (noU A)) A≡B
