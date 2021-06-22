{-# OPTIONS --without-K  #-}

module Definition.Typed.EqualityRelation where

open import Definition.Untyped
open import Definition.Typed
open import Definition.Typed.Weakening using (_∷_⊆_)

import Tools.PropositionalEquality as PE


-- Generic equality relation used with the logical relation

record EqRelSet : Set₁ where
  constructor eqRel
  field
    ---------------
    -- Relations --
    ---------------

    -- Equality of types
    _⊢_≅_⦂_   : Con Term → (A B : Term) → 𝕊 → Set

    -- Equality of terms
    _⊢_≅_∷_⦂_ : Con Term → (t u A : Term) → 𝕊 → Set

    -- Equality of neutral terms
    _⊢_~_∷_⦂_ : Con Term → (t u A : Term) → 𝕊 → Set

    ----------------
    -- Properties --
    ----------------

    -- Generic equality compatibility
    ~-to-≅ₜ : ∀ {k l A s Γ}
            → Γ ⊢ k ~ l ∷ A ⦂ s
            → Γ ⊢ k ≅ l ∷ A ⦂ s

    -- Judgmental conversion compatibility
    ≅-eq  : ∀ {A B s Γ}
          → Γ ⊢ A ≅ B ⦂ s
          → Γ ⊢ A ≡ B ⦂ s
    ≅ₜ-eq : ∀ {t u A s Γ}
          → Γ ⊢ t ≅ u ∷ A ⦂ s
          → Γ ⊢ t ≡ u ∷ A ⦂ s

    -- Universe
    ≅-univ : ∀ {A B s Γ}
           → Γ ⊢ A ≅ B ∷ (Univ s) ⦂ 𝕥y
           → Γ ⊢ A ≅ B ⦂ s

    -- Symmetry
    ≅-sym  : ∀ {A B s Γ} → Γ ⊢ A ≅ B ⦂ s → Γ ⊢ B ≅ A ⦂ s
    ≅ₜ-sym : ∀ {t u A s Γ} → Γ ⊢ t ≅ u ∷ A ⦂ s → Γ ⊢ u ≅ t ∷ A ⦂ s
    ~-sym  : ∀ {k l A s Γ} → Γ ⊢ k ~ l ∷ A ⦂ s → Γ ⊢ l ~ k ∷ A ⦂ s

    -- Transitivity
    ≅-trans  : ∀ {A B C s Γ} → Γ ⊢ A ≅ B ⦂ s → Γ ⊢ B ≅ C ⦂ s → Γ ⊢ A ≅ C ⦂ s
    ≅ₜ-trans : ∀ {t u v A s Γ} → Γ ⊢ t ≅ u ∷ A ⦂ s → Γ ⊢ u ≅ v ∷ A ⦂ s → Γ ⊢ t ≅ v ∷ A ⦂ s
    ~-trans  : ∀ {k l m A s Γ} → Γ ⊢ k ~ l ∷ A ⦂ s → Γ ⊢ l ~ m ∷ A ⦂ s → Γ ⊢ k ~ m ∷ A ⦂ s

    -- Conversion
    ≅-conv : ∀ {t u A B s Γ} → Γ ⊢ t ≅ u ∷ A ⦂ s → Γ ⊢ A ≡ B ⦂ s → Γ ⊢ t ≅ u ∷ B ⦂ s
    ~-conv : ∀ {k l A B s Γ} → Γ ⊢ k ~ l ∷ A ⦂ s → Γ ⊢ A ≡ B ⦂ s → Γ ⊢ k ~ l ∷ B ⦂ s

    -- Weakening
    ≅-wk  : ∀ {A B s ρ Γ Δ}
          → ρ ∷ Δ ⊆ Γ
          → ⊢ Δ
          → Γ ⊢ A ≅ B ⦂ s
          → Δ ⊢ wk ρ A ≅ wk ρ B ⦂ s
    ≅ₜ-wk : ∀ {t u A s ρ Γ Δ}
          → ρ ∷ Δ ⊆ Γ
          → ⊢ Δ
          → Γ ⊢ t ≅ u ∷ A ⦂ s
          → Δ ⊢ wk ρ t ≅ wk ρ u ∷ wk ρ A ⦂ s
    ~-wk  : ∀ {k l A s ρ Γ Δ}
          → ρ ∷ Δ ⊆ Γ
          → ⊢ Δ
          → Γ ⊢ k ~ l ∷ A ⦂ s
          → Δ ⊢ wk ρ k ~ wk ρ l ∷ wk ρ A ⦂ s

    -- Weak head expansion
    ≅-red : ∀ {A A′ B B′ s Γ}
          → Γ ⊢ A ⇒* A′ ⦂ s
          → Γ ⊢ B ⇒* B′ ⦂ s
          → Whnf A′
          → Whnf B′
          → Γ ⊢ A′ ≅ B′ ⦂ s
          → Γ ⊢ A  ≅ B ⦂ s

    ≅ₜ-red : ∀ {a a′ b b′ A B s Γ}
           → Γ ⊢ A ⇒* B ⦂ s
           → Γ ⊢ a ⇒* a′ ∷ B ⦂ s
           → Γ ⊢ b ⇒* b′ ∷ B ⦂ s
           → Whnf B
           → Whnf a′
           → Whnf b′
           → Γ ⊢ a′ ≅ b′ ∷ B ⦂ s
           → Γ ⊢ a  ≅ b  ∷ A ⦂ s

    -- Universe type reflexivity
    ≅-Urefl   : ∀ {s Γ} → ⊢ Γ → Γ ⊢ (Univ s) ≅ (Univ s) ⦂ 𝕥y

    -- Natural number type reflexivity
    ≅-ℕrefl   : ∀ {Γ} → ⊢ Γ → Γ ⊢ ℕ ≅ ℕ ⦂ 𝕥y
    ≅ₜ-ℕrefl  : ∀ {Γ} → ⊢ Γ → Γ ⊢ ℕ ≅ ℕ ∷ U ⦂ 𝕥y

    -- Empty type reflexivity
    ≅-Emptyrefl   : ∀ {Γ} → ⊢ Γ → Γ ⊢ Empty ≅ Empty ⦂ 𝕥y
    ≅ₜ-Emptyrefl  : ∀ {Γ} → ⊢ Γ → Γ ⊢ Empty ≅ Empty ∷ U ⦂ 𝕥y

    -- Π-congurence

    ≅-Π-cong  : ∀ {F G H E sF sG Γ}
              → Γ ⊢ F ⦂ sF
              → Γ ⊢ F ≅ H ⦂ sF
              → Γ ∙ F ⦂ sF ⊢ G ≅ E ⦂ sG
              → Γ ⊢ Π F ⦂ sF ▹ G ≅ Π H ⦂ sF ▹ E ⦂ sG

    ≅ₜ-Π-cong : ∀ {F G H E sF sG Γ}
              → Γ ⊢ F ⦂ sF
              → Γ ⊢ F ≅ H ∷ (Univ sF) ⦂ 𝕥y
              → Γ ∙ F ⦂ sF ⊢ G ≅ E ∷ (Univ sG) ⦂ 𝕥y
              → Γ ⊢ Π F ⦂ sF ▹ G ≅ Π H ⦂ sF ▹ E ∷ (Univ sG) ⦂ 𝕥y

    -- Box-congruence

    ≅-Box-cong : ∀ {F H sF Γ}
               → Γ ⊢ F ⦂ ‼ sF
               → Γ ⊢ F ≅ H ⦂ ‼ sF
               → Γ ⊢ Box sF F ≅ Box sF H ⦂ 𝕥y

    ≅ₜ-Box-cong : ∀ {F F' sF Γ}
               → Γ ⊢ F ∷ 𝕌 sF ⦂ 𝕥y -- KM ?
               → Γ ⊢ F ≅ F' ∷ 𝕌 sF ⦂ 𝕥y
               → Γ ⊢ Box sF F ≅ Box sF F' ∷ 𝕌 sF ⦂ 𝕥y

    -- Zero reflexivity
    ≅ₜ-zerorefl : ∀ {Γ} → ⊢ Γ → Γ ⊢ zero ≅ zero ∷ ℕ ⦂ 𝕥y

    -- Successor congurence
    ≅-suc-cong : ∀ {m n Γ} → Γ ⊢ m ≅ n ∷ ℕ ⦂ 𝕥y → Γ ⊢ suc m ≅ suc n ∷ ℕ ⦂ 𝕥y

    -- η-equality
    ≅-η-eq : ∀ {f g F G sF sG Γ}
              → Γ ⊢ F ⦂ sF
              → Γ ⊢ f ∷ Π F ⦂ sF ▹ G ⦂ sG
              → Γ ⊢ g ∷ Π F ⦂ sF ▹ G ⦂ sG
              → Function f
              → Function g
              → Γ ∙ F ⦂ sF ⊢ wk1 f ∘ var 0 ≅ wk1 g ∘ var 0 ∷ G ⦂ sG
              → Γ ⊢ f ≅ g ∷ Π F ⦂ sF ▹ G ⦂ sG

    -- box congruence
    ≅-box-cong : ∀ {a a' F sF Γ}
               → Γ ⊢ F ⦂ ‼ sF
               → Γ ⊢ a ∷ F ⦂ ‼ sF
               → Γ ⊢ a' ∷ F ⦂ ‼ sF
               → Γ ⊢ a ≅ a' ∷ F ⦂ ‼ sF
               → Γ ⊢ box sF a ≅ box sF a' ∷ Box sF F ⦂ 𝕥y

    -- cstr congruence
    ≅-cstr-cong : ∀ {a a' k Γ s}
                 → cstr-cod k PE.≡ Univ s
                 → Γ ⊢ a ≅ a' ∷ wkAll Γ (cstr-dom k) ⦂ cstr-dom-sort k
                 → Γ ⊢ cstr k a ≅ cstr k a' ⦂ s

    ≅ₜ-cstr-cong : ∀ {a a' k Γ}
                 → Γ ⊢ a ≅ a' ∷ wkAll Γ (cstr-dom k) ⦂ cstr-dom-sort k
                 → Γ ⊢ cstr k a ≅ cstr k a' ∷ (cstr-cod-ctx Γ k) [ a ] ⦂ cstr-𝕊 k

    -- Variable reflexivity
    ~-var : ∀ {x A s Γ} → Γ ⊢ var x ∷ A ⦂ s → Γ ⊢ var x ~ var x ∷ A ⦂ s

    -- Application congurence
    ~-app : ∀ {a b f g F G sF sG Γ}
          → Γ ⊢ f ~ g ∷ Π F ⦂ sF ▹ G ⦂ sG
          → Γ ⊢ a ≅ b ∷ F ⦂ sF
          → Γ ⊢ f ∘ a ~ g ∘ b ∷ G [ a ] ⦂ sG

    -- Natural recursion congurence
    ~-natrec : ∀ {z z′ s s′ n n′ F F′ sF Γ}
             → Γ ∙ ℕ ⦂ 𝕥y ⊢ F ≅ F′ ⦂ sF
             → Γ     ⊢ z ≅ z′ ∷ F [ zero ] ⦂ sF
             → Γ     ⊢ s ≅ s′ ∷ Π ℕ ⦂ 𝕥y ▹ (F ⦂ sF ▹▹ F [ suc (var 0) ]↑) ⦂ sF
             → Γ     ⊢ n ~ n′ ∷ ℕ ⦂ 𝕥y
             → Γ     ⊢ natrec F z s n ~ natrec F′ z′ s′ n′ ∷ F [ n ] ⦂ sF

    -- Empty recursion congruence
    ~-Emptyrec : ∀ {n n′ F F′ sF Γ}
             → Γ ⊢ F ≅ F′ ⦂ sF
             → Γ     ⊢ n ~ n′ ∷ Empty ⦂ 𝕥y
             → Γ     ⊢ Emptyrec F n ~ Emptyrec F′ n′ ∷ F ⦂ sF

    -- Boxrec congruence
    ~-Boxrec : ∀ {t t' u u' F F' G G' sF sG Γ}
             → Γ ⊢ F ⦂ ‼ sF
             → Γ ⊢ F ≅ F' ⦂ ‼ sF
             → Γ ∙ Box sF F ⦂ 𝕥y ⊢ G ≅ G' ⦂ sG
             → Γ ⊢ u ≅ u' ∷ Π F ⦂ ‼ sF ▹ (G [ box sF (var 0) ]↑) ⦂ sG
             → Γ ⊢ t ~ t' ∷ Box sF F ⦂ 𝕥y
             → Γ ⊢ Boxrec sG F G u t ~ Boxrec sG F' G' u' t'  ∷ G [ t ] ⦂ sG

    -- Destructor reflexivity
    ~-dstr : ∀ {k Γ a a' p p'}
           → let open Dstr Γ k in
             Γ ⊢ p ≅ p' ∷ param-type ⦂ dstr-param-sort k
           → Γ ⊢ a ~ a' ∷ dom-type p ⦂ dstr-dom-sort k
           → Γ ⊢ dstr k p a ~ dstr k p' a' ∷ cod-type p a ⦂ dstr-𝕊 k

  -- Composition of universe and generic equality compatibility
  ~-to-≅ : ∀ {k l s Γ} → Γ ⊢ k ~ l ∷ (Univ s) ⦂ 𝕥y → Γ ⊢ k ≅ l ⦂ s
  ~-to-≅ k~l = ≅-univ (~-to-≅ₜ k~l)
