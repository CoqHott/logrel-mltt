-- Martin-Löf identity type without the K axiom
-- (we do not assume uniqueness of identity proofs).

{-# OPTIONS --safe #-}

module Tools.PropositionalEquality where

-- We reexport Agda's builtin equality type.

open import Agda.Builtin.Equality public using (_≡_; refl)
open import Tools.Empty

-- Inequality.

infix 4 _≢_

_≢_ : {A : Set} → A → A → Set
a ≢ b = a ≡ b → ⊥

-- Symmetry.

sym : {A : Set} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

-- Transitivity.

trans : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

-- Non-dependent congruence rules.

cong : {A B : Set} {a b : A} (f : A → B) → a ≡ b → f a ≡ f b
cong f refl = refl

cong₂ : ∀ {A B C : Set} {a a′ b b′}
        (f : A → B → C) → a ≡ a′ → b ≡ b′
      → f a b ≡ f a′ b′
cong₂ f refl refl = refl

cong₃ : ∀ {A B C D : Set} {a a′ b b′ c c′}
        (f : A → B → C → D) → a ≡ a′ → b ≡ b′ → c ≡ c′
      → f a b c ≡ f a′ b′ c′
cong₃ f refl refl refl = refl

cong₄ : ∀ {A B C D E : Set} {a a′ b b′ c c′ d d′}
        (f : A → B → C → D → E) → a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′
      → f a b c d ≡ f a′ b′ c′ d′
cong₄ f refl refl refl refl = refl

cong5 : ∀ {A B C D E F : Set} {a a′ b b′ c c′ d d′ e e'}
        (f : A → B → C → D → E → F) → a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ → e ≡ e' 
      → f a b c d e ≡ f a′ b′ c′ d′ e'
cong5 f refl refl refl refl refl = refl

cong6 : ∀ {A B C D E F G : Set} {a a′ b b′ c c′ d d′ e e' g g'} 
        (f : A → B → C → D → E → G → F) → a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ → e ≡ e' → g ≡ g' 
      → f a b c d e g ≡ f a′ b′ c′ d′ e' g'
cong6 f refl refl refl refl refl refl = refl

-- Substitution (type-cast).

subst : {A : Set} {a b : A} (F : A → Set) → a ≡ b → F a → F b
subst F refl f = f

J : {A : Set} {a : A} (F : ( b : A) (e : a ≡ b) → Set) (b : A) (e : a ≡ b) → F a refl → F b e
J F b refl f = f

-- Two substitutions simultaneously.

subst₂ : ∀ {A B : Set} {a a′ b b′} (F : A → B → Set)
       → a ≡ a′ → b ≡ b′ → F a b → F a′ b′
subst₂ F refl refl f = f

-- Three substitutions simultaneously.

subst₃ : ∀ {A B C : Set} {a a′ b b′ c c′} (F : A → B → C → Set)
       → a ≡ a′ → b ≡ b′ → c ≡ c′ → F a b c → F a′ b′ c′
subst₃ F refl refl refl f = f

subst₄ : ∀ {A B C D : Set} {a a′ b b′ c c′ d d′} (F : A → B → C → D → Set)
       → a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ → F a b c d → F a′ b′ c′ d′
subst₄ F refl refl refl refl f = f

subst5 : ∀ {A B C D E : Set} {a a′ b b′ c c′ d d′ e e′} (F : A → B → C → D → E → Set)
       → a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ → e ≡ e′ → F a b c d e → F a′ b′ c′ d′ e′
subst5 F refl refl refl refl refl f = f
