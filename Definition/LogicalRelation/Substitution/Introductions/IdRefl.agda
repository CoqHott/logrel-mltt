{-# OPTIONS --safe #-}

open import Definition.Typed.EqualityRelation

module Definition.LogicalRelation.Substitution.Introductions.IdRefl {{eqrel : EqRelSet}} where
open EqRelSet {{...}}

open import Definition.Untyped hiding (tt)
open import Definition.Untyped.Properties
open import Definition.Typed 
open import Definition.Typed.Properties
open import Definition.LogicalRelation
open import Definition.LogicalRelation.Irrelevance
open import Definition.LogicalRelation.Properties
open import Definition.LogicalRelation.Substitution
open import Definition.LogicalRelation.Substitution.Properties
open import Definition.LogicalRelation.Substitution.Conversion
open import Definition.LogicalRelation.Substitution.Reduction
open import Definition.LogicalRelation.Substitution.Reflexivity
open import Definition.LogicalRelation.Substitution.ProofIrrelevance
open import Definition.LogicalRelation.Substitution.MaybeEmbed
open import Definition.LogicalRelation.Substitution.Introductions.Nat
open import Definition.LogicalRelation.Substitution.Introductions.Natrec
open import Definition.LogicalRelation.Substitution.Introductions.Empty
open import Definition.LogicalRelation.Substitution.Introductions.Emptyrec
open import Definition.LogicalRelation.Substitution.Introductions.Universe
open import Definition.LogicalRelation.Substitution.Introductions.Pi
open import Definition.LogicalRelation.Substitution.Introductions.Sigma
open import Definition.LogicalRelation.Substitution.Introductions.Id
open import Definition.LogicalRelation.Substitution.Introductions.IdUPiPi
open import Definition.LogicalRelation.Substitution.Introductions.Cast
open import Definition.LogicalRelation.Substitution.Introductions.CastPi
open import Definition.LogicalRelation.Substitution.Introductions.Lambda
open import Definition.LogicalRelation.Substitution.Introductions.Application
open import Definition.LogicalRelation.Substitution.Introductions.Pair
open import Definition.LogicalRelation.Substitution.Introductions.Fst
open import Definition.LogicalRelation.Substitution.Introductions.Snd
open import Definition.LogicalRelation.Substitution.Introductions.SingleSubst
open import Definition.LogicalRelation.Substitution.Introductions.Transp
open import Definition.LogicalRelation.Fundamental.Variable
import Definition.LogicalRelation.Substitution.ProofIrrelevance as PI
import Definition.LogicalRelation.Substitution.Irrelevance as S
open import Definition.LogicalRelation.Substitution.Weakening

open import Tools.Product
open import Tools.Unit
open import Tools.Nat
import Tools.PropositionalEquality as PE

Idreflᵛ : ∀{Γ A l t}
  → ([Γ] : ⊩ᵛ Γ)
  → ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ ! , ι l ] / [Γ])
  → ([t] : Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ [ ! , ι l ] / [Γ] / [A])
  → let [Id] = Idᵛ {A = A} {t = t} {u = t } [Γ] [A] [t] [t]
    in Γ ⊩ᵛ⟨ ∞ ⟩ Idrefl A t ∷ Id A t t ^ [ % , ι l ] / [Γ] / [Id]

Idreflᵛ {Γ} {A} {l} {t} [Γ] [A] [t]  =
  let [Id] = Idᵛ {A = A} {t = t} {u = t } [Γ] [A] [t] [t]
  in validityIrr {A = Id A t t} {t = Idrefl A t} [Γ] [Id] λ ⊢Δ [σ] → Idreflⱼ (escapeTerm (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([t] ⊢Δ [σ])))

castreflᵛ : ∀{Γ A t}
  → ([Γ] : ⊩ᵛ Γ)
  → ([UA] : Γ ⊩ᵛ⟨ ∞ ⟩ U ⁰ ^ [ ! , next ⁰ ] / [Γ])
  → ([A]ₜ : Γ ⊩ᵛ⟨ ∞ ⟩ A ∷ U ⁰ ^ [ ! , next ⁰ ] / [Γ] / [UA] )
  → ([A] : Γ ⊩ᵛ⟨ ∞ ⟩ A ^ [ ! , ι ⁰ ] / [Γ])
  → ([t]ₜ : Γ ⊩ᵛ⟨ ∞ ⟩ t ∷ A ^ [ ! , ι ⁰ ] / [Γ] / [A])
  → let [Id] : Γ ⊩ᵛ⟨ ∞ ⟩ Id A t (cast ⁰ A A (Idrefl (U ⁰) A) t) ^ [ % , ι ⁰ ] / [Γ]
        [Id] = Idᵛ {A = A} {t = t} {u = cast ⁰ A A (Idrefl (U ⁰) A) t} [Γ] [A] [t]ₜ
                   (castᵗᵛ {A = A} {B = A} {t = t} {e = Idrefl (U ⁰) A} [Γ] [UA] [A]ₜ [A]ₜ [A] [A] [t]ₜ
                           (Idᵛ {A = U _} {t = A} {u = A} [Γ] [UA] [A]ₜ [A]ₜ)
                           (Idreflᵛ {A = U _} {t = A} [Γ] [UA] [A]ₜ))
    in Γ ⊩ᵛ⟨ ∞ ⟩ castrefl A t ∷ Id A t (cast ⁰ A A (Idrefl (U ⁰) A) t) ^ [ % , ι ⁰ ] / [Γ] / [Id]


castreflᵛ {Γ} {A} {t} [Γ] [UA] [A]ₜ [A] [t]ₜ =
  let [Id] : Γ ⊩ᵛ⟨ ∞ ⟩ Id A t (cast ⁰ A A (Idrefl (U ⁰) A) t) ^ [ % , ι ⁰ ] / [Γ]
      [Id] = Idᵛ {A = A} {t = t} {u = cast ⁰ A A (Idrefl (U ⁰) A) t} [Γ] [A] [t]ₜ
                 (castᵗᵛ {A = A} {B = A} {t = t} {e = Idrefl (U ⁰) A} [Γ] [UA] [A]ₜ [A]ₜ [A] [A] [t]ₜ
                 (Idᵛ {A = U _} {t = A} {u = A} [Γ] [UA] [A]ₜ [A]ₜ)
                 (Idreflᵛ {A = U _} {t = A} [Γ] [UA] [A]ₜ))
  in  validityIrr {A = Id A t (cast ⁰ A A (Idrefl (U ⁰) A) t)} {t = castrefl A t}
                  [Γ] [Id] λ ⊢Δ [σ] → castreflⱼ (escapeTerm (proj₁ ([UA] ⊢Δ [σ])) (proj₁ ([A]ₜ ⊢Δ [σ]))) (escapeTerm (proj₁ ([A] ⊢Δ [σ])) (proj₁ ([t]ₜ ⊢Δ [σ])))

