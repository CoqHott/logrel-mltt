{-# OPTIONS --safe #-}

module Definition.Typed.Weakening where

open import Definition.Untyped as U hiding (wk)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Tools.List using ()

open import Tools.Product
import Tools.PropositionalEquality as PE


-- Weakening type

data _∷_⊆_ : Wk → Con Term → Con Term → Set where
  id   : ∀ {Γ}       → id ∷ Γ ⊆ Γ
  step : ∀ {Γ Δ A r ρ} → ρ  ∷ Δ ⊆ Γ → step ρ ∷ Δ ∙ A ^ r ⊆ Γ
  lift : ∀ {Γ Δ A r ρ} → ρ  ∷ Δ ⊆ Γ → lift ρ ∷ Δ ∙ U.wk ρ A ^ r ⊆ Γ ∙ A ^ r


-- -- Weakening composition

_•ₜ_ : ∀ {ρ ρ′ Γ Δ Δ′} → ρ ∷ Γ ⊆ Δ → ρ′ ∷ Δ ⊆ Δ′ → ρ • ρ′ ∷ Γ ⊆ Δ′
id     •ₜ η′ = η′
step η •ₜ η′ = step (η •ₜ η′)
lift η •ₜ id = lift η
lift η •ₜ step η′ = step (η •ₜ η′)
_•ₜ_ {lift ρ} {lift ρ′} {Δ′ = Δ′ ∙ A ^ rA} (lift η) (lift η′) =
  PE.subst (λ x → lift (ρ • ρ′) ∷ x ⊆ Δ′ ∙ A ^ rA)
           (PE.cong₂ (λ x y → x ∙ y ^ rA) PE.refl (PE.sym (wk-comp ρ ρ′ A)))
           (lift (η •ₜ η′))


-- Weakening of judgements

wkIndex : ∀ {Γ Δ n A r ρ} → ρ ∷ Δ ⊆ Γ →
        let ρA = U.wk ρ A
            ρn = wkVar ρ n
        in  ⊢ Δ → n ∷ A ^ r ∈ Γ → ρn ∷ ρA ^ r ∈ Δ
wkIndex id ⊢Δ i = PE.subst (λ x → _ ∷ x ^ _ ∈ _) (PE.sym (wk-id _)) i
wkIndex (step ρ) (⊢Δ ∙ A) i = PE.subst (λ x → _ ∷ x ^ _ ∈ _)
                                       (wk1-wk _ _)
                                       (there (wkIndex ρ ⊢Δ i))
wkIndex (lift ρ) (⊢Δ ∙ A) (there i) = PE.subst (λ x → _ ∷ x ^ _ ∈ _)
                                               (wk1-wk≡lift-wk1 _ _)
                                               (there (wkIndex ρ ⊢Δ i))
wkIndex (lift ρ) ⊢Δ here =
  let G = _
      n = _
  in  PE.subst (λ x → n ∷ x ^ _ ∈ G)
               (wk1-wk≡lift-wk1 _ _)
               here

mutual
  wk : ∀ {Γ Δ A r ρ} → ρ ∷ Δ ⊆ Γ →
     let ρA = U.wk ρ A
     in  ⊢ Δ → Γ ⊢ A ^ r → Δ ⊢ ρA ^ r
  wk ρ ⊢Δ (Uⱼ ⊢Γ) = Uⱼ ⊢Δ
  wk ρ ⊢Δ (univ A) = univ (wkTerm ρ ⊢Δ A)

  wkTerm : ∀ {Γ Δ A t r ρ} → ρ ∷ Δ ⊆ Γ →
         let ρA = U.wk ρ A
             ρt = U.wk ρ t
         in ⊢ Δ → Γ ⊢ t ∷ A ^ r → Δ ⊢ ρt ∷ ρA ^ r
  wkTerm ρ ⊢Δ (univ <l ⊢Γ) = univ <l ⊢Δ
  wkTerm ρ ⊢Δ (ℕⱼ ⊢Γ) = ℕⱼ ⊢Δ
  wkTerm ρ ⊢Δ (Emptyⱼ ⊢Γ) = Emptyⱼ ⊢Δ
  wkTerm ρ ⊢Δ (Πⱼ <l ▹ <l' ▹ F ▹ G) = let ρF = wkTerm ρ ⊢Δ F
                                      in  Πⱼ <l ▹ <l' ▹ ρF ▹ (wkTerm (lift ρ) (⊢Δ ∙ univ ρF) G)
  wkTerm ρ ⊢Δ (var ⊢Γ x) = var ⊢Δ (wkIndex ρ ⊢Δ x)
  wkTerm ρ ⊢Δ (lamⱼ <l <l' F t) = let ρF = wk ρ ⊢Δ F
                                  in lamⱼ <l <l' ρF (wkTerm (lift ρ) (⊢Δ ∙ ρF) t)
  wkTerm ρ ⊢Δ (_▹_▹_▹_∘ⱼ_ {F = F} {G = G} r% ⊢F ⊢G g a) = let ρF = wkTerm ρ ⊢Δ ⊢F
                                                     in  PE.subst (λ x → _ ⊢ _ ∷ x ^ _)
                                                         (PE.sym (wk-β G))
                                                         (r% ▹ wkTerm ρ ⊢Δ ⊢F ▹ wkTerm (lift ρ) (⊢Δ ∙ univ ρF) ⊢G ▹ wkTerm ρ ⊢Δ g ∘ⱼ wkTerm ρ ⊢Δ a)
{-
wkTerm {ρ = ρ} [ρ] ⊢Δ (Id-Π {rA = rA} {t = t} {u = u} <l <l' Aⱼ Bⱼ tⱼ uⱼ) =
    let ρA = wkTerm [ρ] ⊢Δ Aⱼ in
    let ρB = wkTerm (lift [ρ]) (⊢Δ ∙ univ ρA) Bⱼ in
    let ρt = wkTerm [ρ] ⊢Δ tⱼ in
    let ρu = wkTerm [ρ] ⊢Δ uⱼ in
    let idpi = Id-Π <l <l' ρA ρB ρt ρu in
     {!PE.subst
      (λ x → _ ⊢ _ ∷ Π _ ^ _ ° _ ▹ Id _ (x ∘ _ ^ _) _ ° _ ° _ ^ _ ^ % ° ⁰ ▹▹ Id _ (U.wk ρ t) _ ° ⁰ ° ⁰ ^ % ^ [ % , ι ⁰ ])
      (wk1-wk≡lift-wk1 ρ t) ?!}
     {-PE.subst
      (λ x → _ ⊢ _ ∷ Π _ ^ _ ° _ ▹ Id _ (x ∘ _ ^ _) _ ° _ ° _ ^ _ ^ % ° ⁰ ▹▹ Id _ (U.wk ρ t) _ ° ⁰ ° ⁰ ^ % ^ [ % , _ ])
      ? -- (wk1-wk≡lift-wk1 ρ t)
      (PE.subst
        (λ x → _ ⊢ _ ∷ Π _ ^ _ ° _ ▹ Id _ _ (x ∘ _ ^ _) ° _ ° _ ^ _ ^ % ° ⁰ ▹▹ Id _ _ (U.wk ρ u) ° ⁰ ° ⁰ ^ % ^ [ % , _ ])
        ? -- (wk1-wk≡lift-wk1 ρ u)
        idpi)-}
        -}
  wkTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (fstⱼ {A = A} {A' = A'} {rA = rA} {B = B} {B' = B'} {e = e} Aⱼ Bⱼ A'ⱼ B'ⱼ eⱼ) =
    let ρA = wkTerm [ρ] ⊢Δ Aⱼ in
    let ρA' = wkTerm [ρ] ⊢Δ A'ⱼ in
    let ρB = wkTerm (lift [ρ]) (⊢Δ ∙ (univ ρA)) Bⱼ in
    let ρB' = wkTerm (lift [ρ]) (⊢Δ ∙ (univ ρA')) B'ⱼ in
    let ρe = wkTerm [ρ] ⊢Δ eⱼ in
    fstⱼ ρA ρB ρA' ρB' ρe 
  wkTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (sndⱼ {A = A} {A' = A'} {rA = rA} {B = B} {B' = B'} {e = e} Aⱼ Bⱼ A'ⱼ B'ⱼ eⱼ) =
    let ρA = wkTerm [ρ] ⊢Δ Aⱼ in
    let ρA' = wkTerm [ρ] ⊢Δ A'ⱼ in
    let ρB = wkTerm (lift [ρ]) (⊢Δ ∙ (univ ρA)) Bⱼ in
    let ρB' = wkTerm (lift [ρ]) (⊢Δ ∙ (univ ρA')) B'ⱼ in
    let ρe = wkTerm [ρ] ⊢Δ eⱼ in
    let l = ⁰ in
    let l' = ⁰ in     
    let pred = λ A1 A1' A2' B1 B1' E → Δ ⊢ U.wk ρ (snd e) ∷ Π A1' ^ rA ° ⁰ ▹ Id (U l) (B1 [ cast l A2' A1 (Idsym (Univ rA l) A1 A2' (fst E)) (var 0) ]↑) B1' ° l' ° l' ^ % ^ [ % , _ ] in
    let j1 : pred (wk1 (U.wk ρ A)) (U.wk ρ A') (wk1 (U.wk ρ A')) (U.wk (lift ρ) B) (U.wk (lift ρ) B') (wk1 (U.wk ρ e))
        j1 = sndⱼ ρA ρB ρA' ρB' ρe in 
    let j2 = PE.subst (λ x → pred x (U.wk ρ A') (wk1 (U.wk ρ A')) (U.wk (lift ρ) B) (U.wk (lift ρ) B') (wk1 (U.wk ρ e))) (wk1-wk≡lift-wk1 ρ A) j1 in
    let j3 = PE.subst (λ x → pred (U.wk (lift ρ) (wk1 A)) (U.wk ρ A') x  (U.wk (lift ρ) B) (U.wk (lift ρ) B') (wk1 (U.wk ρ e))) (wk1-wk≡lift-wk1 ρ A') j2 in
    let j4 = PE.subst (λ x → pred (U.wk (lift ρ) (wk1 A)) (U.wk ρ A') _ (U.wk (lift ρ) B) (U.wk (lift ρ) B') x) (wk1-wk≡lift-wk1 ρ e) j3 in
    let j5 = PE.subst (λ x → Δ ⊢ U.wk ρ (snd e) ∷  Π U.wk ρ A' ^ rA ° ⁰ ▹ Id (U l) (U.wk (lift ρ) B [ (cast l (U.wk (lift ρ) (wk1 A')) (U.wk (lift ρ) (wk1 A)) x (var 0)) ]↑) (U.wk (lift ρ) B') ° l' ° l' ^ % ^ [ % , ι ⁰ ])
                      (PE.sym (wk-Idsym (lift ρ) (Univ rA l) (wk1 A) (wk1 A') (fst (wk1 e))))
                      j4 in
    PE.subst (λ x → Δ ⊢ U.wk ρ (snd e) ∷  Π U.wk ρ A' ^ rA ° ⁰ ▹ Id (U l) x (U.wk (lift ρ) B') ° l' ° l' ^ % ^ [ % , _ ])
             (PE.sym (wk-β↑ {ρ = ρ} {a = cast l (wk1 A') (wk1 A) (Idsym (Univ rA l) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0)} B)) j5
  wkTerm ρ ⊢Δ (zeroⱼ ⊢Γ) = zeroⱼ ⊢Δ
  wkTerm ρ ⊢Δ (sucⱼ n) = sucⱼ (wkTerm ρ ⊢Δ n)
  wkTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrecⱼ {G = G} {rG = rG} {lG = lG}  {s = s} rGlG ⊢G ⊢z ⊢s ⊢n) =
    PE.subst (λ x → _ ⊢ natrec _ _ _ _ _ ∷ x ^ _) (PE.sym (wk-β G))
             (natrecⱼ rGlG
                      (wk (lift [ρ]) (⊢Δ ∙ univ (ℕⱼ ⊢Δ)) ⊢G)
                      (PE.subst (λ x → _ ⊢ _ ∷ x ^ _) (wk-β G) (wkTerm [ρ] ⊢Δ ⊢z))
                      (PE.subst (λ x → Δ ⊢ U.wk ρ s ∷ x ^ [ rG , ι lG ])
                                (wk-β-natrec ρ G rG lG)
                                (wkTerm [ρ] ⊢Δ ⊢s))
                      (wkTerm [ρ] ⊢Δ ⊢n))
  wkTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (Emptyrecⱼ {A = A} {e = e} ⊢A ⊢e) =
    (Emptyrecⱼ (wk [ρ] ⊢Δ ⊢A) (wkTerm [ρ] ⊢Δ ⊢e))
  wkTerm ρ ⊢Δ (Idⱼ A t u) = Idⱼ (wkTerm ρ ⊢Δ A) (wkTerm ρ ⊢Δ t) (wkTerm ρ ⊢Δ u)
  wkTerm ρ ⊢Δ (Idreflⱼ t) = Idreflⱼ (wkTerm ρ ⊢Δ t)
  wkTerm ρ ⊢Δ (transpⱼ {P = P} A Pⱼ t s u e) =
    let ρA = wk ρ ⊢Δ A in
    let ρP = wk (lift ρ) (⊢Δ ∙ ρA) Pⱼ in
    let ρt = wkTerm ρ ⊢Δ t in
    let ρs = PE.subst (λ x → _ ⊢ _ ∷ x ^ _) (wk-β P) (wkTerm ρ ⊢Δ s) in
    let ρu = wkTerm ρ ⊢Δ u in
    let ρe = wkTerm ρ ⊢Δ e in
    PE.subst (λ x → _ ⊢ transp _ _ _ _ _ _ ∷ x ^ _) (PE.sym (wk-β P))
      (transpⱼ ρA ρP ρt ρs ρu ρe)
  wkTerm ρ ⊢Δ (castⱼ A B e t) =
    castⱼ (wkTerm ρ ⊢Δ A) (wkTerm ρ ⊢Δ B) (wkTerm ρ ⊢Δ e) (wkTerm ρ ⊢Δ t)
  wkTerm ρ ⊢Δ (conv t A≡B) = conv (wkTerm ρ ⊢Δ t) (wkEq ρ ⊢Δ A≡B)


  wkEq : ∀ {Γ Δ A B r ρ} → ρ ∷ Δ ⊆ Γ →
       let ρA = U.wk ρ A
           ρB = U.wk ρ B
       in ⊢ Δ → Γ ⊢ A ≡ B ^ r → Δ ⊢ ρA ≡ ρB ^ r
  wkEq ρ ⊢Δ (univ A≡B) = univ (wkEqTerm ρ ⊢Δ A≡B)
  wkEq ρ ⊢Δ (refl A) = refl (wk ρ ⊢Δ A)
  wkEq ρ ⊢Δ (sym A≡B) = sym (wkEq ρ ⊢Δ A≡B)
  wkEq ρ ⊢Δ (trans A≡B B≡C) = trans (wkEq ρ ⊢Δ A≡B) (wkEq ρ ⊢Δ B≡C)

  wkEqTerm : ∀ {Γ Δ A t u r ρ} → ρ ∷ Δ ⊆ Γ →
           let ρA = U.wk ρ A
               ρt = U.wk ρ t
               ρu = U.wk ρ u
           in ⊢ Δ → Γ ⊢ t ≡ u ∷ A ^ r → Δ ⊢ ρt ≡ ρu ∷ ρA ^ r
  wkEqTerm ρ ⊢Δ (refl t) = refl (wkTerm ρ ⊢Δ t)
  wkEqTerm ρ ⊢Δ (sym t≡u) = sym (wkEqTerm ρ ⊢Δ t≡u)
  wkEqTerm ρ ⊢Δ (trans t≡u u≡r) = trans (wkEqTerm ρ ⊢Δ t≡u) (wkEqTerm ρ ⊢Δ u≡r)
  wkEqTerm ρ ⊢Δ (conv t≡u A≡B) = conv (wkEqTerm ρ ⊢Δ t≡u) (wkEq ρ ⊢Δ A≡B)
  wkEqTerm ρ ⊢Δ (Π-cong <l <l' F F≡H G≡E) =
    let ρF = wk ρ ⊢Δ F
    in  Π-cong <l <l' ρF (wkEqTerm ρ ⊢Δ F≡H)
                         (wkEqTerm (lift ρ) (⊢Δ ∙ ρF) G≡E)
  wkEqTerm ρ ⊢Δ (app-cong {G = G} f≡g a≡b) =
    PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x ^ _)
             (PE.sym (wk-β G))
             (app-cong (wkEqTerm ρ ⊢Δ f≡g) (wkEqTerm ρ ⊢Δ a≡b))
  wkEqTerm ρ ⊢Δ (β-red {a = a} {t = t} {G = G} l< l<' F ⊢t ⊢a) =
    let ρF = wk ρ ⊢Δ F
    in  PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x ^ _)
                 (PE.sym (wk-β G))
                 (PE.subst (λ x → _ ⊢ U.wk _ ((lam _ ▹ t ^ _) ∘ a ^ _) ≡ x ∷ _ ^ _)
                           (PE.sym (wk-β t))
                           (β-red l< l<' ρF (wkTerm (lift ρ) (⊢Δ ∙ ρF) ⊢t)
                                     (wkTerm ρ ⊢Δ ⊢a)))
  wkEqTerm ρ ⊢Δ (η-eq lF lG F f g f0≡g0) =
    let ρF = wk ρ ⊢Δ F
    in  η-eq lF lG ρF (wkTerm ρ ⊢Δ f)
                (wkTerm ρ ⊢Δ g)
                (PE.subst (λ t → _ ⊢ t ∘ _ ^ _ ≡ _ ∷ _ ^ _)
                          (PE.sym (wk1-wk≡lift-wk1 _ _))
                          (PE.subst (λ t → _ ⊢ _ ≡ t ∘ _ ^ _ ∷ _ ^ _)
                                    (PE.sym (wk1-wk≡lift-wk1 _ _))
                                    (wkEqTerm (lift ρ) (⊢Δ ∙ ρF) f0≡g0)))
  wkEqTerm ρ ⊢Δ (suc-cong m≡n) = suc-cong (wkEqTerm ρ ⊢Δ m≡n)
  wkEqTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-cong {s = s} {s′ = s′} {F = F} {l = l}
                                     F≡F′ z≡z′ s≡s′ n≡n′) =
    PE.subst (λ x → Δ ⊢ natrec _ _ _ _ _ ≡ _ ∷ x ^ _) (PE.sym (wk-β F))
             (natrec-cong (wkEq (lift [ρ]) (⊢Δ ∙ univ (ℕⱼ ⊢Δ)) F≡F′)
                          (PE.subst (λ x → Δ ⊢ _ ≡ _ ∷ x ^ _) (wk-β F)
                                    (wkEqTerm [ρ] ⊢Δ z≡z′))
                          (PE.subst (λ x → Δ ⊢ U.wk ρ s
                                             ≡ U.wk ρ s′ ∷ x ^ [ ! , ι l ])
                                    (wk-β-natrec _ F ! l)
                                    (wkEqTerm [ρ] ⊢Δ s≡s′))
                          (wkEqTerm [ρ] ⊢Δ n≡n′))
  wkEqTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-zero {z} {s} {F} {l = l} ⊢F ⊢z ⊢s) =
    PE.subst (λ x → Δ ⊢ natrec _ (U.wk (lift _) F) _ _ _ ≡ _ ∷ x ^ _)
             (PE.sym (wk-β F))
             (natrec-zero (wk (lift [ρ]) (⊢Δ ∙ univ (ℕⱼ ⊢Δ)) ⊢F)
                          (PE.subst (λ x → Δ ⊢ U.wk ρ z ∷ x ^ _)
                                    (wk-β F)
                                    (wkTerm [ρ] ⊢Δ ⊢z))
                          (PE.subst (λ x → Δ ⊢ U.wk ρ s ∷ x ^ [ ! , ι l ])
                                    (wk-β-natrec _ F ! l)
                                    (wkTerm [ρ] ⊢Δ ⊢s)))
  wkEqTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-suc {n} {z} {s} {F} {l = l} ⊢n ⊢F ⊢z ⊢s) =
    PE.subst (λ x → Δ ⊢ natrec _ (U.wk (lift _) F) _ _ _
                      ≡ _ ∘ (natrec _ _ _ _ _) ^ _ ∷ x ^ _)
             (PE.sym (wk-β F))
             (natrec-suc (wkTerm [ρ] ⊢Δ ⊢n)
                         (wk (lift [ρ]) (⊢Δ ∙ univ (ℕⱼ ⊢Δ)) ⊢F)
                         (PE.subst (λ x → Δ ⊢ U.wk ρ z ∷ x ^ _)
                                   (wk-β F)
                                   (wkTerm [ρ] ⊢Δ ⊢z))
                         (PE.subst (λ x → Δ ⊢ U.wk ρ s ∷ x ^ [ ! , ι l ])
                                   (wk-β-natrec _ F ! l)
                                   (wkTerm [ρ] ⊢Δ ⊢s)))
  wkEqTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (Emptyrec-cong {A = A} {A' = A'} {e = e} {e' = e'} A≡A' ⊢e ⊢e') =
    Emptyrec-cong (wkEq [ρ] ⊢Δ A≡A') (wkTerm [ρ] ⊢Δ ⊢e) (wkTerm [ρ] ⊢Δ ⊢e')
  wkEqTerm [ρ] ⊢Δ (proof-irrelevance t u) = proof-irrelevance (wkTerm [ρ] ⊢Δ t) (wkTerm [ρ] ⊢Δ u)
  wkEqTerm ρ ⊢Δ (Id-cong A t u) = Id-cong (wkEqTerm ρ ⊢Δ A) (wkEqTerm ρ ⊢Δ t) (wkEqTerm ρ ⊢Δ u)
  wkEqTerm ρ ⊢Δ (cast-refl A e t) = cast-refl (wkEqTerm ρ ⊢Δ A) (wkTerm ρ ⊢Δ e) (wkTerm ρ ⊢Δ t)
  wkEqTerm ρ ⊢Δ (cast-cong A B t e e') = cast-cong (wkEqTerm ρ ⊢Δ A) (wkEqTerm ρ ⊢Δ B) (wkEqTerm ρ ⊢Δ t) (wkTerm ρ ⊢Δ e) (wkTerm ρ ⊢Δ e')
  wkEqTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (cast-Π {A = A} {A' = A'} {rA = rA} {B = B} {B' = B'} {e = e} {f = f} Aⱼ Bⱼ A'ⱼ B'ⱼ eⱼ fⱼ) = let l = ⁰ in let lA = ⁰ in let lB = ⁰ in
    let ρA = wkTerm [ρ] ⊢Δ Aⱼ in
    let ρA' = wkTerm [ρ] ⊢Δ A'ⱼ in
    let ρB = wkTerm (lift [ρ]) (⊢Δ ∙ (univ ρA)) Bⱼ in
    let ρB' = wkTerm (lift [ρ]) (⊢Δ ∙ (univ ρA')) B'ⱼ in
    let ρe = wkTerm [ρ] ⊢Δ eⱼ in
    let ρf = wkTerm [ρ] ⊢Δ fⱼ in
    let pred = λ A1 A1' e1 f1 → Δ ⊢ U.wk ρ (cast l (Π A ^ rA ° lA ▹ B ° lB ° l ^ _) (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ _) e f) ≡ (lam (U.wk ρ A') ▹ (let a = cast l A1' A1 (Idsym (Univ rA l) A1 A1' (fst e1)) (var 0) in cast l ((U.wk (lift ρ) B) [ a ]↑) (U.wk (lift ρ) B') ((snd e1) ∘ (var 0) ^ ⁰) (f1 ∘ a ^ l)) ^ l) ∷ U.wk ρ (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ _) ^ [ ! , _ ] in
    let j0 : pred (wk1 (U.wk ρ A)) (wk1 (U.wk ρ A')) (wk1 (U.wk ρ e)) (wk1 (U.wk ρ f))
        j0 = cast-Π ρA ρB ρA' ρB' ρe ρf
    in
    let j1 = PE.subst (λ x → pred x (wk1 (U.wk ρ A')) (wk1 (U.wk ρ e)) (wk1 (U.wk ρ f))) (wk1-wk≡lift-wk1 ρ A) j0 in
    let j2 = PE.subst (λ x → pred (U.wk (lift ρ) (wk1 A)) x (wk1 (U.wk ρ e)) (wk1 (U.wk ρ f))) (wk1-wk≡lift-wk1 ρ A') j1 in
    let j3 = PE.subst (λ x → pred (U.wk (lift ρ) (wk1 A)) (U.wk (lift ρ) (wk1 A')) x (wk1 (U.wk ρ f))) (wk1-wk≡lift-wk1 ρ e) j2 in
    let j4 = PE.subst (λ x → pred (U.wk (lift ρ) (wk1 A)) (U.wk (lift ρ) (wk1 A')) (U.wk (lift ρ) (wk1 e)) x) (wk1-wk≡lift-wk1 ρ f) j3 in
    let j5 = PE.subst (λ x → Δ ⊢ U.wk ρ (cast l (Π A ^ rA ° lA ▹ B ° lB ° l ^ !) (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ !) e f) ≡ (lam (U.wk ρ A') ▹ (let a = cast l (U.wk (lift ρ) (wk1 A')) (U.wk (lift ρ) (wk1 A)) x (var 0) in cast l ((U.wk (lift ρ) B) [ a ]↑) (U.wk (lift ρ) B') ((snd (U.wk (lift ρ) (wk1 e))) ∘ (var 0) ^ ⁰) ((U.wk (lift ρ) (wk1 f)) ∘ a ^ l)) ^ l) ∷ U.wk ρ (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ !) ^ [ ! , ι l ]) (PE.sym (wk-Idsym (lift ρ) (Univ rA l) (wk1 A) (wk1 A') (fst (wk1 e)))) j4 in
    PE.subst (λ x → Δ ⊢ U.wk ρ (cast l (Π A ^ rA ° lA ▹ B ° lB ° l ^ _) (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ _) e f) ≡ (lam (U.wk ρ A') ▹ (let a = U.wk (lift ρ) (cast l (wk1 A') (wk1 A) (Idsym (Univ rA l) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0)) in cast l x (U.wk (lift ρ) B') ((snd (U.wk (lift ρ) (wk1 e))) ∘ (var 0) ^ ⁰) ((U.wk (lift ρ) (wk1 f)) ∘ a ^ l)) ^ l) ∷ U.wk ρ (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ _) ^ [ ! , ι l ]) (PE.sym (wk-β↑ {ρ = ρ} {a = (cast l (wk1 A') (wk1 A) (Idsym (Univ rA l) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0))} B)) j5
  wkEqTerm ρ ⊢Δ (cast-ℕ-0 e) = cast-ℕ-0 (wkTerm ρ ⊢Δ e)
  wkEqTerm ρ ⊢Δ (cast-ℕ-S e n) = cast-ℕ-S (wkTerm ρ ⊢Δ e) (wkTerm ρ ⊢Δ n)

wkIsLambda : ∀ {ρ} → (t : Term) → IsLambda (U.wk ρ t) → IsLambda t
wkIsLambda (gen (Lamkind l) (⟦ 0 , t ⟧ Tools.List.∷ ⟦ 1 , t₁ ⟧ Tools.List.∷ Tools.List.[])) X = lamₙ

wkIsNatural : ∀ {ρ} → (t : Term) → IsNatural (U.wk ρ t) → IsNatural t
wkIsNatural (gen Zerokind Tools.List.[]) X = zeroₙ
wkIsNatural (gen Suckind (⟦ 0 , t ⟧ Tools.List.∷ Tools.List.[])) X = sucₙ

wkIsType : ∀ {ρ} → (t : Term) → IsType (U.wk ρ t) → IsType t
wkIsType (Univ x x₁) X = Uₙ
wkIsType (gen (Pikind x x₁ x₂ x₃ x₄) (⟦ 0 , A ⟧ Tools.List.∷ ⟦ 1 , B ⟧ Tools.List.∷ Tools.List.[])) X = Πₙ
wkIsType (gen Natkind Tools.List.[]) X = ℕₙ
wkIsType (gen (Emptykind x) Tools.List.[]) X = Emptyₙ
wkIsType (gen Idkind (⟦ 0 , A ⟧ Tools.List.∷ ⟦ 0 , t ⟧ Tools.List.∷ ⟦ 0 , u ⟧ Tools.List.∷ Tools.List.[])) X = Idₙ


mutual
  wkRed : ∀ {Γ Δ A B r ρ} → ρ ∷ Δ ⊆ Γ →
           let ρA = U.wk ρ A
               ρB = U.wk ρ B
           in ⊢ Δ → Γ ⊢ A ⇒ B ^ r → Δ ⊢ ρA ⇒ ρB ^ r
  wkRed ρ ⊢Δ (univ A⇒B) = univ (wkRedTerm ρ ⊢Δ A⇒B)

  wkRedTerm : ∀ {Γ Δ A l t u ρ} → ρ ∷ Δ ⊆ Γ →
           let ρA = U.wk ρ A
               ρt = U.wk ρ t
               ρu = U.wk ρ u
           in ⊢ Δ → Γ ⊢ t ⇒ u ∷ A ^ l → Δ ⊢ ρt ⇒ ρu ∷ ρA ^ l
  wkRedTerm ρ ⊢Δ (conv t⇒u A≡B) = conv (wkRedTerm ρ ⊢Δ t⇒u) (wkEq ρ ⊢Δ A≡B)
  wkRedTerm ρ ⊢Δ (app-subst {B = B} ⊢F ⊢G t⇒u a notlam) =
    let ρF = wkTerm ρ ⊢Δ ⊢F
    in PE.subst (λ x → _ ⊢ _ ⇒ _ ∷ x ^ _) (PE.sym (wk-β B))
             (app-subst  (wkTerm ρ ⊢Δ ⊢F) (wkTerm (lift ρ) (⊢Δ ∙ univ ρF) ⊢G) (wkRedTerm ρ ⊢Δ t⇒u) (wkTerm ρ ⊢Δ a) λ x → notlam (wkIsLambda _ x))
  wkRedTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (app-subst' {B = B} ⊢F ⊢G t net a⇒b) =
    let ρF = wkTerm [ρ] ⊢Δ ⊢F
    in PE.subst (λ x → _ ⊢ _ ⇒ _ ∷ x ^ _) (PE.sym (wk-β B))
             (app-subst'  (wkTerm [ρ] ⊢Δ ⊢F) (wkTerm (lift [ρ]) (⊢Δ ∙ univ ρF) ⊢G) (wkTerm [ρ] ⊢Δ t) (wkNeutral ρ net) (wkRedTerm [ρ] ⊢Δ a⇒b))
  wkRedTerm ρ ⊢Δ (β-red {A} {B} {lF} {lG} {a} {t} l< l<' ⊢A ⊢B ⊢t ⊢a) =
    let ⊢ρA = wk ρ ⊢Δ ⊢A
    in  PE.subst (λ x → _ ⊢ _ ⇒ _ ∷ x ^ _) (PE.sym (wk-β B))
                 (PE.subst (λ x → _ ⊢ U.wk _ ((lam _ ▹ t ^ _) ∘ a ^ _) ⇒ x ∷ _ ^ _)
                           (PE.sym (wk-β t))
                           (β-red l< l<' ⊢ρA (wkTerm (lift ρ) (⊢Δ ∙ ⊢ρA) ⊢B) (wkTerm (lift ρ) (⊢Δ ∙ ⊢ρA) ⊢t)
                                      (wkTerm ρ ⊢Δ ⊢a)))
  wkRedTerm [ρ] ⊢Δ (suc-subst n⇒n′) = suc-subst (wkRedTerm [ρ] ⊢Δ n⇒n′)
  wkRedTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-subst {s = s} {F = F} {l = l} ⊢F ⊢z ⊢s n⇒n′ notNat) =
    PE.subst (λ x → _ ⊢ natrec _ _ _ _ _ ⇒ _ ∷ x ^ _) (PE.sym (wk-β F))
             (natrec-subst (wk (lift [ρ]) (⊢Δ ∙ univ (ℕⱼ ⊢Δ)) ⊢F)
                           (PE.subst (λ x → _ ⊢ _ ∷ x ^ _) (wk-β F)
                                     (wkTerm [ρ] ⊢Δ ⊢z))
                           (PE.subst (λ x → Δ ⊢ U.wk ρ s ∷ x ^ [ ! , ι l ])
                                     (wk-β-natrec _ F ! l)
                                     (wkTerm [ρ] ⊢Δ ⊢s))
                           (wkRedTerm [ρ] ⊢Δ n⇒n′)
                           λ x → notNat (wkIsNatural _ x))
  wkRedTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-substF {s = s} {F = F} {l = l} F⇒F′ ⊢z ⊢s ⊢n nen) =
    PE.subst (λ x → _ ⊢ natrec _ _ _ _ _ ⇒ _ ∷ x ^ _) (PE.sym (wk-β F))
             (natrec-substF (wkRed (lift [ρ]) (⊢Δ ∙ univ (ℕⱼ ⊢Δ)) F⇒F′)
                           (PE.subst (λ x → _ ⊢ _ ∷ x ^ _) (wk-β F)
                                     (wkTerm [ρ] ⊢Δ ⊢z))
                           (PE.subst (λ x → Δ ⊢ U.wk ρ s ∷ x ^ [ ! , ι l ])
                                     (wk-β-natrec _ F ! l)
                                     (wkTerm [ρ] ⊢Δ ⊢s))
                           (wkTerm [ρ] ⊢Δ ⊢n)
                           (wkNeutral ρ nen))
  wkRedTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-substZ {s = s} {F = F} {l = l} ⊢F z⇒z′ ⊢s ⊢n nen nfF) =
    PE.subst (λ x → _ ⊢ natrec _ _ _ _ _ ⇒ natrec _ _ _ _ _ ∷ x ^ _) (PE.sym (wk-β F))
             (natrec-substZ (wk (lift [ρ]) (⊢Δ ∙ univ (ℕⱼ ⊢Δ)) ⊢F)
                           (PE.subst (λ x → _ ⊢ _ ⇒ _ ∷ x ^ _) (wk-β F)
                                     (wkRedTerm [ρ] ⊢Δ z⇒z′))
                           (PE.subst (λ x → Δ ⊢ U.wk ρ s ∷ x ^ [ ! , ι l ])
                                     (wk-β-natrec ρ F ! l)
                                     (wkTerm [ρ] ⊢Δ ⊢s))
                           (wkTerm [ρ] ⊢Δ ⊢n)
                           (wkNeutral ρ nen)
                           (wkNf (lift ρ) nfF))
  wkRedTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-substS {s = s} {s′ = s′} {F = F} {l = l} ⊢F ⊢z s⇒s′ ⊢n nen nfF nfZ) =
    PE.subst (λ x → _ ⊢ natrec _ _ _ _ _ ⇒ natrec _ _ _ _ _ ∷ x ^ _) (PE.sym (wk-β F))
             (natrec-substS (wk (lift [ρ]) (⊢Δ ∙ univ (ℕⱼ ⊢Δ)) ⊢F)
                           (PE.subst (λ x → _ ⊢ _ ∷ x ^ _) (wk-β F)
                                     (wkTerm [ρ] ⊢Δ ⊢z))
                           (PE.subst (λ x → Δ ⊢ U.wk ρ s ⇒ U.wk ρ s′ ∷ x ^ ι l)
                                     (wk-β-natrec ρ F ! l)
                                     (wkRedTerm [ρ] ⊢Δ s⇒s′))
                           (wkTerm [ρ] ⊢Δ ⊢n)
                           (wkNeutral ρ nen)
                           (wkNf (lift ρ) nfF)
                           (wkNf ρ nfZ))
  wkRedTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-zero {s = s} {F = F} {l = l} ⊢F ⊢z ⊢s) =
    PE.subst (λ x → _ ⊢ natrec _ (U.wk (lift ρ) F) _ _ _ ⇒ _ ∷ x ^ _)
             (PE.sym (wk-β F))
             (natrec-zero (wk (lift [ρ]) (⊢Δ ∙ univ (ℕⱼ ⊢Δ)) ⊢F)
                          (PE.subst (λ x → _ ⊢ _ ∷ x ^ _)
                                    (wk-β F)
                                    (wkTerm [ρ] ⊢Δ ⊢z))
                          (PE.subst (λ x → Δ ⊢ U.wk ρ s ∷ x ^ [ ! , ι l ])
                                    (wk-β-natrec ρ F ! l)
                                    (wkTerm [ρ] ⊢Δ ⊢s)))
  wkRedTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-suc {s = s} {F = F} {l = l} ⊢n ⊢F ⊢z ⊢s) =
    PE.subst (λ x → _ ⊢ natrec _ _ _ _ _ ⇒ _ ∘ natrec _ _ _ _ _ ^ _ ∷ x  ^ _)
             (PE.sym (wk-β F))
             (natrec-suc (wkTerm [ρ] ⊢Δ ⊢n)
                         (wk (lift [ρ]) (⊢Δ ∙ univ (ℕⱼ ⊢Δ)) ⊢F)
                         (PE.subst (λ x → _ ⊢ _ ∷ x ^ _)
                                   (wk-β F)
                                   (wkTerm [ρ] ⊢Δ ⊢z))
                         (PE.subst (λ x → Δ ⊢ U.wk ρ s ∷ x ^ [ ! , ι l ])
                                   (wk-β-natrec ρ F ! l)
                                   (wkTerm [ρ] ⊢Δ ⊢s)))
  wkRedTerm ρ ⊢Δ  (cast-subst A B e t notType) = cast-subst (wkRedTerm ρ ⊢Δ A) (wkTerm ρ ⊢Δ  B) (wkTerm ρ ⊢Δ e) (wkTerm ρ ⊢Δ t) λ x → notType (wkIsType _ x)
  wkRedTerm {Γ} {Δ} {A} {l} {t'} {u} {ρ₁} ρ ⊢Δ  (cast-ne-subst K neK B e t notType) = cast-ne-subst (wkTerm ρ ⊢Δ K) (wkNeutral ρ₁ neK) (wkRedTerm ρ ⊢Δ  B) (wkTerm ρ ⊢Δ e) (wkTerm ρ ⊢Δ t) λ x → notType (wkIsType _ x)
  wkRedTerm ρ ⊢Δ  (cast-ℕ-subst B e t notType) = cast-ℕ-subst (wkRedTerm ρ ⊢Δ B) (wkTerm ρ ⊢Δ e) (wkTerm ρ ⊢Δ t) λ x → notType (wkIsType _ x)
  wkRedTerm ρ ⊢Δ  (cast-Π-subst A P B e t notType) =
    let ρA = wkTerm ρ ⊢Δ A
    in cast-Π-subst ρA (wkTerm (lift ρ) (⊢Δ ∙ (univ ρA)) P) (wkRedTerm ρ ⊢Δ B) (wkTerm ρ ⊢Δ e) (wkTerm ρ ⊢Δ t) λ x → notType (wkIsType _ x)
  wkRedTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (cast-Π {A = A} {A' = A'} {rA = rA} {B = B} {B' = B'} {e = e} {f = f} Aⱼ Bⱼ A'ⱼ B'ⱼ eⱼ fⱼ) = let l = ⁰ in let lA = ⁰ in let lB = ⁰ in
    let ρA = wkTerm [ρ] ⊢Δ Aⱼ in
    let ρA' = wkTerm [ρ] ⊢Δ A'ⱼ in
    let ρB = wkTerm (lift [ρ]) (⊢Δ ∙ (univ ρA)) Bⱼ in
    let ρB' = wkTerm (lift [ρ]) (⊢Δ ∙ (univ ρA')) B'ⱼ in
    let ρe = wkTerm [ρ] ⊢Δ eⱼ in
    let ρf = wkTerm [ρ] ⊢Δ fⱼ in
    let pred = λ A1 A1' e1 f1 → Δ ⊢ U.wk ρ (cast l (Π A ^ rA ° lA ▹ B ° lB ° l ^ _) (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ _) e f) ⇒ (lam (U.wk ρ A') ▹ (let a = cast l A1' A1 (Idsym (Univ rA l) A1 A1' (fst e1)) (var 0) in cast l ((U.wk (lift ρ) B) [ a ]↑) (U.wk (lift ρ) B') ((snd e1) ∘ (var 0) ^ ⁰) (f1 ∘ a ^ l))  ^ l) ∷ U.wk ρ (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ _) ^ _ in
    let j0 : pred (wk1 (U.wk ρ A)) (wk1 (U.wk ρ A')) (wk1 (U.wk ρ e)) (wk1 (U.wk ρ f))
        j0 = cast-Π ρA ρB ρA' ρB' ρe ρf
    in
    let j1 = PE.subst (λ x → pred x (wk1 (U.wk ρ A')) (wk1 (U.wk ρ e)) (wk1 (U.wk ρ f))) (wk1-wk≡lift-wk1 ρ A) j0 in
    let j2 = PE.subst (λ x → pred (U.wk (lift ρ) (wk1 A)) x (wk1 (U.wk ρ e)) (wk1 (U.wk ρ f))) (wk1-wk≡lift-wk1 ρ A') j1 in
    let j3 = PE.subst (λ x → pred (U.wk (lift ρ) (wk1 A)) (U.wk (lift ρ) (wk1 A')) x (wk1 (U.wk ρ f))) (wk1-wk≡lift-wk1 ρ e) j2 in
    let j4 = PE.subst (λ x → pred (U.wk (lift ρ) (wk1 A)) (U.wk (lift ρ) (wk1 A')) (U.wk (lift ρ) (wk1 e)) x) (wk1-wk≡lift-wk1 ρ f) j3 in
    let j5 = PE.subst (λ x → Δ ⊢ U.wk ρ (cast l (Π A ^ rA ° lA ▹ B ° lB ° l ^ !) (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ !) e f) ⇒ (lam (U.wk ρ A') ▹ (let a = cast l (U.wk (lift ρ) (wk1 A')) (U.wk (lift ρ) (wk1 A)) x (var 0) in cast l ((U.wk (lift ρ) B) [ a ]↑) (U.wk (lift ρ) B') ((snd (U.wk (lift ρ) (wk1 e))) ∘ (var 0) ^ ⁰) ((U.wk (lift ρ) (wk1 f)) ∘ a ^ l)) ^ l) ∷ U.wk ρ (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ !) ^ ι l) (PE.sym (wk-Idsym (lift ρ) (Univ rA l) (wk1 A) (wk1 A') (fst (wk1 e)))) j4 in
   PE.subst (λ x → Δ ⊢ U.wk ρ (cast l (Π A ^ rA ° lA ▹ B ° lB ° l ^ _) (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ _) e f) ⇒ (lam (U.wk ρ A') ▹ (let a = U.wk (lift ρ) (cast l (wk1 A') (wk1 A) (Idsym (Univ rA l) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0)) in cast l x (U.wk (lift ρ) B') ((snd (U.wk (lift ρ) (wk1 e))) ∘ (var 0) ^ ⁰) ((U.wk (lift ρ) (wk1 f)) ∘ a ^ l)) ^ l) ∷ U.wk ρ (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ _) ^ ι l) (PE.sym (wk-β↑ {ρ = ρ} {a = (cast l (wk1 A') (wk1 A) (Idsym (Univ rA l) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0))} B)) j5
  wkRedTerm ρ ⊢Δ (cast-ℕ-0 e) = cast-ℕ-0 (wkTerm ρ ⊢Δ e)
  wkRedTerm ρ ⊢Δ (cast-ℕ-S e n) = cast-ℕ-S (wkTerm ρ ⊢Δ e) (wkTerm ρ ⊢Δ n)
  wkRedTerm ρ ⊢Δ (cast-ℕ-cong e n notNat) = cast-ℕ-cong (wkTerm ρ ⊢Δ e) (wkRedTerm ρ ⊢Δ n)  λ x → notNat (wkIsNatural _ x)
  wkRedTerm {ρ = ρ₁} ρ ⊢Δ (cast-ne-cong K neK L neL e n) = cast-ne-cong (wkTerm ρ ⊢Δ K) (wkNeutral ρ₁ neK) (wkTerm ρ ⊢Δ L) (wkNeutral ρ₁ neL) (wkTerm ρ ⊢Δ e) (wkRedTerm ρ ⊢Δ n)
  
wkRed* : ∀ {Γ Δ A B r ρ} → ρ ∷ Δ ⊆ Γ →
           let ρA = U.wk ρ A
               ρB = U.wk ρ B
           in ⊢ Δ → Γ ⊢ A ⇒* B ^ r → Δ ⊢ ρA ⇒* ρB ^ r
wkRed* ρ ⊢Δ (id A) = id (wk ρ ⊢Δ A)
wkRed* ρ ⊢Δ (A⇒A′ ⇨ A′⇒*B) = wkRed ρ ⊢Δ A⇒A′ ⇨ wkRed* ρ ⊢Δ A′⇒*B

wkRed*Term : ∀ {Γ Δ A l t u ρ} → ρ ∷ Δ ⊆ Γ →
           let ρA = U.wk ρ A
               ρt = U.wk ρ t
               ρu = U.wk ρ u
           in ⊢ Δ → Γ ⊢ t ⇒* u ∷ A ^ l → Δ ⊢ ρt ⇒* ρu ∷ ρA ^ l
wkRed*Term ρ ⊢Δ (id t) = id (wkTerm ρ ⊢Δ t)
wkRed*Term ρ ⊢Δ (t⇒t′ ⇨ t′⇒*u) = wkRedTerm ρ ⊢Δ t⇒t′ ⇨ wkRed*Term ρ ⊢Δ t′⇒*u

wkRed:*: : ∀ {Γ Δ A B r ρ} → ρ ∷ Δ ⊆ Γ →
         let ρA = U.wk ρ A
             ρB = U.wk ρ B
         in ⊢ Δ → Γ ⊢ A :⇒*: B ^ r → Δ ⊢ ρA :⇒*: ρB ^ r
wkRed:*: ρ ⊢Δ [[ ⊢A , ⊢B , D ]] = [[ wk ρ ⊢Δ ⊢A , wk ρ ⊢Δ ⊢B , wkRed* ρ ⊢Δ D ]]

wkRed:*:Term : ∀ {Γ Δ A l t u ρ} → ρ ∷ Δ ⊆ Γ →
             let ρA = U.wk ρ A
                 ρt = U.wk ρ t
                 ρu = U.wk ρ u
             in ⊢ Δ → Γ ⊢ t :⇒*: u ∷ A ^ l → Δ ⊢ ρt :⇒*: ρu ∷ ρA ^ l
wkRed:*:Term ρ ⊢Δ [[ ⊢t , ⊢u , d ]] = [[ wkTerm ρ ⊢Δ ⊢t , wkTerm ρ ⊢Δ ⊢u , wkRed*Term ρ ⊢Δ d ]]
