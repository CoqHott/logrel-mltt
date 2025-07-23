{-# OPTIONS --safe #-}

module Definition.Typed.Substitution where

open import Definition.Untyped as U hiding (subst)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Weakening

import Tools.PropositionalEquality as PE


-- Weakening of judgements

substIndex : ∀ {Γ Δ n A r ρ} → Δ ⊢ˢ ρ ∷ Γ →
        let ρA = U.subst ρ A
            ρn = substVar ρ n
        in n ∷ A ^ r ∈ Γ → Δ ⊢ ρn ∷ ρA ^ r
substIndex {ρ = ρ} (_,_ {A = A} ρ' x) here =  PE.subst (λ x → _ ⊢ _ ∷ x ^ _) (PE.sym (subst-wk1 ρ A)) x
substIndex (ρ' , x) (there {A = A} i) = let x' = substIndex ρ' i in PE.subst (λ x → _ ⊢ _ ∷ x ^ _) (PE.sym (subst-wk1 _ A)) x'


tailLiftSubst : ∀ {Γ Δ A r ρ} → ⊢ Δ → Δ ⊢ˢ ρ ∷ Γ → Δ ⊢ A ^ r → (Δ ∙ A ^ r) ⊢ˢ tail (liftSubst ρ) ∷ Γ
tailLiftSubst {ρ = ρ} ⊢Δ id ⊢A = id
tailLiftSubst {ρ = ρ} ⊢Δ (_,_ {A = A} x x₁) ⊢A = tailLiftSubst ⊢Δ x ⊢A ,
  let x' = wkTerm (step id) (⊢Δ ∙ ⊢A) x₁ in PE.subst (λ x → _ ⊢ _ ∷ x ^ _) (liftsubst-wk1 (tail ρ) A) x'

substLift : ∀ {Γ Δ A l r ρ} → ⊢ Δ → Δ ⊢ U.subst ρ A ^ [ r , l ] → Δ ⊢ˢ ρ ∷ Γ →
  (Δ ∙ U.subst ρ A ^ [ r , l ]) ⊢ˢ liftSubst ρ ∷ (Γ ∙ A ^ [ r , l ])
substLift {Γ} {Δ} {A} {l} {r} {ρ} ⊢Δ ⊢A [ρ] = tailLiftSubst ⊢Δ [ρ] ⊢A , var (⊢Δ ∙ ⊢A) (PE.subst (λ x → _ ∷ x ^ _ ∈ (Δ ∙ U.subst ρ A ^ [ r , l ])) (liftsubst-wk1 ρ A) here)

mutual
  subst : ∀ {Γ Δ A r ρ} → Δ ⊢ˢ ρ ∷ Γ →
     let ρA = U.subst ρ A
     in  ⊢ Δ → Γ ⊢ A ^ r → Δ ⊢ ρA ^ r
  subst ρ ⊢Δ (Uⱼ ⊢Γ) = Uⱼ ⊢Δ
  subst ρ ⊢Δ (univ A) = univ (substTerm ρ ⊢Δ A)



  substTerm : ∀ {Γ Δ A t r ρ} → Δ ⊢ˢ ρ ∷ Γ →
         let ρA = U.subst ρ A
             ρt = U.subst ρ t
         in ⊢ Δ → Γ ⊢ t ∷ A ^ r → Δ ⊢ ρt ∷ ρA ^ r
  substTerm ρ ⊢Δ (univ <l ⊢Γ) = univ <l ⊢Δ
  substTerm ρ ⊢Δ (ℕⱼ ⊢Γ) = ℕⱼ ⊢Δ
  substTerm ρ ⊢Δ (Emptyⱼ ⊢Γ) = Emptyⱼ ⊢Δ
  substTerm ρ ⊢Δ (Πⱼ <l ▹ <l' ▹ F ▹ G) = let ρF = substTerm ρ ⊢Δ F
                                      in  Πⱼ <l ▹ <l' ▹ ρF ▹ (substTerm (substLift ⊢Δ (univ ρF) ρ) (⊢Δ ∙ univ ρF) G)
  substTerm ρ ⊢Δ (var ⊢Γ x) = substIndex ρ x
  substTerm ρ ⊢Δ (lamⱼ <l <l' F t) = let ρF = subst ρ ⊢Δ F
                                  in lamⱼ <l <l' ρF (substTerm (substLift ⊢Δ ρF ρ) (⊢Δ ∙ ρF) t)
  substTerm ρ ⊢Δ (_▹_▹_▹_∘ⱼ_ {F = F} {G = G} r% ⊢F ⊢G g a) = let ρF = substTerm ρ ⊢Δ ⊢F
                                                     in  PE.subst (λ x → _ ⊢ _ ∷ x ^ _)
                                                         (PE.sym (singleSubstLift G _))
                                                         (r% ▹ substTerm ρ ⊢Δ ⊢F ▹ substTerm (substLift ⊢Δ (univ ρF) ρ) (⊢Δ ∙ univ ρF) ⊢G ▹ substTerm ρ ⊢Δ g ∘ⱼ substTerm ρ ⊢Δ a)
  substTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (fstⱼ {A = A} {A' = A'} {rA = rA} {B = B} {B' = B'} {e = e} Aⱼ Bⱼ A'ⱼ B'ⱼ eⱼ) =
    let ρA = substTerm [ρ] ⊢Δ Aⱼ in
    let ρA' = substTerm [ρ] ⊢Δ A'ⱼ in
    let ρB = substTerm (substLift ⊢Δ (univ ρA) [ρ]) (⊢Δ ∙ (univ ρA)) Bⱼ in
    let ρB' = substTerm (substLift ⊢Δ (univ ρA') [ρ]) (⊢Δ ∙ (univ ρA')) B'ⱼ in
    let ρe = substTerm [ρ] ⊢Δ eⱼ in
    fstⱼ ρA ρB ρA' ρB' ρe 
  substTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (sndⱼ {A = A} {A' = A'} {rA = rA} {B = B} {B' = B'} {e = e} Aⱼ Bⱼ A'ⱼ B'ⱼ eⱼ) =
    let ρA = substTerm [ρ] ⊢Δ Aⱼ in
    let ρA' = substTerm [ρ] ⊢Δ A'ⱼ in
    let ρB = substTerm (substLift ⊢Δ (univ ρA) [ρ]) (⊢Δ ∙ (univ ρA)) Bⱼ in
    let ρB' = substTerm (substLift ⊢Δ (univ ρA') [ρ]) (⊢Δ ∙ (univ ρA')) B'ⱼ in
    let ρe = substTerm [ρ] ⊢Δ eⱼ in
    let l = ⁰ in
    let l' = ⁰ in     
    let pred = λ A1 A1' A2' B1 B1' E → Δ ⊢ U.subst ρ (snd e) ∷ Π A1' ^ rA ° ⁰ ▹ Id (U l) (B1 [ cast l A2' A1 (Idsym (Univ rA l) A1 A2' (fst E)) (var 0) ]↑) B1' ° l' ° l' ^ % ^ [ % , _ ] in
    let j1 : pred (wk1 (U.subst ρ A)) (U.subst ρ A') (wk1 (U.subst ρ A')) (U.subst (liftSubst ρ) B) (U.subst (liftSubst ρ) B') (wk1 (U.subst ρ e))
        j1 = sndⱼ ρA ρB ρA' ρB' ρe in 
    let j2 = PE.subst (λ x → pred x (U.subst ρ A') (wk1 (U.subst ρ A')) (U.subst (liftSubst ρ) B) (U.subst (liftSubst ρ) B') (wk1 (U.subst ρ e)))
                      (PE.sym (Idsym-subst-lemma ρ A)) j1 in
    let j3 = PE.subst (λ x → pred (U.subst (liftSubst ρ) (wk1 A)) (U.subst ρ A') x  (U.subst (liftSubst ρ) B) (U.subst (liftSubst ρ) B') (wk1 (U.subst ρ e)))
                      (PE.sym (Idsym-subst-lemma ρ A')) j2 in
    let j4 = PE.subst (λ x → pred (U.subst (liftSubst ρ) (wk1 A)) (U.subst ρ A') _ (U.subst (liftSubst ρ) B) (U.subst (liftSubst ρ) B') x)
                      (PE.sym (Idsym-subst-lemma ρ e)) j3 in
    let j5 = PE.subst (λ x → Δ ⊢ U.subst ρ (snd e) ∷  Π U.subst ρ A' ^ rA ° ⁰ ▹ Id (U l) (U.subst (liftSubst ρ) B [ (cast l (U.subst (liftSubst ρ) (wk1 A')) (U.subst (liftSubst ρ) (wk1 A)) x (var 0)) ]↑) (U.subst (liftSubst ρ) B') ° l' ° l' ^ % ^ [ % , ι ⁰ ])
                      (PE.sym (subst-Idsym (liftSubst ρ) (Univ rA l) (wk1 A) (wk1 A') (fst (wk1 e))))
                      j4 in
    PE.subst (λ x → Δ ⊢ U.subst ρ (snd e) ∷  Π U.subst ρ A' ^ rA ° ⁰ ▹ Id (U l) x (U.subst (liftSubst ρ) B') ° l' ° l' ^ % ^ [ % , _ ])
             (PE.sym (singleSubstLift↑ ρ B (cast l (wk1 A') (wk1 A) (Idsym (Univ rA l) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0)))) j5
  substTerm ρ ⊢Δ (zeroⱼ ⊢Γ) = zeroⱼ ⊢Δ
  substTerm ρ ⊢Δ (sucⱼ n) = sucⱼ (substTerm ρ ⊢Δ n)
  substTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrecⱼ {G = G} {rG = rG} {lG = lG}  {s = s} rGlG ⊢G ⊢z ⊢s ⊢n) =
    PE.subst (λ x → _ ⊢ natrec _ _ _ _ _ ∷ x ^ _) (PE.sym (singleSubstLift G _))
             (natrecⱼ rGlG
                      (subst (substLift ⊢Δ (univ (ℕⱼ ⊢Δ)) [ρ]) (⊢Δ ∙ univ (ℕⱼ ⊢Δ)) ⊢G)
                      (PE.subst (λ x → _ ⊢ _ ∷ x ^ _) (singleSubstLift G _) (substTerm [ρ] ⊢Δ ⊢z))
                      (PE.subst (λ x → Δ ⊢ U.subst ρ s ∷ x ^ [ rG , ι lG ])
                                (subst-β-natrec ρ G rG lG)
                                (substTerm [ρ] ⊢Δ ⊢s))
                      (substTerm [ρ] ⊢Δ ⊢n))
  substTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (Emptyrecⱼ {A = A} {e = e} ⊢A ⊢e) =
    (Emptyrecⱼ (subst [ρ] ⊢Δ ⊢A) (substTerm [ρ] ⊢Δ ⊢e))
  substTerm ρ ⊢Δ (Idⱼ A t u) = Idⱼ (substTerm ρ ⊢Δ A) (substTerm ρ ⊢Δ t) (substTerm ρ ⊢Δ u)
  substTerm ρ ⊢Δ (Idreflⱼ t) = Idreflⱼ (substTerm ρ ⊢Δ t)
  substTerm ρ ⊢Δ (transpⱼ {P = P} A Pⱼ t s u e) =
    let ρA = subst ρ ⊢Δ A in
    let ρP = subst (substLift ⊢Δ ρA ρ) (⊢Δ ∙ ρA) Pⱼ in
    let ρt = substTerm ρ ⊢Δ t in
    let ρs = PE.subst (λ x → _ ⊢ _ ∷ x ^ _) (singleSubstLift P _) (substTerm ρ ⊢Δ s) in
    let ρu = substTerm ρ ⊢Δ u in
    let ρe = substTerm ρ ⊢Δ e in
    PE.subst (λ x → _ ⊢ transp _ _ _ _ _ _ ∷ x ^ _) (PE.sym (singleSubstLift P _))
      (transpⱼ ρA ρP ρt ρs ρu ρe)
  substTerm ρ ⊢Δ (castⱼ A B e t) =
    castⱼ (substTerm ρ ⊢Δ A) (substTerm ρ ⊢Δ B) (substTerm ρ ⊢Δ e) (substTerm ρ ⊢Δ t)
  substTerm ρ ⊢Δ (conv t A≡B) = conv (substTerm ρ ⊢Δ t) (substEq ρ ⊢Δ A≡B)


  substEq : ∀ {Γ Δ A B r ρ} → Δ ⊢ˢ ρ ∷ Γ →
       let ρA = U.subst ρ A
           ρB = U.subst ρ B
       in ⊢ Δ → Γ ⊢ A ≡ B ^ r → Δ ⊢ ρA ≡ ρB ^ r
  substEq ρ ⊢Δ (univ A≡B) = univ (substEqTerm ρ ⊢Δ A≡B)
  substEq ρ ⊢Δ (refl A) = refl (subst ρ ⊢Δ A)
  substEq ρ ⊢Δ (sym A≡B) = sym (substEq ρ ⊢Δ A≡B)
  substEq ρ ⊢Δ (trans A≡B B≡C) = trans (substEq ρ ⊢Δ A≡B) (substEq ρ ⊢Δ B≡C)

  substEqTerm : ∀ {Γ Δ A t u r ρ} → Δ ⊢ˢ ρ ∷ Γ →
           let ρA = U.subst ρ A
               ρt = U.subst ρ t
               ρu = U.subst ρ u
           in ⊢ Δ → Γ ⊢ t ≡ u ∷ A ^ r → Δ ⊢ ρt ≡ ρu ∷ ρA ^ r
  substEqTerm ρ ⊢Δ (refl t) = refl (substTerm ρ ⊢Δ t)
  substEqTerm ρ ⊢Δ (sym t≡u) = sym (substEqTerm ρ ⊢Δ t≡u)
  substEqTerm ρ ⊢Δ (trans t≡u u≡r) = trans (substEqTerm ρ ⊢Δ t≡u) (substEqTerm ρ ⊢Δ u≡r)
  substEqTerm ρ ⊢Δ (conv t≡u A≡B) = conv (substEqTerm ρ ⊢Δ t≡u) (substEq ρ ⊢Δ A≡B)
  substEqTerm ρ ⊢Δ (Π-cong <l <l' F F≡H G≡E) =
    let ρF = subst ρ ⊢Δ F
    in  Π-cong <l <l' ρF (substEqTerm ρ ⊢Δ F≡H)
                         (substEqTerm (substLift ⊢Δ ρF ρ) (⊢Δ ∙ ρF) G≡E)
  substEqTerm ρ ⊢Δ (app-cong {G = G} f≡g a≡b) =
    PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x ^ _)
             (PE.sym (singleSubstLift G _))
             (app-cong (substEqTerm ρ ⊢Δ f≡g) (substEqTerm ρ ⊢Δ a≡b))
  substEqTerm ρ ⊢Δ (β-red {a = a} {t = t} {F = F} {G = G} l< l<' ⊢F ⊢t ⊢a) =
    let ρF = subst ρ ⊢Δ ⊢F
    in  PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x ^ _)
                 (PE.sym (singleSubstLift G _))
                 (PE.subst (λ x → _ ⊢ U.subst _ ((lam F ▹ t ^ _) ∘ a ^ _) ≡ x ∷ _ ^ _)
                           (PE.sym (singleSubstLift t _))
                           (β-red l< l<' ρF (substTerm (substLift ⊢Δ ρF ρ) (⊢Δ ∙ ρF) ⊢t)
                                     (substTerm ρ ⊢Δ ⊢a)))
  substEqTerm {ρ = ρ} [ρ] ⊢Δ (η-eq {f = t} {g = u} lF lG F f g f0≡g0) =
    let ρF = subst [ρ] ⊢Δ F
    in  η-eq lF lG ρF (substTerm [ρ] ⊢Δ f)
                (substTerm [ρ] ⊢Δ g)
                (PE.subst (λ t → _ ⊢ t ∘ _ ^ _ ≡ _ ∷ _ ^ _)
                          (Idsym-subst-lemma ρ t)
                          (PE.subst (λ t → _ ⊢ _ ≡ t ∘ _ ^ _ ∷ _ ^ _)
                                    (Idsym-subst-lemma ρ u)
                                    (substEqTerm (substLift ⊢Δ ρF [ρ]) (⊢Δ ∙ ρF) f0≡g0)))
  substEqTerm ρ ⊢Δ (suc-cong m≡n) = suc-cong (substEqTerm ρ ⊢Δ m≡n)
  substEqTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-cong {s = s} {s′ = s′} {F = F} {l = l}
                                     F≡F′ z≡z′ s≡s′ n≡n′) =
    PE.subst (λ x → Δ ⊢ natrec _ _ _ _ _ ≡ _ ∷ x ^ _) (PE.sym (singleSubstLift F _))
             (natrec-cong (substEq (substLift ⊢Δ (univ (ℕⱼ ⊢Δ)) [ρ]) (⊢Δ ∙ univ (ℕⱼ ⊢Δ)) F≡F′)
                          (PE.subst (λ x → Δ ⊢ _ ≡ _ ∷ x ^ _) (singleSubstLift F _)
                                    (substEqTerm [ρ] ⊢Δ z≡z′))
                          (PE.subst (λ x → Δ ⊢ U.subst ρ s
                                             ≡ U.subst ρ s′ ∷ x ^ [ ! , ι l ])
                                    (subst-β-natrec _ F ! l)
                                    (substEqTerm [ρ] ⊢Δ s≡s′))
                          (substEqTerm [ρ] ⊢Δ n≡n′))
  substEqTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-zero {z} {s} {F} {l = l} ⊢F ⊢z ⊢s) =
    PE.subst (λ x → Δ ⊢ natrec _ (U.subst (liftSubst _) F) _ _ _ ≡ _ ∷ x ^ _)
             (PE.sym (singleSubstLift F _))
             (natrec-zero (subst (substLift ⊢Δ (univ (ℕⱼ ⊢Δ)) [ρ]) (⊢Δ ∙ univ (ℕⱼ ⊢Δ)) ⊢F)
                          (PE.subst (λ x → Δ ⊢ U.subst ρ z ∷ x ^ _)
                                    (singleSubstLift F _)
                                    (substTerm [ρ] ⊢Δ ⊢z))
                          (PE.subst (λ x → Δ ⊢ U.subst ρ s ∷ x ^ [ ! , ι l ])
                                    (subst-β-natrec _ F ! l)
                                    (substTerm [ρ] ⊢Δ ⊢s)))
  substEqTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-suc {n} {z} {s} {F} {l = l} ⊢n ⊢F ⊢z ⊢s) =
    PE.subst (λ x → Δ ⊢ natrec _ (U.subst (liftSubst _) F) _ _ _
                      ≡ _ ∘ (natrec _ _ _ _ _) ^ _ ∷ x ^ _)
             (PE.sym (singleSubstLift F _))
             (natrec-suc (substTerm [ρ] ⊢Δ ⊢n)
                         (subst (substLift ⊢Δ (univ (ℕⱼ ⊢Δ)) [ρ]) (⊢Δ ∙ univ (ℕⱼ ⊢Δ)) ⊢F)
                         (PE.subst (λ x → Δ ⊢ U.subst ρ z ∷ x ^ _)
                                   (singleSubstLift F _)
                                   (substTerm [ρ] ⊢Δ ⊢z))
                         (PE.subst (λ x → Δ ⊢ U.subst ρ s ∷ x ^ [ ! , ι l ])
                                   (subst-β-natrec _ F ! l)
                                   (substTerm [ρ] ⊢Δ ⊢s)))
  substEqTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (Emptyrec-cong {A = A} {A' = A'} {e = e} {e' = e'} A≡A' ⊢e ⊢e') =
    Emptyrec-cong (substEq [ρ] ⊢Δ A≡A') (substTerm [ρ] ⊢Δ ⊢e) (substTerm [ρ] ⊢Δ ⊢e')
  substEqTerm [ρ] ⊢Δ (proof-irrelevance t u) = proof-irrelevance (substTerm [ρ] ⊢Δ t) (substTerm [ρ] ⊢Δ u)
  substEqTerm ρ ⊢Δ (Id-cong A t u) = Id-cong (substEqTerm ρ ⊢Δ A) (substEqTerm ρ ⊢Δ t) (substEqTerm ρ ⊢Δ u)
  substEqTerm ρ ⊢Δ (cast-refl A e t) = cast-refl (substEqTerm ρ ⊢Δ A) (substTerm ρ ⊢Δ e) (substTerm ρ ⊢Δ t)
  substEqTerm ρ ⊢Δ (cast-cong A B t e e') = cast-cong (substEqTerm ρ ⊢Δ A) (substEqTerm ρ ⊢Δ B) (substEqTerm ρ ⊢Δ t) (substTerm ρ ⊢Δ e) (substTerm ρ ⊢Δ e')
  substEqTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (cast-Π {A = A} {A' = A'} {rA = rA} {B = B} {B' = B'} {e = e} {f = f} Aⱼ Bⱼ A'ⱼ B'ⱼ eⱼ fⱼ) = let l = ⁰ in let lA = ⁰ in let lB = ⁰ in
    let ρA = substTerm [ρ] ⊢Δ Aⱼ in
    let ρA' = substTerm [ρ] ⊢Δ A'ⱼ in
    let ρB = substTerm (substLift ⊢Δ (univ ρA) [ρ]) (⊢Δ ∙ (univ ρA)) Bⱼ in
    let ρB' = substTerm (substLift ⊢Δ (univ ρA') [ρ]) (⊢Δ ∙ (univ ρA')) B'ⱼ in
    let ρe = substTerm [ρ] ⊢Δ eⱼ in
    let ρf = substTerm [ρ] ⊢Δ fⱼ in
    let pred = λ A1 A1' e1 f1 → Δ ⊢ U.subst ρ (cast l (Π A ^ rA ° lA ▹ B ° lB ° l ^ _) (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ _) e f) ≡ (lam (U.subst ρ A') ▹ (let a = cast l A1' A1 (Idsym (Univ rA l) A1 A1' (fst e1)) (var 0) in cast l ((U.subst (liftSubst ρ) B) [ a ]↑) (U.subst (liftSubst ρ) B') ((snd e1) ∘ (var 0) ^ ⁰) (f1 ∘ a ^ l)) ^ l) ∷ U.subst ρ (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ _) ^ [ ! , _ ] in
    let j0 : pred (wk1 (U.subst ρ A)) (wk1 (U.subst ρ A')) (wk1 (U.subst ρ e)) (wk1 (U.subst ρ f))
        j0 = cast-Π ρA ρB ρA' ρB' ρe ρf
    in
    let j1 = PE.subst (λ x → pred x (wk1 (U.subst ρ A')) (wk1 (U.subst ρ e)) (wk1 (U.subst ρ f))) (PE.sym (Idsym-subst-lemma ρ A)) j0 in
    let j2 = PE.subst (λ x → pred (U.subst (liftSubst ρ) (wk1 A)) x (wk1 (U.subst ρ e)) (wk1 (U.subst ρ f))) (PE.sym (Idsym-subst-lemma ρ A')) j1 in
    let j3 = PE.subst (λ x → pred (U.subst (liftSubst ρ) (wk1 A)) (U.subst (liftSubst ρ) (wk1 A')) x (wk1 (U.subst ρ f))) (PE.sym (Idsym-subst-lemma ρ e)) j2 in
    let j4 = PE.subst (λ x → pred (U.subst (liftSubst ρ) (wk1 A)) (U.subst (liftSubst ρ) (wk1 A')) (U.subst (liftSubst ρ) (wk1 e)) x) (PE.sym (Idsym-subst-lemma ρ f)) j3 in
    let j5 = PE.subst (λ x → Δ ⊢ U.subst ρ (cast l (Π A ^ rA ° lA ▹ B ° lB ° l ^ !) (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ !) e f) ≡ (lam (U.subst ρ A') ▹ (let a = cast l (U.subst (liftSubst ρ) (wk1 A')) (U.subst (liftSubst ρ) (wk1 A)) x (var 0) in cast l ((U.subst (liftSubst ρ) B) [ a ]↑) (U.subst (liftSubst ρ) B') ((snd (U.subst (liftSubst ρ) (wk1 e))) ∘ (var 0) ^ ⁰) ((U.subst (liftSubst ρ) (wk1 f)) ∘ a ^ l)) ^ l) ∷ U.subst ρ (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ !) ^ [ ! , ι l ]) (PE.sym (subst-Idsym (liftSubst ρ) (Univ rA l) (wk1 A) (wk1 A') (fst (wk1 e)))) j4 in
    PE.subst (λ x → Δ ⊢ U.subst ρ (cast l (Π A ^ rA ° lA ▹ B ° lB ° l ^ _) (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ _) e f) ≡ (lam (U.subst ρ A') ▹ (let a = U.subst (liftSubst ρ) (cast l (wk1 A') (wk1 A) (Idsym (Univ rA l) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0)) in cast l x (U.subst (liftSubst ρ) B') ((snd (U.subst (liftSubst ρ) (wk1 e))) ∘ (var 0) ^ ⁰) ((U.subst (liftSubst ρ) (wk1 f)) ∘ a ^ l)) ^ l) ∷ U.subst ρ (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ _) ^ [ ! , ι l ]) (PE.sym (singleSubstLift↑ ρ B (cast l (wk1 A') (wk1 A) (Idsym (Univ rA l) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0)))) j5
  substEqTerm ρ ⊢Δ (cast-ℕ-0 e) = cast-ℕ-0 (substTerm ρ ⊢Δ e)
  substEqTerm ρ ⊢Δ (cast-ℕ-S e n) = cast-ℕ-S (substTerm ρ ⊢Δ e) (substTerm ρ ⊢Δ n)

{-
mutual
  substRed : ∀ {Γ Δ A B r ρ} → ρ ∷ Δ ⊆ Γ →
           let ρA = U.subst ρ A
               ρB = U.subst ρ B
           in ⊢ Δ → Γ ⊢ A ⇒ B ^ r → Δ ⊢ ρA ⇒ ρB ^ r
  substRed ρ ⊢Δ (univ A⇒B) = univ (substRedTerm ρ ⊢Δ A⇒B)

  substRedTerm : ∀ {Γ Δ A l t u ρ} → ρ ∷ Δ ⊆ Γ →
           let ρA = U.subst ρ A
               ρt = U.subst ρ t
               ρu = U.subst ρ u
           in ⊢ Δ → Γ ⊢ t ⇒ u ∷ A ^ l → Δ ⊢ ρt ⇒ ρu ∷ ρA ^ l
  substRedTerm ρ ⊢Δ (conv t⇒u A≡B) = conv (substRedTerm ρ ⊢Δ t⇒u) (substEq ρ ⊢Δ A≡B)
  substRedTerm ρ ⊢Δ (app-subst {B = B} ⊢F ⊢G t⇒u a) =
    let ρF = substTerm ρ ⊢Δ ⊢F
    in PE.subst (λ x → _ ⊢ _ ⇒ _ ∷ x ^ _) (PE.sym (subst-β B))
             (app-subst  (substTerm ρ ⊢Δ ⊢F) (substTerm (liftSubst ρ) (⊢Δ ∙ univ ρF) ⊢G) (substRedTerm ρ ⊢Δ t⇒u) (substTerm ρ ⊢Δ a))
  substRedTerm ρ ⊢Δ (β-red {A} {B} {lF} {lG} {a} {t} l< l<' ⊢A ⊢B ⊢t ⊢a) =
    let ⊢ρA = subst ρ ⊢Δ ⊢A
    in  PE.subst (λ x → _ ⊢ _ ⇒ _ ∷ x ^ _) (PE.sym (subst-β B))
                 (PE.subst (λ x → _ ⊢ U.subst _ ((lam _ ▹ t ^ _) ∘ a ^ _) ⇒ x ∷ _ ^ _)
                           (PE.sym (subst-β t))
                           (β-red l< l<' ⊢ρA (substTerm (liftSubst ρ) (⊢Δ ∙ ⊢ρA) ⊢B) (substTerm (liftSubst ρ) (⊢Δ ∙ ⊢ρA) ⊢t)
                                      (substTerm ρ ⊢Δ ⊢a)))
  substRedTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-subst {s = s} {F = F} {l = l} ⊢F ⊢z ⊢s n⇒n′) =
    PE.subst (λ x → _ ⊢ natrec _ _ _ _ _ ⇒ _ ∷ x ^ _) (PE.sym (subst-β F))
             (natrec-subst (subst (lift [ρ]) (⊢Δ ∙ univ (ℕⱼ ⊢Δ)) ⊢F)
                           (PE.subst (λ x → _ ⊢ _ ∷ x ^ _) (subst-β F)
                                     (substTerm [ρ] ⊢Δ ⊢z))
                           (PE.subst (λ x → Δ ⊢ U.subst ρ s ∷ x ^ [ ! , ι l ])
                                     (subst-β-natrec _ F ! l)
                                     (substTerm [ρ] ⊢Δ ⊢s))
                           (substRedTerm [ρ] ⊢Δ n⇒n′))
  substRedTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-zero {s = s} {F = F} {l = l} ⊢F ⊢z ⊢s) =
    PE.subst (λ x → _ ⊢ natrec _ (U.subst (liftSubst ρ) F) _ _ _ ⇒ _ ∷ x ^ _)
             (PE.sym (subst-β F))
             (natrec-zero (subst (lift [ρ]) (⊢Δ ∙ univ (ℕⱼ ⊢Δ)) ⊢F)
                          (PE.subst (λ x → _ ⊢ _ ∷ x ^ _)
                                    (subst-β F)
                                    (substTerm [ρ] ⊢Δ ⊢z))
                          (PE.subst (λ x → Δ ⊢ U.subst ρ s ∷ x ^ [ ! , ι l ])
                                    (subst-β-natrec ρ F ! l)
                                    (substTerm [ρ] ⊢Δ ⊢s)))
  substRedTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (natrec-suc {s = s} {F = F} {l = l} ⊢n ⊢F ⊢z ⊢s) =
    PE.subst (λ x → _ ⊢ natrec _ _ _ _ _ ⇒ _ ∘ natrec _ _ _ _ _ ^ _ ∷ x  ^ _)
             (PE.sym (subst-β F))
             (natrec-suc (substTerm [ρ] ⊢Δ ⊢n)
                         (subst (lift [ρ]) (⊢Δ ∙ univ (ℕⱼ ⊢Δ)) ⊢F)
                         (PE.subst (λ x → _ ⊢ _ ∷ x ^ _)
                                   (subst-β F)
                                   (substTerm [ρ] ⊢Δ ⊢z))
                         (PE.subst (λ x → Δ ⊢ U.subst ρ s ∷ x ^ [ ! , ι l ])
                                   (subst-β-natrec ρ F ! l)
                                   (substTerm [ρ] ⊢Δ ⊢s)))
  substRedTerm ρ ⊢Δ  (cast-subst A B e t) = cast-subst (substRedTerm ρ ⊢Δ A) (substTerm ρ ⊢Δ  B) (substTerm ρ ⊢Δ e) (substTerm ρ ⊢Δ t)
  substRedTerm {Γ} {Δ} {A} {l} {t'} {u} {ρ₁} ρ ⊢Δ  (cast-ne-subst K neK B e t) = cast-ne-subst (substTerm ρ ⊢Δ K) (substNeutral ρ₁ neK) (substRedTerm ρ ⊢Δ  B) (substTerm ρ ⊢Δ e) (substTerm ρ ⊢Δ t)
  substRedTerm ρ ⊢Δ  (cast-ℕ-subst B e t) = cast-ℕ-subst (substRedTerm ρ ⊢Δ B) (substTerm ρ ⊢Δ e) (substTerm ρ ⊢Δ t)
  substRedTerm ρ ⊢Δ  (cast-Π-subst A P B e t) = let ρA = substTerm ρ ⊢Δ A in cast-Π-subst ρA (substTerm (liftSubst ρ) (⊢Δ ∙ (univ ρA)) P) (substRedTerm ρ ⊢Δ B) (substTerm ρ ⊢Δ e) (substTerm ρ ⊢Δ t)
  substRedTerm {Δ = Δ} {ρ = ρ} [ρ] ⊢Δ (cast-Π {A = A} {A' = A'} {rA = rA} {B = B} {B' = B'} {e = e} {f = f} Aⱼ Bⱼ A'ⱼ B'ⱼ eⱼ fⱼ) = let l = ⁰ in let lA = ⁰ in let lB = ⁰ in
    let ρA = substTerm [ρ] ⊢Δ Aⱼ in
    let ρA' = substTerm [ρ] ⊢Δ A'ⱼ in
    let ρB = substTerm (lift [ρ]) (⊢Δ ∙ (univ ρA)) Bⱼ in
    let ρB' = substTerm (lift [ρ]) (⊢Δ ∙ (univ ρA')) B'ⱼ in
    let ρe = substTerm [ρ] ⊢Δ eⱼ in
    let ρf = substTerm [ρ] ⊢Δ fⱼ in
    let pred = λ A1 A1' e1 f1 → Δ ⊢ U.subst ρ (cast l (Π A ^ rA ° lA ▹ B ° lB ° l ^ _) (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ _) e f) ⇒ (lam (U.subst ρ A') ▹ (let a = cast l A1' A1 (Idsym (Univ rA l) A1 A1' (fst e1)) (var 0) in cast l ((U.subst (liftSubst ρ) B) [ a ]↑) (U.subst (liftSubst ρ) B') ((snd e1) ∘ (var 0) ^ ⁰) (f1 ∘ a ^ l))  ^ l) ∷ U.subst ρ (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ _) ^ _ in
    let j0 : pred (wk1 (U.subst ρ A)) (wk1 (U.subst ρ A')) (wk1 (U.subst ρ e)) (wk1 (U.subst ρ f))
        j0 = cast-Π ρA ρB ρA' ρB' ρe ρf
    in
    let j1 = PE.subst (λ x → pred x (wk1 (U.subst ρ A')) (wk1 (U.subst ρ e)) (wk1 (U.subst ρ f))) (wk1-subst≡lift-wk1 ρ A) j0 in
    let j2 = PE.subst (λ x → pred (U.subst (liftSubst ρ) (wk1 A)) x (wk1 (U.subst ρ e)) (wk1 (U.subst ρ f))) (wk1-subst≡lift-wk1 ρ A') j1 in
    let j3 = PE.subst (λ x → pred (U.subst (liftSubst ρ) (wk1 A)) (U.subst (liftSubst ρ) (wk1 A')) x (wk1 (U.subst ρ f))) (wk1-subst≡lift-wk1 ρ e) j2 in
    let j4 = PE.subst (λ x → pred (U.subst (liftSubst ρ) (wk1 A)) (U.subst (liftSubst ρ) (wk1 A')) (U.subst (liftSubst ρ) (wk1 e)) x) (wk1-subst≡lift-wk1 ρ f) j3 in
    let j5 = PE.subst (λ x → Δ ⊢ U.subst ρ (cast l (Π A ^ rA ° lA ▹ B ° lB ° l ^ !) (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ !) e f) ⇒ (lam (U.subst ρ A') ▹ (let a = cast l (U.subst (liftSubst ρ) (wk1 A')) (U.subst (liftSubst ρ) (wk1 A)) x (var 0) in cast l ((U.subst (liftSubst ρ) B) [ a ]↑) (U.subst (liftSubst ρ) B') ((snd (U.subst (liftSubst ρ) (wk1 e))) ∘ (var 0) ^ ⁰) ((U.subst (liftSubst ρ) (wk1 f)) ∘ a ^ l)) ^ l) ∷ U.subst ρ (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ !) ^ ι l) (PE.sym (subst-Idsym (liftSubst ρ) (Univ rA l) (wk1 A) (wk1 A') (fst (wk1 e)))) j4 in
   PE.subst (λ x → Δ ⊢ U.subst ρ (cast l (Π A ^ rA ° lA ▹ B ° lB ° l ^ _) (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ _) e f) ⇒ (lam (U.subst ρ A') ▹ (let a = U.subst (liftSubst ρ) (cast l (wk1 A') (wk1 A) (Idsym (Univ rA l) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0)) in cast l x (U.subst (liftSubst ρ) B') ((snd (U.subst (liftSubst ρ) (wk1 e))) ∘ (var 0) ^ ⁰) ((U.subst (liftSubst ρ) (wk1 f)) ∘ a ^ l)) ^ l) ∷ U.subst ρ (Π A' ^ rA ° lA ▹ B' ° lB ° l ^ _) ^ ι l) (PE.sym (subst-β↑ {ρ = ρ} {a = (cast l (wk1 A') (wk1 A) (Idsym (Univ rA l) (wk1 A) (wk1 A') (fst (wk1 e))) (var 0))} B)) j5
  substRedTerm ρ ⊢Δ (cast-ℕ-0 e) = cast-ℕ-0 (substTerm ρ ⊢Δ e)
  substRedTerm ρ ⊢Δ (cast-ℕ-S e n) = cast-ℕ-S (substTerm ρ ⊢Δ e) (substTerm ρ ⊢Δ n)
  substRedTerm ρ ⊢Δ (cast-ℕ-cong e n) = cast-ℕ-cong (substTerm ρ ⊢Δ e) (substRedTerm ρ ⊢Δ n)
  substRedTerm {ρ = ρ₁} ρ ⊢Δ (cast-ne-cong K neK L neL e n) = cast-ne-cong (substTerm ρ ⊢Δ K) (substNeutral ρ₁ neK) (substTerm ρ ⊢Δ L) (substNeutral ρ₁ neL) (substTerm ρ ⊢Δ e) (substRedTerm ρ ⊢Δ n)
  
substRed* : ∀ {Γ Δ A B r ρ} → ρ ∷ Δ ⊆ Γ →
           let ρA = U.subst ρ A
               ρB = U.subst ρ B
           in ⊢ Δ → Γ ⊢ A ⇒* B ^ r → Δ ⊢ ρA ⇒* ρB ^ r
substRed* ρ ⊢Δ (id A) = id (subst ρ ⊢Δ A)
substRed* ρ ⊢Δ (A⇒A′ ⇨ A′⇒*B) = substRed ρ ⊢Δ A⇒A′ ⇨ substRed* ρ ⊢Δ A′⇒*B

substRed*Term : ∀ {Γ Δ A l t u ρ} → ρ ∷ Δ ⊆ Γ →
           let ρA = U.subst ρ A
               ρt = U.subst ρ t
               ρu = U.subst ρ u
           in ⊢ Δ → Γ ⊢ t ⇒* u ∷ A ^ l → Δ ⊢ ρt ⇒* ρu ∷ ρA ^ l
substRed*Term ρ ⊢Δ (id t) = id (substTerm ρ ⊢Δ t)
substRed*Term ρ ⊢Δ (t⇒t′ ⇨ t′⇒*u) = substRedTerm ρ ⊢Δ t⇒t′ ⇨ substRed*Term ρ ⊢Δ t′⇒*u

substRed:*: : ∀ {Γ Δ A B r ρ} → ρ ∷ Δ ⊆ Γ →
         let ρA = U.subst ρ A
             ρB = U.subst ρ B
         in ⊢ Δ → Γ ⊢ A :⇒*: B ^ r → Δ ⊢ ρA :⇒*: ρB ^ r
substRed:*: ρ ⊢Δ [[ ⊢A , ⊢B , D ]] = [[ subst ρ ⊢Δ ⊢A , subst ρ ⊢Δ ⊢B , substRed* ρ ⊢Δ D ]]

substRed:*:Term : ∀ {Γ Δ A l t u ρ} → ρ ∷ Δ ⊆ Γ →
             let ρA = U.subst ρ A
                 ρt = U.subst ρ t
                 ρu = U.subst ρ u
             in ⊢ Δ → Γ ⊢ t :⇒*: u ∷ A ^ l → Δ ⊢ ρt :⇒*: ρu ∷ ρA ^ l
substRed:*:Term ρ ⊢Δ [[ ⊢t , ⊢u , d ]] =
  [[ substTerm ρ ⊢Δ ⊢t , substTerm ρ ⊢Δ ⊢u , substRed*Term ρ ⊢Δ d ]]
-}

