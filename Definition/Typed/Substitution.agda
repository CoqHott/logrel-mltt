{-# OPTIONS --safe #-}

module Definition.Typed.Substitution where

open import Definition.Untyped as U hiding (wk;subst)
open import Definition.Untyped.Properties
open import Definition.Typed
open import Definition.Typed.Weakening
open import Definition.Typed.Properties

open import Tools.Empty using (⊥; ⊥-elim)
import Tools.PropositionalEquality as PE
open import Tools.Product
open import Tools.Nat


-- Weakening of judgements

substIndex : ∀ {Γ Δ n A r ρ} → Δ ⊢ˢ ρ ∷ Γ →
        let ρA = U.subst ρ A
            ρn = substVar ρ n
        in n ∷ A ^ r ∈ Γ → Δ ⊢ ρn ∷ ρA ^ r
substIndex {ρ = ρ} (_,_ {A = A} ρ' x) here =  PE.subst (λ x → _ ⊢ _ ∷ x ^ _) (PE.sym (subst-wk1 ρ A)) x
substIndex (ρ' , x) (there {A = A} i) = let x' = substIndex ρ' i in PE.subst (λ x → _ ⊢ _ ∷ x ^ _) (PE.sym (subst-wk1 _ A)) x'

substIndexEq : ∀ {Γ Δ n A r ρ ρ′} → Δ ⊢ˢ ρ ≡ ρ′ ∷ Γ →
        let ρA = U.subst ρ A
            ρn = substVar ρ n
            ρn′ = substVar ρ′ n
        in n ∷ A ^ r ∈ Γ → Δ ⊢ ρn ≡ ρn′ ∷ ρA ^ r
substIndexEq {ρ = ρ} (_,_ {A = A} ρ' x) here = PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x ^ _) (PE.sym (subst-wk1 ρ A)) x
substIndexEq (ρ' , x) (there {A = A} i) = let x' = substIndexEq ρ' i in PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x ^ _) (PE.sym (subst-wk1 _ A)) x'

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
  substEqTerm ρ ⊢Δ (β-red {a = a} {t = t} {F = F} {G = G} l< l<' ⊢F ⊢G ⊢t ⊢a) =
    let ρF = subst ρ ⊢Δ ⊢F
    in  PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x ^ _)
                 (PE.sym (singleSubstLift G _))
                 (PE.subst (λ x → _ ⊢ U.subst _ ((lam F ▹ t ^ _) ∘ a ^ _) ≡ x ∷ _ ^ _)
                           (PE.sym (singleSubstLift t _))
                           (β-red l< l<' ρF (substTerm (substLift ⊢Δ ρF ρ) (⊢Δ ∙ ρF) ⊢G) (substTerm (substLift ⊢Δ ρF ρ) (⊢Δ ∙ ρF) ⊢t)
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



-- Reflexivity of well-formed substitution.

substRefl : ∀ {σ Γ Δ}
          → Δ ⊢ˢ σ ∷ Γ
          → Δ ⊢ˢ σ ≡ σ ∷ Γ
substRefl id = id
substRefl (σ , x) = substRefl σ , genRefl x

Wk-step : ∀ {Γ Δ ρ A r} → ⊢ Γ ∙ A ^ r → Γ ⊢ˢ ρ ∷ Δ → (Γ ∙ A ^ r) ⊢ˢ tail (liftSubst ρ) ∷ Δ
Wk-step ⊢ΓA id = id
Wk-step {ρ = ρ} ⊢ΓA (_,_ {A = A} ⊢Γ x) = Wk-step ⊢ΓA ⊢Γ ,
  PE.subst (λ A →  _  ⊢ _ ∷ A ^ _) (liftsubst-wk1 (tail ρ) A) (wkTerm (step id) ⊢ΓA x)

Wk-valid : ∀ {Γ Δ ρ} → ρ ∷ Γ ⊆ Δ → ⊢ Γ → Γ ⊢ˢ (toSubst ρ) ∷ Δ
Wk-valid {Γ} {ε} {ρ} [ρ] ⊢Γ = id
Wk-valid {.(Δ ∙ x ^ x₁)} {Δ ∙ x ^ x₁} {.id} id (_∙_ {Γ} {A} {r} ⊢Γ ⊢x) =  Wk-valid (step id) (⊢Γ ∙ ⊢x) , var (⊢Γ ∙ ⊢x) (PE.subst (λ x →  _ ∷ x ^ _ ∈ (Γ ∙ A ^ r )) (PE.trans (PE.sym (subst-id (wk1 A))) (subst-wk1 idSubst A)) here)
Wk-valid {.(_ ∙ _ ^ _)} {Δ ∙ x ^ x₁} {.(step _)} (step [ρ]) (_∙_ {Γ} {A} {r} ⊢Γ ⊢x) = let wkρ = Wk-valid [ρ] ⊢Γ in Wk-step (⊢Γ ∙ ⊢x) wkρ
Wk-valid {.(_ ∙ U.wk _ x ^ x₁)} {Δ ∙ x ^ x₁} {.(lift _)} (lift {ρ = ρ} [ρ]) (_∙_ {Γ} {A} {r} ⊢Γ ⊢x) = Wk-valid (step [ρ]) (⊢Γ ∙ ⊢x) , var (⊢Γ ∙ ⊢x) (PE.subst (λ x →  _ ∷ x ^ _ ∈ (Γ ∙ A ^ r ))
  (PE.trans (PE.cong wk1 (wk≡subst ρ x)) (liftsubst-wk1 (toSubst _) x)) here)

idSubst-valid : ∀ {Γ} → ⊢ Γ → Γ ⊢ˢ idSubst ∷ Γ
idSubst-valid ⊢Γ = Wk-valid id ⊢Γ


-- Weakening of well-formed substitution.
wkSubst′ : ∀ {ρ σ Γ Δ Δ′} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ) (⊢Δ′ : ⊢ Δ′)
           ([ρ] : ρ ∷ Δ′ ⊆ Δ)
           ([σ] : Δ ⊢ˢ σ ∷ Γ)
         → Δ′ ⊢ˢ ρ •ₛ σ ∷ Γ
wkSubst′ ε ⊢Δ ⊢Δ′ ρ id = id
wkSubst′ (_∙_ {Γ} {A} ⊢Γ ⊢A) ⊢Δ ⊢Δ′ ρ (tailσ , headσ) =
  wkSubst′ ⊢Γ ⊢Δ ⊢Δ′ ρ tailσ
  , PE.subst (λ x → _ ⊢ _ ∷ x ^ _) (wk-subst A) (wkTerm ρ ⊢Δ′ headσ)

wkSubstEq′ : ∀ {ρ σ σ' Γ Δ Δ′} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ) (⊢Δ′ : ⊢ Δ′)
           ([ρ] : ρ ∷ Δ′ ⊆ Δ)
           ([σ] : Δ ⊢ˢ σ ≡ σ' ∷ Γ)
         → Δ′ ⊢ˢ ρ •ₛ σ ≡ ρ •ₛ σ' ∷ Γ
wkSubstEq′ ⊢Γ ⊢Δ ⊢Δ′ ρ id = id
wkSubstEq′ (_∙_ {Γ} {A} ⊢Γ ⊢A) ⊢Δ ⊢Δ′ ρ (tailσ , headσ) = wkSubstEq′ ⊢Γ ⊢Δ ⊢Δ′ ρ tailσ ,
           PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x ^ _) (wk-subst A) (wkEqTerm ρ ⊢Δ′ headσ)

-- Weakening of well-formed substitution by one.
wk1Subst′ : ∀ {F rF σ Γ Δ} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
            (⊢F : Δ ⊢ F ^ rF)
            ([σ] : Δ ⊢ˢ σ ∷ Γ)
          → (Δ ∙ F ^ rF) ⊢ˢ wk1Subst σ ∷ Γ
wk1Subst′ ⊢Γ ⊢Δ ⊢F [σ] =
  wkSubst′ ⊢Γ ⊢Δ (⊢Δ ∙ ⊢F) (step id) [σ]

wk1SubstEq′ : ∀ {F rF σ σ' Γ Δ} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
            (⊢F : Δ ⊢ F ^ rF)
            ([σ] : Δ ⊢ˢ σ ≡ σ' ∷ Γ)
          → (Δ ∙ F ^ rF) ⊢ˢ wk1Subst σ ≡ wk1Subst σ' ∷ Γ
wk1SubstEq′ ⊢Γ ⊢Δ ⊢F [σ] =
  wkSubstEq′ ⊢Γ ⊢Δ (⊢Δ ∙ ⊢F) (step id) [σ]

-- Lifting of well-formed substitution.

liftSubst′ : ∀ {F rF σ Γ Δ} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
             (⊢F  : Γ ⊢ F ^ rF)
             ([σ] : Δ ⊢ˢ σ ∷ Γ)
           → (Δ ∙ U.subst σ F ^ rF) ⊢ˢ liftSubst σ ∷ Γ ∙ F ^ rF
liftSubst′ {F} {rF} {σ} {Γ} {Δ} ⊢Γ ⊢Δ ⊢F [σ] =
  let ⊢Δ∙F = ⊢Δ ∙ subst [σ] ⊢Δ ⊢F 
  in  wkSubst′ ⊢Γ ⊢Δ ⊢Δ∙F (step id) [σ]
  ,   var ⊢Δ∙F (PE.subst (λ x → 0 ∷ x ^ rF ∈ (Δ ∙ U.subst σ F ^ rF))
                         (wk-subst F) here)

singleSubst : ∀ {A t rA Γ} → Γ ⊢ t ∷ A ^ rA → Γ ⊢ˢ sgSubst t ∷ Γ ∙ A ^ rA
singleSubst {A} {rA = rA} t =
  let ⊢Γ = wfTerm t
  in  idSubst-valid ⊢Γ , PE.subst (λ x → _ ⊢ _ ∷ x ^ rA) (PE.sym (subst-id A)) t

substType : ∀ {t F rF G rG Γ} → Γ ∙ F ^ rF ⊢ G ^ rG → Γ ⊢ t ∷ F ^ rF → Γ ⊢ G [ t ] ^ rG
substType {t} {F} {G} ⊢G ⊢t =
  let ⊢Γ = wfTerm ⊢t
  in  subst (singleSubst ⊢t) ⊢Γ ⊢G 

singleSubst↑ : ∀ {A t rA Γ} → Γ ∙ A ^ rA ⊢ t ∷ wk1 A ^ rA
             → Γ ∙ A ^ rA ⊢ˢ consSubst (wk1Subst idSubst) t ∷ Γ ∙ A ^ rA
singleSubst↑ {A} {rA = rA} t with wfTerm t
... | ⊢Γ ∙ ⊢A = wk1Subst′ ⊢Γ ⊢Γ ⊢A (idSubst-valid ⊢Γ)
              , PE.subst (λ x → _ ∙ A ^ rA ⊢ _ ∷ x ^ _) (wk1-tailId A) t

subst↑Type : ∀ {t F rF G rG Γ}
           → Γ ∙ F ^ rF ⊢ G ^ rG
           → Γ ∙ F ^ rF ⊢ t ∷ wk1 F ^ rF
           → Γ ∙ F ^ rF ⊢ G [ t ]↑ ^ rG
subst↑Type ⊢G ⊢t = subst (singleSubst↑ ⊢t) (wfTerm ⊢t) ⊢G

convFirstTerm : ∀ {Γ t u A l } → Γ ⊢ t ≡ u ∷ A ^ l → Γ ⊢ t ∷ A ^ l × Γ ⊢ u ∷ A ^ l
convFirst : ∀ {Γ A B r} → Γ ⊢ A ≡ B ^ r → Γ ⊢ A ^ r × Γ ⊢ B ^ r

convFirstTerm (refl x) = x , x
convFirstTerm (sym X) = let res = convFirstTerm X in proj₂ res , proj₁ res
convFirstTerm (trans X X₁) = proj₁ (convFirstTerm X) , proj₂ (convFirstTerm X₁)
convFirstTerm (conv X x) = let res = convFirstTerm X in conv (proj₁ res) x , conv (proj₂ res) x
convFirstTerm (Π-cong x x₁ x₂ X X₁) = {!!}
convFirstTerm (app-cong X X₁) = {!!}
convFirstTerm (β-red {F = F} {lF = lA} {lG = lB} lA< lB< ⊢A ⊢B ⊢t ⊢a) = (λ abs → ⊥-elim (!≢% abs)) ▹ un-univ ⊢A ▹ ⊢B ▹ (lamⱼ (λ _ → lA< , lB<) (λ abs → ⊥-elim (!≢% abs)) ⊢A ⊢t) ∘ⱼ ⊢a , substTerm (idSubst-valid (wfTerm ⊢a) , PE.subst (λ x →  _ ⊢ _ ∷ x ^ _) (PE.sym (subst-id F)) ⊢a) (wfTerm ⊢a) ⊢t 
convFirstTerm (η-eq x x₁ x₂ x₃ x₄ X) = x₃ , x₄
convFirstTerm (suc-cong X) = sucⱼ (proj₁ (convFirstTerm X)) , sucⱼ (proj₂ (convFirstTerm X))
convFirstTerm (natrec-cong x X X₁ X₂) = {!!}
convFirstTerm (natrec-zero x x₁ x₂) = natrecⱼ (λ abs → ⊥-elim (!≢% abs)) x x₁ x₂ (zeroⱼ (wfTerm x₂)) , x₁
convFirstTerm (natrec-suc n F z s) = natrecⱼ (λ x → ⊥-elim (!≢% x)) F z s (sucⱼ n) ,
                                     let sn = ((λ x → ⊥-elim (!≢% x)) ▹ (ℕⱼ (wfTerm n)) ▹
                                                  (▹▹ⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ un-univ F ▹
                                                    un-univ (subst↑Type F (sucⱼ (var (wf F) here))) ) ▹ s ∘ⱼ n) in
                                     let snF = (λ abs → ⊥-elim (!≢% abs)) ▹ un-univ (substType F n) ▹
                                               un-univ (substType {!!} (sucⱼ (wkTerm (step id) (wfTerm n ∙ (substType F n)) n))) ▹
                                               sn ∘ⱼ (natrecⱼ (λ x → ⊥-elim (!≢% x)) F z s n) in
                                     {!!}
convFirstTerm (Emptyrec-cong x x₁ x₂) = Emptyrecⱼ (proj₁ (convFirst x)) x₁ , conv (Emptyrecⱼ (proj₂ (convFirst x)) x₂) (sym x)
convFirstTerm (proof-irrelevance x x₁) = x , x₁
convFirstTerm (Id-cong X X₁ X₂) = Idⱼ (proj₁ (convFirstTerm X)) (proj₁ (convFirstTerm X₁)) (proj₁ (convFirstTerm X₂)) ,
                                  Idⱼ (proj₂ (convFirstTerm X)) (conv (proj₂ (convFirstTerm X₁)) (univ X)) (conv (proj₂ (convFirstTerm X₂)) (univ X))
convFirstTerm (cast-refl X x x₁) = castⱼ  (proj₁ (convFirstTerm X)) (proj₂ (convFirstTerm X)) x x₁ , conv x₁ (univ X)
convFirstTerm (cast-cong X X₁ X₂ x x₁) = castⱼ (proj₁ (convFirstTerm X)) (proj₁ (convFirstTerm X₁)) x (proj₁ (convFirstTerm X₂)) ,
                           conv (castⱼ (proj₂ (convFirstTerm X)) (proj₂ (convFirstTerm X₁)) x₁ (conv (proj₂ (convFirstTerm X₂)) (univ X))) (sym (univ X₁))
convFirstTerm (cast-Π A B A' B' e f) = castⱼ (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ A ▹ B) (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → ⊥-elim (!≢% x)) ▹ A' ▹ B') e f , {!!}
convFirstTerm (cast-ℕ-0 e) = castⱼ (ℕⱼ (wfTerm e)) (ℕⱼ (wfTerm e)) e (zeroⱼ (wfTerm e)) , (zeroⱼ (wfTerm e))
convFirstTerm (cast-ℕ-S e n) = castⱼ (ℕⱼ (wfTerm e)) (ℕⱼ (wfTerm e)) e (sucⱼ n) , sucⱼ (castⱼ (ℕⱼ (wfTerm e)) (ℕⱼ (wfTerm e)) e n)

convFirst (univ A≡B) = univ (proj₁ (convFirstTerm A≡B)) , univ (proj₂ (convFirstTerm A≡B))  
convFirst (refl A) = A , A
convFirst (sym A≡B) = let res = convFirst A≡B in proj₂ res , proj₁ res
convFirst (trans A≡B B≡C) = proj₁ (convFirst A≡B) , proj₂ (convFirst B≡C)


validityCon :  ∀ {Γ A x r } → ⊢ Γ → x ∷ A ^ r ∈ Γ → Γ ⊢ A ^ r
validityCon (⊢Γ ∙ x) here = wk (step id) (⊢Γ ∙ x) x
validityCon (⊢Γ ∙ x) (there X) = wk (step id) (⊢Γ ∙ x) (validityCon ⊢Γ X)

validity : ∀ {Γ A t r} →
  Γ ⊢ t ∷ A ^ r → Γ ⊢ A ^ r
validity (univ 0<1 ⊢Γ) = Uⱼ ⊢Γ
validity (ℕⱼ ⊢Γ) = univ (univ 0<1 ⊢Γ)
validity (Emptyⱼ ⊢Γ) = univ (univ 0<1 ⊢Γ)
validity (Πⱼ_▹_▹_▹_ x x₁ X X₁) = univ-gen (wfTerm X)
validity (var x x₁) = validityCon x x₁
validity (lamⱼ <l <l' F t) = univ (Πⱼ <l ▹ <l' ▹ (un-univ F) ▹ (un-univ (validity t)))
validity (_▹_▹_▹_∘ⱼ_ {F = F} {G = G} r% ⊢F ⊢G g a) = substType (univ ⊢G) a
validity (fstⱼ X X₁ X₂ X₃ X₄) = univ (Idⱼ (univ 0<1 (wfTerm X)) X X₂)
validity (sndⱼ X X₁ X₂ X₃ X₄) = univ (Πⱼ (λ x → ≡is≤ PE.refl , ≡is≤ PE.refl) ▹ (λ x → PE.refl , PE.refl) ▹ X₂ ▹
  (Idⱼ (univ 0<1 (wfTerm X₃)) {!!} -- (un-univ (subst↑Type (univ {!!})  {!!}))
       X₃))
validity (zeroⱼ x) = univ (ℕⱼ x)
validity (sucⱼ X) = univ (ℕⱼ (wfTerm X))
validity (natrecⱼ x x₁ X X₁ X₂) = substType x₁ X₂
validity (Emptyrecⱼ x X) = x
validity (Idⱼ X X₁ X₂) = univ (univ 0<1 (wfTerm X))
validity (Idreflⱼ X) = univ (Idⱼ (un-univ (validity X)) X X)
validity (transpⱼ x x₁ X X₁ X₂ X₃) = substType x₁ X₂
validity (castⱼ X X₁ X₂ X₃) = univ X₁
validity (conv X x) = proj₂ (convFirst x)

validityEq : ∀ {Γ A t u r} →
  Γ ⊢ t ≡ u ∷ A ^ r → Γ ⊢ A ^ r
validityEq ⊢tu = validity (proj₁ (convFirstTerm ⊢tu))

validitySubst : ∀ {Γ Δ σ σ'} → Δ ⊢ˢ σ ≡ σ' ∷ Γ → Δ ⊢ˢ σ ∷ Γ 
validitySubst id = id 
validitySubst (ρ , x) = (validitySubst ρ , proj₁ (convFirstTerm x)) 

-- validitySubstSym : ∀ {Γ Δ σ σ'} → Δ ⊢ˢ σ ≡ σ' ∷ Γ → ⊢ Γ → ⊢ Δ → Δ ⊢ˢ σ' ∷ Γ 
-- validitySubstSym id ⊢Γ ⊢Δ = id
-- validitySubstSym (ρ , x) (⊢Γ ∙ ⊢A) ⊢Δ = validitySubstSym ρ ⊢Γ ⊢Δ , {!!}

liftSubstEq′ : ∀ {F rF σ ρ Γ Δ} (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
             (⊢F  : Γ ⊢ F ^ rF)
             ([σ] : Δ ⊢ˢ σ ≡ ρ ∷ Γ)
           → (Δ ∙ U.subst σ F ^ rF) ⊢ˢ liftSubst σ ≡ liftSubst ρ ∷ Γ ∙ F ^ rF
liftSubstEq′ {F} {rF} {σ} {ρ} {Γ} {Δ} ⊢Γ ⊢Δ ⊢F [σ] =
  let ⊢Δ∙F = ⊢Δ ∙ subst (validitySubst [σ]) ⊢Δ ⊢F 
  in wkSubstEq′ ⊢Γ ⊢Δ ⊢Δ∙F (step id) [σ] , PE.subst (λ x → (Δ ∙ U.subst σ F ^ rF) ⊢ _ ≡ _ ∷ x ^ rF)  (wk-subst F)
     (genRefl (var ⊢Δ∙F here))

mutual 
  symSubst : ∀ {Γ Δ ρ ρ′} → Δ ⊢ˢ ρ ≡ ρ′ ∷ Γ → ⊢ Γ → ⊢ Δ → Δ ⊢ˢ ρ′ ≡ ρ ∷ Γ
  symSubst id ⊢Γ ⊢Δ = id
  symSubst {Γ} {Δ} {ρ} {ρ′} (_,_ {A = A} {rA = [ ! , l ]} X x) (⊢Γ ∙ [A]) ⊢Δ = symSubst X ⊢Γ ⊢Δ , conv (sym x) (substConv X ⊢Δ [A])
  symSubst {Γ} {Δ} {ρ} {ρ′} (_,_ {A = A} {rA = [ % , l ]} X x) (⊢Γ ∙ [A]) ⊢Δ = symSubst X ⊢Γ ⊢Δ , 
    let x , y = convFirstTerm x in proof-irrelevance (conv y (substConv X ⊢Δ [A])) (conv x (substConv X ⊢Δ [A]))

  validitySubstSym : ∀ {Γ Δ σ σ'} → Δ ⊢ˢ σ ≡ σ' ∷ Γ → ⊢ Γ → ⊢ Δ → Δ ⊢ˢ σ' ∷ Γ 
  validitySubstSym ρ ⊢Γ ⊢Δ = validitySubst (symSubst ρ ⊢Γ ⊢Δ)

  substConv : ∀ {Γ Δ A r ρ ρ′} → Δ ⊢ˢ ρ ≡ ρ′ ∷ Γ →
         let ρA = U.subst ρ A
             ρA′ = U.subst ρ′ A
         in ⊢ Δ → Γ ⊢ A ^ r → Δ ⊢ ρA ≡ ρA′ ^ r
  substConv ρ ⊢Δ (Uⱼ x) = refl (Uⱼ ⊢Δ)
  substConv ρ ⊢Δ (univ x) = univ (substConvTerm ρ ⊢Δ x)

  substConvTerm : ∀ {Γ Δ A t r ρ ρ′} → Δ ⊢ˢ ρ ≡ ρ′ ∷ Γ →
         let ρA = U.subst ρ A
             ρt = U.subst ρ t
             ρt′ = U.subst ρ′ t
         in ⊢ Δ → Γ ⊢ t ∷ A ^ r → Δ ⊢ ρt ≡ ρt′ ∷ ρA ^ r
  substConvTerm ρ ⊢Δ (univ x x₁) = refl (univ x ⊢Δ)
  substConvTerm ρ ⊢Δ (ℕⱼ x) = refl (ℕⱼ ⊢Δ)
  substConvTerm ρ ⊢Δ (Emptyⱼ x) = refl (Emptyⱼ ⊢Δ)
  substConvTerm ρ ⊢Δ (Πⱼ x ▹ x₁ ▹ X ▹ X₁) = let F = (subst (validitySubst ρ) ⊢Δ (univ X)) in
                Π-cong x x₁ F (substConvTerm ρ ⊢Δ X) (substConvTerm (liftSubstEq′ (wfTerm X) ⊢Δ (univ X) ρ) (⊢Δ ∙ F) X₁)
  substConvTerm ρ ⊢Δ (var x x₁) = substIndexEq ρ x₁
  substConvTerm ρ ⊢Δ (lamⱼ {r = !} <l <l' F t) with <l PE.refl
  ... | (lF , lG ) = let F' = (subst (validitySubst ρ) ⊢Δ F) in
                     let F'' = (subst (validitySubstSym ρ (wf F) ⊢Δ) ⊢Δ F) in
        η-eq lF lG F' (lamⱼ <l <l' F' (substTerm (liftSubst′ (wf F) ⊢Δ F (validitySubst ρ)) (⊢Δ ∙ F') t))
                      (conv (lamⱼ <l <l' F'' (substTerm (liftSubst′ (wf F) ⊢Δ F (validitySubstSym ρ {!!} ⊢Δ)) (⊢Δ ∙ F'') t)) {!!})
                      {!!}
  substConvTerm ρ ⊢Δ (lamⱼ {r = %} <l <l' F t) = proof-irrelevance {!!} {!!}
  substConvTerm ρ ⊢Δ (x ▹ X ▹ X₁ ▹ X₂ ∘ⱼ X₃) = {!!}
  substConvTerm ρ ⊢Δ (fstⱼ X X₁ X₂ X₃ X₄) = {!!}
  substConvTerm ρ ⊢Δ (sndⱼ X X₁ X₂ X₃ X₄) = {!!}
  substConvTerm ρ ⊢Δ (zeroⱼ x) = {!!}
  substConvTerm ρ ⊢Δ (sucⱼ X) = {!!}
  substConvTerm ρ ⊢Δ (natrecⱼ x x₁ X X₁ X₂) = {!!}
  substConvTerm ρ ⊢Δ (Emptyrecⱼ x X) = {!!}
  substConvTerm ρ ⊢Δ (Idⱼ X X₁ X₂) = {!!}
  substConvTerm ρ ⊢Δ (Idreflⱼ X) = {!!}
  substConvTerm ρ ⊢Δ (transpⱼ x x₁ X X₁ X₂ X₃) = {!!}
  substConvTerm ρ ⊢Δ (castⱼ X X₁ X₂ X₃) = {!!}
  substConvTerm ρ ⊢Δ (conv X x) = {!!}

  substConvEqTerm : ∀ {Γ Δ A t u r ρ ρ′} → Δ ⊢ˢ ρ ≡ ρ′ ∷ Γ →
         let ρA = U.subst ρ A
             ρt = U.subst ρ t
             ρu = U.subst ρ′ u
         in ⊢ Δ → Γ ⊢ t ≡ u ∷ A ^ r → Δ ⊢ ρt ≡ ρu ∷ ρA ^ r
  substConvEqTerm ρ ⊢Δ (refl x) = substConvTerm ρ ⊢Δ x
  substConvEqTerm ρ ⊢Δ (sym X) = let ⊢u = proj₁ (convFirstTerm X) in
   conv (sym (substConvEqTerm (symSubst ρ (wfEqTerm X) ⊢Δ) ⊢Δ X))
     (substConv (symSubst ρ (wfEqTerm X) ⊢Δ) ⊢Δ (validity ⊢u))
  substConvEqTerm ρ ⊢Δ (trans X X₁) = trans (substConvEqTerm ρ ⊢Δ X)
    (conv (substConvEqTerm (substRefl (validitySubstSym ρ (wfEqTerm X) ⊢Δ)) ⊢Δ X₁) (substConv (symSubst ρ (wfEqTerm X) ⊢Δ) ⊢Δ (validityEq X)))
  substConvEqTerm ρ ⊢Δ (conv X x) = conv (substConvEqTerm ρ ⊢Δ X) (substConvEq (substRefl (validitySubst ρ)) ⊢Δ x)
  substConvEqTerm ρ ⊢Δ (Π-cong x x₁ x₂ X X₁) = {!!}
  substConvEqTerm ρ ⊢Δ (app-cong X X₁) = {!!}
  substConvEqTerm ρ ⊢Δ (β-red x x₁ x₂ X x₃ x₄) = {!!} -- β-red x x₁ ? ? ? {!!}
  substConvEqTerm ρ ⊢Δ (η-eq x x₁ x₂ x₃ x₄ X) = {!!}
  substConvEqTerm ρ ⊢Δ (suc-cong X) = suc-cong (substConvEqTerm ρ ⊢Δ X)
  substConvEqTerm ρ ⊢Δ (natrec-cong {F = F} x X X₁ X₂) = conv (natrec-cong
                  (substConvEq (liftSubstEq′ (wfEqTerm X) ⊢Δ (univ (ℕⱼ (wfEqTerm X))) ρ) (⊢Δ ∙ (univ (ℕⱼ ⊢Δ))) x)
                  (PE.subst (λ x → _ ⊢ _ ≡ _ ∷ x ^ _) (singleSubstLift F _) (substConvEqTerm ρ ⊢Δ X))
                  {!!} {!!}) {!!}
  substConvEqTerm ρ ⊢Δ (natrec-zero x x₁ x₂) = {!!}
  substConvEqTerm ρ ⊢Δ (natrec-suc x x₁ x₂ x₃) = {!!}
  substConvEqTerm ρ ⊢Δ (Emptyrec-cong x x₁ x₂) = {!!}
  substConvEqTerm ρ ⊢Δ (proof-irrelevance x x₁) = proof-irrelevance (substTerm (validitySubst ρ) ⊢Δ x)
                                                                    (conv (substTerm (validitySubstSym ρ (wfTerm x) ⊢Δ) ⊢Δ x₁)
                                                                      (substConv (symSubst ρ (wfTerm x) ⊢Δ) ⊢Δ (validity x)))
  substConvEqTerm ρ ⊢Δ (Id-cong X X₁ X₂) = {!!}
  substConvEqTerm ρ ⊢Δ (cast-refl X x x₁) = trans (cast-refl (substConvEqTerm (substRefl (validitySubst ρ)) ⊢Δ X)
                                                             (substTerm (validitySubst ρ) ⊢Δ x)
                                                             (substTerm (validitySubst ρ) ⊢Δ x₁))
                  (conv (substConvTerm ρ ⊢Δ x₁) (univ (substConvEqTerm (substRefl (validitySubst ρ)) ⊢Δ X)))
  substConvEqTerm ρ ⊢Δ (cast-cong X X₁ X₂ x x₁) = {!!}
  substConvEqTerm ρ ⊢Δ (cast-Π x x₁ x₂ x₃ x₄ x₅) = {!!}
  substConvEqTerm ρ ⊢Δ (cast-ℕ-0 x) = {!!}
  substConvEqTerm ρ ⊢Δ (cast-ℕ-S x x₁) = {!!}

  substConvEq : ∀ {Γ Δ A B r ρ ρ′} → Δ ⊢ˢ ρ ≡ ρ′ ∷ Γ →
         let ρA = U.subst ρ A
             ρB = U.subst ρ′ B
         in ⊢ Δ → Γ ⊢ A ≡ B ^ r → Δ ⊢ ρA ≡ ρB ^ r
  substConvEq ρ ⊢Δ (univ A≡B) = univ (substConvEqTerm ρ ⊢Δ A≡B)
  substConvEq ρ ⊢Δ (refl A) = substConv ρ ⊢Δ A
  substConvEq ρ ⊢Δ (sym A≡B) = sym (substConvEq (symSubst ρ (wfEq A≡B) ⊢Δ) ⊢Δ A≡B)
  substConvEq ρ ⊢Δ (trans A≡B B≡C) = trans (substConvEq (substRefl (validitySubst ρ)) ⊢Δ A≡B) (substConvEq ρ ⊢Δ B≡C)
