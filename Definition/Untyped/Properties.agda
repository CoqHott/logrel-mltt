-- Laws for weakenings and substitutions.

{-# OPTIONS --without-K  #-}

module Definition.Untyped.Properties where

open import Definition.Untyped

open import Tools.Nat
open import Tools.List
open import Tools.PropositionalEquality hiding (subst)


-- Weakening properties

-- Two weakenings ρ and ρ′ are extensionally equal if they agree on
-- all arguments when interpreted as functions mapping variables to
-- variables.  Formally, they are considered equal iff
--
--   (∀ x → wkVar ρ x ≡ wkVar ρ′ x)
--
-- Intensional (propositional) equality would be too fine.  For
-- instance,
--
--   lift id : Γ∙A ≤ Γ∙A
--
-- is extensionally equal to
--
--   id : Γ∙A ≤ Γ∙A
--
-- but syntactically different.

-- "lift" preserves equality of weakenings.  Or:
-- If two weakenings are equal under wkVar, then they are equal when lifted.

wkVar-lift : ∀ {ρ ρ′}
  → (∀ x → wkVar ρ x ≡ wkVar ρ′ x)
  → (∀ x → wkVar (lift ρ) x ≡ wkVar (lift ρ′) x)

wkVar-lift eq 0      = refl
wkVar-lift eq (1+ x) = cong 1+ (eq x)

wkVar-lifts : ∀ {ρ ρ′}
  → (∀ x → wkVar ρ x ≡ wkVar ρ′ x)
  → (∀ n x → wkVar (repeat lift ρ n) x ≡ wkVar (repeat lift ρ′ n) x)
wkVar-lifts eq 0 x = eq x
wkVar-lifts eq (1+ n) x = wkVar-lift (wkVar-lifts eq n) x

-- Extensionally equal weakenings, if applied to a term,
-- yield the same weakened term.  Or:
-- If two weakenings are equal under wkVar, then they are equal under wk.

mutual
  wkVar-to-wk : ∀ {ρ ρ′}
    → (∀ x → wkVar ρ x ≡ wkVar ρ′ x)
    → ∀ t → wk ρ t ≡ wk ρ′ t
  wkVar-to-wk eq (var x) = cong var (eq x)
  wkVar-to-wk eq (gen x c) = cong (gen x) (wkVar-to-wkGen eq c)

  wkVar-to-wkGen : ∀ {ρ ρ′}
    → (∀ x → wkVar ρ x ≡ wkVar ρ′ x)
    → ∀ t → wkGen ρ t ≡ wkGen ρ′ t
  wkVar-to-wkGen eq [] = refl
  wkVar-to-wkGen eq (⟦ l , t ⟧ ∷ g) =
    cong₂ _∷_ (cong (⟦_,_⟧ l) (wkVar-to-wk (wkVar-lifts eq l) t))
              (wkVar-to-wkGen eq g)

-- lift id  is extensionally equal to  id.

wkVar-lift-id : (x : Nat) → wkVar (lift id) x ≡ wkVar id x
wkVar-lift-id 0    = refl
wkVar-lift-id (1+ x) = refl

wkVar-lifts-id : (n x : Nat) → wkVar (repeat lift id n) x ≡ wkVar id x
wkVar-lifts-id 0 x = refl
wkVar-lifts-id (1+ n) 0 = refl
wkVar-lifts-id (1+ n) (1+ x) = cong 1+ (wkVar-lifts-id n x)

-- id is the identity renaming.

wkVar-id : (x : Nat) → wkVar id x ≡ x
wkVar-id x = refl

mutual
  wk-id : (t : Term) → wk id t ≡ t
  wk-id (var x) = refl
  wk-id (gen x c) = cong (gen x) (wkGen-id c)

  wkGen-id : ∀ x → wkGen id x ≡ x
  wkGen-id [] = refl
  wkGen-id (⟦ l , t ⟧ ∷ g) =
    cong₂ _∷_ (cong (⟦_,_⟧ l)
              (trans (wkVar-to-wk (wkVar-lifts-id l) t) (wk-id t))) (wkGen-id g)

-- lift id  is also the identity renaming.

wk-lift-id : (t : Term) → wk (lift id) t ≡ t
wk-lift-id t = trans (wkVar-to-wk wkVar-lift-id t) (wk-id t)

-- The composition of weakenings is correct...
--
-- ...as action on variables.

wkVar-comp : ∀ ρ ρ′ x → wkVar ρ (wkVar ρ′ x) ≡ wkVar (ρ • ρ′) x
wkVar-comp id       ρ′        x       = refl
wkVar-comp (step ρ) ρ′        x       = cong 1+ (wkVar-comp ρ ρ′ x)
wkVar-comp (lift ρ) id        x       = refl
wkVar-comp (lift ρ) (step ρ′) x       = cong 1+ (wkVar-comp ρ ρ′ x)
wkVar-comp (lift ρ) (lift ρ′) 0    = refl
wkVar-comp (lift ρ) (lift ρ′) (1+ x) = cong 1+ (wkVar-comp ρ ρ′ x)

wkVar-comps : ∀ n ρ ρ′ x
            → wkVar (repeat lift ρ n • repeat lift ρ′ n) x
            ≡ wkVar (repeat lift (ρ • ρ′) n) x
wkVar-comps 0 ρ ρ′ x = refl
wkVar-comps (1+ n) ρ ρ′ 0 = refl
wkVar-comps (1+ n) ρ ρ′ (1+ x) = cong 1+ (wkVar-comps n ρ ρ′ x)

-- ... as action on terms.

mutual
  wk-comp : ∀ ρ ρ′ t → wk ρ (wk ρ′ t) ≡ wk (ρ • ρ′) t
  wk-comp ρ ρ′ (var x) = cong var (wkVar-comp ρ ρ′ x)
  wk-comp ρ ρ′ (gen x c) = cong (gen x) (wkGen-comp ρ ρ′ c)

  wkGen-comp : ∀ ρ ρ′ g → wkGen ρ (wkGen ρ′ g) ≡ wkGen (ρ • ρ′) g
  wkGen-comp ρ ρ′ [] = refl
  wkGen-comp ρ ρ′ (⟦ l , t ⟧ ∷ g) =
    cong₂ _∷_ (cong (⟦_,_⟧ l) (trans (wk-comp (repeat lift ρ l) (repeat lift ρ′ l) t)
                                     (wkVar-to-wk (wkVar-comps l ρ ρ′) t)))
              (wkGen-comp ρ ρ′ g)

-- The following lemmata are variations on the equality
--
--   wk1 ∘ ρ = lift ρ ∘ wk1.
--
-- Typing:  Γ∙A ≤ Γ ≤ Δ  <==>  Γ∙A ≤ Δ∙A ≤ Δ.

lift-step-comp : (ρ : Wk) → step id • ρ ≡ lift ρ • step id
lift-step-comp id       = refl
lift-step-comp (step ρ) = cong step (lift-step-comp ρ)
lift-step-comp (lift ρ) = refl

wk1-wk : ∀ ρ t → wk1 (wk ρ t) ≡ wk (step ρ) t
wk1-wk ρ t = wk-comp (step id) ρ t

lift-wk1 : ∀ ρ t → wk (lift ρ) (wk1 t) ≡ wk (step ρ) t
lift-wk1 pr A = trans (wk-comp (lift pr) (step id) A)
                      (sym (cong (λ x → wk x A) (lift-step-comp pr)))

wk1-wk≡lift-wk1 : ∀ ρ t → wk1 (wk ρ t) ≡ wk (lift ρ) (wk1 t)
wk1-wk≡lift-wk1 ρ t = trans (wk1-wk ρ t) (sym (lift-wk1 ρ t))

wk12-wk≡lift2-wk12 : ∀ ρ t → wk1 (wk1 (wk ρ t)) ≡ wk (lift (lift ρ)) (wk1 (wk1 t))
wk12-wk≡lift2-wk12 ρ t = trans (cong wk1 (wk1-wk≡lift-wk1 ρ t)) (wk1-wk≡lift-wk1 (lift ρ) (wk1 t))

-- Substitution properties.

-- Two substitutions σ and σ′ are equal if they are pointwise equal,
-- i.e., agree on all variables.
--
--   ∀ x →  σ x ≡ σ′ x

-- If  σ = σ′  then  lift σ = lift σ′.

substVar-lift : ∀ {σ σ′}
  → (∀ x → σ x ≡ σ′ x)
  → ∀ x → liftSubst σ x ≡ liftSubst σ′ x

substVar-lift eq 0    = refl
substVar-lift eq (1+ x) = cong wk1 (eq x)

substVar-lifts : ∀ {σ σ′}
  → (∀ x → σ x ≡ σ′ x)
  → ∀ n x → repeat liftSubst σ n x ≡ repeat liftSubst σ′ n x

substVar-lifts eq 0 x = eq x
substVar-lifts eq (1+ n) 0 = refl
substVar-lifts eq (1+ n) (1+ x) = cong wk1 (substVar-lifts eq n x)

-- If  σ = σ′  then  subst σ t = subst σ′ t.

mutual
  substVar-to-subst : ∀ {σ σ′}
    → ((x : Nat) → σ x ≡ σ′ x)
    → (t : Term) → subst σ t ≡ subst σ′ t
  substVar-to-subst eq (var x) = eq x
  substVar-to-subst eq (gen x c) = cong (gen x) (substVar-to-substGen eq c)

  substVar-to-substGen : ∀ {σ σ′}
    → ((x : Nat) → σ x ≡ σ′ x)
    → ∀ g → substGen σ g ≡ substGen σ′ g
  substVar-to-substGen eq [] = refl
  substVar-to-substGen eq (⟦ l , t ⟧ ∷ g) =
    cong₂ _∷_ (cong (⟦_,_⟧ l) (substVar-to-subst (substVar-lifts eq l) t))
              (substVar-to-substGen eq g)

-- lift id = id  (as substitutions)

subst-lift-id : (x : Nat) → (liftSubst idSubst) x ≡ idSubst x
subst-lift-id 0    = refl
subst-lift-id (1+ x) = refl

subst-lifts-id : (n x : Nat) → (repeat liftSubst idSubst n) x ≡ idSubst x
subst-lifts-id 0 x = refl
subst-lifts-id (1+ n) 0 = refl
subst-lifts-id (1+ n) (1+ x) = cong wk1 (subst-lifts-id n x)

-- Identity substitution.

mutual
  subst-id : (t : Term) → subst idSubst t ≡ t
  subst-id (var x) = refl
  subst-id (gen x c) = cong (gen x) (substGen-id c)

  substGen-id : ∀ g → substGen idSubst g ≡ g
  substGen-id [] = refl
  substGen-id (⟦ l , t ⟧ ∷ g) =
    cong₂ _∷_ (cong (⟦_,_⟧ l) (trans (substVar-to-subst (subst-lifts-id l) t)
                                     (subst-id t)))
              (substGen-id g)


-- Correctness of composition of weakening and substitution.

-- Composition of liftings is lifting of the composition.
-- lift ρ •ₛ lift σ = lift (ρ •ₛ σ)

subst-lift-•ₛ : ∀ {ρ σ} t
              → subst (lift ρ •ₛ liftSubst σ) t
              ≡ subst (liftSubst (ρ •ₛ σ)) t
subst-lift-•ₛ =
  substVar-to-subst (λ { 0 → refl ; (1+ x) → sym (wk1-wk≡lift-wk1 _ _)})

helper1 : ∀ {ρ σ} (n x : Nat) →
      (lift (repeat lift ρ n) •ₛ liftSubst (repeat liftSubst σ n)) x ≡
      liftSubst (repeat liftSubst (ρ •ₛ σ) n) x
helper1 0 0 = refl
helper1 0 (1+ x) = sym (wk1-wk≡lift-wk1 _ _)
helper1 (1+ n) 0 = refl
helper1 (1+ n) (1+ x) = trans (sym (wk1-wk≡lift-wk1 _ _)) (cong wk1 (helper1 n x))

subst-lifts-•ₛ : ∀ {ρ σ} n t
              → subst (repeat lift ρ n •ₛ repeat liftSubst σ n) t
              ≡ subst (repeat liftSubst (ρ •ₛ σ) n) t
subst-lifts-•ₛ 0 t = refl
subst-lifts-•ₛ (1+ n) t = substVar-to-subst (helper1 n) t

-- lift σ ₛ• lift ρ = lift (σ ₛ• ρ)

subst-lift-ₛ• : ∀ {ρ σ} t
              → subst (liftSubst σ ₛ• lift ρ) t
              ≡ subst (liftSubst (σ ₛ• ρ)) t
subst-lift-ₛ• = substVar-to-subst (λ { 0 → refl ; (1+ x) → refl})

helper2 : ∀ {ρ σ} (n x : Nat) →
      liftSubst (repeat liftSubst σ n) (wkVar (lift (repeat lift ρ n)) x) ≡
      liftSubst (repeat liftSubst (λ x₁ → σ (wkVar ρ x₁)) n) x
helper2 0 0 = refl
helper2 0 (1+ x) = refl
helper2 (1+ n) 0 = refl
helper2 (1+ n) (1+ x) = cong wk1 (helper2 n x)

subst-lifts-ₛ• : ∀ {ρ σ} n t
              → subst (repeat liftSubst σ n ₛ• repeat lift ρ n) t
              ≡ subst (repeat liftSubst (σ ₛ• ρ) n) t
subst-lifts-ₛ• 0 t = refl
subst-lifts-ₛ• (1+ n) t = substVar-to-subst (helper2 n) t

-- wk ρ ∘ subst σ = subst (ρ •ₛ σ)

mutual
  wk-subst : ∀ {ρ σ} t → wk ρ (subst σ t) ≡ subst (ρ •ₛ σ) t
  wk-subst (var x) = refl
  wk-subst (gen x c) = cong (gen x) (wkGen-substGen c)

  wkGen-substGen : ∀ {ρ σ} t → wkGen ρ (substGen σ t) ≡ substGen (ρ •ₛ σ) t
  wkGen-substGen [] = refl
  wkGen-substGen (⟦ l , t ⟧ ∷ c) =
    cong₂ _∷_ (cong (⟦_,_⟧ l) (trans (wk-subst t) (subst-lifts-•ₛ l t)))
              (wkGen-substGen c)

-- subst σ ∘ wk ρ = subst (σ •ₛ ρ)

mutual
  subst-wk : ∀ {ρ σ} t → subst σ (wk ρ t) ≡ subst (σ ₛ• ρ) t
  subst-wk (var x) = refl
  subst-wk (gen x c) = cong (gen x) (substGen-wkGen c)

  substGen-wkGen : ∀ {ρ σ} t → substGen σ (wkGen ρ t) ≡ substGen (σ ₛ• ρ) t
  substGen-wkGen [] = refl
  substGen-wkGen (⟦ l , t ⟧ ∷ c) =
    cong₂ _∷_ (cong (⟦_,_⟧ l) (trans (subst-wk t) (subst-lifts-ₛ• l t)))
              (substGen-wkGen c)

-- Composition of liftings is lifting of the composition.

wk-subst-lift : ∀ {ρ σ} G
              → wk (lift ρ) (subst (liftSubst σ) G)
              ≡ subst (liftSubst (ρ •ₛ σ)) G
wk-subst-lift G = trans (wk-subst G) (subst-lift-•ₛ G)

-- Renaming with ρ is the same as substituting with ρ turned into a substitution.

wk≡subst : ∀ ρ t → wk ρ t ≡ subst (toSubst ρ) t
wk≡subst ρ t = trans (cong (wk ρ) (sym (subst-id t))) (wk-subst t)


-- Composition of substitutions.

-- Composition of liftings is lifting of the composition.

substCompLift : ∀ {σ σ′} x
              → (liftSubst σ ₛ•ₛ liftSubst σ′) x
              ≡ (liftSubst (σ ₛ•ₛ σ′)) x
substCompLift          0    = refl
substCompLift {σ} {σ′} (1+ x) = trans (subst-wk (σ′ x)) (sym (wk-subst (σ′ x)))

substCompLifts : ∀ {σ σ′} n x
              → (repeat liftSubst σ n ₛ•ₛ repeat liftSubst σ′ n) x
              ≡ (repeat liftSubst (σ ₛ•ₛ σ′) n) x
substCompLifts 0 x = refl
substCompLifts (1+ n) 0 = refl
substCompLifts {σ} {σ′} (1+ n) (1+ x) =
  trans (substCompLift {repeat liftSubst σ n} {repeat liftSubst σ′ n} (1+ x))
        (cong wk1 (substCompLifts n x))

-- Soundness of the composition of substitutions.

mutual
  substCompEq : ∀ {σ σ′} (t : Term)
              → subst σ (subst σ′ t) ≡ subst (σ ₛ•ₛ σ′) t
  substCompEq (var x) = refl
  substCompEq (gen x c) = cong (gen x) (substGenCompEq c)

  substGenCompEq : ∀ {σ σ′} t
              → substGen σ (substGen σ′ t) ≡ substGen (σ ₛ•ₛ σ′) t
  substGenCompEq [] = refl
  substGenCompEq (⟦ l , t ⟧ ∷ c) =
    cong₂ _∷_ (cong (⟦_,_⟧ l) (trans (substCompEq t)
                                     (substVar-to-subst (substCompLifts l) t)))
              (substGenCompEq c)

-- Weakening single substitutions.

-- Pulling apart a weakening composition in specific context _[a].

wk-comp-subst : ∀ {a} ρ ρ′ G
  → wk (lift (ρ • ρ′)) G [ a ] ≡ wk (lift ρ) (wk (lift ρ′) G) [ a ]

wk-comp-subst {a} ρ ρ′ G =
  cong (λ x → x [ a ]) (sym (wk-comp (lift ρ) (lift ρ′) G))

-- Pushing a weakening into a single substitution.
-- ρ (t[a]) = ((lift ρ) t)[ρ a]

wk-β : ∀ {ρ a} t → wk ρ (t [ a ]) ≡ wk (lift ρ) t [ wk ρ a ]
wk-β t = trans (wk-subst t) (sym (trans (subst-wk t)
               (substVar-to-subst (λ { 0 → refl ; (1+ x) → refl}) t)))

wk-β-eq : ∀ {ρ a t t' a'} → wk (lift ρ) t ≡ t' → wk ρ a ≡ a' → wk ρ (t [ a ]) ≡ t' [ a' ]
wk-β-eq {t = t} eqt eqa = trans (wk-β t) (cong₂ _[_] eqt eqa)

-- Pushing a weakening into a single shifting substitution.
-- If  ρ′ = lift ρ  then  ρ′(t[a]↑) = ρ′(t) [ρ′(a)]↑

wk-β↑ : ∀ {ρ a} t → wk (lift ρ) (t [ a ]↑) ≡ wk (lift ρ) t [ wk (lift ρ) a ]↑
wk-β↑ t = trans (wk-subst t) (sym (trans (subst-wk t)
                (substVar-to-subst (λ { 0 → refl ; (1+ x) → refl}) t)))

-- A specific equation on weakenings used for the reduction of natrec.

wk-β-natrec : ∀ ρ G sG
  → Π ℕ ⦂ 𝕥y ▹ (Π wk (lift ρ) G ⦂ sG ▹ wk (lift (lift ρ)) (wk1 (G [ suc (var 0) ]↑)))
  ≡ Π ℕ ⦂ 𝕥y ▹ (wk (lift ρ) G ⦂ sG ▹▹ wk (lift ρ) G [ suc (var 0) ]↑)
wk-β-natrec ρ G sG =
  cong₃ Π_⦂_▹_ refl refl (cong₃ Π_⦂_▹_ refl refl
    (trans (wk-comp (lift (lift ρ)) (step id)
                    (subst (consSubst (wk1Subst var) (suc (var 0))) G))
       (trans (wk-subst G) (sym (trans (wk-subst (wk (lift ρ) G))
         (trans (subst-wk G)
                (substVar-to-subst (λ { 0 → refl ; (1+ x) → refl}) G)))))))

wk-β-Boxrec : ∀ ρ F sF E
  → Π F ⦂ ‼ sF ▹ wk (lift ρ) (E [ box sF (var 0) ]↑)
  ≡ Π F ⦂ ‼ sF ▹ (wk (lift ρ) E [ box sF (var 0) ]↑)
wk-β-Boxrec ρ F sF E = cong₃ Π_⦂_▹_ refl refl (wk-β↑ E)


-- Composing a singleton substitution and a lifted substitution.
-- sg u ∘ lift σ = cons id u ∘ lift σ = cons σ u

substVasSingletonComp : ∀ {u σ} (x : Nat)
  → (sgSubst u ₛ•ₛ liftSubst σ) x ≡ (consSubst σ u) x
substVasSingletonComp 0 = refl
substVasSingletonComp {σ = σ} (1+ x) = trans (subst-wk (σ x)) (subst-id (σ x))

-- The same again, as action on a term t.

substSingletonComp : ∀ {a σ} t
  → subst (sgSubst a ₛ•ₛ liftSubst σ) t ≡ subst (consSubst σ a) t
substSingletonComp = substVar-to-subst substVasSingletonComp

-- A single substitution after a lifted substitution.
-- ((lift σ) G)[t] = (cons σ t)(G)

singleSubstComp : ∀ t σ G
                 → (subst (liftSubst σ) G) [ t ]
                 ≡ subst (consSubst σ t) G
singleSubstComp t σ G = trans (substCompEq G) (substSingletonComp G)

-- A single substitution after a lifted substitution (with weakening).
-- ((lift (ρ ∘ σ)) G)[t] = (cons (ρ ∘ σ) t)(G)

singleSubstWkComp : ∀ {ρ} t σ G
               → wk (lift ρ) (subst (liftSubst σ) G) [ t ]
               ≡ subst (consSubst (ρ •ₛ σ) t) G
singleSubstWkComp t σ G =
  trans (cong (subst (consSubst var t))
              (trans (wk-subst G) (subst-lift-•ₛ G)))
        (trans (substCompEq G) (substSingletonComp G))

-- Pushing a substitution into a single substitution.

singleSubstLift : ∀ {σ} G t
                → subst σ (G [ t ])
                ≡ subst (liftSubst σ) G [ subst σ t ]
singleSubstLift G t =
  trans (substCompEq G)
        (trans (trans (substVar-to-subst (λ { 0 → refl ; (1+ x) → refl}) G)
                      (sym (substSingletonComp G)))
               (sym (substCompEq G)))

-- More specific laws.

idWkLiftSubstLemma : ∀ σ G
  → wk (lift (step id)) (subst (liftSubst σ) G) [ var 0 ]
  ≡ subst (liftSubst σ) G
idWkLiftSubstLemma σ G =
  trans (singleSubstWkComp (var 0) σ G)
        (substVar-to-subst (λ { 0 → refl ; (1+ x) → refl}) G)

substVasComp↑ : ∀ {t} σ x
  → (consSubst (wk1Subst idSubst) (subst (liftSubst σ) t) ₛ•ₛ liftSubst σ) x
  ≡ (liftSubst σ ₛ•ₛ consSubst (wk1Subst idSubst) t) x
substVasComp↑ σ 0 = refl
substVasComp↑ σ (1+ x) = trans (subst-wk (σ x)) (sym (wk≡subst (step id) (σ x)))

singleSubstLift↑ : ∀ σ G t
                 → subst (liftSubst σ) (G [ t ]↑)
                 ≡ subst (liftSubst σ) G [ subst (liftSubst σ) t ]↑
singleSubstLift↑ σ G t =
  trans (substCompEq G)
        (sym (trans (substCompEq G) (substVar-to-subst (substVasComp↑ σ) G)))

substConsComp : ∀ {σ t G}
       → subst (consSubst (λ x → σ (1+ x)) (subst (tail σ) t)) G
       ≡ subst σ (subst (consSubst (λ x → var (1+ x)) (wk1 t)) G)
substConsComp {t = t} {G = G} =
  trans (substVar-to-subst (λ { 0 → sym (subst-wk t) ; (1+ x) → refl }) G)
        (sym (substCompEq G))

wkSingleSubstId : ∀ F → (wk (lift (step id)) F) [ var 0 ] ≡ F
wkSingleSubstId F =
  trans (subst-wk F)
        (trans (substVar-to-subst (λ { 0 → refl ; (1+ x) → refl}) F)
               (subst-id F))

cons-wk-subst : ∀ ρ σ a t
       → subst (sgSubst a ₛ• lift ρ ₛ•ₛ liftSubst σ) t
       ≡ subst (consSubst (ρ •ₛ σ) a) t
cons-wk-subst ρ σ a = substVar-to-subst
  (λ { 0 → refl
     ; (1+ x) → trans (subst-wk (σ x)) (sym (wk≡subst ρ (σ x))) })

natrecSucCaseLemma : ∀ {σ} (x : Nat)
  → (step id •ₛ consSubst (wk1Subst idSubst) (suc (var 0)) ₛ•ₛ liftSubst σ) x
  ≡ (liftSubst (liftSubst σ) ₛ• step id ₛ•ₛ consSubst (wk1Subst idSubst) (suc (var 0))) x
natrecSucCaseLemma 0 = refl
natrecSucCaseLemma {σ} (1+ x) =
  trans (subst-wk (σ x))
           (sym (trans (wk1-wk (step id) _)
                             (wk≡subst (step (step id)) (σ x))))

natrecSucCase : ∀ σ F sF
  → Π ℕ ⦂ 𝕥y ▹ (Π subst (liftSubst σ) F ⦂ sF
                ▹ subst (liftSubst (liftSubst σ)) (wk1 (F [ suc (var 0) ]↑)))
  ≡ Π ℕ ⦂ 𝕥y ▹ (subst (liftSubst σ) F ⦂ sF ▹▹ subst (liftSubst σ) F [ suc (var 0) ]↑)
natrecSucCase σ F sF =
  cong₃ Π_⦂_▹_ refl refl
    (cong₃ Π_⦂_▹_ refl refl
       (trans (trans (subst-wk (F [ suc (var 0) ]↑))
                           (substCompEq F))
                 (sym (trans (wk-subst (subst (liftSubst σ) F))
                                   (trans (substCompEq F)
                                             (substVar-to-subst natrecSucCaseLemma F))))))

natrecIrrelevantSubstLemma : ∀ F z s m σ (x : Nat)
  → (sgSubst (natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) m)
     ₛ•ₛ liftSubst (sgSubst m)
     ₛ•ₛ liftSubst (liftSubst σ)
     ₛ•  step id
     ₛ•ₛ consSubst (tail idSubst) (suc (var 0))) x
  ≡ (consSubst σ (suc m)) x
natrecIrrelevantSubstLemma F z s m σ 0 =
  cong suc (trans (subst-wk m) (subst-id m))
natrecIrrelevantSubstLemma F z s m σ (1+ x) =
  trans (subst-wk (wk (step id) (σ x)))
           (trans (subst-wk (σ x))
                     (subst-id (σ x)))

natrecIrrelevantSubst : ∀ F z s m σ
  → subst (consSubst σ (suc m)) F
  ≡ subst (liftSubst (sgSubst m))
          (subst (liftSubst (liftSubst σ))
                 (wk1 (F [ suc (var 0) ]↑)))
                   [ natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) m ]
natrecIrrelevantSubst F z s m σ =
  sym (trans (substCompEq (subst (liftSubst (liftSubst σ))
        (wk (step id)
         (subst (consSubst (tail idSubst) (suc (var 0))) F))))
         (trans (substCompEq (wk (step id)
        (subst (consSubst (tail idSubst) (suc (var 0))) F)))
        (trans
           (subst-wk (subst (consSubst (tail idSubst) (suc (var 0))) F))
           (trans (substCompEq F)
                     (substVar-to-subst (natrecIrrelevantSubstLemma F z s m σ) F)))))

natrecIrrelevantSubstLemma′ : ∀ F z s n (x : Nat)
  → (sgSubst (natrec F z s n)
     ₛ•ₛ liftSubst (sgSubst n)
     ₛ•  step id
     ₛ•ₛ consSubst (tail idSubst) (suc (var 0))) x
  ≡ (consSubst var (suc n)) x
natrecIrrelevantSubstLemma′ F z s n 0 =
  cong suc (trans (subst-wk n) (subst-id n))
natrecIrrelevantSubstLemma′ F z s n (1+ x) = refl

natrecIrrelevantSubst′ : ∀ F z s n
  → subst (liftSubst (sgSubst n))
      (wk1 (F [ suc (var 0) ]↑))
      [ natrec F z s n ]
  ≡ F [ suc n ]
natrecIrrelevantSubst′ F z s n =
  trans (substCompEq (wk (step id)
                         (subst (consSubst (tail idSubst) (suc (var 0))) F)))
        (trans (subst-wk (subst (consSubst (tail idSubst) (suc (var 0))) F))
               (trans (substCompEq F)
                      (substVar-to-subst (natrecIrrelevantSubstLemma′ F z s n) F)))

cons0wkLift1-id : ∀ σ G
    → subst (sgSubst (var 0))
            (wk (lift (step id)) (subst (liftSubst σ) G))
    ≡ subst (liftSubst σ) G
cons0wkLift1-id σ G =
  trans (subst-wk (subst (liftSubst σ) G))
        (trans (substVar-to-subst (λ { 0 → refl ; (1+ x) → refl })
                                  (subst (liftSubst σ) G))
               (subst-id (subst (liftSubst σ) G)))

substConsId : ∀ {σ t} G
        → subst (consSubst σ (subst σ t)) G
        ≡ subst σ (subst (sgSubst t) G)
substConsId G =
  sym (trans (substCompEq G)
             (substVar-to-subst (λ { 0 → refl ; (1+ x) → refl}) G))

substConsTailId : ∀ {G t σ}
                → subst (consSubst (tail σ) (subst σ t)) G
                ≡ subst σ (subst (consSubst (tail idSubst) t) G)
substConsTailId {G} {t} {σ} =
  trans (substVar-to-subst (λ { 0 → refl
                            ; (1+ x) → refl }) G)
        (sym (substCompEq G))

substConcatSingleton′ : ∀ {a σ} t
                      → subst (σ ₛ•ₛ sgSubst a) t
                      ≡ subst (consSubst σ (subst σ a)) t
substConcatSingleton′ t = substVar-to-subst (λ { 0 → refl ; (1+ x) → refl}) t

wk1-tailId : ∀ t → wk1 t ≡ subst (tail idSubst) t
wk1-tailId t = trans (sym (subst-id (wk1 t))) (subst-wk t)


-- helpers
open import Tools.Product
open import Tools.Sum using (_⊎_; inj₁; inj₂)

subst-Univ-either : ∀ {s} a b → subst (sgSubst a) b ≡ Univ s
                  → (a ≡ Univ s × b ≡ var 0) ⊎ (b ≡ Univ s)
subst-Univ-either a (var 0) e = inj₁ (e , refl)
subst-Univ-either a (Univ x) refl = inj₂ refl
subst-Univ-either a (var (1+ x)) ()
subst-Univ-either a (gen (Ukind x) (x₁ ∷ y)) ()
subst-Univ-either a (gen (Pikind x) c) ()
subst-Univ-either a (gen Natkind c) ()
subst-Univ-either a (gen Lamkind c) ()
subst-Univ-either a (gen Appkind c) ()
subst-Univ-either a (gen Zerokind c) ()
subst-Univ-either a (gen Suckind c) ()
subst-Univ-either a (gen Natreckind c) ()
subst-Univ-either a (gen Emptykind c) ()
subst-Univ-either a (gen Emptyreckind c) ()

wk-sgSubst-pointwise : ∀ ρ {t} x → (ρ •ₛ sgSubst t) x ≡ (sgSubst (wk ρ t) ₛ• lift ρ) x
wk-sgSubst-pointwise ρ Nat.zero = refl
wk-sgSubst-pointwise ρ (1+ x) = refl

wk-sgSubst : ∀ {ρ t} u → subst (sgSubst (wk ρ t)) (wk (lift ρ) u) ≡ wk ρ (subst (sgSubst t) u)
wk-sgSubst {ρ} {t} u =
  sym (
  trans (wk-subst u)
    (trans (substVar-to-subst (wk-sgSubst-pointwise ρ) u)
      (sym (subst-wk u))))
