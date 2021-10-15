{-# OPTIONS --rewriting --prop --confluence-check #-}

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Data.Vec.Base
open import Data.Bool
open import Data.Sum

-- sigma type in Prop used to handle telescopes. 

record Tel {a b} (A : Prop a) (B : A → Prop b) : Prop (a ⊔ b) where
  constructor _,_
  field
    fstC : A
    sndC : B fstC

open Tel public

infixr 4 _,_

record ΣCov {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fstCov : A
    sndCov : B fstCov

open ΣCov public

record prod {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fstprod : A
    sndprod : B 

open prod public


variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

-- a bit of boilerplate to deal with Prop

data ⊥ : Prop where

record ⊤P : Prop ℓ where
  constructor ttP

record Box (A : Prop ℓ) : Set ℓ where
  constructor box
  field
    unbox : A

open Box public

_×_ : ∀ (A : Prop ℓ) (B : Prop ℓ₁) → Prop (ℓ ⊔ ℓ₁)
A × B = Tel A (λ _ → B)

-- we need this for cumulativity

record i (A : Prop ℓ) : Prop (ℓ ⊔ ℓ₁) where
  constructor inj
  field
    uninj : A

open i public

record iS (A : Set ℓ) : Set (ℓ ⊔ ℓ₁) where
  constructor inj
  field
    uninj : A

open iS public

{- 
 Axiomatisation of Id, Id-refl, transport (for proposition), cast 

 Note that Id-refl, transport are axioms in Prop, 
 so we don't need to give them a computation content. 

 Also transport-refl is useless for transport on Prop
-}

postulate Id : (A : Set ℓ) → A → A → Prop ℓ

postulate cast : (A B : Set ℓ) (e : Id (Set ℓ) A B) → A → B 

postulate Id-refl : {A : Set ℓ} (x : A) → Id A x x

postulate cast-refl : {A : Set ℓ} (e : Id _ A A) (a : A) → Id A (cast A A e a) a

postulate transport : {A : Set ℓ} (P : A → Prop ℓ₁) (x : A) (t : P x) (y : A) (e : Id A x y) → P y

-- cast-refl' : {A : Set ℓ} (e : Id (Set ℓ) A A) (a : A) → Id A (cast A A e a) a
-- cast-refl' {A = A} e a = transport (λ z → Id A z a) {!!} (Id-refl a) {!!} {!!}

-- direct derived functions 

ap : {A : Set ℓ} {B : Set ℓ₁} {x y : A} (f : A → B) (e : Id A x y) →
     Id B (f x) (f y)
ap {ℓ} {ℓ₁} {A} {B} {x} {y} f e = transport (λ z → Id B (f x) (f z)) x (Id-refl _) y e

transport-Id : {A : Set ℓ} (P : A → Set ℓ₁) (x : A) (t : P x) (y : A) (e : Id A x y) → P y
transport-Id P x t y e = cast (P x) (P y) (ap P e) t

transport-refl : {A : Set ℓ} (P : A → Set ℓ₁) (x : A) (t : P x) (e : Id A x x) → Id _ (transport-Id P x t x e) t
transport-refl P x t e = cast-refl (ap P e) t


inverse  : (A : Set ℓ) {x y : A} (p : Id {ℓ} A x y) → Id A y x
inverse A {x} {y} p = transport (λ z → Id A z x) x (Id-refl x) y p

concatId : (A : Set ℓ) {x y z : A} (p : Id {ℓ} A x y)
           (q : Id {ℓ} A y z) → Id A x z
concatId A {x} {y} {z} p q = transport (λ t → Id A x t) y p z q

-- we now state rewrite rules for the identity type

postulate Id-Pi : (A : Set ℓ) (B : A → Set ℓ₁) (f g : (a : A) → B a) →
                  Id ((a : A) → B a) f g ≡ ((a : A) → Id (B a) (f a) (g a))

{-# REWRITE Id-Pi #-}

-- rewrite rules on Id-refl are not needed because it is in Prop

refl-Pi : (A : Set ℓ) (B : A → Set ℓ₁) (f : (a : A) → B a) →
          box (Id-refl f) ≡ box (λ a → Id-refl (f a))
refl-Pi A B f = refl

-- sanity check for funext

funext : (A : Set ℓ) (B : A → Set ℓ₁) (f g : (a : A) → B a) →
         ((a : A) → Id (B a) (f a) (g a)) → Id ((a : A) → B a) f g  
funext A B f g e = e



postulate Id-Sigma : (A : Set ℓ) (B : A → Set ℓ₁) (a a' : A)
                     (b : B a) (b' : B a') → 
                     Id (Σ A B) (a , b) (a' , b') ≡
                     Tel (Id A a a')
                         (λ e → Id (B a') (transport-Id B a b a' e) b')

{-# REWRITE Id-Sigma #-}

postulate Id-SigmaCov : (A : Set ℓ) (B : A → Set ℓ₁) (a a' : A)
                     (b : B a) (b' : B a') → 
                     Id (ΣCov A B) (a , b) (a' , b') ≡
                     Tel (Id A a a')
                         (λ e → Id (B a) b (transport-Id B a' b' a (inverse A e)))

{-# REWRITE Id-SigmaCov #-}

postulate Id-prod : (A : Set ℓ) (B : Set ℓ₁) (a a' : A)
                     (b b' : B) → 
                     Id (prod A B) (a , b) (a' , b') ≡
                     (Id A a a') × (Id B b b')

{-# REWRITE Id-prod #-}

postulate Id-Box : (A : Prop ℓ) (p q : A) → Id (Box A) (box p) (box q) ≡ ⊤P

{-# REWRITE Id-Box #-}

postulate Id-Unit : (p q : ⊤) → Id ⊤ p q ≡ ⊤P

{-# REWRITE Id-Unit #-}

postulate Id-list-nil-nil : (A : Set ℓ) →
                            Id (List A) [] [] ≡ ⊤P

-- postulate Id-list-nil-cons : (A : Set ℓ) (a' : A) (l' : List A) →
--                              Id (List A) [] (a' ∷ l') ≡ i ⊥

-- postulate Id-list-cons-nil : (A : Set ℓ) (a : A) (l : List A) →
--                              Id (List A) (a ∷ l) [] ≡ i ⊥

postulate Id-list-cons-cons : (A : Set ℓ) (a a' : A) (l l' : List A) →
                             Id (List A) (a ∷ l) (a' ∷ l') ≡
                             Id A a a' × Id (List A) l l'

{-# REWRITE Id-list-nil-nil #-}
{-# REWRITE Id-list-cons-cons #-}

postulate Id-nat-zero-zero : Id Nat 0 0 ≡ ⊤P

-- postulate Id-nat-zero-suc : (n : Nat) →
--                             Id Nat 0 (suc n) ≡ i ⊥

-- postulate Id-nat-suc-zero : (n : Nat) →
--                             Id Nat (suc n) zero ≡ i ⊥

postulate Id-nat-suc-suc : (n n' : Nat) →
                           Id Nat (suc n) (suc n') ≡
                           Id Nat n n'

{-# REWRITE Id-nat-zero-zero #-}
{-# REWRITE Id-nat-suc-suc #-}

postulate Id-bool-true-true : Id Bool true true ≡ ⊤P
postulate Id-bool-false-false : Id Bool false false ≡ ⊤P

{-# REWRITE Id-bool-true-true #-}
{-# REWRITE Id-bool-false-false #-}

postulate Id-sum-inj₁-inj₁ : (A : Set ℓ) (B : Set ℓ₁) (a a' : A) →
                           Id (A ⊎ B) (inj₁ a) (inj₁ a') ≡
                           i {ℓ = ℓ} {ℓ₁ = ℓ₁} (Id A a a')

postulate Id-sum-inj₂-inj₂ : (A : Set ℓ) (B : Set ℓ₁) (b b' : B) →
                           Id (A ⊎ B) (inj₂ b) (inj₂ b') ≡
                           i {ℓ = ℓ₁} {ℓ₁ = ℓ} (Id B b b')

{-# REWRITE Id-sum-inj₁-inj₁ #-}
{-# REWRITE Id-sum-inj₂-inj₂ #-}

-- rewrite rules for the identity type on the universe

telescope-Sigma : Set (lsuc (ℓ ⊔ ℓ₁))
telescope-Sigma {ℓ} {ℓ₁} = ΣCov (Set ℓ) (λ A → A → Set ℓ₁)

postulate Id-Type-Sigma : (A A' : Set ℓ) (B : A → Set ℓ₁) (B' : A' → Set ℓ₁) →
                          Id (Set (ℓ ⊔ ℓ₁)) (Σ A B) (Σ A' B') ≡
                          Id telescope-Sigma (A , B) (A' , B')

{-# REWRITE Id-Type-Sigma #-}

telescope-Forall : Set (lsuc (ℓ ⊔ ℓ₁))
telescope-Forall {ℓ} {ℓ₁} = Σ (Set ℓ) (λ A → A → Set ℓ₁)

postulate Id-Type-Pi : (A A' : Set ℓ) (B : A → Set ℓ₁) (B' : A' → Set ℓ₁) →
                       Id (Set (ℓ ⊔ ℓ₁)) ((a : A) → B a) ((a' : A') → B' a') ≡
                       Id telescope-Forall (A , B) (A' , B')

{-# REWRITE Id-Type-Pi #-}


telescope-Sum : Set (lsuc (ℓ ⊔ ℓ₁))
telescope-Sum {ℓ} {ℓ₁} = Σ (Set ℓ) (λ _ → Set ℓ₁)

postulate Id-Type-Sum : (A A' : Set ℓ) (B B' : Set ℓ₁)  →
                          Id (Set (ℓ ⊔ ℓ₁)) (A ⊎ B) (A' ⊎ B') ≡
                          Id telescope-Sum (A , B) (A' , B')

{-# REWRITE Id-Type-Sum #-}

postulate Id-Type-prod : (A A' : Set ℓ) (B B' : Set ℓ₁)  →
                          Id (Set (ℓ ⊔ ℓ₁)) (prod A B) (prod A' B') ≡
                          Id telescope-Sum (A , B) (A' , B')

{-# REWRITE Id-Type-prod #-}


telescope-List : Set (lsuc ℓ)
telescope-List {ℓ} = Set ℓ

postulate Id-Type-List : (A A' : Set ℓ) →
                       Id (Set ℓ) (List A) (List A') ≡
                       Id telescope-List A A'

{-# REWRITE Id-Type-List #-}

postulate Id-Type-Unit : Id Set ⊤ ⊤ ≡ ⊤P
                        
{-# REWRITE Id-Type-Unit #-}

postulate Id-Type-Nat : Id Set Nat Nat ≡ Id Set ⊤ ⊤
                        
{-# REWRITE Id-Type-Nat #-}

postulate Id-Type-Bool : Id Set Bool Bool ≡ Id Set ⊤ ⊤
                        
{-# REWRITE Id-Type-Bool #-}

telescope-Box : Set (lsuc ℓ)
telescope-Box {ℓ} = Prop ℓ

postulate Id-Type-Box : (P P' : Prop ℓ) → Id (Set ℓ) (Box P) (Box P') ≡ Id telescope-Box P P'
                        
{-# REWRITE Id-Type-Box #-}

-- rewrite rules for the identity type on Prop : Prop ext modulo cumul 

postulate Id-prop : (P Q : Prop ℓ) → Id (Prop ℓ) P Q ≡ i (P → Q) × (Q → P)

{-# REWRITE Id-prop #-}


postulate Id-set : Id (Set (lsuc ℓ₁)) (Set ℓ₁) (Set ℓ₁) ≡ ⊤P

{-# REWRITE Id-set #-}


-- non-diagonal cases

{- There are n^2 cases, that's a pain, this is not exhaustive for the moment -}

postulate Id-set-nat : Id _ (Set ℓ) (iS Nat) ≡ i ⊥
postulate Id-nat-set : Id (Set (lsuc ℓ)) (iS Nat) (Set ℓ) ≡ i ⊥
postulate Id-set-bool : Id _ (Set ℓ) (iS Bool) ≡ i ⊥
postulate Id-bool-set : Id (Set (lsuc ℓ)) (iS Bool) (Set ℓ) ≡ i ⊥
postulate Id-bool-nat : Id _ Bool Nat ≡ i ⊥
postulate Id-nat-bool : Id _ Nat Bool ≡ i ⊥
postulate Id-set-pi : (A : Set ℓ₁) (B : A → Set ℓ₂) → Id (Set (lsuc ℓ ⊔ ℓ₁ ⊔ ℓ₂)) (iS {lsuc ℓ} {lsuc ℓ ⊔ ℓ₁ ⊔ ℓ₂} (Set ℓ))
                                                                                  (iS {ℓ₁ ⊔ ℓ₂} {lsuc ℓ ⊔ ℓ₁ ⊔ ℓ₂} ((a : A) → B a)) ≡ i ⊥
postulate Id-pi-set : (A : Set ℓ₁) (B : A → Set ℓ₂) → Id (Set (lsuc ℓ ⊔ ℓ₁ ⊔ ℓ₂)) (iS {ℓ₁ ⊔ ℓ₂} {lsuc ℓ ⊔ ℓ₁ ⊔ ℓ₂} ((a : A) → B a))
                                                                                  (iS {lsuc ℓ} {lsuc ℓ ⊔ ℓ₁ ⊔ ℓ₂} (Set ℓ)) ≡ i ⊥
postulate Id-set-sigma : (A : Set ℓ₁) (B : A → Set ℓ₂) → Id (Set (lsuc ℓ ⊔ ℓ₁ ⊔ ℓ₂)) (iS {lsuc ℓ} {lsuc ℓ ⊔ ℓ₁ ⊔ ℓ₂} (Set ℓ))
                                                                                  (iS {ℓ₁ ⊔ ℓ₂} {lsuc ℓ ⊔ ℓ₁ ⊔ ℓ₂} (Σ A B)) ≡ i ⊥
postulate Id-sigma-set : (A : Set ℓ₁) (B : A → Set ℓ₂) → Id (Set (lsuc ℓ ⊔ ℓ₁ ⊔ ℓ₂)) (iS {ℓ₁ ⊔ ℓ₂} {lsuc ℓ ⊔ ℓ₁ ⊔ ℓ₂} (Σ A B))
                                                                                  (iS {lsuc ℓ} {lsuc ℓ ⊔ ℓ₁ ⊔ ℓ₂} (Set ℓ)) ≡ i ⊥

{-# REWRITE Id-set-nat Id-nat-set Id-set-bool Id-bool-set Id-bool-nat Id-nat-bool Id-set-pi Id-pi-set Id-set-sigma Id-sigma-set #-}

--- Contractibility of singletons and J can be defined

contr-sing : (A : Set ℓ) {x y : A} (p : Id {ℓ} A x y) →
    Id (Σ A (λ y → Box (Id A x y))) (x , box (Id-refl x)) (y , box p) 
contr-sing A {x} {y} p = p , ttP

J : (A : Set ℓ) (x : A) (P : (y : A) → Id A x y → Prop ℓ₁) 
    (t : P x (Id-refl x)) (y : A) (e : Id A x y) → P y e
J A x P t y e = transport (λ z → P (fst z) (unbox (snd z))) (x , box (Id-refl x)) t (y , box e) (contr-sing A e)

-- tranporting back and forth is the identity

-- cast-inv : (A B : Set ℓ) (e : Id _ A B) (a : A) →
--                      Id A (cast B A (inverse (Set ℓ) {x = A} {y = B} e) (cast A B e a)) a
-- cast-inv {ℓ} A B e a = let e-refl = cast-refl (Id-refl A) a in
--                        let e-refl-cast = cast-refl (Id-refl A) (cast A A (Id-refl A) a) in
--                        J (Set ℓ) A (λ B e → Id A (cast B A (inverse (Set ℓ) {x = A} {y = B} e) (cast A B e a)) a)
--                          (concatId A e-refl-cast e-refl) B e

postulate cast-set : (A : Set ℓ) (e : _) → cast (Set ℓ) (Set ℓ) e A ≡ A

{-# REWRITE cast-set #-}

postulate cast-prop : (A : Prop ℓ) (e : _) → cast (Prop ℓ) (Prop ℓ) e A ≡ A

{-# REWRITE cast-prop #-}

postulate cast-type-family : (A A' : Set ℓ) (f : (a : A) → Set ℓ₁) (e : _) →
                    cast ((a : A) → Set ℓ₁) ((a' : A') → Set ℓ₁) e f ≡
                    λ (a' : A') → let a = cast A' A (inverse (Set ℓ) {x = A} {y = A'} (fstC e)) a' in f a 

{-# REWRITE cast-type-family #-}

postulate cast-Pi : (A A' : Set ℓ) (B : A → Set ℓ₁) (B' : A' → Set ℓ₁) (f : (a : A) → B a) (e : Id _ ((a : A) → B a) ((a' : A') → B' a')) →
                    cast ((a : A) → B a) ((a' : A') → B' a') e f ≡
                    λ (a' : A') → let a = cast A' A (inverse (Set ℓ) {x = A} {y = A'} (fstC e)) a' in
                                  cast _ _ (sndC e a') (f a)

{-# REWRITE cast-Pi #-}

postulate cast-Sigma : (A A' : Set ℓ) (B : A → Set ℓ₁) (B' : A' → Set ℓ₁) (x : A) (y : B x) (e : _) →
                    let eA = fstC e in
                    let x' = cast A A' eA x in 
                    let eB = sndC e x in
                    cast (Σ A B) (Σ A' B') e (x , y) ≡
                    (cast A A' eA x , cast (B x) (B' x') eB y)

{-# REWRITE cast-Sigma #-}

postulate cast-prod : (A A' : Set ℓ) (B B' : Set ℓ₁) (x : A) (y : B) (e : _) →
                    let eA = fstC e in
                    let eB = sndC e in
                    cast (prod A B) (prod A' B') e (x , y) ≡
                    (cast A A' eA x , cast B B' eB y)

{-# REWRITE cast-prod #-}

postulate cast-Sum-inj₁ : (A A' : Set ℓ) (B B' : Set ℓ₁) (a : A) (e : _) →
                    let eA = fstC e in
                    let eB = sndC e in
                    cast (A ⊎ B) (A' ⊎ B') e (inj₁ a) ≡
                    inj₁ (cast A A' eA a)

postulate cast-Sum-inj₂ : (A A' : Set ℓ) (B B' : Set ℓ₁) (b : B) (e : _) →
                    let eA = fstC e in
                    let eB = sndC e in
                    cast (A ⊎ B) (A' ⊎ B') e (inj₂ b) ≡
                    inj₂ (cast B B' eB b)


{-# REWRITE cast-Sum-inj₁ #-}
{-# REWRITE cast-Sum-inj₂ #-}

 
postulate cast-List-nil : (A A' : Set ℓ) (e : _) →
                          cast (List A) (List A') e [] ≡ []

postulate cast-List-cons : (A A' : Set ℓ) (e : _) (a : A) (l : List A) →
                           cast (List A) (List A') e (a ∷ l) ≡
                           cast A A' e a ∷ cast _ _ e l

{-# REWRITE cast-List-nil #-}

{-# REWRITE cast-List-cons #-}


postulate cast-Nat : (e : _) (n : Nat) → cast Nat Nat e n ≡ n

{-# REWRITE cast-Nat #-}

postulate cast-Bool : (e : _) (b : Bool) → cast Bool Bool e b ≡ b

{-# REWRITE cast-Bool #-}

postulate cast-Unit : (e : _) (t : ⊤) → cast ⊤ ⊤ e t ≡ t

{-# REWRITE cast-Unit #-}

postulate cast-Box : (A A' : Prop ℓ) (a : A) (f : _) (g : _) →
                    cast (Box A) (Box A') (f , g) (box a) ≡ box (uninj f a)

{-# REWRITE cast-Box #-}

-- sanity check on closed terms

foo : transport-Id (λ (T : Σ Set (λ A → Σ A (λ _ → A → Set))) → ((snd (snd T)) (fst (snd T))))
                          (Nat , (0 , λ _ → Nat))
                          3
                          (Nat , (0 , λ _ → Nat))
                          (Id-refl {A = Σ Set (λ A → Σ A (λ _ → A → Set))} (Nat , (0 , λ _ → Nat)))
      ≡ 3
foo = refl


test-J-refl-on-closed-term : (X : Set ℓ) (x : X) →
       transport-Id (λ z → Σ ⊤ (λ z → ⊤)) x (tt , tt) x (Id-refl x) ≡ (tt , tt)
test-J-refl-on-closed-term X x = refl 



-- Quotient types

{- 
  Note that r s and t are not used in the definitions, they are just here
  to make sure the theory stays consistent, because postulating the quotient, 
  we can derive them. In particular, with R = λ - - → ⊥, we would get
  a direct inconsistency using Id-refl
-}

record quotient-data ℓ : Set (lsuc ℓ) where
  constructor q-data
  field
    carrier : Set ℓ
    rel : carrier → carrier → Prop ℓ
    rel-refl : (x : carrier) → rel x x
    rel-sym : (x y : carrier) → rel x y → rel y x
    rel-trans : (x y z : carrier) → rel x y → rel y z → rel x z

open quotient-data public

postulate Quotient : (Q : quotient-data ℓ) →
                     Set ℓ

postulate pi : {Q : quotient-data ℓ} →
               carrier Q → Quotient Q

telescope-Quotient : Set (lsuc ℓ)
telescope-Quotient {ℓ} = Σ (Set ℓ) (λ A → A → A → Prop ℓ)

postulate Id-Quotient : (Q : quotient-data ℓ)
                        (a a' : carrier Q) →
                        Id (Quotient Q)
                           (pi a) (pi a') ≡ rel Q a a'

{-# REWRITE Id-Quotient #-}

postulate Quotient-elim : (Q : quotient-data ℓ)
               (P : Quotient Q → Set ℓ₁) 
               (p : (x : carrier Q) → P (pi x))
               (e : (x y : carrier Q) → (r : rel Q x y) →
                    Id _ (transport-Id P (pi x) (p x) (pi y) r) (p y))
               (w : Quotient Q) → P w

postulate Quotient-elim-red : (Q : quotient-data ℓ)
                (P : Quotient Q → Set ℓ₁) 
                (p : (x : carrier Q) → P (pi x))
                (e : (x y : carrier Q) → (r : rel Q x y) →
                     Id _ (transport-Id P (pi x) (p x) (pi y) r) (p y))
                (a : carrier Q) →
                Quotient-elim Q P p e (pi a)
                ≡ p a

{-# REWRITE Quotient-elim-red #-}

postulate Quotient-elim-prop : (Q : quotient-data ℓ)
               (P : Quotient Q → Prop ℓ₁) 
               (p : (x : carrier Q) → P (pi x))
               (w : Quotient Q) → P w


postulate Id-Type-Quotient : (Q Q' : quotient-data ℓ) →
                Id (Set ℓ) (Quotient Q) (Quotient Q')
                ≡
                Id telescope-Quotient (carrier Q , rel Q) (carrier Q' , rel Q')

{-# REWRITE Id-Type-Quotient #-}

postulate cast-Quotient : (Q Q' : quotient-data ℓ) 
                (a : carrier Q) (e : _) →
                cast (Quotient Q) (Quotient Q') e (pi a) ≡
                pi (cast (carrier Q) (carrier Q') (fstC e) a)

{-# REWRITE cast-Quotient #-}

-- double induction principle

Quotient-elim2-aux : (Q : quotient-data ℓ)
                 (P : Quotient Q → Quotient Q → Set ℓ₁)
                 (p : (x y : carrier Q) → P (pi x) (pi y))
                 (e : (x x' y y' : carrier Q) → (Q-rel1 : rel Q x x') → (Q-rel2 : rel Q y y') →
                            Id _ (transport-Id (P (pi x')) (pi y) (transport-Id (λ x → P x (pi y)) (pi x) (p x y) (pi x') Q-rel1) (pi y') Q-rel2) (p x' y')) (x : carrier Q) (w : Quotient Q) → P w (pi x)
Quotient-elim2-aux Q P p e x = Quotient-elim Q (λ w → P w (pi x)) (λ y → p y x) (λ y y' r → let e-cst = e y y' x x r (rel-refl Q x) in transport (λ e → Id (P (pi y') (pi x))
        (e
         (cast (P (pi y) (pi x)) (P (pi y') (pi x)) (ap (λ y → P y (pi x)) r) (p y x)))
        (p y' x)) (cast (P (pi y') (pi x)) (P (pi y') (pi x)) (ap (P (pi y')) (rel-refl Q x)))
           e-cst (λ w → w) λ a → cast-refl {A = P (pi y') (pi x)} (Id-refl (P (pi y') (pi x))) a ) 

Quotient-elim2 : (Q : quotient-data ℓ)
                 (P : Quotient Q → Quotient Q → Set ℓ₁)
                 (p : (x y : carrier Q) → P (pi x) (pi y))
                 (e : (x x' y y' : carrier Q) → (Q-rel1 : rel Q x x') → (Q-rel2 : rel Q y y') →
                         Id _ (transport-Id (P (pi x')) (pi y) (transport-Id (λ x → P x (pi y)) (pi x) (p x y) (pi x') Q-rel1) (pi y') Q-rel2) (p x' y'))
                 (w w' : Quotient Q) → P w w'
Quotient-elim2 Q P p e w =
  Quotient-elim Q (P w) (λ x → Quotient-elim2-aux Q P p e x w)
                (λ x x' r → Quotient-elim-prop Q (λ w → Id (P w (pi x'))
                (transport-Id (P w) (pi x) (Quotient-elim2-aux Q P p e x w) (pi x') r)
                (Quotient-elim2-aux Q P p e x' w)) (λ y → let e-cst = e y y x x' (rel-refl Q y) r in
                                    transport (λ e → Id (P (pi y) (pi x'))
        (cast (P (pi y) (pi x)) (P (pi y) (pi x')) (ap (P (pi y)) r) (e (p y x)))
        (p y x')) (cast (P (pi y) (pi x)) (P (pi y) (pi x)) (ap (P (pi y)) (rel-refl Q x)))
           e-cst (λ w → w)  λ a → cast-refl {A = P (pi y) (pi x)} (Id-refl (P (pi y) (pi x))) a  ) w)



{-
-- Sanity Check: transport-refl on quotient type

transport-refl-Quotient : (X : Set ℓ)
                  (carrier Q : X -> Set ℓ₁)
                  (R : (x : X) → carrier Q x → carrier Q x → Prop ℓ₁)
                  (r : (z : X) (x : carrier Q z) → R z x x)
                  (s : (z : X) (x y : carrier Q z) → R z x y → R z y x)
                  (t : (zz : X) (x y z : carrier Q zz) → R zz x y → R zz y z → R zz x z)
                  (x : X) (q : Quotient (carrier Q x) (R x) (r x) (s x) (t x))
                  (e : Id X x x) →
                  Id _
                    (transport-Id (λ x → Quotient (carrier Q x) (R x) (r x) (s x) (t x))
                               x q x e)
                    q
transport-refl-Quotient X carrier Q R r s t x q e =
  Quotient-elim-prop (carrier Q x) (R x) (r x) (s x) (t x)
                     ((λ a → Id _ (transport-Id (λ (x : X) → Quotient (carrier Q x) (R x) (r x) (s x) (t x)) x a x e) a))
                     (λ a →  transport (λ a' → R x a' a) a (r x a) (cast (carrier Q x) (carrier Q x) _ a) (inverse (carrier Q x) (transport-refl carrier Q x a e)))
                     q

-}

-- Now for Path

telescope-Path : Set (lsuc ℓ)
telescope-Path {ℓ} = Σ (Set ℓ) (λ A → prod A A)

postulate Id-Path : (A : Set ℓ) (x : A) (y : A) (e e' : _)→
                    Id (x ≡ y) e e' ≡ ⊤P

{-# REWRITE Id-Path #-}

postulate Id-Type-Path : (A A' : Set ℓ) (x y : A) (x' y' : A') →
                       Id (Set ℓ) (x ≡ y) (x' ≡ y') ≡
                       Id telescope-Path 
                         (A  , (x , y))
                         (A' , (x' , y' ))

{-# REWRITE Id-Type-Path #-}

-- not enough to get canonicity

-- postulate cast-Path : (A A' : Set ℓ) (x : A) (x' : A') (e : _) →
                    -- cast (x ≡ x) (x' ≡ x') e refl ≡ refl

-- {-# REWRITE cast-Path #-}

transport-Path : {A : Set ℓ} (x : A) (P :  (y : A) → Set ℓ₁)  (t : P x) (y : A) (e : x ≡ y) → P y
transport-Path P x t y refl = t

transport-Path-refl : {A : Set ℓ} (P : A → Prop ℓ₁) (x : A) (t : P x) (y : A) (e : x ≡ y) → P y
transport-Path-refl P x t .x refl = t


path-to-Id : {A : Set ℓ} {x y : A} → x ≡ y → Id A x y 
path-to-Id {ℓ} {A} {x} {y} = transport-Path-refl (Id A x) x (Id-refl x) y

-- we treat cast X (a ≡ b) e x as a new constructor of equality

postulate IdPath : {A : Set ℓ} {x y : A} → Id A x y → x ≡ y

postulate transport-Path-cast-refl : {A B : Set ℓ} (a : A) (b b' : B) (e : Id (Set ℓ) (a ≡ a) (b ≡ b')) → 
                             cast (a ≡ a) (b ≡ b') e refl ≡
                             IdPath ( let X = fstC (sndC e) in let Y = sndC (sndC e) in concatId B (inverse B X) Y)

{-# REWRITE transport-Path-cast-refl #-}

postulate transport-Path-IdPath : {A : Set ℓ} (x : A) (P : (y : A) → Set ℓ₁) (t : P x) (y : A) (e : Id A x y) →
                        transport-Path x P t y (IdPath e) ≡ transport-Id P x t y e

{-# REWRITE transport-Path-IdPath #-}

postulate transport-Path-cast-IdPath : {A B : Set ℓ} (a a' : A) (b b' : B) (ea : Id A a a') (e : Id (Set ℓ) (a ≡ a') (b ≡ b')) → 
                             cast (a ≡ a') (b ≡ b') e (IdPath ea) ≡
                             IdPath (concatId B (inverse B (fstC (sndC e)))
                                          (concatId B  (ap (cast A B (fstC e)) ea) (sndC (sndC e))))

{-# REWRITE transport-Path-cast-IdPath #-}

transport-refl-Path : {A : Set ℓ} (P : A → Set ℓ₁) (x : A) (t : P x) → transport-Path x P t x refl ≡ t
transport-refl-Path P x t = refl

funext-Path : (A : Set ℓ) (B : A → Set ℓ₁) (f g : (a : A) → B a) →
          ((a : A) → f a ≡ g a) → f ≡ g 
funext-Path A B f g e = IdPath (λ a → path-to-Id (e a))

etaBool : (a : Bool) → a ≡ (if a then true else false)
etaBool true = refl
etaBool false = refl

eq_fun : (λ (b : Bool) → b) ≡ (λ (b : Bool) → if b then true else false)
eq_fun = funext-Path Bool (λ - → Bool) _ _ λ a → etaBool a

-- standard boolean using equality

std-bool : Bool
std-bool = transport-Path (λ (b : Bool) → b) (λ f → Bool) true (λ (b : Bool) → if b then true else false) eq_fun

sanity-check : std-bool ≡ true
sanity-check = refl

