{-# OPTIONS --safe #-}

open import Tools.Nat
open import Tools.List
open import Tools.PropositionalEquality

module Tools.Inequality where

data Bool : Set where
  true : Bool
  false : Bool

_∧_ : Bool → Bool → Bool
true ∧ true = true
true ∧ false = false
false ∧ b₂ = false

and-elim-left : ∀ {a b} → (a ∧ b) ≡ true → a ≡ true
and-elim-left {true} {true} H = refl

and-elim-right : ∀ {a b} → (a ∧ b) ≡ true → b ≡ true
and-elim-right {true} {true} H = refl

data BinTree (A : Set) : Set where
  leaf : (l : A) → BinTree A
  node : (t₁ : BinTree A) → (t₂ : BinTree A) → BinTree A

Var : Set
Var = Nat

-- Arithmetic expressions are binary trees of variables

Expr : Set
Expr = BinTree Var

-- Expressions in normal form are list of integers
-- For instance, the list [1; 0; 2] corresponds to 1*x₀ + 0*x₁ + 2*x₂

NormalExpr : Set
NormalExpr = List Nat

normalVar : Var → NormalExpr
normalVar Nat.zero = 1 ∷ []
normalVar (1+ n) = 0 ∷ normalVar n

normalAdd : NormalExpr → NormalExpr → NormalExpr
normalAdd [] e₂ = e₂
normalAdd (x ∷ e₁) [] = x ∷ e₁
normalAdd (x ∷ e₁) (x₁ ∷ e₂) = (x + x₁) ∷ (normalAdd e₁ e₂)

normalize : Expr → NormalExpr
normalize (leaf l) = normalVar l
normalize (node e e₁) = normalAdd (normalize e) (normalize e₁)

-- Evaluating expressions and normal expressions by assigning number to variables

Assignment : Set
Assignment = Var → Nat

evalExpr : Assignment → Expr → Nat
evalExpr a (leaf l) = a l
evalExpr a (node e e₁) = (evalExpr a e) + (evalExpr a e₁)

evalNormalExpr′ : Assignment → Nat → NormalExpr → Nat
evalNormalExpr′ a v [] = 0
evalNormalExpr′ a v (n ∷ e) = (n ⋅ (a v)) + (evalNormalExpr′ a (1+ v) e)

evalNormalExpr : Assignment → NormalExpr → Nat
evalNormalExpr a e = evalNormalExpr′ a 0 e

evalNormalVar′ : (a : Assignment) → (n : Nat) → (v : Var) → evalNormalExpr′ a n (normalVar v) ≡ a (n + v)
evalNormalVar′ a n Nat.zero = trans (trans (plusZero _) (plusZero _)) (cong a (sym (plusZero n)))
evalNormalVar′ a n (1+ v) = trans (evalNormalVar′ a (1+ n) v) (cong a (sym (plusSuc n v)))

evalNormalVar : (a : Assignment) → (v : Var) → evalNormalExpr a (normalVar v) ≡ a v
evalNormalVar a v = evalNormalVar′ a 0 v

evalNormalAdd′ : (a : Assignment) → (n : Nat) → (e₁ e₂ : NormalExpr)
              → evalNormalExpr′ a n (normalAdd e₁ e₂) ≡ evalNormalExpr′ a n e₁ + evalNormalExpr′ a n e₂
evalNormalAdd′ a n [] e₂ = refl
evalNormalAdd′ a n (x ∷ e₁) [] = sym (plusZero _)
evalNormalAdd′ a n (x ∷ e₁) (x₁ ∷ e₂) =
  let α = evalNormalAdd′ a (1+ n) e₁ e₂ in
  trans (cong₂ (λ X Y → X + Y) (distr-left x x₁ (a n)) α)
        (comm-lemma₁ (x ⋅ a n) (x₁ ⋅ a n) (evalNormalExpr′ a (1+ n) e₁) (evalNormalExpr′ a (1+ n) e₂))

evalNormalAdd : (a : Assignment) → (e₁ e₂ : NormalExpr)
              → evalNormalExpr a (normalAdd e₁ e₂) ≡ evalNormalExpr a e₁ + evalNormalExpr a e₂
evalNormalAdd a e₁ e₂ = evalNormalAdd′ a 0 e₁ e₂

evalNormalize : (a : Assignment) → (e : Expr) → evalNormalExpr a (normalize e) ≡ evalExpr a e
evalNormalize a (leaf l) = evalNormalVar a l
evalNormalize a (node e e₁) = trans (evalNormalAdd a (normalize e) (normalize e₁))
                                    (cong₂ (λ X Y → X + Y) (evalNormalize a e) (evalNormalize a e₁))
is≤ : Nat → Nat → Bool
is≤ Nat.zero m = true
is≤ (1+ n) Nat.zero = false
is≤ (1+ n) (1+ m) = is≤ n m

is≤-le : ∀ {n m} → (is≤ n m ≡ true) → n <= m
is≤-le {Nat.zero} {m} H = le0
is≤-le {1+ n} {1+ m} H = leS (is≤-le H)

isSmaller : NormalExpr → NormalExpr → Bool
isSmaller [] e₂ = true
isSmaller (x ∷ e₁) [] = false
isSmaller (x ∷ e₁) (x₁ ∷ e₂) = (is≤ x x₁) ∧ (isSmaller e₁ e₂)

evalSmallerNorm′ : ∀ a n e₁ e₂ → (isSmaller e₁ e₂ ≡ true) → evalNormalExpr′ a n e₁ <= evalNormalExpr′ a n e₂
evalSmallerNorm′ a n [] e₂ H = le0
evalSmallerNorm′ a n (x ∷ e₁) [] ()
evalSmallerNorm′ a n (x ∷ e₁) (x₁ ∷ e₂) H = le-plus (le-times-right {x} {x₁} (a n) (is≤-le (and-elim-left H)))
  (evalSmallerNorm′ a (1+ n) e₁ e₂ (and-elim-right {is≤ x x₁} {isSmaller e₁ e₂} H))

evalSmallerNorm : ∀ a e₁ e₂ → (isSmaller e₁ e₂ ≡ true) → evalNormalExpr a e₁ <= evalNormalExpr a e₂
evalSmallerNorm a e₁ e₂ = evalSmallerNorm′ a 0 e₁ e₂

inequality : ∀ a e₁ e₂ → (isSmaller (normalize e₁) (normalize e₂) ≡ true) → evalExpr a e₁ <= evalExpr a e₂
inequality a e₁ e₂ H = subst₂ (λ X Y → X <= Y) (evalNormalize a e₁) (evalNormalize a e₂)
  (evalSmallerNorm a (normalize e₁) (normalize e₂) H)

[_+_] : Expr → Expr → Expr
[ e + e₁ ] = node e e₁

var : Var → Expr
var n = leaf n

vars : List Nat → Assignment
vars [] = λ _ → 0
vars (n ∷ l) Nat.zero = n
vars (n ∷ l) (1+ x) = vars l x

test : ∀ n m l → (n + (m + l)) <= ((m + l) + (n + l))
test n m l = inequality (vars (n ∷ m ∷ l ∷ []))
  [ var 0 + [ var 1 + var 2 ] ]
  [ [ var 1 + var 2 ] + [ var 0 + var 2 ] ] refl
