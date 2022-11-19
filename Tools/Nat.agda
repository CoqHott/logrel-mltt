-- The natural numbers.

{-# OPTIONS --safe #-}

module Tools.Nat where

open import Tools.PropositionalEquality
open import Tools.Nullary

-- We reexport Agda's built-in type of natural numbers.

open import Agda.Builtin.Nat using (zero; suc)
open import Agda.Builtin.Nat using (Nat) public

pattern 1+ n = suc n

infix 4 _≟_
infixl 5 _+_
infix 7 _<<_ _<=_

-- Predecessor, cutting off at 0.

pred : Nat → Nat
pred zero = zero
pred (suc n) = n

-- Decision of number equality.

_≟_ : (m n : Nat) → Dec (m ≡ n)
zero  ≟ zero   = yes refl
suc m ≟ suc n  with m ≟ n
suc m ≟ suc .m | yes refl = yes refl
suc m ≟ suc n  | no prf   = no (λ x → prf (subst (λ y → m ≡ pred y) x refl))
zero  ≟ suc n  = no λ()
suc m ≟ zero   = no λ()

_+_ : (m n : Nat) → Nat
0 + n = n
suc m + n = suc (m + n)

_×_ : Nat → Nat → Nat
0 × m = 0
(1+ n) × m = m + (n × m)

data _<=_ : Nat → Nat → Set where
  le0 : ∀ {n : Nat} → 0 <= n
  leS : ∀ {n m : Nat} → n <= m → 1+ n <= 1+ m

le-suc :  ∀ {n m : Nat} → n <= m → n <= 1+ m
le-suc le0 = le0
le-suc (leS e) = leS (le-suc e)

le-refl :  (n : Nat) → n <= n
le-refl 0 = le0
le-refl (1+ n) = leS (le-refl n)

_<<_ :  Nat → Nat → Set
n << m = 1+ n <= m

<<inv-suc :  ∀ {n m : Nat} → 1+ n << 1+ m → n << m
<<inv-suc (leS e) = e

<<rem-suc :  ∀ {n m : Nat} → 1+ n << m → n << m
<<rem-suc (leS e) = le-suc e

plusZero : (n : Nat) → n + 0 ≡ n
plusZero Nat.zero = refl
plusZero (1+ n) = cong 1+ (plusZero n)

plusSuc : (n m : Nat) → n + 1+ m ≡ 1+ (n + m)
plusSuc Nat.zero m = refl
plusSuc (1+ n) m = cong 1+ (plusSuc n m)

plus-assoc : ∀ m n l → m + (n + l) ≡ (m + n) + l
plus-assoc Nat.zero n l = refl
plus-assoc (1+ m) n l = cong 1+ (plus-assoc m n l)

plus-succ : ∀ m n → 1+ (m + n) ≡ m + (1+ n)
plus-succ Nat.zero n = refl
plus-succ (1+ m) n = cong 1+ (plus-succ m n)

plus-comm : ∀ m n → m + n ≡ n + m
plus-comm Nat.zero n = sym (plusZero n)
plus-comm (1+ m) n = trans (cong 1+ (plus-comm m n)) (plus-succ n m)

prod-zero : ∀ m → m × 0 ≡ 0
prod-zero Nat.zero = refl
prod-zero (1+ m) = prod-zero m

prod-suc : ∀ n m → n × (1+ m) ≡ n + (n × m)
prod-suc Nat.zero m = refl
prod-suc (1+ n) m = cong 1+ (trans (cong (λ X → m + X) (prod-suc n m))
  (trans (plus-assoc m n (n × m)) (trans (cong (λ X → X + (n × m)) (plus-comm m n)) (sym (plus-assoc n m (n × m))))))

prod-comm : ∀ m n → m × n ≡ n × m
prod-comm Nat.zero n = sym (prod-zero n)
prod-comm (1+ m) n = trans (cong (λ X → (n + X)) (prod-comm m n)) (sym (prod-suc n m))

distr-left : ∀ m n l → (m + n) × l ≡ (m × l) + (n × l)
distr-left Nat.zero n l = refl
distr-left (1+ m) n l = trans (cong (λ X → l + X) (distr-left m n l)) (plus-assoc l (m × l) (n × l))

comm-lemma₁ : ∀ m n l k → (m + n) + (l + k) ≡ (m + l) + (n + k)
comm-lemma₁ m n l k =
  trans (plus-assoc (m + n) l k)
    (trans (cong (λ X → X + k) (trans (trans (sym (plus-assoc m n l)) (cong (λ X → m + X) (plus-comm n l))) (plus-assoc m l n)))
      (sym (plus-assoc (m + l) n k)))

le-plus-left : ∀ {m n} l → m <= n → m <= (l + n)
le-plus-left Nat.zero H = H
le-plus-left (1+ l) H = le-suc (le-plus-left l H)

le-plus : ∀ {m n l k} → m <= n → l <= k → (m + l) <= (n + k)
le-plus {Nat.zero} {Nat.zero} H₁ H₂ = H₂
le-plus {Nat.zero} {1+ n} le0 H₂ = le-plus-left (1+ n) H₂
le-plus {1+ m} {1+ n} (leS H₁) H₂ = leS (le-plus H₁ H₂)

le-times-left : ∀ {m n} l → m <= n → (l × m) <= (l × n)
le-times-left Nat.zero H = le0
le-times-left (1+ l) H = le-plus H (le-times-left l H)

le-times-right : ∀ {m n} l → m <= n → (m × l) <= (n × l)
le-times-right l H = subst₂ (λ X Y → X <= Y) (prod-comm l _) (prod-comm l _) (le-times-left l H)
