{-# OPTIONS --safe #-}

module Definition.Conversion.TransitivityHelper where

open import Tools.Nat as Nat
open import Tools.List
open import Tools.Product
open import Tools.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Tools.Empty
open import Tools.Inequality

import Tools.PropositionalEquality as PE


<=inv-suc :  ∀ {n m : Nat} → 1+ n <= 1+ m → n <= m
<=inv-suc (leS e) = e

+-0 : ∀ {a : Nat} → a + 0 PE.≡ a
+-0 {0} = PE.refl
+-0 {1+ a} = PE.cong 1+ +-0

+-suc : ∀ {a b : Nat} → a + (1+ b) PE.≡ 1+ (a + b)
+-suc {0} {b} = PE.refl
+-suc {1+ a} {b} = PE.cong 1+ +-suc

+-sym : ∀ (a b : Nat) → a + b PE.≡ b + a
+-sym 0 b = PE.sym +-0
+-sym (1+ a) b = PE.trans (PE.cong 1+ (+-sym a b)) (PE.sym +-suc)

+-assoc : ∀ (a b c : Nat) → a + b + c PE.≡ a + (b + c)
+-assoc 0 b c = PE.refl
+-assoc (1+ a) b c = PE.cong 1+ (+-assoc a b c)

<=-trans :  ∀ {a b c : Nat} → a <= b → b <= c → a <= c
<=-trans le0 e = le0
<=-trans (leS e) (leS e') = leS (<=-trans e e')

<=+k :  ∀ {a b c : Nat} → a <= b → a <= (c + b)
<=+k {c = Nat.zero} e = e
<=+k {c = 1+ c} e = <=-trans (<=+k e) (le-suc (le-refl _))

<<-trans :  ∀ {a b c : Nat} → a <= b → b << c → a << c
<<-trans e e' = <=-trans (leS e) e'

≡-to-<= :  ∀ {a b : Nat} → a PE.≡ b → a <= b
≡-to-<= PE.refl = le-refl _

<=-cong-+ : ∀ {a a' b b' : Nat} → a <= a' → b <= b' → (a + b) <= (a' + b')
<=-cong-+ le0 e' = <=+k e'
<=-cong-+ (leS e) e' = leS (<=-cong-+ e e')

<=-cong-+3 : ∀ {a a' b b' c c' : Nat} → a <= a' → b <= b' → c <= c' → (a + b + c) <= (a' + b' + c')
<=-cong-+3 ea eb ec = <=-cong-+ (<=-cong-+ ea eb) ec

<=-cong-+4 : ∀ {a a' b b' c c' d d' : Nat} → a <= a' → b <= b' → c <= c' → d <= d' → (a + b + c + d) <= (a' + b' + c' + d')
<=-cong-+4 ea eb ec ed = <=-cong-+ (<=-cong-+ (<=-cong-+ ea eb) ec) ed

<<cong-right :  ∀ {a b c d : Nat} → (c + d) <= (a + c + (b + d))
<<cong-right {a} {b} {c} {d} = <=-trans (<=-cong-+ (<=+k (le-refl c)) (le-refl d))
                                            (<=-cong-+ (le-refl (a + c)) (<=+k (le-refl d)))

<<bind-suc :  ∀ {n a b : Nat} → (b <= a) → 1+ a << n → 1+ b << n
<<bind-suc eba e = <<-trans (leS eba) e

<=-switch-bc : ∀ {a b c d : Nat} → (a + b + (c + d)) <= (a + c + (b + d))
<=-switch-bc {a} {b} {c} {d} =
  ≡-to-<= (PE.trans (PE.trans (PE.sym (+-assoc (a + b) c d))
                    (PE.cong (λ X →  X + d) (PE.trans (+-assoc a b c)
                    (PE.trans (PE.cong (_+_ a) (+-sym b c)) (PE.sym (+-assoc a c b))))))
                    (+-assoc (a + c) b d))

<=-help-2-2 :  ∀ {a b c : Nat} → (2 + (b + (2 + a + c))) <= (a + (2 + (b + (2 + c))))
<=-help-2-2 {a} {b} {c} = inequality (vars (2 ∷ a ∷ b ∷ c ∷ []))
  [ var 0 + [ var 2 + [ [ var 0 + var 1 ] + var 3 ] ] ]
  [ var 1 + [ var 0 + [ var 2 + [ var 0 + var 3 ] ] ] ] PE.refl

<=-help-2-2' :  ∀ {a b c : Nat} → (2 + (b + (2 + (a + c)))) <= (2 + (b + (2 + a) + c))
<=-help-2-2' {a} {b} {c} = inequality (vars (2 ∷ a ∷ b ∷ c ∷ []))
  [ var 0 + [ var 2 + [ var 0 + [ var 1 + var 3 ] ] ] ]
  [ var 0 + [ [ var 2 + [ var 0 + var 1 ] ] + var 3 ] ] PE.refl

<=-help-1-2 :  ∀ {a b : Nat} → (1+ (a + b)) <= (a + (2 + b))
<=-help-1-2 {a} {b} = inequality (vars (1 ∷ a ∷ b ∷ []))
  [ var 0 + [ var 1 + var 2 ] ]
  [ var 1 + [ [ var 0 + var 0 ] + var 2 ] ] PE.refl

<=-help-2-1 :  ∀ {a b : Nat} → (a + b) <= ((2 + a) + (1+ b))
<=-help-2-1 {a} {b} = inequality (vars (1 ∷ a ∷ b ∷ []))
  [ var 1 + var 2 ]
  [ [ [ var 0 + var 0 ] + var 1 ] + [ var 0 + var 2 ] ] PE.refl

<=-help-2 :  ∀ {a b : Nat} → (2 + (a + b)) <= (a + (2 + b))
<=-help-2 {a} {b} = inequality (vars (2 ∷ a ∷ b ∷ []))
  [ var 0 + [ var 1 + var 2 ] ]
  [ var 1 + [ var 0 + var 2 ] ] PE.refl

<=-help-22-rem :  ∀ {a b c d : Nat} → (b + d) <= (a + (2 + b) + (c + (2 + d)))
<=-help-22-rem {a} {b} {c} {d} = inequality (vars (2 ∷ a ∷ b ∷ c ∷ d ∷ []))
  [ var 2 + var 4 ]
  [ [ var 1 + [ var 0 + var 2 ] ] + [ var 3 + [ var 0 + var 4 ] ] ] PE.refl

<=-help-ab :  ∀ {a b c d : Nat} → 1+ (a + b) <= (a + (1+ c) + (b + d))
<=-help-ab = {!!}

<=-help-ab1 :  ∀ {a b : Nat} → 1+ (a + b) <= (a + 1 + (b + 1))
<=-help-ab1 = {!!}

<=-help-abc :  ∀ {a b c : Nat} → 1+ (a + c) <= (a + 1+ (b + (2 + c)))
<=-help-abc = {!!}

<=-help-abc' :  ∀ {a b c : Nat} → 1+ (a + c) <= (1+ b + (2 + a) + c)
<=-help-abc' = {!!}

<=-help-ab1' :  ∀ {a b : Nat} → (a + b) <= (a + 1+ b)
<=-help-ab1' = {!!}

<=-help-ab' :  ∀ {a b c d : Nat} → (a + b) <= (a + c + 1+ (b + d))
<=-help-ab' = {!!}

<=-help-ab'' :  ∀ {a b c d : Nat} → (b + d) <= (a + b + 1+ (c + d))
<=-help-ab'' = {!!}

<=-help-3-ab :  ∀ {a b b' c d : Nat} → (a + b) <= (a + c + 1+ (b + b' + d))
<=-help-3-ab = {!!}

<=-help-3-ab' :  ∀ {a b b' c d : Nat} → (b' + (1+ a)) <= (a + c + 1+ (b + (1+ b') + d))
<=-help-3-ab' = {!!}

<=-help-3-abb' :  ∀ {a b b' c d : Nat} → (b' + a + b) <= (a + c + 1+ (b + b' + d))
<=-help-3-abb' = {!!}

<=-help-3-ab'c :  ∀ {a b b' c c' d : Nat} → (b' + c) <= (a + c + c' + 1+ (b + (1+ b') + d))
<=-help-3-ab'c = {!!}

<=-help-3-abcde :  ∀ {a b c d e : Nat} → (a + b + c + (d + e)) <= (b + d + 1+ (c + a + e))
<=-help-3-abcde = {!!}

<=-help-3-abcde' :  ∀ {a b c d e : Nat} → (a + d + b + (c + e)) <= (a + b + c + 1+ (d + e))
<=-help-3-abcde' = {!!}

<=-help-abcd-b :  ∀ {a b c d : Nat} → (a + c + d) <= (a + b + 1+ (c + d))
<=-help-abcd-b = {!!}

<=-help-3-abcd :  ∀ {a b c d : Nat} → (a + b + (c + d)) <= (a + c + 1+ (b + d))
<=-help-3-abcd = {!!}

<=-help-nat-cong-ab :  ∀ {a b b' b'' b''' c' c'' c''' : Nat} → (a + b) <= (a + b' + b'' + b''' + 1+ (b + c' + c'' + c'''))
<=-help-nat-cong-ab = {!!}

<=-help-nat-congb'c' :  ∀ {a b b' b'' b''' c' c'' c''' : Nat} → (b' + c') <= (a + b' + b'' + b''' + 1+ (b + c' + c'' + c'''))
<=-help-nat-congb'c' = {!!}

<=-help-nat-congb''c'' :  ∀ {a b b' b'' b''' c' c'' c''' : Nat} → (b'' + c'') <= (a + b' + b'' + b''' + 1+ (b + c' + c'' + c'''))
<=-help-nat-congb''c'' = {!!}

<=-help-nat-congb'''c''' :  ∀ {a b b' b'' b''' c' c'' c''' : Nat} → (b''' + c''') <= (a + b' + b'' + b''' + 1+ (b + c' + c'' + c'''))
<=-help-nat-congb'''c''' = {!!}

<=-help-nat-cong :  ∀ {a b b' b'' b''' c' c'' c''' : Nat} → (a + b + (b' + c') + (b'' + c'') + (b''' + c''')) <= (a + b' + b'' + b''' + 1+ (b + c' + c'' + c'''))
<=-help-nat-cong = {!!}

<=-help-id-cong :  ∀ {a b b' b'' c' c''  : Nat} → (a + b) <= (a + b' + b'' + 1+ (b + c' + c''))
<=-help-id-cong = {!!}

<=-help-id-cong' :  ∀ {a b b' b'' c' c''  : Nat} → (a + b + (b' + c') + (b'' + c'') ) <= (a + b' + b'' + 1+ (b + c' + c''))
<=-help-id-cong' = {!!}

<=-help-id-cong'' :  ∀ {a b b' b'' c' c''  : Nat} → (a + b + (c' + b') + (b'' + c'') ) <= (a + b' + b'' + 1+ (b + c' + c''))
<=-help-id-cong'' = {!!}

<=-help-b''c'' :  ∀ {a b b' b'' c' c''  : Nat} → (b'' + c'') <= (a + b' + b'' + 1+ (b + c' + c''))
<=-help-b''c'' = {!!}

<=-help-b'c' :  ∀ {a b b' b'' c' c''  : Nat} → (b' + c') <= (a + b' + b'' + 1+ (b + c' + c''))
<=-help-b'c' = {!!}

<=-help-id-cong-c'' :  ∀ {a b b' b'' c' : Nat} → (a + b) <= (a + b' + b'' + 1+ (b + c'))
<=-help-id-cong-c'' = {!!}

<=-help-abb'-c'' :  ∀ {a b b' b'' c' : Nat} → (a + b + b') <= (a + b' + b'' + 1+ (b + c'))
<=-help-abb'-c'' = {!!}


<=-help-id-cong-ab' :  ∀ {a b b' b'' c' c''  : Nat} → (a + b') <= (a + b' + b'' + 1+ (b + c' + c''))
<=-help-id-cong-ab' = {!!}

<=-help-id-cong-bc' :  ∀ {a b b' b'' c' c''  : Nat} → (b + c') <= (a + b' + b'' + 1+ (b + c' + c''))
<=-help-id-cong-bc' = {!!}

<=-help-cast :  ∀ {a b c d : Nat} → (c + d) <= (a + b + (2 + c) + d)
<=-help-cast = {!!}

<=-help-cast' :  ∀ {a b b' b'' c' c''  : Nat} → (1+ (a + b' + b'') + c'') <= (a + b' + b'' + 1+ (b + c' + (2 + c'')))
<=-help-cast' = {!!}


<=-help-abrem :  ∀ {x a b : Nat} → a <= (x + 1+ (a + b))
<=-help-abrem = {!!}

<=-help-abrem' :  ∀ {x a b : Nat} → b <= (1+ (a + (x + b)))
<=-help-abrem' = {!!}

<=-help-barem :  ∀ {x a b : Nat} → a <= (a + b + x)
<=-help-barem = {!!}

<=-help-barem' :  ∀ {x a b : Nat} → (b + x) <= (a + (2 + b) + x)
<=-help-barem' = {!!}

sizeSubst₃-gen :  ∀ {A B C a b c a' b' c'}
              → (P : A → B → C → Set)
              → (size : ∀ {a b c} → P a b c → Nat)
              → (t : P a b c)
              → (ea : a PE.≡ a')
              → (eb : b PE.≡ b')
              → (ec : c PE.≡ c')
              → size (PE.subst₃ P ea eb ec t) PE.≡ size t
sizeSubst₃-gen _ _ _ PE.refl PE.refl PE.refl = PE.refl
