module nat where

open import Agda.Builtin.Equality
-- open import Relation.Binary.PropositionalEquality

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data Bool : Set where
  true : Bool
  false : Bool

data List : Set where
  [] : List
  _∷_ : Nat → List → List

-- size : List → Nat
-- size l = {!!}

one = (suc zero)
two = (suc one)
three = (suc two)
four = (suc three)
five = (suc four)
six = (suc five)

a = one ∷ (two ∷ (three ∷ []))

_+_ : Nat → Nat → Nat
zero + y = y
suc x + y = suc (x + y)

_*_ : Nat → Nat → Nat
x * zero = zero
x * suc y = x + (x * y)

_*2_ : Nat → Nat → Nat
zero *2 y = zero
suc x *2 y = y + (x * y)

_-_ : Nat → Nat → Nat
zero - y = zero
suc x - zero = suc x
suc x - suc y = x - y


-- data _≡_ {A : Set} : A → A → Set where
--   refl : {x : A} → x ≡ x

sym : {A : Set} {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

cong : {A B : Set} → {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

add-suc : (a b : Nat) → suc (a + b) ≡ (a + (suc b))
add-suc zero b = refl
add-suc (suc a) b = cong suc (add-suc a b)

-- 加法が可換であることの証明
add-comm : (x y : Nat) → (x + y) ≡ (y + x)
add-comm zero zero = refl
add-comm zero (suc y) = cong suc (add-comm zero y)
add-comm (suc x) y = trans (cong suc (add-comm x y)) (add-suc y x)


_≤_ : Nat → Nat → Bool
zero ≤ b = true
suc a ≤ zero = false
suc a ≤ suc b = a ≤ b

{-# TERMINATING #-}
_/_ : Nat → Nat → Nat
zero / y = zero
suc x / zero = zero
suc x / suc y with (y ≤ x)
... | true = suc ((suc x - suc y) / suc y)
... | false = zero

div-helper : Nat → Nat → Nat → Nat → Nat
div-helper zero y₁ y₂ i = i
div-helper (suc x) zero y₂ i = div-helper x y₂ y₂ (suc i)
div-helper (suc x) (suc y₁) y₂ i = div-helper x y₁ y₂ i

div : Nat → Nat → Nat
div x zero = zero
div x (suc y) = div-helper x y y zero

-- div : Nat → Nat → Nat
-- div zero y = zero
-- div (suc x) zero = zero
-- div (suc x) (suc y) = div-helper (suc x) y y zero 

add-assoc-lemma : (x y z : Nat) → suc (x + (y + z)) ≡ ((suc x) + (y + z))
add-assoc-lemma zero y z = refl
add-assoc-lemma (suc x) y z = cong suc (add-assoc-lemma x y z)


add-assoc : (x y z : Nat) → ((x + y) + z) ≡ (x + (y + z))
add-assoc zero y z = refl
add-assoc (suc x) y z = trans (cong suc (add-assoc x y z)) (add-assoc-lemma x y z)


-- ( (suc x) + y ) + z
-- suc (x + (y + z))
-- (suc x) + (y + z)

left-mul-0 : (x : Nat) → zero * x ≡ zero
left-mul-0 zero = refl
left-mul-0 (suc x) = left-mul-0 x

right-mul-0 : (x : Nat) → x * zero ≡ zero * x
right-mul-0 zero = refl 
right-mul-0 (suc x) rewrite left-mul-0 x = refl

left-mul-1 : (x : Nat) → (suc zero) * x ≡ x
left-mul-1 zero = refl
left-mul-1 (suc x) = cong suc (left-mul-1 x)


add-0 : (x : Nat) → x + zero ≡ x
add-0 zero = refl
add-0 (suc x) = cong suc (add-0 x)


mul-zero-l : (x : Nat) → (zero * x) ≡ zero
mul-zero-l zero = refl
mul-zero-l (suc x) = mul-zero-l x

add-swap-lemma : (x y z : Nat) → suc (x + (y + z)) ≡ (x + suc (y + z))
add-swap-lemma zero y z = refl
add-swap-lemma (suc x) y z = cong suc (add-swap-lemma x y z)

add-swap : (x y z : Nat) → x + (y + z) ≡ y + (x + z)
add-swap zero y z = refl
add-swap (suc x) y z = trans (cong suc (add-swap x y z)) (add-swap-lemma y x z)

right-lemma : (x y : Nat) → x * (suc y) ≡ x + (x * y)
right-lemma x y = refl

-- trans を使うためにクソみたいな証明している．
-- ↓ の rewrite 使った方が良い．
lemma-lemma1 : (x : Nat) → suc x ≡ (suc x + (zero * suc x))
lemma-lemma1 zero = refl
lemma-lemma1 (suc x) = cong suc (lemma-lemma1 x)

lemma2 : (x y : Nat) → (suc (suc x)) * (suc y) ≡ (suc (suc x)) + ((suc (suc x)) * y)
lemma2 x y = refl

lemma3 : (x : Nat) → (suc (suc x)) ≡ (suc zero) + (suc x)
lemma3 x = refl

lemma4 : (x : Nat) → ((suc zero) + x) ≡ (suc x)
lemma4 x = refl


lemma1 : (x y : Nat) → (suc x) * y ≡ y + (x * y)
lemma1 zero zero = refl
lemma1 zero (suc y) = trans (cong suc (left-mul-1 y)) (lemma-lemma1 y)
-- lemma1 zero (suc y) rewrite left-mul-1 y | left-mul-0 y | add-0 y = refl
lemma1 (suc x) zero = refl
lemma1 (suc x) (suc y) = trans (lemma2 x y)
  (trans (cong (λ a → (suc (suc x)) + a) (lemma1 (suc x) y))
    (trans (cong (λ a → a + (y + ((suc x) * y))) (lemma3 x))
      (trans (cong (λ a → (suc zero) + a) (add-swap (suc x) y ((suc x) * y)))
        (trans (cong (λ a → (suc zero) + (y + a)) (sym (right-lemma (suc x) y)))
          (trans (cong (λ a → a) (sym (add-assoc (suc zero) y ((suc x) * (suc y))))) (cong (λ a → a + ((suc x) * (suc y))) (lemma4 y))
          )
        )
      )
    )
  )

-- (suc (suc x) * suc y) ≡ (suc y + (suc x * suc y))
-- (suc (suc x) * suc y)
-- (suc (suc x)) + (suc (suc x)) * y
-- (suc (suc x)) + (y + (suc x) * y)
-- (suc zero) + (suc x) + (y + (suc x) * y)
-- (suc zero) + y + (suc x) +(suc x) * y)
-- (suc zero) + y + (suc x) * (suc y)
-- (suc y) + (suc x) * (suc y)

mul-comm : (x y : Nat) → (x * y) ≡ (y * x)
mul-comm x zero = right-mul-0 x
mul-comm x (suc y) = trans (cong (λ a → x + a) (mul-comm x y)) (sym (lemma1 y x))
