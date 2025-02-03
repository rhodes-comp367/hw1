module Int2Sol where

open import Nat

data Int : Set where
  -- (+ n) represents positive n.
  + : Nat → Int
  -- (- n) represents negative n.
  - : Nat → Int
  -- 0 can be represented as (+ zero) or (- zero).

ineg : Int → Int
ineg (+ n) = - n
ineg (- n) = + n

isuc : Int → Int
isuc (+ n) = + (suc n)
isuc (- zero) = + (suc zero)
isuc (- (suc n)) = - n

ipred : Int → Int
ipred (- n) = - (suc n)
ipred (+ zero) = - (suc zero)
ipred (+ (suc n)) = + n

iplus : Int → Int → Int
iplus (+ zero) n = n
iplus (- zero) n = n
iplus (+ (suc m)) n = isuc (iplus (+ m) n)
iplus (- (suc m)) n = ipred (iplus (- m) n)

iminus : Int → Int → Int
iminus m n = iplus m (ineg n)

itimes : Int → Int → Int
itimes (+ m) (+ n) = + (times m n)
itimes (+ m) (- n) = - (times m n)
itimes (- m) (+ n) = - (times m n)
itimes (- m) (- n) = + (times m n)

