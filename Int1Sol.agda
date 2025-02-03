module Int1Sol where

open import Nat

data Int : Set where
  -- int a b represents (a - b).
  int : Nat → Nat → Int

isuc : Int → Int
isuc (int a b) = int (suc a) b

ipred : Int → Int
ipred (int a b) = int a (suc b)

ineg : Int → Int
ineg (int a b) = int b a

iplus : Int → Int → Int
iplus (int a₁ b₁) (int a₂ b₂) = int (plus a₁ a₂) (plus b₁ b₂)

iminus : Int → Int → Int
iminus i j = iplus i (ineg j)

itimes : Int → Int → Int
itimes (int a₁ b₁) (int a₂ b₂) = int (plus (times a₁ a₂) (times b₁ b₂)) (plus (times a₁ b₂) (times a₂ b₁))

