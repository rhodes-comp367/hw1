module Int1 where

-- import `plus` & `times` on Nats;
-- use these functions where appropriate below.
open import Nat

data Int : Set where
  -- int a b represents (a - b).
  int : Nat → Nat → Int

-- given i, return i + 1.
isuc : Int → Int
isuc (int a b) = int (suc a) b

-- given i, return i - 1.
ipred : Int → Int
ipred = ?

-- given i, return -i.
ineg : Int → Int
ineg = ?

-- given i & j, return i + j.
iplus : Int → Int → Int
iplus = ?

-- given i & j, return i - j.
iminus : Int → Int → Int
iminus = ?

-- given i & j, return i * j.
itimes : Int → Int → Int
itimes = ?

