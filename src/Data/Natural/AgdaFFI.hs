module Data.Natural.AgdaFFI ( Natural, nfoldl, nfoldl', nfoldr, convert ) where

import Unsafe.Coerce ( unsafeCoerce )

newtype Natural = Natural Integer
  deriving Eq

-- Begin yuk.

{-# INLINE [1] coerce #-}
{-# RULES "coerce-id" forall (x :: a) . coerce x = x #-}

coerce :: a -> b
coerce = unsafeCoerce

-- The function f will always really be of type b -> Integer,
-- but it's tricky to get Agda to tell us that.

convert :: (a -> Integer) -> b -> Natural
convert f x = Natural (f (coerce x))

-- End yuk.

nfoldl :: (a -> a) -> a -> Natural -> a
nfoldl f x (Natural (n+1)) = nfoldl f (f x) (Natural n)
nfoldl f x (Natural n)     = x

nfoldl' :: (a -> a) -> a -> Natural -> a
nfoldl' f x (Natural (n+1)) = seq x (nfoldl' f (f x) (Natural n))
nfoldl' f x (Natural n)     = x

nfoldr :: (a -> a) -> a -> Natural -> a
nfoldr f x (Natural (n+1)) = f (nfoldr f x (Natural n))
nfoldr f x (Natural n)     = x

instance Show Natural where
  show (Natural n) = show n

instance Read Natural where
  readsPrec p s = [ (Natural n, t) | (n,t) <- readsPrec p s ]

instance Ord Natural where
  compare (Natural m) (Natural n) = compare m n

instance Enum Natural where
  succ (Natural n)     = Natural (succ n)
  pred (Natural (n+1)) = Natural n
  pred (Natural n)     = Natural 0
  toEnum               = fromInteger . toEnum
  fromEnum             = fromEnum . toInteger

instance Num Natural where
  (Natural n) + (Natural m)         = Natural (n + m)
  (Natural n) - (Natural m) | n < m = Natural 0
  (Natural n) - (Natural m)         = Natural (n - m)
  (Natural n) * (Natural m)         = Natural (n * m)
  negate n                          = Natural 0
  signum (Natural 0)                = Natural 0
  signum (Natural n)                = Natural 1
  abs                               = id
  fromInteger n | n < 0             = Natural n
  fromInteger n                     = Natural n

instance Integral Natural where
  div (Natural m) (Natural n)     = Natural (div m n)
  mod (Natural m) (Natural n)     = Natural (mod m n)
  quotRem (Natural m) (Natural n) = (Natural (m'), Natural (n')) where (m',n') = quotRem m n
  toInteger (Natural n)           = n

instance Real Natural where
  toRational (Natural n) = toRational n
