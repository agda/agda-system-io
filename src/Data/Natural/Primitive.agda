open import Data.Nat using ( ℕ ) renaming ( zero to zero' ; suc to suc' )
open import Data.Nat.GeneralisedArithmetic using ( fold )
open import Data.String using ( String )

module Data.Natural.Primitive where

infixl 6 _+_ 

postulate 
  Natural : Set
  zero : Natural
  suc : Natural → Natural
  _+_ : Natural → Natural → Natural
  show : Natural → String
  foldl : {A : Set} → (A → A) → A → Natural → A
  foldl' : {A : Set} → (A → A) → A → Natural → A
  foldr : {A : Set} → (A → A) → A → Natural → A

{-# FOREIGN GHC import qualified Data.Natural.AgdaFFI #-}
{-# COMPILE GHC Natural = type Data.Natural.AgdaFFI.Natural #-}
{-# COMPILE GHC zero = 0 #-}
{-# COMPILE GHC suc = succ #-}
{-# COMPILE GHC _+_ = (+) #-}
{-# COMPILE GHC show = show #-}
{-# COMPILE GHC foldl = (\ _ -> Data.Natural.AgdaFFI.nfoldl) #-}
{-# COMPILE GHC foldl' = (\ _ -> Data.Natural.AgdaFFI.nfoldl') #-}
{-# COMPILE GHC foldr = (\ _ -> Data.Natural.AgdaFFI.nfoldr) #-}

private
  postulate
    # : ∀ {i} {A : Set i} → A → Natural
{-# COMPILE GHC # = (\ _ -> Data.Natural.AgdaFFI.convert MAlonzo.Data.Nat.mazNatToInteger) #-}

fromℕ : ℕ → Natural
fromℕ = #
