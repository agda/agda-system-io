open import Data.Nat using ( ℕ ; fold ) renaming ( zero to zero' ; suc to suc' )
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
{-# IMPORT Data.Natural.AgdaFFI #-}
{-# COMPILED_TYPE Natural Data.Natural.AgdaFFI.Natural #-}
{-# COMPILED zero 0 #-}
{-# COMPILED suc succ #-}
{-# COMPILED _+_ (+) #-}
{-# COMPILED show show #-}
{-# COMPILED foldl (\ _ -> Data.Natural.AgdaFFI.nfoldl) #-}
{-# COMPILED foldl' (\ _ -> Data.Natural.AgdaFFI.nfoldl') #-}
{-# COMPILED foldr (\ _ -> Data.Natural.AgdaFFI.nfoldr) #-}

private
  postulate
    # : ∀ {A} → A → Natural
{-# COMPILED # (\ _ -> Data.Natural.AgdaFFI.convert MAlonzo.Data.Nat.mazNatToInteger) #-}

fromℕ : ℕ → Natural
fromℕ = #