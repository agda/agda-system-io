open import Data.Nat using ( ℕ )
open import Data.String using ( String )

module Data.Natural.Primitive where

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

-- A hack to get round the fact that ℕ has no FFI binding

private
  postulate
    # : {A : Set} → A → Natural
{-# COMPILED # (\ _ -> fromInteger . MAlonzo.Data.Nat.mazNatToInteger . Unsafe.Coerce.unsafeCoerce) #-}

fromℕ : ℕ → Natural
fromℕ = #
