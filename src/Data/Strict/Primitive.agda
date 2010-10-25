module Data.Strict.Primitive where

data Strict (A : Set) : Set where
  ! : A → Strict A

{-# IMPORT Data.Strict.AgdaFFI #-}
{-# COMPILED_DATA Strict Data.Strict.AgdaFFI.Strict Data.Strict.AgdaFFI.Strict #-}
