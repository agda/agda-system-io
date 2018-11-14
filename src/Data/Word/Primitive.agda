module Data.Word.Primitive where

postulate
  Word : Set
  Word8 : Set
  Word16 : Set
  Word32 : Set
  Word64 : Set

{-# FOREIGN GHC import qualified Data.Word #-}
{-# COMPILE GHC Word = type Data.Word.Word #-}
{-# COMPILE GHC Word8 = type Data.Word.Word8 #-}
{-# COMPILE GHC Word16 = type Data.Word.Word16 #-}
{-# COMPILE GHC Word32 = type Data.Word.Word32 #-}
{-# COMPILE GHC Word64 = type Data.Word.Word64 #-}
