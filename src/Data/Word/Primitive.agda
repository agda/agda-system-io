module Data.Word.Primitive where

postulate
  Word : Set
  Word8 : Set
  Word16 : Set
  Word32 : Set
  Word64 : Set

{-# IMPORT Data.Word #-}
{-# COMPILED_TYPE Word Data.Word.Word #-}
{-# COMPILED_TYPE Word8 Data.Word.Word8 #-}
{-# COMPILED_TYPE Word16 Data.Word.Word16 #-}
{-# COMPILED_TYPE Word32 Data.Word.Word32 #-}
{-# COMPILED_TYPE Word64 Data.Word.Word64 #-}
