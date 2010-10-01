open import Data.Word.Primitive public using ( Word8 ; Word16 ; Word32 ; Word64 )

module Data.Word where

data WordSize : Set where
  #8 #16 #32 #64 : WordSize

Word : WordSize → Set
Word #8  = Word8
Word #16 = Word16
Word #32 = Word32
Word #64 = Word64

Byte : Set
Byte = Word8
