open import Data.Char using ( Char )
open import Data.Bool using ( Bool )

module Data.Char.Classifier.Primitive where

postulate
  isAscii  : Char → Bool
  isLatin1 : Char → Bool
  isControl : Char → Bool
  isSpace : Char → Bool
  isLower : Char → Bool
  isUpper : Char → Bool
  isAlpha : Char → Bool
  isAlphaNum : Char → Bool
  isPrint : Char → Bool
  isDigit : Char → Bool
  isOctDigit : Char → Bool
  isHexDigit : Char → Bool

{-# FOREIGN GHC import qualified Data.Char #-}
{-# COMPILE GHC isAscii = type Data.Char.isAscii  #-}
{-# COMPILE GHC isLatin1 = type Data.Char.isLatin1 #-}
{-# COMPILE GHC isControl = type Data.Char.isControl #-}
{-# COMPILE GHC isSpace = type Data.Char.isSpace #-}
{-# COMPILE GHC isLower = type Data.Char.isLower #-}
{-# COMPILE GHC isUpper = type Data.Char.isUpper #-}
{-# COMPILE GHC isAlpha = type Data.Char.isAlpha #-}
{-# COMPILE GHC isAlphaNum = type Data.Char.isAlphaNum #-}
{-# COMPILE GHC isPrint = type Data.Char.isPrint #-}
{-# COMPILE GHC isDigit = type Data.Char.isDigit #-}
{-# COMPILE GHC isOctDigit = type Data.Char.isOctDigit #-}
{-# COMPILE GHC isHexDigit = type Data.Char.isHexDigit #-}
