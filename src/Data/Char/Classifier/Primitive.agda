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

{-# IMPORT Data.Char #-}
{-# COMPILED isAscii Data.Char.isAscii  #-}
{-# COMPILED isLatin1 Data.Char.isLatin1 #-}
{-# COMPILED isControl Data.Char.isControl #-}
{-# COMPILED isSpace Data.Char.isSpace #-}
{-# COMPILED isLower Data.Char.isLower #-}
{-# COMPILED isUpper Data.Char.isUpper #-}
{-# COMPILED isAlpha Data.Char.isAlpha #-}
{-# COMPILED isAlphaNum Data.Char.isAlphaNum #-}
{-# COMPILED isPrint Data.Char.isPrint #-}
{-# COMPILED isDigit Data.Char.isDigit #-}
{-# COMPILED isOctDigit Data.Char.isOctDigit #-}
{-# COMPILED isHexDigit Data.Char.isHexDigit #-}
