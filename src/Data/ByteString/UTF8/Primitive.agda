open import Data.ByteString.Primitive using ( ByteStringStrict ;  ByteStringStrict² ; ByteStringLazy ; ByteStringLazy² )
open import Data.Bool using ( Bool )
open import Data.Char using ( Char )
open import Data.Natural using ( Natural )
open import Data.String using  ( String )

module Data.ByteString.UTF8.Primitive where
 
postulate
  fromStringStrict : String → ByteStringStrict
  toStringStrict : ByteStringStrict → String
  lengthStrict : ByteStringStrict → Natural
  spanStrict : (Char → Bool) → ByteStringStrict →  ByteStringStrict²
  breakStrict : (Char → Bool) → ByteStringStrict →  ByteStringStrict²

{-# IMPORT Data.ByteString.UTF8 #-}
{-# COMPILED fromStringStrict Data.ByteString.UTF8.fromString #-}
{-# COMPILED toStringStrict Data.ByteString.UTF8.toString #-}
{-# COMPILED lengthStrict fromIntegral . Data.ByteString.UTF8.length #-}
{-# COMPILED spanStrict Data.ByteString.UTF8.span #-}
{-# COMPILED breakStrict Data.ByteString.UTF8.break #-}
 
postulate
  fromStringLazy : String → ByteStringLazy
  toStringLazy : ByteStringLazy → String
  lengthLazy : ByteStringLazy → Natural
  spanLazy : (Char → Bool) → ByteStringLazy →  ByteStringLazy²
  breakLazy : (Char → Bool) → ByteStringLazy →  ByteStringLazy²

{-# IMPORT Data.ByteString.Lazy.UTF8 #-}
{-# COMPILED fromStringLazy Data.ByteString.Lazy.UTF8.fromString #-}
{-# COMPILED toStringLazy Data.ByteString.Lazy.UTF8.toString #-}
{-# COMPILED lengthLazy fromIntegral . Data.ByteString.Lazy.UTF8.length #-}
{-# COMPILED spanLazy Data.ByteString.Lazy.UTF8.span #-}
{-# COMPILED breakLazy Data.ByteString.Lazy.UTF8.break #-}

