open import Data.Bool using ( Bool )
open import Data.String using ( String )
open import Data.Word using ( Byte )
open import Data.Natural using ( Natural )

module Data.ByteString.Primitive where

postulate
  ByteStringLazy : Set
  ByteStringLazy² : Set
  emptyLazy : ByteStringLazy
  consLazy : Byte → ByteStringLazy → ByteStringLazy
  snocLazy : ByteStringLazy → Byte → ByteStringLazy
  appendLazy : ByteStringLazy → ByteStringLazy → ByteStringLazy
  lengthLazy : ByteStringLazy → Natural
  nullLazy : ByteStringLazy → Bool
  spanLazy : (Byte → Bool) → ByteStringLazy →  ByteStringLazy²
  breakLazy : (Byte → Bool) → ByteStringLazy →  ByteStringLazy²
  lazy₁ : ByteStringLazy² → ByteStringLazy
  lazy₂ : ByteStringLazy² → ByteStringLazy

{-# IMPORT Data.ByteString.Lazy #-}
{-# COMPILED_TYPE ByteStringLazy Data.ByteString.Lazy.ByteString #-}
{-# COMPILED_TYPE ByteStringLazy² (Data.ByteString.Lazy.ByteString,Data.ByteString.Lazy.ByteString) #-}
{-# COMPILED emptyLazy Data.ByteString.Lazy.empty #-}
{-# COMPILED consLazy Data.ByteString.Lazy.cons #-}
{-# COMPILED snocLazy Data.ByteString.Lazy.snoc #-}
{-# COMPILED appendLazy Data.ByteString.Lazy.append #-}
{-# COMPILED lengthLazy fromIntegral . Data.ByteString.Lazy.length #-}
{-# COMPILED nullLazy Data.ByteString.Lazy.null #-}
{-# COMPILED spanLazy Data.ByteString.Lazy.span #-}
{-# COMPILED breakLazy Data.ByteString.Lazy.break #-}
{-# COMPILED lazy₁ \ ( x , y ) -> x #-}
{-# COMPILED lazy₂ \ ( x , y ) -> y #-}

postulate
  ByteStringStrict : Set
  ByteStringStrict² : Set
  emptyStrict : ByteStringStrict
  consStrict : Byte → ByteStringStrict → ByteStringStrict
  snocStrict : ByteStringStrict → Byte → ByteStringStrict
  appendStrict : ByteStringStrict → ByteStringStrict → ByteStringStrict
  lengthStrict : ByteStringStrict → Natural
  nullStrict : ByteStringStrict → Bool
  spanStrict : (Byte → Bool) → ByteStringStrict →  ByteStringStrict²
  breakStrict : (Byte → Bool) → ByteStringStrict →  ByteStringStrict²
  strict₁ : ByteStringStrict² → ByteStringStrict
  strict₂ : ByteStringStrict² → ByteStringStrict

{-# IMPORT Data.ByteString #-}
{-# COMPILED_TYPE ByteStringStrict Data.ByteString.ByteString #-}
{-# COMPILED_TYPE ByteStringStrict² (Data.ByteString.ByteString,Data.ByteString.ByteString) #-}
{-# COMPILED emptyStrict Data.ByteString.empty #-}
{-# COMPILED consStrict Data.ByteString.cons #-}
{-# COMPILED snocStrict Data.ByteString.snoc #-}
{-# COMPILED appendStrict Data.ByteString.append #-}
{-# COMPILED lengthStrict fromIntegral . Data.ByteString.length #-}
{-# COMPILED nullStrict Data.ByteString.null #-}
{-# COMPILED spanStrict Data.ByteString.span #-}
{-# COMPILED breakStrict Data.ByteString.break #-}
{-# COMPILED strict₁ \ ( x , y ) -> x #-}
{-# COMPILED strict₂ \ ( x , y ) -> y #-}

postulate
  mkLazy : ByteStringStrict → ByteStringLazy
  mkStrict : ByteStringLazy → ByteStringStrict

{-# COMPILED mkStrict (Data.ByteString.concat . Data.ByteString.Lazy.toChunks) #-}
{-# COMPILED mkLazy (\ bs -> Data.ByteString.Lazy.fromChunks [ bs ]) #-}
