open import Data.String using ( String )
open import Data.Word using ( Byte )

module Data.ByteString.Primitive where

postulate
  ByteStringLazy : Set
  emptyLazy : ByteStringLazy
  consLazy : Byte → ByteStringLazy → ByteStringLazy
  snocLazy : ByteStringLazy → Byte → ByteStringLazy
  appendLazy : ByteStringLazy → ByteStringLazy → ByteStringLazy

{-# IMPORT Data.ByteString.Lazy #-}
{-# COMPILED_TYPE ByteStringLazy Data.ByteString.Lazy.ByteString #-}
{-# COMPILED emptyLazy Data.ByteString.Lazy.empty #-}
{-# COMPILED consLazy Data.ByteString.Lazy.cons #-}
{-# COMPILED snocLazy Data.ByteString.Lazy.snoc #-}
{-# COMPILED appendLazy Data.ByteString.Lazy.append #-}

postulate
  ByteStringStrict : Set
  emptyStrict : ByteStringStrict
  consStrict : Byte → ByteStringStrict → ByteStringStrict
  snocStrict : ByteStringStrict → Byte → ByteStringStrict
  appendStrict : ByteStringStrict → ByteStringStrict → ByteStringStrict

{-# IMPORT Data.ByteString #-}
{-# COMPILED_TYPE ByteStringStrict Data.ByteString.ByteString #-}
{-# COMPILED emptyStrict Data.ByteString.empty #-}
{-# COMPILED consStrict Data.ByteString.cons #-}
{-# COMPILED snocStrict Data.ByteString.snoc #-}
{-# COMPILED appendStrict Data.ByteString.append #-}

postulate
  mkLazy : ByteStringStrict → ByteStringLazy
  mkStrict : ByteStringLazy → ByteStringStrict

{-# COMPILED mkStrict (Data.ByteString.concat . Data.ByteString.Lazy.toChunks) #-}
{-# COMPILED mkLazy (\ bs -> Data.ByteString.Lazy.fromChunks [ bs ]) #-}
 
-- TODO: Add more codecs, worry about CR/NL conversion
-- TODO: Link directly to the strict versions, or go via mkStrict/mkLazy?

postulate
  fromStringUTF8 : String → ByteStringLazy
  toStringUTF8 : ByteStringLazy → String

{-# IMPORT Data.ByteString.Lazy.UTF8 #-}
{-# COMPILED fromStringUTF8 Data.ByteString.Lazy.UTF8.fromString #-}
{-# COMPILED toStringUTF8 Data.ByteString.Lazy.UTF8.toString #-}
