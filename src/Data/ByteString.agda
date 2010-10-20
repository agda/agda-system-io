-- ByteStrings where we track statically if they're lazy or strict
-- Note that lazy and strict bytestrings have the same semantics
-- in Agda, as all computation is guaranteed to terminate.
-- They may, however, have quite different performance characteristics.

open import Data.Nat using ( ℕ )
open import Data.Natural using ( Natural ; % )
open import Data.Word using ( Byte )
open import Data.String using ( String )
open import Data.ByteString.Primitive 

module Data.ByteString where

open Data.ByteString.Primitive public using ( mkStrict ; mkLazy )

data Style : Set where
  lazy strict : Style

ByteString : Style → Set
ByteString strict = ByteStringStrict
ByteString lazy   = ByteStringLazy

ε : {s : Style} → (ByteString s)
ε {lazy}   = emptyLazy
ε {strict} = emptyStrict

_∙_ : {s : Style} → (ByteString s) → (ByteString s) → (ByteString s)
_∙_ {lazy}   = appendLazy
_∙_ {strict} = appendStrict

_◁_ : {s : Style} → Byte → (ByteString s) → (ByteString s)
_◁_ {lazy}   = consLazy
_◁_ {strict} = consStrict

_▷_ : {s : Style} → (ByteString s) → Byte → (ByteString s)
_▷_ {lazy}   = snocLazy
_▷_ {strict} = snocStrict

length : {s : Style} → (ByteString s) → Natural
length {lazy}   = lengthLazy
length {strict} = lengthStrict

size : {s : Style} → (ByteString s) → ℕ
size bs = %(length bs)

-- TODO: Better handling of codecs?

data Codec : Set where
  utf8 : Codec

toStringLazy : (c : Codec) → (ByteString lazy) → String
toStringLazy utf8 bs = toStringUTF8 bs

toStringStrict : (c : Codec) → (ByteString strict) → String
toStringStrict c bs = toStringLazy c (mkLazy bs)

toString : (c : Codec) → {s : Style} → (ByteString s) → String
toString c {lazy} = toStringLazy c
toString c {strict} = toStringStrict c

fromStringLazy : (c : Codec) → String → (ByteString lazy)
fromStringLazy utf8 s = fromStringUTF8 s

fromStringStrict : (c : Codec) → String → (ByteString strict)
fromStringStrict c s = mkStrict (fromStringLazy c s)

fromString : (c : Codec) → {s : Style} → String → (ByteString s)
fromString c {lazy} = fromStringLazy c
fromString c {strict} = fromStringStrict c
