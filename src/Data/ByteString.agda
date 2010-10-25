-- ByteStrings where we track statically if they're lazy or strict
-- Note that lazy and strict bytestrings have the same semantics
-- in Agda, as all computation is guaranteed to terminate.
-- They may, however, have quite different performance characteristics.

open import Data.Bool using ( Bool )
open import Data.Nat using ( ℕ )
open import Data.Natural using ( Natural ; % )
open import Data.Product using ( _×_ ; _,_ )
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

null : {s : Style} → (ByteString s) → Bool
null {lazy}   = nullLazy
null {strict} = nullStrict

span : {s : Style} → (Byte → Bool) → (ByteString s) → (ByteString s × ByteString s)
span {lazy}   φ bs with spanLazy φ bs
span {lazy}   φ bs | bs² = (lazy₁ bs² , lazy₂ bs²)
span {strict} φ bs with spanStrict φ bs
span {strict} φ bs | bs² = (strict₁ bs² , strict₂ bs²)

break : {s : Style} → (Byte → Bool) → (ByteString s) → (ByteString s × ByteString s)
break {lazy}   φ bs with breakLazy φ bs
break {lazy}   φ bs | bs² = (lazy₁ bs² , lazy₂ bs²)
break {strict} φ bs with breakStrict φ bs
break {strict} φ bs | bs² = (strict₁ bs² , strict₂ bs²)
