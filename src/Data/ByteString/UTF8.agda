open import Data.ByteString using ( ByteString ; Style ; strict ; lazy )
open import Data.ByteString.Primitive using ( strict₁ ; strict₂ ; lazy₁ ; lazy₂ )
open import Data.Bool using ( Bool )
open import Data.Char using ( Char )
open import Data.Nat using ( ℕ )
open import Data.Natural using ( Natural ; % )
open import Data.Product using ( _×_ ; _,_ )
open import Data.String using ( String )

open import Data.ByteString.UTF8.Primitive

module Data.ByteString.UTF8 where

toString : {s : Style} → (ByteString s) → String
toString {lazy}   = toStringLazy
toString {strict} = toStringStrict

fromString : {s : Style} → String → (ByteString s)
fromString {lazy}   = fromStringLazy
fromString {strict} = fromStringStrict

length : {s : Style} → (ByteString s) → Natural
length {lazy}   = lengthLazy
length {strict} = lengthStrict

size : {s : Style} → (ByteString s) → ℕ
size bs = % (length bs)

span : {s : Style} → (Char → Bool) → (ByteString s) → (ByteString s × ByteString s)
span {lazy}   φ bs with spanLazy φ bs
span {lazy}   φ bs | bs² = (lazy₁ bs² , lazy₂ bs²)
span {strict} φ bs with spanStrict φ bs
span {strict} φ bs | bs² = (strict₁ bs² , strict₂ bs²)

break : {s : Style} → (Char → Bool) → (ByteString s) → (ByteString s × ByteString s)
break {lazy}   φ bs with breakLazy φ bs
break {lazy}   φ bs | bs² = (lazy₁ bs² , lazy₂ bs²)
break {strict} φ bs with breakStrict φ bs
break {strict} φ bs | bs² = (strict₁ bs² , strict₂ bs²)

