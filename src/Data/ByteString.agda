-- Bytestrings where we track dynamically if they're lazy or strict
-- Note that lazy and strict bytestrings have the same semantics
-- in Agda, as all computation is guaranteed to terminate.
-- They may, however, have quite different performance characteristics.

open import Data.Word using ( Byte )
open import Data.Bytestring.Static using ( inj ) 
  renaming ( Bytestring to Bytestring' ; ε to ε' ; _◁_ to _◁'_ ; _▷_ to _▷'_ ; _∙_ to _∙'_ )

module Data.Bytestring where

open Data.Bytestring.Static public using ( Style ; lazy ; strict )

data Bytestring : Set where
  lazy : (bs : Bytestring' lazy) → Bytestring
  strict : (bs : Bytestring' strict) → Bytestring

style : Bytestring → Style
style (lazy bs)   = lazy
style (strict bs) = strict

static : (bs : Bytestring) → (Bytestring' (style bs))
static (lazy bs)   = bs
static (strict bs) = bs

ε : Bytestring
ε = strict ε'

_◁_ : Byte → Bytestring → Bytestring
b ◁ (lazy bs)   = lazy (b ◁' bs)
b ◁ (strict bs) = strict (b ◁' bs)

_▷_ : Bytestring → Byte → Bytestring
(lazy bs)   ▷ b = lazy (bs ▷' b)
(strict bs) ▷ b = strict (bs ▷' b)

_∙_ : Bytestring → Bytestring → Bytestring
lazy bs   ∙ lazy bs'   = lazy   (bs     ∙' bs'    )
lazy bs   ∙ strict bs' = lazy   (bs     ∙' inj bs')
strict bs ∙ lazy bs'   = lazy   (inj bs ∙' bs'    )
strict bs ∙ strict bs' = strict (bs     ∙' bs'    )
