open import Data.String using ( String )
open import Data.ByteString using ( ByteString ; Style ; lazy ; strict )
open import Data.ByteString.UTF8 using ( toString ; fromString )
open import System.IO.Primitive using ( HandleR ; HandleW ; hOpenR ; hOpenW ; hCloseR ; hCloseW ; hGetStrict ; hGetLazy ; hPutStrict ; hPutLazy )

-- A proposed binding for the Haskell IO library.

-- The semantics is strict IO, there is no visibility for semi-closed handles.

module System.IO where

open System.IO.Primitive public using ( Unit ; IO ; unit ; return ; _>>=_ ; commit ; onCommit ; stdin ; stdout ; stderr )

-- Command is a synonym for IO Unit

Command : Set
Command = IO Unit

skip : Command
skip = return unit

-- Other operations are defined in terms of _>>=_

infixl 1 _>>_
infixl 4 _<$>_ _<*>_

_>>_ : {A B : Set} → (IO A) → (IO B) → (IO B)
a >> b = a >>= (λ x → b)

_<$>_ : {A B : Set} → (A → B) → (IO A) → (IO B)
_<$>_ f a = a >>= (λ x → return (f x))

_<*>_ : {A B : Set} → (IO (A → B)) → (IO A) → (IO B)
_<*>_ f a = f >>= (λ x → x <$> a)

-- TODO: Use the new "syntax" construct to define do-like notation?

-- TODO: RW and Append mode?

data IOMode : Set where
  read write : IOMode

Handle : IOMode → Set
Handle read = HandleR
Handle write = HandleW

-- TODO: There should really be a separate type for file paths,
-- and some sanity-checking to support protection against
-- injection attacks.

hOpen : {m : IOMode} → String → IO (Handle m)
hOpen {read} = hOpenR
hOpen {write} = hOpenW

hGetBytes : {s : Style} → (Handle read) → IO (ByteString s)
hGetBytes {lazy}   = hGetLazy
hGetBytes {strict} = hGetStrict

getBytes : {s : Style} → IO (ByteString s)
getBytes = hGetBytes stdin

hPutBytes : {s : Style} → (Handle write) → (ByteString s) → Command
hPutBytes {lazy}   = hPutLazy
hPutBytes {strict} = hPutStrict

putBytes : {s : Style} → (ByteString s) → Command
putBytes = hPutBytes stdout

hClose : {m : IOMode} → (Handle m) → Command
hClose {read} = hCloseR
hClose {write} = hCloseW

-- TODO: Better handling of codecs, don't just hard-wire UTF-8!
-- TODO: Lazy vs strict strings?
-- Default arguments would help a lot here.

hGetStr : (Handle read) → (IO String)
hGetStr hdl = toString <$> hGetBytes {lazy} hdl

getStr : (IO String)
getStr = hGetStr stdin

hPutStr : (Handle write) → String → Command
hPutStr hdl s = hPutBytes {lazy} hdl (fromString s)

putStr : String → Command
putStr = hPutStr stdout

