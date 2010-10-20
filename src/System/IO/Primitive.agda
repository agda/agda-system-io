open import Coinduction using ( ∞ )
open import Data.ByteString using ( ByteString ; strict ; lazy )
open import Data.String using ( String )

module System.IO.Primitive where

infixl 1 _>>=_

-- The Unit type and its sole inhabitant

postulate
  Unit : Set
  unit : Unit

{-# COMPILED_TYPE Unit () #-}
{-# COMPILED unit () #-}

-- The IO type and its primitives
-- TODO: Make these universe-polymorphic once the compiler supports it

postulate
  IO : Set → Set
  return : {A : Set} → A → (IO A)
  _>>=_  : {A B : Set} → (IO A) → (A → (IO B)) → (IO B)
  inf : {A : Set} → ∞(IO A) → (IO A)

{-# COMPILED_TYPE IO IO #-}
{-# COMPILED return (\ _ a -> return a) #-}
{-# COMPILED _>>=_ (\ _ _ a f -> a >>= f) #-}
-- {-# COMPILED inf (\ _ a -> a) #-}

-- The commitment primitives
postulate
  commit : IO Unit
  onCommit : (IO Unit) → (IO Unit)

{-# IMPORT System.IO.AgdaFFI #-}
{-# COMPILED commit System.IO.AgdaFFI.commit #-}
{-# COMPILED onCommit System.IO.AgdaFFI.onCommit #-}

-- The low-level binary handle primitives.
-- TODO: Should the string etc. functions be built on top of
-- the binary functions, or should we link directly to the Haskll
-- string functions?
-- TODO: Think about append and read-write modes.

postulate
  HandleR : Set
  stdin : HandleR
  hOpenR : String → (IO HandleR)
  hGetLazy : HandleR → (IO (ByteString lazy))
  hGetStrict : HandleR → (IO (ByteString strict))
  hCloseR : HandleR → (IO Unit)

{-# IMPORT System.IO #-}
{-# COMPILED_TYPE HandleR System.IO.Handle #-}
{-# COMPILED stdin System.IO.stdin #-}
{-# COMPILED hOpenR System.IO.AgdaFFI.hOpen System.IO.ReadMode #-}
{-# COMPILED hGetStrict System.IO.AgdaFFI.hGetStrict #-}
{-# COMPILED hGetLazy System.IO.AgdaFFI.hGetLazy #-}
{-# COMPILED hCloseR System.IO.AgdaFFI.hClose #-}

postulate
  HandleW : Set
  stdout : HandleW
  stderr : HandleW
  hOpenW : String → (IO HandleW)
  hPutLazy : HandleW → (ByteString lazy) → (IO Unit)
  hPutStrict : HandleW → (ByteString strict) → (IO Unit)
  hCloseW : HandleW → (IO Unit)

{-# COMPILED_TYPE HandleW System.IO.Handle #-}
{-# COMPILED stdout System.IO.stdout #-}
{-# COMPILED stderr System.IO.stderr #-}
{-# COMPILED hOpenW System.IO.AgdaFFI.hOpen System.IO.WriteMode #-}
{-# COMPILED hPutStrict System.IO.AgdaFFI.hPutStrict #-}
{-# COMPILED hPutLazy System.IO.AgdaFFI.hPutLazy #-}
{-# COMPILED hCloseW System.IO.AgdaFFI.hClose #-}
