module System.IO.AgdaFFI (
    commit, onCommit, 
    hOpen, hClose,
    hGetLazy, hGetStrict,
    hPutLazy, hPutStrict
  ) where

import qualified Data.ByteString as S
import qualified Data.ByteString.Lazy as L
import Data.IORef ( IORef, newIORef, readIORef, writeIORef, atomicModifyIORef )
import System.IO ( IOMode, Handle, openBinaryFile, hFlush )
import qualified System.IO ( hClose )
import System.IO.Unsafe ( unsafePerformIO )
import Control.Applicative ( (<$>), (<*>) )
import Control.Monad ( join )

-- A library for simple IO transactions.  Currently not handling
-- exceptions, rollback or per-thread transactions.

-- A global variable containing the on-commit actions.
-- Ah, unsafePerformIO you are my very bestest friend.
{-# NOINLINE delayed #-}
delayed :: IORef (IO ())
delayed = unsafePerformIO (newIORef (return ()))

-- Commit executes the delayed actions.
-- TODO: Should this be called "flush" rather than "commit"?
-- TODO: What if this raises an exception?
commit :: IO()
commit = join (atomicModifyIORef delayed (\ io -> (return (), io)))

-- onCommit delays execution until the next commit.
onCommit :: IO() -> IO()
onCommit later = atomicModifyIORef delayed (\ io -> (io >> later, ()))

-- The following could use the Strategy or DeepSeq mechanism
-- to generalize away from just lists and bytestrings,
-- but for the moment we stick to the simple case.

-- force xs evaluates the list structure of xs (not its contents!)
-- Pretty please Dr Haskell, don't do clever loop-hoisting
-- and just always return without touching xs.
forceList :: [a] -> IO ()
forceList [] = return ()
forceList (x : xs) = forceList xs

-- strictList xs returns a list equivalent to xs,
-- which will be forced on the next commit.  There
-- is quite a bit of unsafe hoop-jumping here to avoid keeping
-- xs live, which would rather defeat the point of lazy IO.
strictList :: [a] -> IO [a]
strictList xs = do
  r <- newIORef (xs)
  onCommit (readIORef r >>= forceList)
  return (f r xs) where
    {-# NOINLINE f #-}
    f r [] = []
    f r (x : xs) = unsafePerformIO (writeIORef r ys >> return (x : ys)) where
      ys = f r xs

-- strictByteString is just a wrapper round strictList.
strictByteString :: L.ByteString -> IO L.ByteString
strictByteString bs = L.fromChunks <$> (strictList (L.toChunks bs))

-- Handles are opened immediately
-- TODO: This may have a visible side-effect of creating a file?
-- TODO: What if this raises an exception?
hOpen :: IOMode -> String -> IO Handle
hOpen m s = openBinaryFile s m

-- Input can happen immediately.
-- TODO: Currently, exception-generation is very different
-- between the strict and lazy case, we may wish to revisit this.
hGetLazy :: Handle -> IO L.ByteString
hGetLazy hdl = L.hGetContents hdl >>= strictByteString

hGetStrict :: Handle -> IO S.ByteString
hGetStrict hdl = S.hGetContents hdl

-- Output is buffered to be performed on a commit action.
-- TODO: Better treatment of flushing?
hPutLazy :: Handle -> L.ByteString -> IO ()
hPutLazy hdl bs = onCommit (L.hPut hdl bs >> hFlush hdl)

hPutStrict :: Handle -> S.ByteString -> IO ()
hPutStrict hdl bs = seq bs (onCommit (S.hPut hdl bs >> hFlush hdl))

-- Handles are closed on commit
hClose :: Handle -> IO ()
hClose hdl = onCommit (System.IO.hClose hdl)
