open import Data.ByteString.Static using ( lazy ; strict )
open import System.IO using ( _>>_ ; _>>=_ ; getBytes ; putStr ; commit )

module System.IO.Examples.DevNull where

main =
  getBytes {lazy} >>= λ bs →
  putStr "Done.\n" >>
  commit
