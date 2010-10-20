open import System.IO using ( _>>_ ; putStr ; commit )
open import Data.Natural using ( # ; _+_ ; show )

module System.IO.Examples.HelloFour where

main = putStr "Hello, " >> putStr (show (# 2 + # 2)) >> putStr ".\n" >> commit
