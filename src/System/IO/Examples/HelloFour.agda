open import System.IO using ( _>>_ ; putStr ; commit )
open import Data.Natural using ( show )
open import System.IO.Examples.Four using ( four )

module System.IO.Examples.HelloFour where

main = putStr "Hello, " >> putStr (show four) >> putStr ".\n" >> commit
