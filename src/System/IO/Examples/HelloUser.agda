open import Data.String using ( _++_ )
open import System.IO using ( _>>_ ; _>>=_ ; getStr ; putStr ; commit )

module System.IO.Examples.HelloUser where

main = 
  putStr "What is your name?\n" >>
  commit >>
  getStr >>= λ name → 
  putStr ("Hello, " ++ name ++ "\n") >> 
  commit
