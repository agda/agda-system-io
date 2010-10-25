open import IO using ( _>>_ ; putStr ; run )

module System.IO.Examples.HelloRaw where

main = run (putStr "Hello, World\n")
