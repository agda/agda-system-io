-- A binding to a Haskell natural numbers type

open import Data.Nat using ( ℕ ; zero ; suc )

open import Data.Natural.Primitive using ( fromℕ )

module Data.Natural where

open Data.Natural.Primitive public using ( Natural ; _+_ ; show ; foldl ; foldl' ; foldr ) 

# : ℕ → Natural
# = fromℕ

% : Natural → ℕ
% = foldl suc zero
