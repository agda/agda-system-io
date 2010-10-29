-- A binding to a Haskell natural numbers type

open import Data.Nat using ( ℕ ) renaming ( zero to zero' ; suc to suc' )

module Data.Natural where

open import Data.Natural.Primitive public
  using ( Natural ; zero ; suc ; _+_ ; show ; foldl ; foldl' ; foldr )
  renaming ( fromℕ to # )

% : Natural → ℕ
% = foldr suc' zero'
