-- Strict A is a datatype isomorphic to A, with constructor ! : A → Strict A
-- Semantically it has no impact, but its constructor is strict, so it can be
-- used to force evaluation of a term to whnf by pattern-matching.

open import Data.Strict.Primitive using ()

module Data.Strict where

open Data.Strict.Primitive public using ( Strict ; ! )

