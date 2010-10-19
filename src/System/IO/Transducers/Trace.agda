open import Coinduction using ( ∞ ; ♭ ; ♯_ )
open import Data.Nat using ( ℕ )
open import System.IO.Transducers.Session using ( Session ; [] ; _∷_ ; dom ; Σ ; _/_ )

module System.IO.Transducers.Trace where

infixr 4 _≤_ _≥_
infixr 5 _∷_ _++_ _++'_

-- The semantics of a session is its set of traces.
-- The name "trace" comes from process algebra,
-- it's called a play in games semantics, or a word of an automaton.

-- There's two ways to build traces, both of which are useful.
-- They can be built top-down, as paths from the root of a tree to a subtree:

data _≥_ : Session → Session → Set₁ where
  [] : ∀ {S} → (S ≥ S)
  _∷_ : ∀ {A Ss T} → {V : A → ℕ} → (a : A) → (as : (♭ Ss a) ≥ T) → ((V ∷ Ss) ≥ T)

-- Or they can be built bottom-up, as paths from a subtree back to the root:

data _≤_ : Session → Session → Set₁ where
  [] : ∀ {S} → (S ≤ S)
  _∷_ : ∀ {A Ss T} → {V : A → ℕ} → (a : A) → (as : (V ∷ Ss) ≤ T) → (♭ Ss a ≤ T)

-- Traces form categories, where composition is concatenation.

_++_ : ∀ {S T U} → (S ≥ T) → (T ≥ U) → (S ≥ U)
[]       ++ bs = bs
(a ∷ as) ++ bs = a ∷ (as ++ bs)

_++'_ : ∀ {S T U} → (S ≤ T) → (T ≤ U) → (S ≤ U)
[]       ++' bs = bs
(a ∷ as) ++' bs = a ∷ (as ++' bs)

-- A variant on cons which applies to any session:

_◁_ : ∀ {S T} → (a : Σ S) → (S ≤ T) → (S / a ≤ T)
_◁_ {[]}    () as
_◁_ {V ∷ Ss} a as = a ∷ as

_▷_ : ∀ {S T} → (a : Σ S) → (S / a ≥ T) → (S ≥ T)
_▷_ {[]}    () as
_▷_ {V ∷ Ss} a as = a ∷ as

-- Trace reversal gives a natural isomorphism between the categories.

revApp : ∀ {S T U} → (T ≥ S) → (T ≤ U) → (S ≤ U)
revApp []       bs = bs
revApp (a ∷ as) bs = revApp as (a ∷ bs)

reverse : ∀ {S T} → (T ≥ S) → (S ≤ T)
reverse as = revApp as []

revApp' : ∀ {S T U} → (T ≤ U) → (T ≥ S) → (U ≥ S)
revApp' []       as = as
revApp' (b ∷ bs) as = revApp' bs (b ∷ as)

reverse' : ∀ {S T} → (S ≤ T) → (T ≥ S)
reverse' as = revApp' as []
