open import Coinduction using ( ∞ ; ♭ ; ♯_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; _≢_ ; refl )
open import Relation.Nullary using ( Dec ; yes ; no )
open import System.IO.Transducers.Session using ( Weighted ; Session ; I ; Σ )

module System.IO.Transducers.Trace where

infixr 4 _≤_ _≥_ _⊑_
infixr 5 _∷_ _++_ _++'_

-- The semantics of a session is its set of traces.
-- The name "trace" comes from process algebra,
-- it's called a play in games semantics, or a word of an automaton.

data Trace : Session → Set₁ where
  [] : ∀ {S} → (Trace S)
  _∷_ : ∀ {A F} → {W : Weighted A} → (a : A) → (as : Trace (♭ F a)) → (Trace (Σ W F))

-- Traces ending in [] at type I are completed traces

data ✓ : ∀ {S} → Trace S → Set₁ where
  [] : ✓ ([] {I})
  _∷_ : ∀ {A F W} → (a : A) → ∀ {as} → (✓ {♭ F a} as) → (✓ {Σ W F} (a ∷ as))

-- Partial traces come with a prefix order.

data _⊑_ : ∀ {S} → (Trace S) → (Trace S) → Set₁ where
  [] : ∀ {S} {as : Trace S} → ([] ⊑ as)
  _∷_ : ∀ {A W F} (a : A) {as bs} → (_⊑_ {♭ F a} as bs) → (_⊑_ {Σ W F} (a ∷ as) (a ∷ bs))

-- We can also provide types for partial traces which record the
-- source and target session.  There's two ways to build such traces:
-- either top-down, as paths from the root of a tree to a subtree:

data _≥_ : Session → Session → Set₁ where
  [] : ∀ {S} → (S ≥ S)
  _∷_ : ∀ {A F T} → {W : Weighted A} → (a : A) → (as : (♭ F a) ≥ T) → (Σ W F ≥ T)

-- or bottom-up, as paths from a subtree back to the root:

data _≤_ : Session → Session → Set₁ where
  [] : ∀ {S} → (S ≤ S)
  _∷_ : ∀ {A F T} → {W : Weighted A} → (a : A) → (as : Σ W F ≤ T) → (♭ F a ≤ T)

-- Traces form categories, where composition is concatenation.

_++_ : ∀ {S T U} → (S ≥ T) → (T ≥ U) → (S ≥ U)
[]       ++ bs = bs
(a ∷ as) ++ bs = a ∷ (as ++ bs)

_++'_ : ∀ {S T U} → (S ≤ T) → (T ≤ U) → (S ≤ U)
[]       ++' bs = bs
(a ∷ as) ++' bs = a ∷ (as ++' bs)

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
