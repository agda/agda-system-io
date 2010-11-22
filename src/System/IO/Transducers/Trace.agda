open import Coinduction using ( ∞ ; ♭ ; ♯_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; _≢_ ; refl )
open import Relation.Nullary using ( Dec ; yes ; no )
open import System.IO.Transducers.Session using ( Session ; I ; Σ ; Γ ; _/_ ; IsI )

module System.IO.Transducers.Trace where

infixr 4 _≤_ _≥_ _⊑_
infixr 5 _∷_ _++_ _++'_

-- The semantics of a session is its set of traces.
-- The name "trace" comes from process algebra,
-- it's called a play in games semantics, or a word of an automaton.

data Trace (S : Session) : Set where
  [] : (Trace S)
  [✓] : {isI : IsI S} → (Trace S)
  _∷_ : (a : Γ S) → (as : Trace (S / a)) → (Trace S)

-- Traces ending in [] at type I are completed traces

data ✓ {S : Session} : (Trace S) → Set where
  [✓] : {isI : IsI S} → ✓ ([✓] {S} {isI})
  _∷_ : (a : Γ S) → ∀ {as} → (✓ as) → (✓ (a ∷ as))

-- Partial traces come with a prefix order.

data _⊑_ {S : Session} : (Trace S) → (Trace S) → Set where
  [] : ∀ {as} → ([] ⊑ as)
  _∷_ : ∀ a {as bs} → (as ⊑ bs) → (a ∷ as ⊑ a ∷ bs)

-- We can also provide types for partial traces which record the
-- source and target session.  There's two ways to build such traces:
-- either top-down, as paths from the root of a tree to a subtree:

data _≥_ : Session → Session → Set₁ where
  [] : ∀ {S} → (S ≥ S)
  _∷_ : ∀ {S T} a → (as : S / a ≥ T) → (S ≥ T)

-- or bottom-up, as paths from a subtree back to the root:

data _≤_ : Session → Session → Set₁ where
  [] : ∀ {S} → (S ≤ S)
  _∷_ : ∀ {S T} a → (as : S ≤ T) → (S / a ≤ T)

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
