open import Coinduction using ( ∞ ; ♭ ; ♯_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; _≢_ ; refl )
open import Relation.Nullary using ( Dec ; yes ; no )
open import System.IO.Transducers.Session using ( Session ; I ; Σ ; Γ ; _/_ ; IsI )

module System.IO.Transducers.Trace where

infixr 4 _≤_ _⊑_ _⊨_⊑_ _⊨_✓ _✓
infixr 5 _∷_ _++_

-- The semantics of a session is its set of traces.
-- The name "trace" comes from process algebra,
-- it's called a play in games semantics, or a word of an automaton.

data Trace (S : Session) : Set where
  [] : Trace S
  _∷_ : (a : Γ S) (as : Trace (S / a)) → (Trace S)

-- Traces ending in [] at type I are completed traces

data _⊨_✓ : ∀ S → (Trace S) → Set₁ where
  [] : I ⊨ [] ✓
  _∷_ : ∀ {S} a {as} → (S / a ⊨ as ✓) → (S ⊨ a ∷ as ✓)

_✓ : ∀ {S} → (Trace S) → Set₁
_✓ {S} as = S ⊨ as ✓

-- Prefix order on traces

data _⊨_⊑_ : ∀ S → (Trace S) → (Trace S) → Set₁ where
  [] : ∀ {S as} → (S ⊨ [] ⊑ as)
  _∷_ : ∀ {S} a {as bs} → (S / a ⊨ as ⊑ bs) → (S ⊨ a ∷ as ⊑ a ∷ bs)

_⊑_ : ∀ {S} → (Trace S) → (Trace S) → Set₁
_⊑_ {S} as bs = S ⊨ as ⊑ bs

-- For building buffers, it is useful to provide
-- snoc traces as well as cons traces.

data _≤_ : Session → Session → Set₁ where
  [] : ∀ {S} → (S ≤ S)
  _∷_ : ∀ {S T} a (as : S ≤ T) → (S / a ≤ T)

-- Snoc traces form categories, where composition is concatenation.

_++_ : ∀ {S T U} → (S ≤ T) → (T ≤ U) → (S ≤ U)
[]       ++ bs = bs
(a ∷ as) ++ bs = a ∷ (as ++ bs)

-- snoc traces can be reversed to form cons traces

revApp : ∀ {S T} → (S ≤ T) → (Trace S) → (Trace T)
revApp []       bs = bs
revApp (a ∷ as) bs = revApp as (a ∷ bs)

reverse : ∀ {S T} → (S ≤ T) → (Trace T)
reverse as = revApp as []
