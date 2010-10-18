open import Coinduction using ( ∞ ; ♯_ ; ♭ )
open import Data.Empty using ( ⊥ )
open import Data.Maybe using ( Maybe ; just ; nothing )
open import Data.Sum using ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Unit using ( ⊤ )
open import Level using ( Level )

module System.IO.Transducers.Session where

-- Unidirectional sessions.  These can be viewed as trees,
-- where each node is labelled by a set A, and has a child
-- for each element of A.

-- These are a lot like session types, but are unidirectional,
-- not bidirectional, and are not designed to support session
-- mobility.

-- They are also a lot like arenas in game semantics, but again
-- are unidirectional.

-- Finally, they are a lot like automata: states are sessions,
-- acceptors are leaves, transitions correspond to children.

infixl 5 _/_
infixr 6 _⊕_
infixr 7 _&_ _&¡_

data Session : Set₁ where
  [] : Session
  _∷_ : (A : Set) → (Ss : ∞ (A → Session)) → Session

-- Inital alphabet

-- Pessimistic version which treats Σ [] as ⊥

Σ : Session → Set
Σ []       = ⊥
Σ (A ∷ Ss) = A

_/_ : ∀ S → (Σ S) → Session
[] / ()
(A ∷ Ss) / a = ♭ Ss a

-- Optimistic version which treats Σ' [] as ⊤

Σ' : Session → Set
Σ' []       = ⊤
Σ' (A ∷ Ss) = A

_/'_ : ∀ S → (Σ' S) → Session
[]       /' _ = []
(A ∷ Ss) /' a = (♭ Ss a)

-- Singletons

⟨_⟩ : Set → Session
⟨ A ⟩ = A ∷ (♯ λ a → [])

-- Sequencing

_&_ : Session → Session → Session
[]       & T = T
(A ∷ Ss) & T = A ∷ (♯ λ a → ♭ Ss a & T)

-- Option

opt : ∀ S → (Maybe (Σ' S)) → Session
opt S (just a)  = (S /' a)
opt S (nothing) = []

¿ : Session → Session
¿ S = (Maybe (Σ' S)) ∷ (♯ opt S)

-- Choice

choice : ∀ S T → (Σ' S ⊎ Σ' T) → Session
choice S T (inj₁ a) = S /' a
choice S T (inj₂ b) = T /' b

_⊕_ : Session → Session → Session
S ⊕ T = (Σ' S ⊎ Σ' T) ∷ (♯ choice S T)

-- Kleene star

-- It would be nice if I could just define ¡ S = ¿ (S & ¡ S),
-- but that doesn't pass the termination checker, so I have
-- to expand out the definition.

mutual

  _&¡_ : Session → Session → Session
  []       &¡ T = ¡ T
  (A ∷ Ss) &¡ T = A ∷ (♯ λ a → ♭ Ss a &¡ T)

  many : ∀ S → (Maybe (Σ' S)) → Session
  many S (just a) = (S /' a) &¡ S
  many S nothing  = []

  ¡ : Session → Session
  ¡ S = (Maybe (Σ' S)) ∷ (♯ many S)