open import Coinduction using ( ∞ ; ♯_ ; ♭ )
open import Data.Empty using ( ⊥ )
open import Data.Maybe using ( Maybe ; just ; nothing )
open import Data.Sum using ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Unit using ( ⊤ )
open import Data.Natural using ( Natural ; # )
open import Data.String using ( String )
open import Data.ByteString using ( ByteString ; strict ; length )
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

-- They're a lot like the container types from Ghani, Hancock
-- and Pattison's "Continuous functions on final coalgebras".
-- Note that we are supporting weighted sets, similar to theirs,
-- in order to support induction over weights of input,
-- e.g. on bytestring input we can do induction over the length
-- of the bytestring.

-- Finally, they are a lot like automata: states are sessions,
-- acceptors are leaves, transitions correspond to children.

infixl 5 _/_
infixr 6 _⊕_
infixr 7 _&_ _&¡_

-- Weighting for a set

Weighted : Set → Set
Weighted A = A → Natural

-- Sessions are trees of weighted sets

data Session : Set₁ where
  [] : Session
  _∷_ : {A : Set} → (W : Weighted A) → (Ss : ∞ (A → Session)) → Session

-- Domain of a weighting function

dom : ∀ {A} → (Weighted A) → Set
dom {A} W = A

-- Discrete weighting function

discrete : ∀ {A} → (Weighted A)
discrete a = # 1

-- Optional weighting function

⟨Maybe⟩ : ∀ {A} → (Weighted A) → (Weighted (Maybe A))
⟨Maybe⟩ W (just a) = W a
⟨Maybe⟩ W nothing  = # 1

-- Choice weighting function

_⟨⊎⟩_ : ∀ {A B} → (Weighted A) → (Weighted B) → (Weighted (A ⊎ B))
(V ⟨⊎⟩ W) (inj₁ a) = V a
(V ⟨⊎⟩ W) (inj₂ b) = W b

-- Inital alphabet

Σ : Session → Set
Σ []       = ⊥
Σ (A ∷ Ss) = dom A

Δ : ∀ S → (Weighted (Σ S))
Δ []       ()
Δ (W ∷ Ss) a = W a

_/_ : ∀ S → (Σ S) → Session
[] / ()
(W ∷ Ss) / a = ♭ Ss a

-- Singletons

⟨_w/_⟩ : (A : Set) → (Weighted A) → Session
⟨ A w/ W ⟩ = W ∷ (♯ λ a → [])

⟨_⟩ : Set → Session
⟨ A ⟩ = ⟨ A w/ discrete ⟩

-- Sequencing

_&_ : Session → Session → Session
[]       & T = T
(W ∷ Ss) & T = W ∷ (♯ λ a → ♭ Ss a & T)

-- Ensure an initial action

lift : Session → Session
lift []       = ⟨ ⊤ ⟩
lift (W ∷ Ss) = W ∷ Ss

-- Option

opt : ∀ S → (Maybe (Σ S)) → Session
opt S (just a)  = (S / a)
opt S (nothing) = []

¿ : Session → Session
¿ S = (⟨Maybe⟩ (Δ (lift S))) ∷ (♯ opt (lift S))

-- Choice

choice : ∀ S T → (Σ S ⊎ Σ T) → Session
choice S T (inj₁ a) = S / a
choice S T (inj₂ b) = T / b

_⊕_ : Session → Session → Session
S ⊕ T = (Δ (lift S) ⟨⊎⟩ Δ (lift T)) ∷ (♯ choice (lift S) (lift T))

-- Kleene star

-- It would be nice if I could just define ¡ S = ¿ (S & ¡ S),
-- but that doesn't pass the termination checker, so I have
-- to expand out the definition.
 
mutual

  _&¡_ : Session → Session → Session
  []       &¡ T = ¡ T
  (W ∷ Ss) &¡ T = W ∷ (♯ λ a → ♭ Ss a &¡ T)

  many : ∀ S T → (Maybe (Σ S)) → Session
  many S T (just a) = (S / a) &¡ T
  many S T nothing  = []

  ¡ : Session → Session
  ¡ S = (⟨Maybe⟩ (Δ (lift S))) ∷ (♯ many (lift S) S)

-- Variant of Kleene star that only admits streams, not lists.
-- Note that this type has no completed traces, only partial
-- traces (which are isomorphic to partial lists).

mutual

  _&ω_ : Session → Session → Session
  []       &ω T = ω T
  (W ∷ Ss) &ω T = W ∷ (♯ λ a → ♭ Ss a &ω T)

  inf : ∀ S T → (Σ S) → Session
  inf S T a = (S / a) &ω T

  ω : Session → Session
  ω S = (Δ (lift S)) ∷ (♯ inf (lift S) S)

-- Bytes

Bytes : Session
Bytes = ¡ ⟨ ByteString strict w/ length ⟩

-- TODO: weight strings by their length?

Strings : Session
Strings = ¡ ⟨ String ⟩
