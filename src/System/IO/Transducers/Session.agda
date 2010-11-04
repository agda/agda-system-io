open import Coinduction using ( ∞ ; ♯_ ; ♭ )
open import Data.Bool using ( Bool ; true ; false ; if_then_else_ )
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

infixr 6 _⊕_
infixr 7 _&_ _&*_

-- Weighting for a set

Weighted : Set → Set
Weighted A = A → Natural

-- Discrete weighting function

δ : ∀ {A} → (Weighted A)
δ a = # 1

-- Sessions are trees of weighted sets

data Session : Set₁ where
  I : Session
  Σ : {A : Set} → (W : Weighted A) → (F : ∞ (A → Session)) → Session

-- Inital alphabet

Γ : Session → Set
Γ I           = ⊥
Γ (Σ {A} W F) = A

Δ : ∀ S → (Weighted (Γ S))
Δ I       ()
Δ (Σ W F) a = W a

_/_ : ∀ S → (Γ S) → Session
I       / ()
(Σ W F) / a = ♭ F a

-- Singletons

⟨_w/_⟩ : (A : Set) → (Weighted A) → Session
⟨ A w/ W ⟩ = Σ W (♯ λ a → I)

⟨_⟩ : Set → Session
⟨ A ⟩ = ⟨ A w/ δ ⟩

-- Sequencing

_&_ : Session → Session → Session
I       & T = T
(Σ W F) & T = Σ W (♯ λ a → ♭ F a & T)

-- Lazy choice

_+_ : Session → Session → Session
S + T = Σ δ (♯ λ b → if b then S else T)

-- Strict choice

_⊕_ : Session → Session → Session
I ⊕ T = I
S ⊕ I = I
S ⊕ T = S + T

-- Lazy option

¿ : Session → Session
¿ S = S + I

-- Lazy Kleene star

-- It would be nice if I could just define * S = ¿ (S & * S),
-- but that doesn't pass the termination checker, so I have
-- to expand out the definition.

hd : Session → Set
hd I           = Bool
hd (Σ {A} W F) = A

wt : ∀ S → (Weighted (hd S))
wt I       = δ
wt (Σ W F) = W

mutual

  tl : ∀ S T → (hd S) → Session
  tl I       T true  = T &* T
  tl I       T false = I
  tl (Σ W F) T a     = (♭ F a) &* T

  _&*_ : Session → Session → Session
  S &* T = Σ (wt S) (♯ tl S T)

* : Session → Session
* S = I &* S

+ : Session → Session
+ S = S &* S

-- Bytes

Bytes' : Session
Bytes' = + ⟨ ByteString strict w/ length ⟩

Bytes : Session
Bytes = * ⟨ ByteString strict w/ length ⟩

-- TODO: weight strings by their length?

Strings' : Session
Strings' = + ⟨ String ⟩

Strings : Session
Strings = * ⟨ String ⟩
