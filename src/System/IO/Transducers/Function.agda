open import Coinduction using ( ♭ ; ♯_ )
open import Data.Unit using ( ⊤ ; tt )
open import System.IO.Transducers.Syntax 
  using ( lazy ; strict ; _⇒_is_ ; inp ; out ; done )
  renaming ( _⟫_ to _⟫'_ ; _[&]_ to _[&]'_ ; _⟨&⟩_ to _⟨&⟩'_ ;
    discard to discard' ; π₁ to π₁' ; π₂ to π₂' ;
    ⟦_⟧ to ⟦_⟧' )
open import System.IO.Transducers.Session using ( Session ; I ; Σ ; _&_ )
open import System.IO.Transducers.Trace using ( Trace )

module System.IO.Transducers.Function where

-- We can regard strict transducers as functions.
-- Note that in the case of S ⇒ T where S is a Σ session,
-- this agrees with the type of inp, so we can regard
-- inp as a function of type ∞ (S ⇒ T) → (S to T is s).

LHS : Session → Set
LHS I           = ⊤
LHS (Σ {A} V F) = A

RHS : (S T : Session) → (LHS S) → Set₁
RHS I       T a = I ⇒ T is strict
RHS (Σ V F) T a = ♭ F a ⇒ T is lazy

_⇛_ : Session → Session → Set₁
S ⇛ T = (a : LHS S) → (RHS S T a)

-- Map from functions to syntax and back.

φ : ∀ {S T} → (S ⇒ T is strict) → (S ⇛ T)
φ {I}     done    a = done
φ {Σ W F} (inp P) a = ♭ P a
φ {Σ W F} done    a = out a done

φ' : ∀ {S T} → (S ⇛ T) → (S ⇒ T is strict)
φ' {I}     P = P tt
φ' {Σ W F} P = inp (♯ P)

-- Semantics of functions is inherited from semantics on syntax

⟦_⟧ : ∀ {S T} → (S ⇛ T) → (Trace S) → (Trace T)
⟦ P ⟧ = ⟦ φ' P ⟧'

-- Structure on functions is inherited from structure on syntax

id : ∀ {S} → (S ⇛ S)
id {S} = φ (done {S})

_⟫_ : ∀ {S T U} → (S ⇛ T) → (T ⇛ U) → (S ⇛ U)
_⟫_ {S} P Q = φ (φ' {S} P ⟫' φ' Q)

_[&]_ : ∀ {S T U V} → (S ⇛ T) → (U ⇛ V) → ((S & U) ⇛ (T & V))
_[&]_ {S} P Q = φ (φ' {S} P [&]' φ' Q)

_⟨&⟩_ : ∀ {S T U} → (S ⇛ T) → (S ⇛ U) → (S ⇛ (T & U))
_⟨&⟩_ {S} P Q = φ (φ' {S} P ⟨&⟩' φ' Q)

discard : ∀ {S} → (S ⇛ I)
discard {S} = φ (discard' {S})

π₁ : ∀ {S T} → ((S & T) ⇛ S)
π₁ {S} = φ (π₁' {S})

π₂ : ∀ {S T} → ((S & T) ⇛ T)
π₂ {S} = φ (π₂' {S})
