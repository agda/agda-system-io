open import Coinduction using ( ♭ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )
open import System.IO.Transducers.Lazy using ()
  renaming ( done to doneL ; _⟫_ to _⟫L_ )
open import System.IO.Transducers.Strict using ()
  renaming ( done to doneS ; _⟫_ to _⟫S_ )
open import System.IO.Transducers.Session using ( Session ; I ; Σ )
open import System.IO.Transducers.Trace using ( Trace )

module System.IO.Transducers where

open System.IO.Transducers.Lazy public
  using ( _⇒_ ; inp ; out ; id ; ⟦_⟧ ; _≃_ )

open System.IO.Transducers.Strict public
  using ( _⇛_ )

data Style : Set where
  lazy strict : Style

_⇒_is_ : Session → Session → Style → Set
S ⇒ T is lazy   = S ⇒ T
S ⇒ T is strict = S ⇛ T

done : ∀ {s S} → (S ⇒ S is s)
done {lazy}   = doneL
done {strict} = doneS

_⟫_ : ∀ {s S T U} → (S ⇒ T is s) → (T ⇒ U is s) → (S ⇒ U is s)
_⟫_ {lazy}   = _⟫L_
_⟫_ {strict} = _⟫S_
