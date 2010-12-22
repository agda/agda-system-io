open import Coinduction using ( ∞ ; ♭ ; ♯_ )
open import Data.Bool using ( Bool ; true ; false )
open import Data.Empty using ( ⊥ ; ⊥-elim )
open import Data.Unit using ( ⊤ ; tt )
open import System.IO.Transducers.Lazy using 
  ( _⇒_ ; inp ; out ; done ; choice ) renaming 
  ( ⟦_⟧ to ⟦_⟧' ; _⟫_ to _⟫'_
  ; _[&]_ to _[&]'_ ; _⟨&⟩_ to _⟨&⟩'_ ; assoc to assoc' )
open import System.IO.Transducers.Session using ( Session ; I ; Σ ; Γ ; _/_ ; IsΣ ; ⟨_⟩ ; _&_ ; ¿ ; _⊕_ )
open import System.IO.Transducers.Trace using ( Trace ; [] ; _∷_ )

module System.IO.Transducers.Strict where

infixr 4 _⇛_
infixr 6 _⟫_
infixr 8 _[&]_ _⟨&⟩_

-- Strict tranducers are ones which perform input before any output

data Strict : ∀ {S T} → (S ⇒ T) → Set₁ where
  inp : ∀ {A V F T} P → (Strict (inp {A} {V} {F} {T} P))
  done : ∀ {S} → (Strict (done {S}))

-- Slightly annoyingly, _≡_ has different cardinalities
-- in different versions of the standard library.
-- Until 1.4 of agda-stdlib is more widely distributed,
-- we define a specialized version of _≡_ here.

data _≡_ (S : Session) : Session → Set₁ where
  refl : S ≡ S

-- S ⇛ T is the type of strict transducers regarded as functions

_⇛_ : Session → Session → Set₁
I     ⇛ T = I ≡ T
Σ V F ⇛ T = ∀ a → (♭ F a) ⇒ T

-- Identity transducer

id : ∀ {S} → S ⇛ S
id {I}     = refl
id {Σ V F} = λ a → out a done

-- Inclusion of strict in lazy transducers

ι : ∀ {S T} → (S ⇛ T) → (S ⇒ T)
ι {I}     refl = done
ι {Σ V F} P    = inp (♯ P)

-- Composition

_⟫_ : ∀ {S T U} → (S ⇛ T) → (T ⇛ U) → (S ⇛ U)
_⟫_ {I}             refl refl = refl
_⟫_ {Σ V F} {I}     P    refl = P
_⟫_ {Σ V F} {Σ W G} P    Q    = λ a → (P a ⟫' ι Q)

-- & on transducers

_[&]_ : ∀ {S T U V} → (S ⇛ T) → (U ⇛ V) → ((S & U) ⇛ (T & V))
_[&]_ {I}     refl Q = Q
_[&]_ {Σ V F} P    Q = λ a → (P a [&]' ι Q)

-- Associativity of &

assoc : ∀ {S T U} → ((S & (T & U)) ⇛ ((S & T) & U))
assoc {I}     {T} {U} = id {T & U}
assoc {Σ V F} {T} {U} = λ a → out a (assoc' {♭ F a})

-- Mediating morphism for &

_⟨&⟩_ : ∀ {S T U} → (S ⇛ T) → (S ⇛ U) → (S ⇛ T & U)
_⟨&⟩_ {I}     refl refl = refl
_⟨&⟩_ {Σ V F} P    Q    = λ a → (P a ⟨&⟩' Q a)
