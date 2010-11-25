open import Coinduction using ( ∞ ; ♭ ; ♯_ )
open import Data.Bool using ( Bool ; true ; false )
open import Data.Empty using ( ⊥ ; ⊥-elim )
open import Data.Unit using ( ⊤ ; tt )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )
open import System.IO.Transducers.Lazy using 
  ( _⇒_ ; inp ; out ; id ; choice ) renaming 
  ( done to done' ; ⟦_⟧ to ⟦_⟧' ; _⟫_ to _⟫'_
  ; _[&]_ to _[&]'_ ; _⟨&⟩_ to _⟨&⟩'_ ; assoc to assoc' )
open import System.IO.Transducers.Session using ( Session ; I ; Σ ; Γ ; _/_ ; IsΣ ; ⟨_⟩ ; _&_ ; ¿ ; _⊕_ )
open import System.IO.Transducers.Trace using ( Trace ; [] ; _∷_ )

module System.IO.Transducers.Strict where

infixr 4 _⇛_
infixr 6 _⟫_
infixr 8 _[&]_ _⟨&⟩_

-- Strict tranducers are ones which perform input before any output

data Strict {S T : Session} : (S ⇒ T) → Set where
  inp : {ΣS : IsΣ S} → (P : ∞ (∀ a → (S / a ⇒ T))) → {ΣT : IsΣ T} → (Strict (inp {S} {T} {ΣS} P {ΣT}))
  id : (S≡T : S ≡ T) → (Strict (id S≡T))

-- S ⇛ T is the type of strict transducers regarded as functions

_⇛_ : Session → Session → Set
I     ⇛ T = I ≡ T
S     ⇛ I = I ≡ S
Σ V F ⇛ T = ∀ a → (♭ F a) ⇒ T

-- Inclusion of strict in lazy transducers

ι : ∀ {S T} → (S ⇛ T) → (S ⇒ T)
ι {I}             refl = done'
ι {Σ V F} {Σ W G} P    = inp (♯ P)
ι {Σ V F} {I}     ()

-- Identity

done : ∀ {S} → (S ⇛ S)
done {I}     = refl
done {Σ V F} = λ a → out a done'

-- Composition

_⟫_ : ∀ {S T U} → (S ⇛ T) → (T ⇛ U) → (S ⇛ U)
_⟫_ {I}                     refl refl = refl
_⟫_ {Σ V F} {Σ W G} {Σ X H} P    Q    = λ a → P a ⟫' ι Q
_⟫_ {Σ V F} {I}             ()   Q
_⟫_ {Σ V F} {Σ W G} {I}     P    ()

-- & on transducers

_[&]_ : ∀ {S T U V} → (S ⇛ T) → (U ⇛ V) → ((S & U) ⇛ (T & V))
_[&]_ {I}             refl Q = Q
_[&]_ {Σ V F} {Σ W G} P    Q = λ a → P a [&]' ι Q
_[&]_ {Σ V F} {I}     ()   Q

-- Associativity of &

assoc : ∀ {S T U} → ((S & (T & U)) ⇛ ((S & T) & U))
assoc {I}     {T} {U} = done {T & U}
assoc {Σ V F} {T} {U} = λ a → out a (assoc' {♭ F a})

-- Mediating morphism for &

_⟨&⟩_ : ∀ {S T U} → (S ⇛ T) → (S ⇛ U) → (S ⇛ T & U)
_⟨&⟩_ {I}                     refl refl = refl
_⟨&⟩_ {Σ V F} {Σ W G} {Σ X H} P    Q    = λ a → P a ⟨&⟩' Q a
_⟨&⟩_ {Σ V F} {I}             ()   Q
_⟨&⟩_ {Σ V F} {Σ W G} {I}     P    ()
