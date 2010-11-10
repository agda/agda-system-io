open import Coinduction using ( ∞ ; ♭ ; ♯_ )
open import Data.Bool using ( Bool ; true ; false )
open import Data.Empty using ( ⊥ ; ⊥-elim )
open import Data.Unit using ( ⊤ ; tt )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )
open import System.IO.Transducers.Lazy using ( _⇒_ ; inp ; out ; id ; choice ) renaming 
  ( done to done' ; ⟦_⟧ to ⟦_⟧' ; _⟫_ to _⟫'_ ; _[&]_ to _[&]'_ ; assoc to assoc'
  ; discard to discard' ; π₁ to π₁' ; π₂ to π₂' ; _⟨&⟩_ to _⟨&⟩'_ )
open import System.IO.Transducers.Session using ( Session ; I ; Σ ; Γ ; _/_ ; IsΣ ; ⟨_⟩ ; _&_ ; ¿ ; _⊕_ )
open import System.IO.Transducers.Trace using ( Trace ; [] ; _∷_ )

module System.IO.Transducers.Strict where

infixr 4 _⇛_
infixr 6 _⟫_
infixr 8 _[&]_ _⟨&⟩_ _⟨⊕⟩_

-- Strict tranducers are ones which perform input before any output

data Strict {S T : Session} : (S ⇒ T) → Set where
  inp : {isΣ : IsΣ S} → (P : ∞ ((a : Γ S) → (S / a ⇒ T))) → (Strict (inp {isΣ = isΣ} P))
  id : (S≡T : S ≡ T) → (Strict (id S≡T))

-- S ⇛ T is the type of strict transducers regarded as functions

_⇛_ : Session → Session → Set
I     ⇛ T = I ≡ T
Σ V F ⇛ T = ∀ a → (♭ F a) ⇒ T

-- Inclusion of strict in lazy transducers

ι : ∀ {S T} → (S ⇛ T) → (S ⇒ T)
ι {I}     refl = done'
ι {Σ V F} P    = inp (♯ P)

-- Identity

done : ∀ {S} → (S ⇛ S)
done {I}     = refl
done {Σ V F} = λ a → out a done'

-- Composition

_⟫_ : ∀ {S T U} → (S ⇛ T) → (T ⇛ U) → (S ⇛ U)
_⟫_ {I}     refl Q = Q
_⟫_ {Σ V F} P    Q = λ a → P a ⟫' ι Q

-- & on transducers

_[&]_ : ∀ {S T U V} → (S ⇛ T) → (U ⇛ V) → ((S & U) ⇛ (T & V))
_[&]_ {I}     refl Q = Q
_[&]_ {Σ V F} P    Q = λ a → P a [&]' ι Q

-- Associativity of &

assoc : ∀ {S T U} → ((S & (T & U)) ⇛ ((S & T) & U))
assoc {I}     {T} {U} = done {T & U}
assoc {Σ V F} {T} {U} = λ a → out a (assoc' {♭ F a})

-- The projection morphisms for [] and &:

discard : ∀ {S} → (S ⇛ I)
discard {I}     = done {I}
discard {Σ W F} = λ a → discard'

π₁ : ∀ {S T} → ((S & T) ⇛ S)
π₁ {I}     {T} = discard {T}
π₁ {Σ W F} {T} = λ a → out a π₁'

π₂ : ∀ {S T} → ((S & T) ⇛ T)
π₂ {I}     {T} = done {T}
π₂ {Σ W F} {T} = λ a → π₂' {♭ F a}

-- Mediating morphism for &

_⟨&⟩_ : ∀ {S T U} → (S ⇛ T) → (S ⇛ U) → (S ⇛ T & U)
_⟨&⟩_ {I}     refl Q = Q
_⟨&⟩_ {Σ W F} P    Q = λ a → P a ⟨&⟩' Q a

-- Natural transforms for & 

copy : ∀ {S} → (S ⇛ (S & S))
copy = done ⟨&⟩ done

swap : ∀ {S T} → ((S & T) ⇛ (T & S))
swap {S} = π₂ {S} ⟨&⟩ π₁ {S}

-- Strict coproduct structure.

κ₁ : ∀ {S T} → (S ⇛ S ⊕ T)
κ₁ {I}     {T}     = done 
κ₁ {Σ V F} {I}     = discard {Σ V F}
κ₁ {Σ V F} {Σ W G} = λ a → out true (out a done')

κ₂ : ∀ {S T} → (T ⇛ S ⊕ T)
κ₂ {I}     {T}     = discard
κ₂ {Σ V F} {I}     = done
κ₂ {Σ V F} {Σ W G} = λ b → out false (out b done')

_⟨⊕⟩_ : ∀ {S T U} → (S ⇛ U) → (T ⇛ U) → ((S ⊕ T) ⇛ U)
_⟨⊕⟩_ {I}             refl Q    = refl
_⟨⊕⟩_ {Σ V F} {I}     P    refl = refl
_⟨⊕⟩_ {Σ V F} {Σ W G} P    Q    = choice (inp (♯ P)) (inp (♯ Q))
