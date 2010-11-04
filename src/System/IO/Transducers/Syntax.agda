open import Coinduction using ( ∞ ; ♭ ; ♯_ )
open import Data.Empty using ( ⊥ )
open import Data.Bool using ( Bool ; true ; false ; if_then_else_ )
open import Data.Product using ( ∃ ; _×_ ; _,_ ; ,_ )
open import Data.Strict using ( Strict ; ! )
open import Data.Sum using ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Unit using ( ⊤ ; tt )
open import System.IO.Transducers.Session using ( Weighted ; Session ; I ; Σ ; Γ ; ⟨_⟩ ; _&_ ; ¿ ; _+_ ; _⊕_ ; _&*_ ; * )
open import System.IO.Transducers.Trace using ( _≥_ ; _≤_ ; Trace ; _⊑_ ; [] ; _∷_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ )

module System.IO.Transducers.Syntax where

-- As ⇛ Bs is the type of transducers whose inputs
-- are traces through As, and whose output are traces through Bs.

-- Note that input is coinductive, but output is inductive,
-- which guarantees that transducers will map finite traces
-- to finite traces.

-- The name transducer comes from automata theory -- these
-- are essentially I/O automata, or strategies in a two-player 
-- game without the move alternation restriction.

infixr 4 _⇒_is_ _⇒_ _≃_ _≲_ 
infixr 6 _⟫_

-- Transducers are parameterized on how strict they are:
-- strict transducers are required to produce empty output on empty input.

data Strictness : Set where
  strict lazy : Strictness

data _⇒_is_ : Session → Session → Strictness → Set₁ where
  inp : ∀ {A F T V s} → ∞ ((a : A) → (♭ F a ⇒ T is lazy)) → (Σ V F ⇒ T is s)
  out : ∀ {S B G W} → (b : B) → (S ⇒ ♭ G b is lazy) → (S ⇒ Σ W G is lazy)
  done : ∀ {S s} → (S ⇒ S is s)

-- Default strictness is lazy

_⇒_ : Session → Session → Set₁
S ⇒ T = S ⇒ T is lazy

-- Inclusion of strict transducers to lazy transducers

ι : ∀ {s S T} → (S ⇒ T is s) → (S ⇒ T is lazy)
ι (inp P)   = inp P
ι (out b P) = out b P
ι done      = done

-- Helper function to output a whole trace.

out* : ∀ {S T U} → (T ≤ U) → (S ⇒ T is lazy) → (S ⇒ U is lazy)
out* []       P = P
out* (b ∷ bs) P = out* bs (out b P)

-- Semantics as a function from partial traces to partial traces

mutual

  ⟦_⟧ : ∀ {S T s} → (S ⇒ T is s) → (Trace S) → (Trace T)
  ⟦ inp P   ⟧ as = apply P as
  ⟦ out b P ⟧ as = b ∷ ⟦ P ⟧ as
  ⟦ done    ⟧ as = as

  -- We define apply as a separate function so that
  -- we have ⟦ inp {s = strict} P ⟧ as ≡ ⟦ inp {s = lazy} P ⟧ as
  -- without having to do a case analysis on as.

  apply : ∀ {A F T V} → ∞ ((a : A) → (♭ F a ⇒ T is lazy)) → 
    (Trace (Σ V F)) → (Trace T)
  apply P []       = []
  apply P (a ∷ as) = ⟦ ♭ P a ⟧ as

-- Extensional equivalence on trace functions

_≃_ : ∀ {S T} → (f g : Trace S → Trace T) → Set₁
f ≃ g = ∀ as → f as ≡ g as

-- Improvement order on trace functions

_≲_ : ∀ {S T} → (f g : Trace S → Trace T) → Set₁
f ≲ g = ∀ as → f as ⊑ g as

-- Transducers form a category with composition given by 
-- parallel (data flow) composition.  This is defined by the
-- usual expansion laws for parallel composition, together with
-- the unit law for done.  Since composition is deterministic,
-- we prioritize output over input.

_⟫_ : ∀ {S T U s} → (S ⇒ T is s) → (T ⇒ U is s) → (S ⇒ U is s)
done    ⟫ Q       = Q
P       ⟫ done    = P
P       ⟫ out b Q = out b (P ⟫ Q)
out b P ⟫ inp Q   = P ⟫ ♭ Q b
inp P   ⟫ inp Q   = inp (♯ λ a → ♭ P a ⟫ inp Q)

-- The category has monoidal structure given by &, with
-- action on morphisms:
 
_[&]_ : ∀ {S T U V s} → (S ⇒ T is s) → (U ⇒ V is s) → ((S & U) ⇒ (T & V) is s)
inp P          [&] Q = inp (♯ λ a → ♭ P a [&] ι Q)
out b P        [&] Q = out b (P [&] Q)
(done {I})     [&] Q = Q
(done {Σ V F}) [&] Q = inp (♯ λ a → out a (done {♭ F a} [&] ι Q))

-- Associativity of &

assoc : ∀ {S T U s} → ((S & (T & U)) ⇒ ((S & T) & U) is s)
assoc {I}     = done
assoc {Σ V F} = inp (♯ λ a → out a (assoc {♭ F a}))

-- The projection morphisms for [] and &:

discard : ∀ {S s} → (S ⇒ I is s)
discard {I}     = done
discard {Σ W F} = inp (♯ λ a → discard)

π₁ : ∀ {S T s} → ((S & T) ⇒ S is s)
π₁ {I}     = discard
π₁ {Σ W F} = inp (♯ λ a → out a π₁)

π₂ : ∀ {S T s} → ((S & T) ⇒ T is s)
π₂ {I}     = done
π₂ {Σ W F} = inp (♯ λ a → π₂ {♭ F a})

-- The category is almost cartesian, at the cost of
-- buffering.  WARNING.  BUFFERING.  This is bad.  Do not do this.

-- The "almost" is due to a failure of the projection properties:
-- P ⟨&⟩ Q ⟫ π₂ is not equivalent to Q, since Q may do output immediately,
-- and P ⟨&⟩ Q ⟫ π₂ can only output after it has consumed all its input.
-- Similarly π₁ ⟨&⟩ π₂ is not equivalent to done, as π₂'s output will
-- be bufferred.

-- This implementation uses output buffering, hopefully output
-- is usually smaller than input.

_⟨&⟩[_]_ : ∀ {S T U V} → (S ⇒ T is lazy) → (U ≤ V) → (S ⇒ U is lazy) → (S ⇒ T & V is lazy)
inp P        ⟨&⟩[ cs ] inp Q   = inp (♯ λ a → ♭ P a ⟨&⟩[ cs ] ♭ Q a)
inp P        ⟨&⟩[ cs ] out c Q = inp P ⟨&⟩[ c ∷ cs ] Q
inp P        ⟨&⟩[ cs ] done    = inp (♯ λ a → ♭ P a ⟨&⟩[ a ∷ cs ] done)
out b P      ⟨&⟩[ cs ] Q       = out b (P ⟨&⟩[ cs ] Q)
done {I}     ⟨&⟩[ cs ] Q       = out* cs Q
done {Σ W F} ⟨&⟩[ cs ] inp Q   = inp (♯ λ a → out a (done ⟨&⟩[ cs ] ♭ Q a))
done {Σ W F} ⟨&⟩[ cs ] out c Q = done ⟨&⟩[ c ∷ cs ] Q
done {Σ W F} ⟨&⟩[ cs ] done    = inp (♯ λ c → out c (done ⟨&⟩[ c ∷ cs ] done))

_⟨&⟩_ : ∀ {S T U s} → (S ⇒ T is s) → (S ⇒ U is s) → (S ⇒ T & U is s)
inp P        ⟨&⟩ inp Q   = inp (♯ λ a → ♭ P a ⟨&⟩ ♭ Q a)
inp P        ⟨&⟩ out c Q = inp P ⟨&⟩[ c ∷ [] ] Q
inp P        ⟨&⟩ done    = inp (♯ λ a → ♭ P a ⟨&⟩[ a ∷ [] ] done)
out b P      ⟨&⟩ Q       = out b (P ⟨&⟩ Q)
done {I}     ⟨&⟩ Q       = Q
done {Σ W F} ⟨&⟩ inp Q   = inp (♯ λ a → out a (done ⟨&⟩ ♭ Q a))
done {Σ W F} ⟨&⟩ out c Q = done ⟨&⟩[ c ∷ [] ] Q
done {Σ W F} ⟨&⟩ done    = inp (♯ λ c → out c (done ⟨&⟩[ c ∷ [] {Σ W F} ] done))

-- If you want input buffering, you can implement it using copy and _[&]_.

copy : ∀ {S s} → (S ⇒ (S & S) is s)
copy = done ⟨&⟩ done

swap : ∀ {S T s} → ((S & T) ⇒ (T & S) is s)
swap {S} = π₂ {S} ⟨&⟩ π₁ {S}

-- Lazy coproduct structure.

ι₁ : ∀ {S T} → (S ⇒ S + T is lazy)
ι₁ = out true done

ι₂ : ∀ {S T} → (T ⇒ S + T is lazy)
ι₂ = out false done

choice : ∀ {S T U} → (S ⇒ U is lazy) → (T ⇒ U is lazy) → 
  ∀ b → ((if b then S else T) ⇒ U is lazy)
choice P Q true  = P
choice P Q false = Q

_⟨+⟩_ : ∀ {S T U s} → (S ⇒ U is lazy) → (T ⇒ U is lazy) → ((S + T) ⇒ U is s)
P ⟨+⟩ Q = inp (♯ choice P Q)

-- Strict coproduct structure.

κ₁ : ∀ {S T} → (S ⇒ S ⊕ T is strict)
κ₁ {I}     {T}     = done
κ₁ {Σ V F} {I}     = discard
κ₁ {Σ V F} {Σ W G} = inp (♯ λ a → out true (out a done))

κ₂ : ∀ {S T} → (T ⇒ S ⊕ T is strict)
κ₂ {I}     {T}     = discard
κ₂ {Σ V F} {I}     = done
κ₂ {Σ V F} {Σ W G} = inp (♯ λ b → out false (out b done))

_⟨⊕⟩_ : ∀ {S T U} → (S ⇒ U is strict) → (T ⇒ U is strict) → ((S ⊕ T) ⇒ U is strict)
_⟨⊕⟩_ {I}     {T}     P Q = P
_⟨⊕⟩_ {Σ V F} {I}     P Q = Q
_⟨⊕⟩_ {Σ V F} {Σ W G} P Q = (ι P) ⟨+⟩ (ι Q)

-- Options.

some : ∀ {S} → (S ⇒ ¿ S is lazy)
some = ι₁

none : ∀ {S} → (I ⇒ ¿ S is lazy)
none = ι₂

_⟨¿⟩_ : ∀ {S T s} → (S ⇒ T is lazy) → (I ⇒ T is lazy) → (¿ S ⇒ T is s)
P ⟨¿⟩ Q = P ⟨+⟩ Q
