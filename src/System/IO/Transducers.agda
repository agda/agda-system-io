open import Coinduction using ( ∞ ; ♭ ; ♯_ )
open import Data.Maybe using ( Maybe ; just ; nothing ; maybe )
open import Data.Natural using ( Natural ; _+_ ; # )
open import Data.Product using ( ∃ ; _×_ ; _,_ ; ,_ )
open import Data.Strict using ( Strict ; ! )
open import Data.Sum using ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Unit using ( ⊤ ; tt )
open import System.IO.Transducers.Session using ( Weighted ; Session ; [] ; _∷_ ; Σ ; _/_ ; ⟨_⟩ ; _&_ ; lift ; opt ; ¿ ; choice ; _⊕_ ; _&¡_ ; many ; ¡ )
open import System.IO.Transducers.Trace using ( _≥_ ; _≤_ ; Trace ; [] ; _∷_ ; _▷_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ )

module System.IO.Transducers where

-- As ⇒ Bs is the type of transducers whose inputs
-- are traces through As, and whose output are traces through Bs.

-- Note that input is coinductive, but output is inductive,
-- which guarantees that transducers will map finite traces
-- to finite traces.

-- The name transducer comes from automata theory -- these
-- are essentially I/O automata, or strategies in a two-player 
-- game without the move alternation restriction.

infixr 4 _⇒_ Inp_⇒_
infixr 6 _⟫_

data _⇒_ : Session → Session → Set₁ where
  inp : ∀ {A Ss T} → {V : Weighted A} → ∞ ((a : A) → (♭ Ss a ⇒ T)) → (V ∷ Ss ⇒ T)
  out : ∀ {B S Ts} → {W : Weighted B} → (b : B) → (S ⇒ ♭ Ts b) → (S ⇒ W ∷ Ts)
  done : ∀ {S} → (S ⇒ S)

-- Input transducer function type

data ⊥₁ : Set₁ where

Inp_⇒_ : Session → Session → Set₁
Inp []       ⇒ T = ⊥₁
Inp (V ∷ Ss) ⇒ T = ∀ a → (♭ Ss a ⇒ T)

-- Helper functions to output a whole trace.

out* : ∀ {S T T'} → (T ≥ T') → (S ⇒ T') → (S ⇒ T)
out* []       P = P
out* (b ∷ bs) P = out b (out* bs P)

out*' : ∀ {S T T'} → (T' ≤ T) → (S ⇒ T') → (S ⇒ T)
out*' []       P = P
out*' (b ∷ bs) P = out*' bs (out b P)

-- Operational semantics.

S⟦_⟧ : ∀ {S T} → (S ⇒ T) → ∀ {S'} → (S ≥ S') → (∃ λ T' → (S' ⇒ T') × (T ≥ T'))
S⟦ inp F   ⟧ []                  = (_ , inp F , [])
S⟦ inp F   ⟧ (a ∷ as)            = S⟦ ♭ F a ⟧ as
S⟦ out b P ⟧ as with S⟦ P ⟧ as
S⟦ out b P ⟧ as | (T' , P' , bs) = (T' , P' , b ▷ bs)
S⟦ done    ⟧ as                  = (_ , done , as)

-- Semantics on incomplete traces

I⟦_⟧ : ∀ {S T} → (S ⇒ T) → (Trace S) → (Trace T)
I⟦ inp F   ⟧ []             = []
I⟦ inp F   ⟧ (a ∷ as)       = I⟦ ♭ F a ⟧ as
I⟦ out b P ⟧ as             = b ∷ I⟦ P ⟧ as
I⟦ done    ⟧ as             = as

-- Transducer equivalence is defined extensionally, over
-- possibly incomplete traces.

_≃_ : ∀ {S T} → (S ⇒ T) → (S ⇒ T) → Set₁
P ≃ Q = ∀ as → I⟦ P ⟧ as ≡ I⟦ Q ⟧ as

-- Transducers map completed traces to completed traces.

C⟦_⟧ : ∀ {S T} → (S ⇒ T) → (S ≥ []) → (T ≥ [])
C⟦ inp F   ⟧ (a ∷ as) = C⟦ ♭ F a ⟧ as
C⟦ out b P ⟧ as       = b ▷ C⟦ P ⟧ as
C⟦ done    ⟧ as       = as

-- Transducers form a category with composition given by 
-- parallel (data flow) composition.  This is defined by the
-- usual expansion laws for parallel composition, together with
-- the unit law for done.  Since composition is deterministic,
-- we prioritize output over input.

_⟫_ : ∀ {S T U} → (S ⇒ T) → (T ⇒ U) → (S ⇒ U)
P       ⟫ out c Q = out c (P ⟫ Q)
inp F   ⟫ Q       = inp (♯ λ a → ♭ F a ⟫ Q)
out b P ⟫ inp G   = P ⟫ ♭ G b
done    ⟫ Q       = Q
P       ⟫ done    = P

-- Apply a process to an argument:

_$_ : ∀ {S T} → (S ⇒ T) → (a : Σ S) → (S / a ⇒ T)
_$_ {[]}     P ()
_$_ {A ∷ As} P a = out a done ⟫ P

-- Delay a process:

delay : ∀ S → ∀ {T U} → (T ⇒ U) → (S & T ⇒ S & U)
delay []       P = P
delay (A ∷ Ss) P = inp (♯ λ a → out a (delay (♭ Ss a) P))

-- The category has premonoidal structure given by &, with
-- action on morphisms:
 
_[&]_ : ∀ {S T U V} → (S ⇒ T) → (U ⇒ V) → (S & U ⇒ T & V)
inp F   [&] Q    = inp (♯ λ a → ♭ F a [&] Q)
out b P [&] Q    = out b (P [&] Q)
_[&]_ {S} done Q = delay S Q

-- The projection morphisms for [] and &:

discard : ∀ {S} → (S ⇒ [])
discard {[]}     = done
discard {A ∷ Ss} = inp (♯ λ a → discard)

π₁ : ∀ {S T} → (S & T ⇒ S)
π₁ {[]}     = discard
π₁ {A ∷ Ss} = inp (♯ λ a → out a π₁)

π₂ : ∀ {S T} → (S & T ⇒ T)
π₂ {[]}     = done
π₂ {A ∷ Ss} = inp (♯ λ a → π₂ {♭ Ss a})

-- The category is almost cartesian, at the cost of
-- buffering.  WARNING.  BUFFERING.  This is bad.  Do not do this.

-- The "almost" is due to a failure of the projection properties:
-- P ⟨&⟩ Q ⟫ π₂ is not equivalent to Q, since Q may do output immediately,
-- and P ⟨&⟩ Q ⟫ π₂ can only output after it has consumed all its input.
-- Similarly π₁ ⟨&⟩ π₂ is not equivalent to done, as π₂'s output will
-- be bufferred.

-- This implementation uses output buffering, hopefully output
-- is usually smaller than input.

_⟨&⟩[_]_ : ∀ {S T U V} → (S ⇒ T) → (U ≤ V) → (S ⇒ U) → (S ⇒ T & V)
inp {T = []}     F ⟨&⟩[ cs ] Q       = out*' cs Q
inp {T = W ∷ Ts} F ⟨&⟩[ cs ] inp G   = inp (♯ λ a → ♭ F a ⟨&⟩[ cs ] ♭ G a)
inp {T = W ∷ Ts} F ⟨&⟩[ cs ] out c Q = inp F ⟨&⟩[ c ∷ cs ] Q
inp {T = W ∷ Ts} F ⟨&⟩[ cs ] done    = inp (♯ λ c → ♭ F c ⟨&⟩[ c ∷ cs ] done)
out b P            ⟨&⟩[ cs ] Q       = out b (P ⟨&⟩[ cs ] Q)
done {[]}          ⟨&⟩[ cs ] Q       = out*' cs Q
done {W ∷ Ts}      ⟨&⟩[ cs ] inp F   = inp (♯ λ a → out a (done ⟨&⟩[ cs ] ♭ F a))
done {W ∷ Ts}      ⟨&⟩[ cs ] out c Q = done ⟨&⟩[ c ∷ cs ] Q
done {W ∷ Ts}      ⟨&⟩[ cs ] done    = inp (♯ λ c → out c (done ⟨&⟩[ c ∷ cs ] done))

_⟨&⟩_ : ∀ {S T U} → (S ⇒ T) → (S ⇒ U) → (S ⇒ T & U)
P ⟨&⟩ Q = P ⟨&⟩[ [] ] Q

-- If you want input buffering, you can implement it using copy and _[&]_.

copy : ∀ {S} → (S ⇒ S & S)
copy = done ⟨&⟩ done

swap : ∀ {S T} → (S & T ⇒ T & S)
swap {S} = π₂ {S} ⟨&⟩ π₁ {S}

-- Lifting forms an embedding-projection pair
-- TODO: Formalize the "earlier output" partial order.

lower : ∀ {S} → (lift S ⇒ S)
lower {[]}     = inp (♯ λ _ → done)
lower {A ∷ Ss} = done

raise : ∀ {S} → (S ⇒ lift S)
raise {[]}     = out tt done
raise {A ∷ Ss} = done

[lift] : ∀ {S T} → (S ⇒ T) → (lift S ⇒ lift T)
[lift] P = lower ⟫ P ⟫ raise

⟨lift⟩ : ∀ {S T} → (S ⇒ T) → (lift S ⇒ T)
⟨lift⟩ P = lower ⟫ P

-- Coproduct structure.

κ₁ : ∀ {S T} → (S ⇒ S ⊕ T)
κ₁ {[]}     = out (inj₁ tt) done
κ₁ {A ∷ Ss} = inp (♯ λ a → out (inj₁ a) done)

κ₂ : ∀ {S T} → (S ⇒ T ⊕ S)
κ₂ {[]}     = out (inj₂ tt) done
κ₂ {A ∷ Ss} = inp (♯ λ a → out (inj₂ a) done)

choose : ∀ {S T U} → (S ⇒ U) → (T ⇒ U) → (a : Σ S ⊎ Σ T) → (choice S T a ⇒ U)
choose P Q (inj₁ a) = P $ a
choose P Q (inj₂ b) = Q $ b

_⟨⊕⟩_ : ∀ {S T U} → (S ⇒ U) → (T ⇒ U) → (S ⊕ T ⇒ U)
P ⟨⊕⟩ Q = inp (♯ choose (⟨lift⟩ P) (⟨lift⟩ Q))

-- Specialization of coproducts to the case S ⊕ []

some : ∀ {S} → (S ⇒ ¿ S)
some {[]}     = out (just tt) done
some {A ∷ Ss} = inp (♯ λ a → out (just a) done)

none : ∀ {S} → ([] ⇒ ¿ S)
none = out nothing done

decide : ∀ {S T} → (S ⇒ T) → ([] ⇒ T) → (a : Maybe (Σ S)) → (opt S a ⇒ T)
decide P Q (just a) = P $ a
decide P Q nothing  = Q

_⟨¿⟩_ : ∀ {S T} → (S ⇒ T) → ([] ⇒ T) → (¿ S ⇒ T)
P ⟨¿⟩ Q = inp (♯ decide (⟨lift⟩ P) Q)

-- Weight of a trace

weight' : ∀ {S} → (Strict Natural) → S ⇒ ⟨ Natural ⟩
weight' {[]} (! n) = out n done
weight' {W ∷ Ss} (! n) = inp (♯ λ a → weight' (! (n + W a)))

weight : ∀ {S} → S ⇒ ⟨ Natural ⟩
weight = weight' (! (# 0))

-- Length of a list

mutual

  length'' : ∀ {T S} → (Strict Natural) → T &¡ S ⇒ ⟨ Natural ⟩
  length'' {[]}     {S} (! n) = inp (♯ length' {S} (! n))
  length'' {V ∷ Ts} {S} (! n) = inp (♯ λ x → length'' {♭ Ts x} {S} (! n))

  length' : ∀ {S} → (Strict Natural) → Inp ¡ S ⇒ ⟨ Natural ⟩
  length' {S} (! n) (just x) = length'' {lift S / x} {S} (! (n + # 1))
  length' {S} (! n) nothing  = out n done

length : ∀ {S} → (¡ S) ⇒ ⟨ Natural ⟩
length {S} = inp (♯ length' {S} (! (# 0)))

-- Flatten a list of lists

mutual

  concat''' : ∀ {T S} → (T &¡ S) &¡ ¡ S ⇒ T &¡ S
  concat''' {[]}     {S} = inp (♯ concat'' {S})
  concat''' {V ∷ Ts} {S} = inp (♯ λ x → out x (concat''' {♭ Ts x} {S}))

  concat'' : ∀ {S} → Inp ¡ S &¡ ¡ S ⇒ ¡ S
  concat'' {S} (just x) = out (just x) (concat''' {lift S / x} {S})
  concat'' {S} nothing  = inp (♯ concat' {S})

  concat' : ∀ {S} → Inp (¡ (¡ S)) ⇒ (¡ S)
  concat' {S} (just x) = concat'' {S} x
  concat' {S} nothing  = out nothing done

concat : ∀ {S}  → (¡ (¡ S)) ⇒ (¡ S)
concat {S} = inp (♯ concat' {S})

-- Some inclusions, which coerce traces from one session to another.

-- TODO: Add more inclusions.
-- TODO: Prove that these are monomorphisms.
-- TODO: It would be nice if inclusions like this could be handled by subtyping.

S⊆S&¡T : ∀ {S T} → (S ⇒ S &¡ T)
S⊆S&¡T {[]}     = out nothing done
S⊆S&¡T {A ∷ As} = inp (♯ λ a → out a S⊆S&¡T)

optS⊆manyST : ∀ {S T} → (a : Maybe (Σ S)) → (opt S a ⇒ many S T a)
optS⊆manyST (just a) = S⊆S&¡T
optS⊆manyST nothing  = done

¿S⊆¡S : {S : Session} → (¿ S ⇒ ¡ S)
¿S⊆¡S {S} = inp (♯ λ a → out a (optS⊆manyST {lift S} a))
