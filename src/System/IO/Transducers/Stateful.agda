open import Coinduction using ( ∞ ; ♭ ; ♯_ )
open import Data.Bool using ( Bool ; true ; false )
open import Data.Nat using ( ℕ ; zero ; suc )
open import Data.Natural using ( Natural ; # ; % ; _+_ )
open import Data.Strict using ( Strict ; ! )
open import System.IO.Transducers.List using ( S⊆S&*T )
open import System.IO.Transducers.Syntax using ( _⇒_ ; inp ; out ; done ; out* ; _[&]_ ; _⟫_ )
open import System.IO.Transducers.Session using ( I ; Σ ; ⟨_⟩ ; _&_ ; ¿ ; * ; _&*_ )
open import System.IO.Transducers.Trace using ( [] ; _∷_ ; _≤_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )

module System.IO.Transducers.Stateful where

-- We apply the usual state transformer construction
-- for a premonoial category: morphisms
-- from T to U with state S are just regular morphisms
-- from T & S to U & S.

-- We are particularly interested in the case where T is []
-- and S is Bytes, since this collapses to Bytes ⇒ U & Bytes,
-- that is, the type for a parser over a byte stream.
 
-- The type Bytes ⇒ U & Bytes (or more generally * ⟨ B ⟩ ⇒ U & * ⟨ B ⟩)
-- is the type of an iteratee returning U.

-- Lookahead.

-- Lookahead buffers up all input until some output is produced.
-- If the output is (just x), then we discard the buffer, and
-- continue with the process.  If the output is nothing, then we
-- return the buffer to the output stream and discard the process.

lookahead¿' : ∀ {T S S'} → (S' ≤ S) → (S' ⇒ ¿ T & S) → (S' ⇒ ¿ T & S)
lookahead¿' {T} as (inp F) = inp (♯ λ a → lookahead¿' {T} (a ∷ as) (♭ F a))
lookahead¿' {T} as (out true P) = out true P
lookahead¿' {T} as (out false P) = out false (out* as done)
lookahead¿' {T} as (done) = inp (♯ λ a → lookahead¿' {T} (a ∷ as) (out a done))

lookahead¿ : ∀ {T S} → (S ⇒ ¿ T & S) → (S ⇒ ¿ T & S)
lookahead¿ {T} = lookahead¿' {T} []

lookahead*' : ∀ {T S S'} → (S' ≤ S) → (S' ⇒ * T & S) → (S' ⇒ * T & S)
lookahead*' {T} as (inp F) = inp (♯ λ a → lookahead*' {T} (a ∷ as) (♭ F a))
lookahead*' {T} as (out true P) = out true P
lookahead*' {T} as (out false P) = out false (out* as done)
lookahead*' {T} as (done) = inp (♯ λ a → lookahead*' {T} (a ∷ as) (out a done))

lookahead* : ∀ {T S} → (S ⇒ * T & S) → (S ⇒ * T & S)
lookahead* {T} = lookahead*' {T} []

-- Iteration structure.

-- Deep breath.

-- This is the trickiest bit of building a stateful transducer
-- library.  The idea is to turn a stateful transducer generating
-- an optional U into a stateful transducer generating many Us.
-- We transform the transducer P into one which runs P, then
-- if P returns nothing, then loop P returns nothing and terminates, and
-- if P returns (just x), then loop P finishes running P, then runs loop P again.

-- For example, given a function nat? : ℤ → (Maybe ℕ) which
-- such that nat? n = nothing if n < 0 and just n otherwise,
-- we can define:

--  loop (lookahead (inp (♯ λ n → out (nat? n) done))) : 
--    * ⟨ ℤ ⟩ ⇒ * ⟨ ℕ ⟩ & * ⟨ ℤ ⟩

-- This transducer will return the longest non-negative prefix
-- of its input, for example on input just 2 ∷ just 5 ∷ just -3 ∷ ...
-- it will produce output just 2 ∷ just 5 ∷ nothing ∷ just -3 ∷ ...

mutual
 
  -- This is a remarkably obscure piece of code, given that all its doing is wiring...

  -- The n : ℕ parameter is the induction scheme that gets it all to pass the 
  -- termination checker.  When loop P is used properly, it is with a contracting
  -- P, that is one which produces stricly fewer S tokens than it consumes.
  -- Without the n parameter, loop P could produce infinite output if P isn't
  -- contracting.  For example loop (out (just x) done) would just produce the stream
  -- (just x) ∷ (just x) ∷ ... without ever consuming any input.  With the n parameter
  -- we keep track of how many tokens have been consumed.  If we ever hit
  -- a loop where n==0, we just run P one last time, then terminate.
  -- For example, loop (out (just x) done) just produces the trace (just x) ∷ [].

  -- For efficiency, we also pass n around as a Natural, not just an ℕ.  When we
  -- read input a, we add the weight of a onto n, strictly (in order to
  -- avoid potentially keeping a live), discard the previous ℕ and build a new ℕ.
  -- It would be nice to have an induction scheme for Natural.

  -- It would be a bit nicer to track statically which processes are contractions,
  -- and only allow loop P on contraction maps.

  -- Note that contractions come up in many contexts with treatments of recursion,
  -- for example in Plotkin uniformity, they're called strict maps.  They're
  -- closely related to the notion of guarded recursion which is used in checking
  -- productivity of coinductive functions in Agda.

  -- TODO: Find a way to statically enforce contraction and non-expansion maps.
  --   Or alternatively, give in and allow coinductive output,
  --   and hence lose termination for transducers.
  -- TODO: Present this as a trace structure?  Show that
  --   it has the expected properties on contracting morphisms.
 
  -- loop''' 0 P Q R is equivant to P ⟫ Q ⟫ (done ⟨&⟩ loop R)

  loop'''' : ∀ {T T' U S S'} → (Strict Natural) → (U ⇒ S) → (S ⇒ T' & S') → (S' ⇒ ¿ T & S') → (U ⇒ (T' &* T) & S')
  loop'''' {T} {T'} (! n) P Q R = loop''' {T} {T'} (% n) n P Q R

  loop''' : ∀ {T T' U S S'} → ℕ → Natural → (U ⇒ S) → (S ⇒ T' & S') → (S' ⇒ ¿ T & S') → (U ⇒ (T' &* T) & S')
  loop''' {T} {I}             m n P           Q         R = loop' {T} m n (P ⟫ Q) R R
  loop''' {T} {Σ V F} {Σ W G} m n (inp P)     (inp Q)   R = inp (♯ λ a → loop'''' {T} {Σ V F} (! (n + W a)) (♭ P a) (inp Q) R)
  loop''' {T} {Σ V F}         m n (out a P)   (inp Q)   R = loop''' {T} {Σ V F} m n P (♭ Q a) R
  loop''' {T} {Σ V F} {Σ W G} m n done        (inp P)   R = inp (♯ λ a → loop'''' {T} {Σ V F} (! (n + W a)) done (♭ P a) R)
  loop''' {T} {Σ V F}         m n P           (out b Q) R = out b (loop''' {T} {♭ F b} m n P Q R)
  loop''' {T} {Σ V F} {Σ W G} m n (inp P)     done      R = inp (♯ λ a → loop'''' {T} {Σ V F} (! (n + W a)) (♭ P a) done R)
  loop''' {T} {Σ V F}         m n (out a P)   done      R = out a (loop''' {T} {♭ F a} m n P done R)
  loop''' {T} {Σ V F}         m n done        done      R = inp (♯ λ a → out a (loop'''' {T} {♭ F a} (! (n + (V a))) done done R))

  -- loop' 0 P Q R is equivalent to P ⟫ Q ⟫ loop R ⟨¿⟩ done

  loop'' : ∀ {T U S S'} → (Strict Natural) → (U ⇒ S) → (S ⇒ ¿ T & S') → (S' ⇒ ¿ T & S') → (U ⇒ * T & S')
  loop'' {T} (! n) P Q R = loop' {T} (% n) n P Q R

  loop' : ∀ {T U S S'} → ℕ → Natural → (U ⇒ S) → (S ⇒ ¿ T & S') → (S' ⇒ ¿ T & S') → (U ⇒ * T & S')
  loop' {T} {Σ V F} m       n (inp P)   (inp Q)       R = inp (♯ λ a → loop'' {T} (! (n + V a)) (♭ P a) (inp Q) R)
  loop' {T}         m       n (out a P) (inp Q)       R = loop' {T} m n P (♭ Q a) R
  loop' {T} {Σ V F} m       n done      (inp Q)       R = inp (♯ λ a → loop'' {T} (! (n + V a)) done (♭ Q a) R)
  loop' {T}         zero    n P         (out true Q)  R = out true (P ⟫ Q ⟫ S⊆S&*T {T} [&] done)
  loop' {T}         (suc m) n P         (out true Q)  R = out true (loop''' {T} {T} m n P Q R)
  loop' {T}         m       n P         (out false Q) R = out false (P ⟫ Q)
  loop' {T} {Σ V F} m       n (inp P)   done          R = inp (♯ λ a → loop'' {T} (! (n + V a)) (♭ P a) done R)
  loop' {T}         m       n (out a P) done          R = loop' {T} m n P (out a done) R
  loop' {T}         m       n done      done          R = inp (♯ λ a → loop'' {T} (! (n + # 1)) done (out a done) R)

loop : ∀ {T S} → (S ⇒ ¿ T & S) → (S ⇒ * T & S)
loop {T} P = loop' {T} zero (# 0) done P P
