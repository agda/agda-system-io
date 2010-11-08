open import Coinduction using ( ♯_ ; ♭ )
open import Data.Strict using ( Strict ; ! )
open import Data.Natural using ( Natural ; # ; _+_ )
open import Data.Bool using ( Bool ; true ; false )
open import System.IO.Transducers.Session using ( I ; Σ ; ⟨_⟩ ; * ; _&*_ ; ¿ ) 
open import System.IO.Transducers.Lazy using ( _⇒_ ; inp ; out ; done )
open import System.IO.Transducers.Strict using ( _⇛_ )

module System.IO.Transducers.List where

-- Length of a list

length' : ∀ {T S} → (Strict Natural) → (T &* S) ⇛ ⟨ Natural ⟩
length' {I}     {S} (! n) true  = inp (♯ length' {S} {S} (! (n + # 1)))
length' {I}     {S} (! n) false = out n done
length' {Σ V G} {S} (! n) b     = inp (♯ length' {♭ G b} {S} (! n))

length : ∀ {S} → (* S) ⇛ ⟨ Natural ⟩
length {S} = length' {I} {S} (! (# 0))

-- Flatten a list of lists

mutual

  concat' : ∀ {T S} → ((T &* S) &* * S) ⇛ (T &* S)
  concat' {I}     {S} true  = out true (inp (♯ concat' {S} {S}))
  concat' {I}     {S} false = inp (♯ concat {S})
  concat' {Σ W G} {S} a     = out a (inp (♯ concat' {♭ G a} {S}))

  concat : ∀ {S} → (* (* S)) ⇛ (* S)
  concat {S} true  = inp (♯ concat' {I} {S})
  concat {S} false = out false done

-- Some inclusions, which coerce traces from one session to another.

-- TODO: Add more inclusions.
-- TODO: Prove that these are monomorphisms.
-- TODO: It would be nice if inclusions like this could be handled by subtyping.

S⊆S&*T : ∀ {S T} → S ⇒ S &* T
S⊆S&*T {I}     = out false done
S⊆S&*T {Σ V F} = inp (♯ λ a → out a S⊆S&*T)

S⊆*S : ∀ {S} → S ⇒ * S
S⊆*S = out true S⊆S&*T 

¿S⊆*S : ∀ {S} → ¿ S ⇛ * S
¿S⊆*S {S} true  = out true (S⊆S&*T {S} {S})
¿S⊆*S {S} false = out false done

