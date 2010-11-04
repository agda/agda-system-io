open import Coinduction using ( ♯_ )
open import Data.Natural using ( Natural ; # ; _+_ )
open import Data.Strict using ( Strict ; ! )
open import System.IO.Transducers.Session using ( I ; Σ ; ⟨_⟩ )
open import System.IO.Transducers.Syntax using ( _⇒_ ; inp ; out ; done )

module System.IO.Transducers.Weight where

-- Weight of a trace

weight' : ∀ {S} → (Strict Natural) → S ⇒ ⟨ Natural ⟩
weight' {I}     (! n) = out n done
weight' {Σ W F} (! n) = inp (♯ λ a → weight' (! (n + W a)))

weight : ∀ {S} → S ⇒ ⟨ Natural ⟩
weight = weight' (! (# 0))