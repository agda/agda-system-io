{-# OPTIONS --no-termination-check #-}
-- TODO: switch the termination checker back on.

open import Coinduction using ( ∞ ; ♭ ; ♯_ )
open import Data.Bool using ( Bool ; true ; false )
open import Data.Maybe using ( Maybe ; just ; nothing )
open import Data.Sum using ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Product using ( ∃ ; _,_ )
open import Data.ByteString using ( ByteString ; strict ; null )
open import System.IO using ( IO ; Command ; return ; _>>_ ; _>>=_ ; skip ; getBytes ; putBytes ; commit )
open import System.IO.Transducers.Syntax using ( _⇒_ ; inp ; out ; done ; _⟫_ )
open import System.IO.Transducers.Session using ( I ; Σ ; Bytes )
open import System.IO.Transducers.Function using ( _⇛_ )

module System.IO.Transducers.IO where

postulate 
  IOError : Set
  _catch_ : ∀ {A} → (IO A) → (IOError → (IO A)) → (IO A)
{-# COMPILED_TYPE IOError IOError #-}
{-# COMPILED _catch_ (\ _ -> catch) #-}

runI : (I ⇒ Bytes) → Command
runI (out true (out x P)) = putBytes x >> commit >> runI P
runI (out false done)     = skip

getBytes? : IO (Maybe (ByteString strict))
getBytes? = (getBytes >>= λ x → return (just x)) catch (λ e → return nothing)

inp/out : ∀ {S B W G} → (S ⇒ Σ {B} W G) → (∞ (S ⇛ Σ W G)) ⊎ (∃ λ b → S ⇒ ♭ G b)
inp/out (inp P)   = inj₁ P
inp/out (out b P) = inj₂ (b , P)
inp/out done      = inj₁ (♯ λ a → out a done)

mutual

  run' : (Bytes ⇒ Bytes) → (Maybe (ByteString strict)) → Command
  run' P (just x) = run (out true (out x done) ⟫ P)
  run' P nothing  = runI (out false done ⟫ P)

  run : (Bytes ⇒ Bytes) → Command
  run (inp P)       = getBytes? >>= run' (inp P)
  run (out true P)  with inp/out P
  run (out true P)  | inj₁ Q       = getBytes? >>= run' (out true (inp Q))
  run (out true P)  | inj₂ (b , Q) = putBytes b >> run Q
  run (out false P) = skip
  run done          = getBytes? >>= run' done
  