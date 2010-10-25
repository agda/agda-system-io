{-# OPTIONS --no-termination-check #-}
-- TODO: switch the termination checker back on.

open import Coinduction using ( ♭ ; ♯_ )
open import Data.Bool using ( Bool ; true ; false )
open import Data.Maybe using ( Maybe ; just ; nothing )
open import Data.ByteString using ( ByteString ; strict ; null )
open import System.IO using ( IO ; Command ; return ; _>>_ ; _>>=_ ; skip ; getBytes ; putBytes ; commit )
open import System.IO.Transducers using ( _⇒_ ; Inp_⇒_ ; inp ; out ; done )
open import System.IO.Transducers.Session using ( [] ; Bytes )

module System.IO.Transducers.IO where

postulate 
  IOError : Set
  _catch_ : ∀ {A} → (IO A) → (IOError → (IO A)) → (IO A)
{-# COMPILED_TYPE IOError IOError #-}
{-# COMPILED _catch_ (\ _ -> catch) #-}

mutual
  
  run' : ([] ⇒ Bytes) → Command
  run' (out (just x) P)   = putBytes x >> commit >> run' P
  run' (out nothing done) = skip
  
  run : (Bytes ⇒ Bytes) → Command
  run (inp F)          = (getBytes >>= λ x → run (♭ F (just x))) catch (λ e → run' (♭ F nothing))
  run (out (just x) P) = putBytes x >> commit >> run P
  run (out nothing P)  = skip
  run done             = (getBytes >>= λ x → run (out (just x) done)) catch (λ e → skip)
  