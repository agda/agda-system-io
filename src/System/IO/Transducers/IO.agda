{-# OPTIONS --no-termination-check #-}
-- TODO: switch the termination checker back on.

open import Coinduction using ( ∞ ; ♭ ; ♯_ )
open import Data.Bool using ( Bool ; true ; false )
open import Data.Maybe using ( Maybe ; just ; nothing )
open import Data.Sum using ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Product using ( ∃ ; _,_ )
open import Data.ByteString using ( ByteString ; strict ; null )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )
open import System.IO using ( IO ; Command ; return ; _>>_ ; _>>=_ ; skip ; getBytes ; putBytes ; commit )
open import System.IO.Transducers.Lazy using ( _⇒_ ; inp ; out ; id ; done ; _⟫_ )
open import System.IO.Transducers.Session using ( I ; Σ ; Bytes )
open import System.IO.Transducers.Strict using ( _⇛_ )

module System.IO.Transducers.IO where

postulate 
  IOError : Set
  _catch_ : ∀ {A} → (IO A) → (IOError → (IO A)) → (IO A)
{-# COMPILED_TYPE IOError IOError #-}
{-# COMPILED _catch_ (\ _ -> catch) #-}

runI : (I ⇒ Bytes) → Command
runI (id ())
runI (inp {} P)
runI (out true (id ()))
runI (out true (inp {} P))
runI (out true (out x P)) = putBytes x >> commit >> runI P
runI (out false P)        = skip

getBytes? : IO (Maybe (ByteString strict))
getBytes? = (getBytes >>= λ x → return (just x)) catch (λ e → return nothing)

mutual

  run' : (Bytes ⇒ Bytes) → (Maybe (ByteString strict)) → Command
  run' P (just x) = run (out true (out x done) ⟫ P)
  run' P nothing  = runI (out false done ⟫ P)

  run : (Bytes ⇒ Bytes) → Command
  run (inp P)                      = getBytes? >>= run' (inp P)
  run (out true (inp P))           = getBytes? >>= run' (out true (inp P))
  run (out true (out b P))         = putBytes b >> run P
  run (out true (id Bytes≡Bytes')) = skip
  run (out false P)                = skip
  run (id refl)                    = getBytes? >>= run' done
  