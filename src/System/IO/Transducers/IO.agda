{-# OPTIONS --no-termination-check #-}
-- TODO: switch the termination checker back on.

open import Coinduction using ( ∞ ; ♭ ; ♯_ )
open import Data.Bool using ( Bool ; true ; false )
open import Data.Maybe using ( Maybe ; just ; nothing )
open import Data.Sum using ( _⊎_ ; inj₁ ; inj₂ )
open import Data.Product using ( ∃ ; _,_ )
open import Data.ByteString using ( ByteString ; strict ; null )
open import System.IO using ( IO ; Command ; return ; _>>_ ; _>>=_ ; skip ; getBytes ; putBytes ; commit )
open import System.IO.Transducers.Lazy using ( _⇒_ ; _⤇_ ; inp ; out ; done ; ι⁻¹ )
open import System.IO.Transducers.Session using ( I ; Σ ; Bytes )
open import System.IO.Transducers.Strict using ( _⇛_ )

module System.IO.Transducers.IO where

infixl 5 _$_

postulate 
  IOError : Set
  _catch_ : ∀ {A} → (IO A) → (IOError → (IO A)) → (IO A)
{-# COMPILED_TYPE IOError IOError #-}
{-# COMPILED _catch_ (\ _ -> catch) #-}

_$_ : ∀ {A V F T} → (Σ {A} V F ⤇ T) → (a : A) → (♭ F a ⤇ T)
inp P   $ a = ♭ P a
out b P $ a = out b (P $ a)

getBytes? : IO (Maybe (ByteString strict))
getBytes? = (getBytes >>= λ x → return (just x)) catch (λ e → return nothing)

runI : (I ⤇ Bytes) → Command
runI (out true (out x P)) = putBytes x >> commit >> runI P
runI (out false P)        = skip

mutual

  run? : (Bytes ⤇ Bytes) → (Maybe (ByteString strict)) → Command
  run? P (just b) = run' (P $ true $ b)
  run? P nothing = runI (P $ false)

  run' : (Bytes ⤇ Bytes) → Command
  run' (out true (out b P)) = putBytes b >> commit >> run' P
  run' (out false P)        = skip
  run' P                    = getBytes? >>= run? P

run : (Bytes ⇒ Bytes) → Command
run P = run' (ι⁻¹ P)
