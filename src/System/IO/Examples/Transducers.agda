open import Coinduction using ( ♯_ )
open import Data.Maybe using ( Maybe ; just ; nothing ; maybe )
open import Data.Nat using ( ℕ ; _+_ )
open import Data.Integer using ( ℤ ; +_ ; _⊖_ )
open import System.IO.Transducers using ( inp ; out ; done ; _⇒_ ; Inp_⇒_ ; C⟦_⟧ ; _⟨¿⟩_ )
open import System.IO.Transducers.Trace using ( [] ; _∷_ )
open import System.IO.Transducers.Session using ( ⟨_⟩ ; _&_ ; ¡ ; ¿ ; _/'_ )
open import System.IO.Transducers.Stateful using ( loop ; lookahead¿ )

module System.IO.Examples.Transducers where

add : ⟨ ℕ ⟩ & ⟨ ℕ ⟩ ⇒ ⟨ ℕ ⟩
add = inp (♯ λ x → inp (♯ λ y → out (x + y) done))

-- runAdd == 8 ∷ []
runAdd = C⟦ add ⟧ ( 3 ∷ 5 ∷ [] )

nat? : ¡ ⟨ ℤ ⟩ ⇒ ¿ ⟨ ℕ ⟩ & ¡ ⟨ ℤ ⟩
nat? = lookahead¿ {⟨ ℕ ⟩} (inp (♯ rest)) where
  rest : Inp ¡ ⟨ ℤ ⟩ ⇒ ¿ ⟨ ℕ ⟩ & ¡ ⟨ ℤ ⟩
  rest nothing      = out nothing (out nothing done)
  rest (just (+ n)) = out (just n) done
  rest (just _)     = out nothing done

-- runNat? == ( just 5 ∷ just (+ 7) ∷ just (0 ⊖ 3) ∷ just (+ 8) ∷ nothing ∷ [])
runNat? = C⟦ nat? ⟧ ( just (+ 5) ∷ just (+ 7) ∷ just (0 ⊖ 3) ∷ just (+ 8) ∷ nothing ∷ [])

nat! : ¡ ⟨ ℤ ⟩ ⇒ ¡ ⟨ ℕ ⟩ & ¡ ⟨ ℤ ⟩
nat! = loop {⟨ ℕ ⟩} nat?

-- runNat! == ( just 5 ∷ just 7 ∷ nothing ∷ just (0 ⊖ 3) ∷ just (+ 8) ∷ nothing ∷ [])
runNat! = C⟦ nat! ⟧ ( just (+ 5) ∷ just (+ 7) ∷ just (0 ⊖ 3) ∷ just (+ 8) ∷ nothing ∷ [])
