-- A simple word counter

open import Coinduction using ( ♯_ )
open import Data.Char.Classifier using ( isSpace )
open import Data.Maybe using ( Maybe ; just ; nothing )
open import Data.Natural using ( Natural ; show )
open import System.IO using ( Command )
open import System.IO.Transducers using ( _⇒_ ; inp ; out ; done ; _⟫_ ; _⟨&⟩_ ; length )
open import System.IO.Transducers.Bytes using ( bytes )
open import System.IO.Transducers.IO using ( run )
open import System.IO.Transducers.UTF8 using ( split ; encode )
open import System.IO.Transducers.Session using ( ⟨_⟩ ; _&_ ; Bytes ; Strings )

module System.IO.Examples.WC where

words : Bytes ⇒ ⟨ Natural ⟩
words = split isSpace ⟫ length { Bytes }

-- TODO: this isn't exactly lovely user syntax.

report : ⟨ Natural ⟩ & ⟨ Natural ⟩ ⇒ Strings
report = 
  (inp (♯ λ #bytes → 
  (out (just (show #bytes)) 
  (out (just " ") 
  (inp (♯ λ #words → 
  (out (just (show #words)) 
  (out (just "\n")
  (out nothing done)))))))))

wc : Bytes ⇒ Bytes
wc = bytes ⟨&⟩ words ⟫ report ⟫ encode

main : Command
main = run wc
