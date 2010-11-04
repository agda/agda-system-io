-- A simple word counter

open import Coinduction using ( ♯_ )
open import Data.Char.Classifier using ( isSpace )
open import Data.Bool using ( Bool ; true ; false )
open import Data.Natural using ( Natural ; show )
open import System.IO using ( Command )
open import System.IO.Transducers.Syntax using ( _⇒_ ; inp ; out ; done ; _⟫_ ; _⟨&⟩_ )
open import System.IO.Transducers.List using ( length )
open import System.IO.Transducers.Bytes using ( bytes )
open import System.IO.Transducers.IO using ( run )
open import System.IO.Transducers.UTF8 using ( split ; encode )
open import System.IO.Transducers.Session using ( ⟨_⟩ ; _&_ ; Bytes ; Strings )

module System.IO.Examples.WC where

words : Bytes ⇒ ⟨ Natural ⟩
words = split isSpace ⟫ inp (♯ length { Bytes })

-- TODO: this isn't exactly lovely user syntax.

report : ⟨ Natural ⟩ & ⟨ Natural ⟩ ⇒ Strings
report = 
  (inp (♯ λ #bytes → 
  (out true
  (out (show #bytes)
  (out true
  (out " " 
  (inp (♯ λ #words → 
  (out true
  (out (show #words)
  (out true
  (out "\n"
  (out false done)))))))))))))

wc : Bytes ⇒ Bytes
wc = bytes ⟨&⟩ words ⟫ report ⟫ inp (♯ encode)

main : Command
main = run wc
