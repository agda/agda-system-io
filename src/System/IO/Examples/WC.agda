-- A simple word counter

-- open import Data.Bool using ( Bool ; true ; false ; not )
-- open import Data.Char using ( Char )
-- open import Data.ByteString using ( ByteString ) renaming ( length to lengthBS )
-- open import Data.Product using ( _×_ ; _,_ )
-- open import Data.Word using ( Byte )
-- open import Data.String using ( String )
-- open import System.IO.Transducers using ( _⇒_ ; Inp_⇒_ ; inp ; out ; done ; _⟫_ ; _[&]_ ; π₁ ; π₂ ; _⟨&⟩'_ )
-- open import System.IO.Transducers.Stateful using ( loop )
-- open import System.IO.Transducers.Session using ( Session ; [] ; _∷_ ; ⟨_⟩ ; _&_ ; ¿ ; ¡ ; _&¡_ ; Bytes )

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
