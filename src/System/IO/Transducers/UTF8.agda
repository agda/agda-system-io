open import Coinduction using ( ♯_ )
open import Data.Bool using ( Bool ; true ; false ; not )
open import Data.ByteString using ( null )
open import Data.ByteString.UTF8 using ( fromString ) renaming ( span to #span )
open import Data.Maybe using ( Maybe ; just ; nothing )
open import Data.Product using ( _×_ ; _,_ )
open import Data.Char using ( Char )
open import System.IO.Transducers using ( _⇒_ ; Inp_⇒_ ; inp ; out ; done ; _⟫_ ; π₁ ; π₂ ; _[&]_ )
open import System.IO.Transducers.Stateful using ( loop )
open import System.IO.Transducers.Session using ( _&_ ; ¿ ; ¡ ; Bytes ; Strings )

module System.IO.Transducers.UTF8 where

-- TODO: This doesn't behave properly when chunk boundaries don't align with char boundaries.

span' : (Char → Bool) → Inp Bytes ⇒ Bytes & Bytes
span' φ (just x) with #span φ x
span' φ (just x) | (x₁ , x₂) with null x₁ | null x₂ 
span' φ (just x) | (x₁ , x₂) | true  | true  = inp (♯ span' φ)
span' φ (just x) | (x₁ , x₂) | true  | false = out nothing (out (just x₂) done)
span' φ (just x) | (x₁ , x₂) | false | true  = out (just x₁) (inp (♯ span' φ))
span' φ (just x) | (x₁ , x₂) | false | false = out (just x₁) (out nothing (out (just x₂) done))
span' φ nothing  = out nothing (out nothing done)

span : (Char → Bool) → Bytes ⇒ Bytes & Bytes
span φ = inp (♯ span' φ)

break : (Char → Bool) → Bytes ⇒ Bytes & Bytes
break φ = span (λ x → not (φ x))

nonempty' : Inp Bytes ⇒ ¿ Bytes
nonempty' (just x) with null x
nonempty' (just x) | true  = inp (♯ nonempty')
nonempty' (just x) | false = out (just (just x)) done
nonempty' nothing  = out nothing done

nonempty : Bytes ⇒ ¿ Bytes
nonempty = inp (♯ nonempty')

split? : (Char → Bool) → Bytes ⇒ ¿ Bytes & Bytes
split? φ = span φ ⟫ π₂ {Bytes} ⟫ break φ ⟫ nonempty [&] done

split : (Char → Bool) → Bytes ⇒ ¡ Bytes
split φ = loop {Bytes} (split? φ) ⟫ π₁

-- TODO: decode

encode' : Inp Strings ⇒ Bytes
encode' (just s) = out (just (fromString s)) (inp (♯ encode'))
encode' nothing  = out nothing done

encode : Strings ⇒ Bytes
encode = inp (♯ encode')

