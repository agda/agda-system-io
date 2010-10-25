open import Coinduction using ( ♯_ )
open import Data.Bool using ( Bool ; true ; false ; not )
open import Data.ByteString using ( null ) renaming ( span to #span )
open import Data.Maybe using ( Maybe ; just ; nothing )
open import Data.Natural using ( Natural )
open import Data.Product using ( _×_ ; _,_ )
open import Data.Word using ( Byte )
open import System.IO.Transducers using ( _⇒_ ; Inp_⇒_ ; inp ; out ; done ; _⟫_ ; π₁ ; π₂ ; _[&]_ ; weight )
open import System.IO.Transducers.Stateful using ( loop )
open import System.IO.Transducers.Session using ( ⟨_⟩ ; _&_ ; ¿ ; ¡ ; Bytes )

module System.IO.Transducers.Bytes where

open import System.IO.Transducers.Session public using ( Bytes )

span' : (Byte → Bool) → Inp Bytes ⇒ Bytes & Bytes
span' φ (just x) with #span φ x
span' φ (just x) | (x₁ , x₂) with null x₁ | null x₂ 
span' φ (just x) | (x₁ , x₂) | true  | true  = inp (♯ span' φ)
span' φ (just x) | (x₁ , x₂) | true  | false = out nothing (out (just x₂) done)
span' φ (just x) | (x₁ , x₂) | false | true  = out (just x₁) (inp (♯ span' φ))
span' φ (just x) | (x₁ , x₂) | false | false = out (just x₁) (out nothing (out (just x₂) done))
span' φ nothing  = out nothing (out nothing done)

span : (Byte → Bool) → Bytes ⇒ Bytes & Bytes
span φ = inp (♯ span' φ)

break : (Byte → Bool) → Bytes ⇒ Bytes & Bytes
break φ = span (λ x → not (φ x))

nonempty' : Inp Bytes ⇒ ¿ Bytes
nonempty' (just x) with null x
nonempty' (just x) | true  = inp (♯ nonempty')
nonempty' (just x) | false = out (just (just x)) done
nonempty' nothing  = out nothing done

nonempty : Bytes ⇒ ¿ Bytes
nonempty = inp (♯ nonempty')

split? : (Byte → Bool) → Bytes ⇒ ¿ Bytes & Bytes
split? φ = span φ ⟫ π₂ {Bytes} ⟫ break φ ⟫ nonempty [&] done

split : (Byte → Bool) → Bytes ⇒ ¡ Bytes
split φ = loop {Bytes} (split? φ) ⟫ π₁

bytes : Bytes ⇒ ⟨ Natural ⟩
bytes = weight
