open import Coinduction using ( ♭ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; cong )
open import System.IO.Transducers using ( _⇒_ ; inp ; out ; done ; _⟫_ ; assoc ; delay ; _[&]_ ; ⟦_⟧ ; _≃_ )
open import System.IO.Transducers.Session using ( [] ; _∷_ ; _&_ )
open import System.IO.Transducers.Trace using ( Trace ; [] ; _∷_ )
open import System.IO.Transducers.Properties.Category using ( _⟦⟫⟧_ ; ⟫-semantics )

module System.IO.Transducers.Properties.BraidedMonoidal where

_++_ : ∀ {S T} → (Trace S) → (Trace T) → (Trace (S & T))
([] {[]})     ++ bs = bs
([] {W ∷ Ss}) ++ bs = []
(a ∷ as)      ++ bs = a ∷ (as ++ bs)

front : ∀ {S T} → (Trace (S & T)) → (Trace S)
front {[]}     as       = []
front {W ∷ Ss} []       = []
front {W ∷ Ss} (a ∷ as) = a ∷ front as

back : ∀ {S T} → (Trace (S & T)) → (Trace T)
back {[]}     as       = as
back {W ∷ Ss} []       = []
back {W ∷ Ss} (a ∷ as) = back {♭ Ss a} as

⟦assoc⟧ : ∀ {S T U} → (Trace (S & (T & U)) → Trace ((S & T) & U))
⟦assoc⟧ {[]}     as       = as
⟦assoc⟧ {W ∷ Ss} []       = []
⟦assoc⟧ {W ∷ Ss} (a ∷ as) = a ∷ ⟦assoc⟧ {♭ Ss a} as

assoc-semantics : ∀ {S T U} → (⟦ assoc {S} {T} {U} ⟧ ≃ ⟦assoc⟧ {S} {T} {U})
assoc-semantics {[]} as = refl
assoc-semantics {W ∷ Ss} [] = refl
assoc-semantics {W ∷ Ss} (a ∷ as) = cong (_∷_ a) (assoc-semantics {♭ Ss a} as)

⟦delay⟧ : ∀ S {T U} → (Trace T → Trace U) → (Trace (S & T) → Trace U)
⟦delay⟧ S f as = f (back {S} as)

delay-semantics : ∀ S {T U} → (P : T ⇒ U) → (⟦ delay S P ⟧ ≃ ⟦delay⟧ S ⟦ P ⟧)
delay-semantics []       P         as       = refl
delay-semantics (W ∷ Ss) (inp F)   []       = refl
delay-semantics (W ∷ Ss) (inp F)   (a ∷ as) = delay-semantics (♭ Ss a) (inp F) as
delay-semantics (W ∷ Ss) (out b P) as       = cong (_∷_ b) (delay-semantics (W ∷ Ss) P as)
delay-semantics (W ∷ Ss) done      []       = refl
delay-semantics (W ∷ Ss) done      (a ∷ as) = delay-semantics (♭ Ss a) done as

_⟦[&]⟧_ : ∀ {S T U V} →
  (f : Trace S → Trace T) → (g : Trace U → Trace V) → 
    (Trace (S & U)) → (Trace (T & V))
_⟦[&]⟧_ {S} f g as = f (front as) ++ g (back {S} as)

[&]-semantics : ∀ {S T U V} →
  (P : S ⇒ T) → (Q : U ⇒ V) → 
    (⟦ P [&] Q ⟧ ≃ ⟦ P ⟧ ⟦[&]⟧ ⟦ Q ⟧)
[&]-semantics {S} {T = []} P         Q as with ⟦ P ⟧ (front as)
[&]-semantics {S} {T = []} P         Q as | []  = delay-semantics S Q as
[&]-semantics {T = V ∷ Ts} (inp F) Q []         = refl
[&]-semantics {T = V ∷ Ts} (inp F) Q (a ∷ as)   = [&]-semantics (♭ F a) Q as
[&]-semantics {T = V ∷ Ts} (out b P) Q as       = cong (_∷_ b) ([&]-semantics P Q as)
[&]-semantics {T = V ∷ Ts} done      Q []       = refl
[&]-semantics {T = V ∷ Ts} done      Q (a ∷ as) = cong (_∷_ a) ([&]-semantics {T = ♭ Ts a} done Q as)