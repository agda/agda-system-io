open import Coinduction using ( ♭ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; cong )
open import System.IO.Transducers using ( _⇒_ ; inp ; out ; done ; _⟫_ ; I⟦_⟧ )
open import System.IO.Transducers.Trace using ( Trace ; [] ; _∷_ )

module System.IO.Transducers.Properties.Category where

_⟦⟫⟧_ : ∀ {S T U} → 
  (f : Trace S → Trace T) → (g : Trace T → Trace U) → 
    (Trace S) → (Trace U)
(f ⟦⟫⟧ g) as = g (f as)

⟫-semantics : ∀ {S T U} → 
  (P : S ⇒ T) → (Q : T ⇒ U) → ∀ as →
    I⟦ P ⟫ Q ⟧ as ≡ (I⟦ P ⟧ ⟦⟫⟧ I⟦ Q ⟧) as
⟫-semantics P         (out c Q) as       = cong (_∷_ c) (⟫-semantics P Q as)
⟫-semantics (inp F)   (inp G)   []       = refl
⟫-semantics (inp F)   (inp G)   (a ∷ as) = ⟫-semantics (♭ F a) (inp G) as
⟫-semantics (inp F)   done      []       = refl
⟫-semantics (inp F)   done      (a ∷ as) = ⟫-semantics (♭ F a) done as
⟫-semantics (out b P) (inp G)   as       = ⟫-semantics P (♭ G b) as
⟫-semantics (out b P) done      as       = refl
⟫-semantics done      (inp G)   as       = refl
⟫-semantics done      done      as       = refl
