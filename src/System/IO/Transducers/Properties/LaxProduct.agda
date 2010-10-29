open import Coinduction using ( ♭ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; cong ; cong₂ )
open import System.IO.Transducers using ( _⇒_ ; inp ; out ; done ; out*' ; _⟫_ ; _⟨&⟩_ ; _⟨&⟩[_]_ ; discard ; π₁ ; π₂ ; ⟦_⟧ ; _≃_ )
open import System.IO.Transducers.Session using ( [] ; _∷_ ; _&_ )
open import System.IO.Transducers.Trace using ( _≤_ ; Trace ; [] ; _∷_ )
open import System.IO.Transducers.Properties.Lemmas using ( cong₃ ; revApp ; out*'-semantics )
open import System.IO.Transducers.Properties.BraidedMonoidal using ( _++_ )
open import System.IO.Transducers.Properties.Category using ( _⟦⟫⟧_ ; ⟫-semantics )

module System.IO.Transducers.Properties.LaxProduct where

open Relation.Binary.PropositionalEquality.≡-Reasoning

_⟦⟨&⟩⟧_ : ∀ {S T U} → 
  (f : Trace S → Trace T) → (g : Trace S → Trace U) → 
    (Trace S) → (Trace (T & U))
(f ⟦⟨&⟩⟧ g) as = f as ++ g as

_⟦⟨&⟩[_]⟧_ : ∀ {S T U V} → 
  (Trace S → Trace T) → (U ≤ V) → (Trace S → Trace U) → 
    (Trace S → Trace (T & V))
(f ⟦⟨&⟩[ cs ]⟧ g) as = f as ++ (revApp cs (g as))

⟨&⟩[]-semantics : ∀ {S T U V} → 
  (P : S ⇒ T) → (cs : U ≤ V) →  (Q : S ⇒ U) →
    (⟦ P ⟨&⟩[ cs ] Q ⟧ ≃ ⟦ P ⟧ ⟦⟨&⟩[ cs ]⟧ ⟦ Q ⟧)
⟨&⟩[]-semantics (inp {T = []}     F) cs Q         as with ⟦ inp F ⟧ as
⟨&⟩[]-semantics (inp {T = []}     F) cs Q         as    | [] = out*'-semantics cs Q as
⟨&⟩[]-semantics (inp {T = W ∷ Ts} F) cs (inp G)   []         = refl
⟨&⟩[]-semantics (inp {T = W ∷ Ts} F) cs (inp G)   (a ∷ as)   = ⟨&⟩[]-semantics (♭ F a) cs (♭ G a) as
⟨&⟩[]-semantics (inp {T = W ∷ Ts} F) cs (out c Q) as         = ⟨&⟩[]-semantics (inp F) (c ∷ cs) Q as
⟨&⟩[]-semantics (inp {T = W ∷ Ts} F) cs done      []         = refl
⟨&⟩[]-semantics (inp {T = W ∷ Ts} F) cs done      (a ∷ as)   = ⟨&⟩[]-semantics (♭ F a) (a ∷ cs) done as
⟨&⟩[]-semantics (out b P)            cs Q         as         = cong (_∷_ b) (⟨&⟩[]-semantics P cs Q as)
⟨&⟩[]-semantics (done {[]})          cs Q         []         = out*'-semantics cs Q []
⟨&⟩[]-semantics (done {W ∷ Ts})      cs (inp F)   []         = refl
⟨&⟩[]-semantics (done {W ∷ Ts})      cs (inp F)   (a ∷ as)   = cong (_∷_ a) (⟨&⟩[]-semantics done cs (♭ F a) as)
⟨&⟩[]-semantics (done {W ∷ Ts})      cs (out c Q) as         = ⟨&⟩[]-semantics done (c ∷ cs) Q as
⟨&⟩[]-semantics (done {W ∷ Ts})      cs done      []         = refl
⟨&⟩[]-semantics (done {W ∷ Ts})      cs done      (a ∷ as)   = cong (_∷_ a) (⟨&⟩[]-semantics done (a ∷ cs) done as)

⟨&⟩-semantics : ∀ {S T U} → 
  (P : S ⇒ T) → (Q : S ⇒ U) →
    (⟦ P ⟨&⟩ Q ⟧ ≃ ⟦ P ⟧ ⟦⟨&⟩⟧ ⟦ Q ⟧)
⟨&⟩-semantics P Q = ⟨&⟩[]-semantics P [] Q

⟫-dist-⟨&⟩ : ∀ {S T U V} → 
  (P : T ⇒ U) → (Q : T ⇒ V) → (R : S ⇒ T) →
    (⟦ R ⟫ (P ⟨&⟩ Q) ⟧ ≃ ⟦ (R ⟫ P) ⟨&⟩ (R ⟫ Q) ⟧)
⟫-dist-⟨&⟩ P Q R as = 
  begin
    ⟦ R ⟫ P ⟨&⟩ Q ⟧ as
  ≡⟨ ⟫-semantics R (P ⟨&⟩ Q) as ⟩
    ⟦ P ⟨&⟩ Q ⟧ (⟦ R ⟧ as)
  ≡⟨ ⟨&⟩-semantics P Q (⟦ R ⟧ as) ⟩
    ⟦ P ⟧ (⟦ R ⟧ as) ++ ⟦ Q ⟧ (⟦ R ⟧ as)
  ≡⟨ cong₂ _++_ (sym (⟫-semantics R P as)) (sym (⟫-semantics R Q as)) ⟩
    ⟦ R ⟫ P ⟧ as ++ ⟦ R ⟫ Q ⟧ as
  ≡⟨ sym (⟨&⟩-semantics (R ⟫ P) (R ⟫ Q) as) ⟩
    ⟦ (R ⟫ P) ⟨&⟩ (R ⟫ Q) ⟧ as
  ∎
