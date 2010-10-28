open import Coinduction using ( ♭ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; cong ; cong₂ )
open import System.IO.Transducers using ( _⇒_ ; inp ; out ; done ; out*' ; _⟫_ ; _⟨&⟩_ ; _⟨&⟩[_]_ ; discard ; π₁ ; π₂ ; I⟦_⟧ ; _≃_ )
open import System.IO.Transducers.Session using ( [] ; _∷_ ; _&_ )
open import System.IO.Transducers.Trace using ( _≤_ ; Trace ; [] ; _∷_ )
open import System.IO.Transducers.Properties.Lemmas using ( cong₃ ; revApp ; out*'-semantics )
open import System.IO.Transducers.Properties.Category using ( _⟦⟫⟧_ ; ⟫-semantics )

module System.IO.Transducers.Properties.LaxProduct where

open Relation.Binary.PropositionalEquality.≡-Reasoning

_++_ : ∀ {S T} → (Trace S) → (Trace T) → (Trace (S & T))
([] {[]})     ++ bs = bs
([] {W ∷ Ss}) ++ bs = []
(a ∷ as)      ++ bs = a ∷ (as ++ bs)

_⟦⟨&⟩⟧_ : ∀ {S T U} → 
  (f : Trace S → Trace T) → (g : Trace S → Trace U) → 
    (Trace S) → (Trace (T & U))
(f ⟦⟨&⟩⟧ g) as = f as ++ g as

_⟦⟨&⟩[_]⟧_ : ∀ {S T U V} → 
  (Trace S → Trace T) → (U ≤ V) → (Trace S → Trace U) → 
    (Trace S → Trace (T & V))
(f ⟦⟨&⟩[ cs ]⟧ g) as = f as ++ (revApp cs (g as))

⟦⟫⟧-dist-⟦⟨&⟩⟧ : ∀ {S T U V} → 
  (f : Trace T → Trace U) → (g : Trace T → Trace V) → (h : Trace S → Trace T) →
    ∀ as → (h ⟦⟫⟧ (f ⟦⟨&⟩⟧ g)) as ≡ ((h ⟦⟫⟧ f) ⟦⟨&⟩⟧ (h ⟦⟫⟧ g)) as
⟦⟫⟧-dist-⟦⟨&⟩⟧ f g h as = 
  refl

⟨&⟩[]-semantics : ∀ {S T U V} → 
  (P : S ⇒ T) → (cs : U ≤ V) →  (Q : S ⇒ U) →
    ∀ as → I⟦ P ⟨&⟩[ cs ] Q ⟧ as ≡ (I⟦ P ⟧ ⟦⟨&⟩[ cs ]⟧ I⟦ Q ⟧) as
⟨&⟩[]-semantics (inp {T = []}     F) cs Q         as with I⟦ inp F ⟧ as
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
     ∀ as → I⟦ P ⟨&⟩ Q ⟧ as ≡ (I⟦ P ⟧ ⟦⟨&⟩⟧ I⟦ Q ⟧) as
⟨&⟩-semantics P Q as = ⟨&⟩[]-semantics P [] Q as

⟫-dist-⟨&⟩ : ∀ {S T U V} → 
  (P : T ⇒ U) → (Q : T ⇒ V) → (R : S ⇒ T) →
    ((R ⟫ (P ⟨&⟩ Q)) ≃ ((R ⟫ P) ⟨&⟩ (R ⟫ Q)))
⟫-dist-⟨&⟩ P Q R as = 
  begin
    I⟦ R ⟫ P ⟨&⟩ Q ⟧ as
  ≡⟨ ⟫-semantics R (P ⟨&⟩ Q) as ⟩
    I⟦ P ⟨&⟩ Q ⟧ (I⟦ R ⟧ as)
  ≡⟨ ⟨&⟩-semantics P Q (I⟦ R ⟧ as) ⟩
    I⟦ P ⟧ (I⟦ R ⟧ as) ++ I⟦ Q ⟧ (I⟦ R ⟧ as)
  ≡⟨ cong₂ _++_ (sym (⟫-semantics R P as)) (sym (⟫-semantics R Q as)) ⟩
    I⟦ R ⟫ P ⟧ as ++ I⟦ R ⟫ Q ⟧ as
  ≡⟨ sym (⟨&⟩-semantics (R ⟫ P) (R ⟫ Q) as) ⟩
    I⟦ (R ⟫ P) ⟨&⟩ (R ⟫ Q) ⟧ as
  ∎
