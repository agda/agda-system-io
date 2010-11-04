open import Coinduction using ( ♭ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; cong )
open import System.IO.Transducers.Lazy using ( _⇒_is_ ; inp ; out ; done ; strict ; lazy ; ι ; _⟫_ ; ⟦_⟧ ; _≃_ )
open import System.IO.Transducers.Trace using ( Trace ; [] ; _∷_ )

module System.IO.Transducers.Properties.Category where

open Relation.Binary.PropositionalEquality.≡-Reasoning

-- Trace semantics of identity

⟦done⟧ : ∀ {S} → (Trace S)  → (Trace S)
⟦done⟧ as = as

done-semantics : ∀ {S s} → ⟦ done {S} {s} ⟧ ≃ ⟦done⟧
done-semantics as = refl

-- Trace semantics of composition

_⟦⟫⟧_ : ∀ {S T U} → 
  (f : Trace S → Trace T) → (g : Trace T → Trace U) → 
    (Trace S) → (Trace U)
(f ⟦⟫⟧ g) as = g (f as)

⟫-semantics : ∀ {S T U s} → 
  (P : S ⇒ T is s) → (Q : T ⇒ U is s) →
    (⟦ P ⟫ Q ⟧ ≃ ⟦ P ⟧ ⟦⟫⟧ ⟦ Q ⟧)
⟫-semantics done      Q         as       = refl
⟫-semantics (inp P)   done      as       = refl
⟫-semantics (out b P) done      as       = refl
⟫-semantics (inp P)   (out c Q) as       = cong (_∷_ c) (⟫-semantics (inp P) Q as)
⟫-semantics (out b P) (out c Q) as       = cong (_∷_ c) (⟫-semantics (out b P) Q as)
⟫-semantics (out b P) (inp Q)   as       = ⟫-semantics P (♭ Q b) as
⟫-semantics (inp P)   (inp Q)   []       = refl
⟫-semantics (inp P)   (inp Q)   (a ∷ as) = ⟫-semantics (♭ P a) (inp Q) as

-- Composition respects ≃

⟫-resp-≃ : ∀ {S T U s} 
  (P₁ P₂ : S ⇒ T is s) (Q₁ Q₂ : T ⇒ U is s) → 
    (⟦ P₁ ⟧ ≃ ⟦ P₂ ⟧) → (⟦ Q₁ ⟧ ≃ ⟦ Q₂ ⟧) → 
      (⟦ P₁ ⟫ Q₁ ⟧ ≃ ⟦ P₂ ⟫ Q₂ ⟧)
⟫-resp-≃ P₁ P₂ Q₁ Q₂ P₁≃P₂ Q₁≃Q₂ as =
  begin
    ⟦ P₁ ⟫ Q₁ ⟧ as
  ≡⟨ ⟫-semantics P₁ Q₁ as ⟩
    ⟦ Q₁ ⟧ (⟦ P₁ ⟧ as)
  ≡⟨ cong ⟦ Q₁ ⟧ (P₁≃P₂ as) ⟩
    ⟦ Q₁ ⟧ (⟦ P₂ ⟧ as)
  ≡⟨ Q₁≃Q₂ (⟦ P₂ ⟧ as) ⟩
    ⟦ Q₂ ⟧ (⟦ P₂ ⟧ as)
  ≡⟨ sym (⟫-semantics P₂ Q₂ as) ⟩
    ⟦ P₂ ⟫ Q₂ ⟧ as
  ∎

-- Left identity of composition

⟫-identity₁ : ∀ {S T s} (P : S ⇒ T is s) → ⟦ done ⟫ P ⟧ ≃ ⟦ P ⟧
⟫-identity₁ P = ⟫-semantics done P

-- Right identity of composition

⟫-identity₂ : ∀ {S T s} (P : S ⇒ T is s) → ⟦ P ⟫ done ⟧ ≃ ⟦ P ⟧
⟫-identity₂ P = ⟫-semantics P done

-- Associativity of composition

⟫-assoc : ∀ {S T U V s} 
  (P : S ⇒ T is s) (Q : T ⇒ U is s) (R : U ⇒ V is s) → 
    ⟦ (P ⟫ Q) ⟫ R ⟧ ≃ ⟦ P ⟫ (Q ⟫ R) ⟧
⟫-assoc P Q R as =
  begin
    ⟦ (P ⟫ Q) ⟫ R ⟧ as
  ≡⟨ ⟫-semantics (P ⟫ Q) R as ⟩
    ⟦ R ⟧ (⟦ P ⟫ Q ⟧ as)
  ≡⟨ cong ⟦ R ⟧ (⟫-semantics P Q as) ⟩
    ⟦ R ⟧ (⟦ Q ⟧ (⟦ P ⟧ as))
  ≡⟨ sym (⟫-semantics Q R (⟦ P ⟧ as)) ⟩
    ⟦ Q ⟫ R ⟧ (⟦ P ⟧ as)
  ≡⟨ sym (⟫-semantics P (Q ⟫ R) as) ⟩
    ⟦ P ⟫ (Q ⟫ R) ⟧ as
  ∎