open import Coinduction using ( ♭ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; cong )
open import System.IO.Transducers.Lazy using ( _⇒_ ; inp ; out ; id ; done ; _⟫_ ; ⟦_⟧ ; _≃_ ; equiv )
open import System.IO.Transducers.Session using ( Session ; I ; Σ ; _∼_ ; ∼-refl ; ∼-trans )
open import System.IO.Transducers.Trace using ( Trace ; [] ; _∷_ )
open import System.IO.Transducers.Properties.Lemmas using ( ⟦⟧-resp-∼ )

module System.IO.Transducers.Properties.Category where

open Relation.Binary.PropositionalEquality.≡-Reasoning

-- Trace semantics of identity

⟦done⟧ : ∀ {S} → (Trace S)  → (Trace S)
⟦done⟧ as = as

done-semantics : ∀ {S} → ⟦ done {S} ⟧ ≃ ⟦done⟧
done-semantics as = refl

-- Trace semantics of composition

_⟦⟫⟧_ : ∀ {S T U} → 
  (f : Trace S → Trace T) → (g : Trace T → Trace U) → 
    (Trace S) → (Trace U)
(f ⟦⟫⟧ g) as = g (f as)

⟫-semantics : ∀ {S T U} (P : S ⇒ T) (Q : T ⇒ U) →
    (⟦ P ⟫ Q ⟧ ≃ ⟦ P ⟧ ⟦⟫⟧ ⟦ Q ⟧)
⟫-semantics                 (id refl)  Q          as       = refl
⟫-semantics                  (inp P)    (id refl)  as       = refl
⟫-semantics                 (out b P)  (id refl)  as       = refl
⟫-semantics                 (inp P)    (out c Q)  as       = cong (_∷_ c) (⟫-semantics (inp P) Q as)
⟫-semantics                 (out b P)  (out c Q)  as       = cong (_∷_ c) (⟫-semantics (out b P) Q as)
⟫-semantics                 (out b P)  (inp Q)    as       = ⟫-semantics P (♭ Q b) as
⟫-semantics {Σ V F} {Σ W G} (inp P)    (inp Q)    []       = refl
⟫-semantics {Σ V F} {Σ W G} (inp P)    (inp Q)    (a ∷ as) = ⟫-semantics (♭ P a) (inp Q) as
⟫-semantics {I}     {T}     (inp {} P) (inp Q)    as
⟫-semantics {S}     {I}     (inp P)    (inp {} Q) as

-- Reflexivity is equal to identity

equiv-resp-done : ∀ {S} → ⟦ equiv (∼-refl {S}) ⟧ ≃ ⟦ done ⟧
equiv-resp-done {I}     as = refl
equiv-resp-done {Σ V F} [] = refl
equiv-resp-done {Σ V F} (a ∷ as) = cong (_∷_ a) (equiv-resp-done as)

-- Transitivity is equal to composition

equiv-resp-⟦⟫⟧ : ∀ {S T U} (S∼T : S ∼ T) (T∼U : T ∼ U) →
  ⟦ equiv (∼-trans S∼T T∼U) ⟧ ≃ ⟦ equiv S∼T ⟧ ⟦⟫⟧ ⟦ equiv T∼U ⟧
equiv-resp-⟦⟫⟧ I       I        as       = refl
equiv-resp-⟦⟫⟧ (Σ W F) (Σ .W G) []       = refl
equiv-resp-⟦⟫⟧ (Σ W F) (Σ .W G) (a ∷ as) = cong (_∷_ a) (equiv-resp-⟦⟫⟧ (♭ F a) (♭ G a) as)

equiv-resp-⟫ : ∀ {S T U} (S∼T : S ∼ T) (T∼U : T ∼ U) →
  ⟦ equiv (∼-trans S∼T T∼U) ⟧ ≃ ⟦ equiv S∼T ⟫ equiv T∼U ⟧
equiv-resp-⟫ S∼T T∼U as =
  begin
    ⟦ equiv (∼-trans S∼T T∼U) ⟧ as
  ≡⟨ equiv-resp-⟦⟫⟧ S∼T T∼U as ⟩
    (⟦ equiv S∼T ⟧ ⟦⟫⟧ ⟦ equiv T∼U ⟧) as
  ≡⟨ sym (⟫-semantics (equiv S∼T) (equiv T∼U) as) ⟩
    ⟦ equiv S∼T ⟫ equiv T∼U ⟧ as
  ∎

-- Equivalences form isos

equiv-is-iso : ∀ {S T} → (S∼T : S ∼ T) → (T∼S : T ∼ S) →
  ⟦ equiv S∼T ⟫ equiv T∼S ⟧ ≃ ⟦ done ⟧
equiv-is-iso S∼T T∼S as =
  begin
    ⟦ equiv S∼T ⟫ equiv T∼S ⟧ as
  ≡⟨ sym (equiv-resp-⟫ S∼T T∼S as) ⟩
    ⟦ equiv (∼-trans S∼T T∼S) ⟧ as
  ≡⟨ ⟦⟧-resp-∼ (∼-trans S∼T T∼S) ∼-refl as ⟩
    ⟦ equiv ∼-refl ⟧ as
  ≡⟨ equiv-resp-done as ⟩
    ⟦ done ⟧ as
  ∎

-- Composition respects ≃

⟫-resp-≃ : ∀ {S T U} (P₁ P₂ : S ⇒ T) (Q₁ Q₂ : T ⇒ U) → 
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

⟫-identity₁ : ∀ {S T} (P : S ⇒ T) → ⟦ done ⟫ P ⟧ ≃ ⟦ P ⟧
⟫-identity₁ P = ⟫-semantics done P

-- Right identity of composition

⟫-identity₂ : ∀ {S T} (P : S ⇒ T) → ⟦ P ⟫ done ⟧ ≃ ⟦ P ⟧
⟫-identity₂ P = ⟫-semantics P done

-- Associativity of composition

⟫-assoc : ∀ {S T U V} (P : S ⇒ T) (Q : T ⇒ U) (R : U ⇒ V) → 
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