{-# OPTIONS --universe-polymorphism #-}

open import Coinduction using ( ♭ )
open import System.IO.Transducers.Session using ( I ; Σ ; _∼_ )
open import System.IO.Transducers.Trace using ( Trace ; [] ; _∷_ ; ✓ )
open import System.IO.Transducers.Lazy using ( _⇒_ ; inp ; out ; id ; ⟦_⟧ ; _≃_ ; equiv )
open import System.IO.Transducers.Strict using ( Strict ; inp ; id )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; trans ; cong )

module System.IO.Transducers.Properties.Lemmas where

-- ≃ is an equivalence

≃-refl : ∀ {S T} {f : Trace S → Trace T} → (f ≃ f)
≃-refl as = refl

≃-sym : ∀ {S T} {f g : Trace S → Trace T} →
  (f ≃ g) → (g ≃ f)
≃-sym f≃g as = sym (f≃g as)

≃-trans : ∀ {S T} {f g h : Trace S → Trace T} →
  (f ≃ g) → (g ≃ h) → (f ≃ h)
≃-trans f≃g g≃h as = trans (f≃g as) (g≃h as)

-- All transducers respect completed traces

⟦⟧-resp-✓ : ∀ {S T} (P : S ⇒ T) {as} → (✓ as) → (✓ (⟦ P ⟧ as))
⟦⟧-resp-✓ {I} (inp {} P) as
⟦⟧-resp-✓ {Σ V F} (inp P) ([] {})
⟦⟧-resp-✓ {Σ V F} (inp P) (a ∷ as) = ⟦⟧-resp-✓ (♭ P a) as
⟦⟧-resp-✓ (out b P) as = b ∷ ⟦⟧-resp-✓ P as
⟦⟧-resp-✓ (id refl) as = as

-- Strict transducers respect emptiness.

⟦⟧-resp-[] : ∀ {S T} {P : S ⇒ T} → (Strict P) → ∀ {as} → (as ≡ []) → (⟦ P ⟧ as ≡ [])
⟦⟧-resp-[] (inp P)   refl = refl
⟦⟧-resp-[] (id refl) refl = refl

-- Any transducer which respects emptiness is strict.

⟦⟧-resp-[]⁻¹ : ∀ {S T} (P : S ⇒ T) → (∀ {as} → (as ≡ []) → (⟦ P ⟧ as ≡ [])) → (Strict P)
⟦⟧-resp-[]⁻¹ (inp P)   H = inp P
⟦⟧-resp-[]⁻¹ (out b P) H with H refl
⟦⟧-resp-[]⁻¹ (out b P) H | ()
⟦⟧-resp-[]⁻¹ (id refl) H = id refl

-- Coherence wrt ∼

⟦⟧-resp-∼ : ∀ {S T} (eq₁ eq₂ : S ∼ T) → ⟦ equiv eq₁ ⟧ ≃ ⟦ equiv eq₂ ⟧ 
⟦⟧-resp-∼ I       I        as       = refl
⟦⟧-resp-∼ (Σ V F) (Σ .V G) []       = refl
⟦⟧-resp-∼ (Σ V F) (Σ .V G) (a ∷ as) = cong (_∷_ a) (⟦⟧-resp-∼ (♭ F a) (♭ G a) as)