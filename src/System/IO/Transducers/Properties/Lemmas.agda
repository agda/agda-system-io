{-# OPTIONS --universe-polymorphism #-}

open import Coinduction using ( ♭ )
open import System.IO.Transducers.Session using ( I ; Σ ; _∼_ )
open import System.IO.Transducers.Trace using ( Trace ; [] ; _∷_ ; ✓ )
open import System.IO.Transducers.Lazy using ( _⇒_ ; inp ; out ; id ; ⟦_⟧ ; _≃_ ; equiv )
open import System.IO.Transducers.Strict using ( Strict ; inp ; id )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; cong )

module System.IO.Transducers.Properties.Lemmas where

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x y u v r s} → x ≡ y → u ≡ v → r ≡ s → f x u r ≡ f y v s
cong₃ f refl refl refl = refl

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

⟦⟧-resp-∼ : ∀ {S} (eq : S ∼ S) as → ⟦ equiv eq ⟧ as ≡ as
⟦⟧-resp-∼ I       as       = refl
⟦⟧-resp-∼ (Σ V F) []       = refl
⟦⟧-resp-∼ (Σ V F) (a ∷ as) = cong (_∷_ a) (⟦⟧-resp-∼ (♭ F a) as)