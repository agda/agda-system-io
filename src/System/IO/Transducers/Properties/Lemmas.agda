open import Coinduction using ( ♭ )
open import Data.Empty using ( ⊥-elim )
open import System.IO.Transducers.Session using ( Session ; I ; Σ ; IsΣ ; Γ ; _/_ ; _∼_ )
open import System.IO.Transducers.Trace using ( Trace ; [] ; _∷_ ; ✓ )
open import System.IO.Transducers.Lazy using ( _⇒_ ; inp ; out ; id ; ⟦_⟧ ; _≃_ ; equiv )
open import System.IO.Transducers.Strict using ( Strict ; inp ; id )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; trans ; cong )
open import Relation.Nullary using ( Dec ; ¬_ ; yes ; no )

module System.IO.Transducers.Properties.Lemmas where

open Relation.Binary.PropositionalEquality.≡-Reasoning

-- ≃ is an equivalence

≃-refl : ∀ {S T} {f : Trace S → Trace T} → (f ≃ f)
≃-refl as = refl

≃-sym : ∀ {S T} {f g : Trace S → Trace T} →
  (f ≃ g) → (g ≃ f)
≃-sym f≃g as = sym (f≃g as)

≃-trans : ∀ {S T} {f g h : Trace S → Trace T} →
  (f ≃ g) → (g ≃ h) → (f ≃ h)
≃-trans f≃g g≃h as = trans (f≃g as) (g≃h as)

-- Completion is decidable

¬✓[] : ∀ {S} {isΣ : IsΣ S} → (¬ ✓ {S} [])
¬✓[] {I}     {} []
¬✓[] {Σ V F}    ([] {})

✓-tl : ∀ {S} {a : Γ S} {as : Trace (S / a)} → (✓ {S} (a ∷ as)) → (✓ as)
✓-tl (a ∷ ✓as) = ✓as

✓? : ∀ {S} (as : Trace S) → Dec (✓ as)
✓? {I}     []                 = yes []
✓? {Σ V F} []                 = no ¬✓[]
✓?         (a ∷ as) with ✓? as
✓?         (a ∷ as) | yes ✓as = yes (a ∷ ✓as)
✓?         (a ∷ as) | no ¬✓as = no (λ ✓a∷as → ¬✓as (✓-tl ✓a∷as))

-- Eta conversion for traces of type I

I-η : ∀ (as : Trace I) → (as ≡ [])
I-η [] = refl
I-η (() ∷ as)

-- All traces at type I are complete

I-✓ : ∀ (as : Trace I) → (✓ as)
I-✓ [] = []
I-✓ (() ∷ as)

-- Make a function reflective

liat : ∀ {S} → (Trace S) → (Trace S)
liat []           = []
liat (a ∷ [])     = []
liat (a ∷ b ∷ bs) = a ∷ liat (b ∷ bs)

incomplete : ∀ {S} → (Trace S) → (Trace S)
incomplete as with ✓? as
incomplete as | yes ✓as = liat as
incomplete as | no ¬✓as = as

reflective : ∀ {S T} → (Trace S → Trace T) → (Trace S → Trace T)
reflective f as with ✓? as
reflective f as | yes ✓as = f as
reflective f as | no ¬✓as = incomplete (f as)

liat-¬✓ : ∀ {S} a as → ¬ ✓ {S} (liat (a ∷ as))
liat-¬✓ {I}     () []       []
liat-¬✓ {Σ V F} a  []       ([] {})
liat-¬✓         a  (b ∷ bs) (.a ∷ ✓cs) = liat-¬✓ b bs ✓cs

incomplete-¬✓ : ∀ {S} {isΣ : IsΣ S} (as : Trace S) → ¬ ✓ (incomplete as)
incomplete-¬✓ as with ✓? as
incomplete-¬✓ {I}  {} [] | yes []
incomplete-¬✓ {Σ V F} [] | yes ([] {})
incomplete-¬✓ (a ∷ as)   | yes ✓a∷as = liat-¬✓ a as
incomplete-¬✓ as         | no ¬✓as = ¬✓as

reflective-refl-✓ : ∀ {S T} {isΣ : IsΣ T} (f : Trace S → Trace T) as → (✓ (reflective f as)) → (✓ as)
reflective-refl-✓             f as ✓bs with ✓? as 
reflective-refl-✓             f as ✓bs | yes ✓as = ✓as
reflective-refl-✓ {S} {Σ V F} f as ✓bs | no ¬✓as = ⊥-elim (incomplete-¬✓ (f as) ✓bs)
reflective-refl-✓ {S} {I}  {} f as ✓bs | no ¬✓as

reflective-≡-✓ : ∀ {S T} (f : Trace S → Trace T) {as} → (✓ as) → (reflective f as ≡ f as)
reflective-≡-✓ f {as} ✓as with ✓? as
reflective-≡-✓ f {as} ✓as | yes _   = refl
reflective-≡-✓ f {as} ✓as | no ¬✓as = ⊥-elim (¬✓as ✓as)

-- All transducers respect completed traces

⟦⟧-resp-✓ : ∀ {S T} (P : S ⇒ T) as → (✓ as) → (✓ (⟦ P ⟧ as))
⟦⟧-resp-✓ {Σ V F} (inp P)    (a ∷ as) (.a ∷ ✓as) = ⟦⟧-resp-✓ (♭ P a) as ✓as
⟦⟧-resp-✓         (out b P)  as       ✓as        = b ∷ ⟦⟧-resp-✓ P as ✓as
⟦⟧-resp-✓         (id refl)  as       ✓as        = ✓as
⟦⟧-resp-✓ {I}     (inp {} P) as       ✓as
⟦⟧-resp-✓ {Σ V F} (inp P)    []       ([] {})

-- All transducers reflect completed traces

⟦⟧-refl-✓ : ∀ {S T} (P : S ⇒ T) as → (✓ (⟦ P ⟧ as)) → (✓ as)
⟦⟧-refl-✓ {Σ V F}         (inp P)    (a ∷ as) bs        = a ∷ ⟦⟧-refl-✓ (♭ P a) as bs
⟦⟧-refl-✓                 (out b P)  as       (.b ∷ bs) = ⟦⟧-refl-✓ P as bs
⟦⟧-refl-✓                 (id refl)  as       bs        = bs
⟦⟧-refl-✓ {I}             (inp {} P) as       bs
⟦⟧-refl-✓ {Σ V F} {I}     (inp P {}) as       bs
⟦⟧-refl-✓ {Σ V F} {Σ W G} (inp P)    []       ([] {})

-- Strict transducers respect emptiness.

⟦⟧-resp-[] : ∀ {S T} {P : S ⇒ T} → (Strict P) → (⟦ P ⟧ [] ≡ [])
⟦⟧-resp-[] (inp P)   = refl
⟦⟧-resp-[] (id refl) = refl

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

-- IsEquiv P is inhabited whenever P is equivalent to an equivalence

data IsEquiv {S T : Session} (P : S ⇒ T) : Set₁ where
  isEquiv : (S∼T : S ∼ T) → (⟦ P ⟧ ≃ ⟦ equiv S∼T ⟧) → (IsEquiv P)

-- Equivalences are equivalent

≃-equiv : ∀ {S T} {P Q : S ⇒ T} → (IsEquiv P) → (IsEquiv Q) → (⟦ P ⟧ ≃ ⟦ Q ⟧)
≃-equiv {S} {T} {P} {Q} (isEquiv eq₁ P≃eq₁) (isEquiv eq₂ Q≃eq₂) as =
  begin
    ⟦ P ⟧ as
  ≡⟨ P≃eq₁ as ⟩
    ⟦ equiv eq₁ ⟧ as
  ≡⟨ ⟦⟧-resp-∼ eq₁ eq₂ as ⟩
    ⟦ equiv eq₂ ⟧ as
  ≡⟨ sym (Q≃eq₂ as) ⟩
    ⟦ Q ⟧ as
  ∎
  