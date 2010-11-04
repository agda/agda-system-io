open import Coinduction using ( ♭ )
open import Data.Empty using ( ⊥-elim )
open import Data.Sum using ( _⊎_ ; inj₁ ; inj₂ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; cong ; cong₂ )
open import Relation.Nullary using ( ¬_ ; Dec ; yes ; no )
open import System.IO.Transducers using ( _⇒_ ; inp ; out ; done ; _⟫_ ; assoc ; delay ; _[&]_ ; ⟦_⟧ ; _≃_ )
open import System.IO.Transducers.Session using ( I ; Σ ; _&_ )
open import System.IO.Transducers.Trace using ( Trace ; ✓ ; [] ; _∷_ )
open import System.IO.Transducers.Properties.Category using ( ⟦done⟧ ; _⟦⟫⟧_ ; ⟫-semantics )

module System.IO.Transducers.Properties.Monoidal where

open Relation.Binary.PropositionalEquality.≡-Reasoning

-- Concatenation of traces

_++_ : ∀ {S T} → (Trace S) → (Trace T) → (Trace (S & T))
_++_ {I}     []       bs = bs
_++_ {Σ V F} []       bs = []
_++_ {Σ V F} (a ∷ as) bs = a ∷ (as ++ bs)

-- Projection of traces

front : ∀ {S T} → (Trace (S & T)) → (Trace S)
front {I}     as       = []
front {Σ V F} []       = []
front {Σ V F} (a ∷ as) = a ∷ front as

back : ∀ {S T} → (Trace (S & T)) → (Trace T)
back {I}     as       = as
back {Σ V F} []       = []
back {Σ V F} (a ∷ as) = back {♭ F a} as

-- Termination is decidable:

✓? : ∀ {S} → (as : Trace S) → (Dec (✓ as))
✓? = {!!}

-- Beta and eta equivalence for concatenation
-- Note that β₂ only holds when as is completed or bs is empty.

++-β₁ : ∀ {S T} (as : Trace S) (bs : Trace T) → (front (as ++ bs) ≡ as)
++-β₁ {I}     []       bs = refl
++-β₁ {Σ V F} []       bs = refl
++-β₁ {Σ V F} (a ∷ as) bs = cong (_∷_ a) (++-β₁ as bs)

++-β₂-✓ : ∀ {S T} {as : Trace S} → (✓ as) → (bs : Trace T) → (back {S} (as ++ bs) ≡ bs)
++-β₂-✓ {I}     []       bs = refl
++-β₂-✓ {Σ V F} (a ∷ as) bs = ++-β₂-✓ as bs

++-β₂-[] : ∀ {S T} (as : Trace S) {bs : Trace T} → (bs ≡ []) → (back {S} (as ++ bs) ≡ bs)
++-β₂-[] {I}     []       refl  = refl
++-β₂-[] {Σ V F} []       refl  = refl
++-β₂-[] {Σ V F} (a ∷ as) refl = ++-β₂-[] as refl

++-η : ∀ {S T} (as : Trace (S & T)) → (front {S} as ++ back {S} as ≡ as)
++-η {I}     as = refl
++-η {Σ V F} [] = refl
++-η {Σ V F} (a ∷ as) = cong (_∷_ a) (++-η {♭ F a} as)

-- Either front as is complete, or back as is empty.

front✓/back[] : ∀ {S T} as → (✓ (front {S} {T} as)) ⊎ (back {S} {T} as ≡ [])
front✓/back[] {I} as                        = inj₁ []
front✓/back[] {Σ W F} []                    = inj₂ refl
front✓/back[] {Σ W F} (a ∷ as) with front✓/back[] {♭ F a} as
front✓/back[] {Σ W F} (a ∷ as) | inj₁ bs✓   = inj₁ (a ∷ bs✓)
front✓/back[] {Σ W F} (a ∷ as) | inj₂ cs≡[] = inj₂ cs≡[]

-- Semantics of tensor

_⟦[&]⟧_ : ∀ {S T U V} →
  (f : Trace S → Trace T) → (g : Trace U → Trace V) → 
    (Trace (S & U)) → (Trace (T & V))
_⟦[&]⟧_ {S} f g as = f (front as) ++ g (back {S} as)

-- & is a functor in its left argument if f respects completion

⟦[&]⟧-resp-⟦⟫⟧₁ : ∀ {S T U V} → 
  (f : Trace S → Trace T) → (g : Trace T → Trace U) → 
    (∀ {bs} → (✓ bs) → (✓ (f bs))) →
      (((f ⟦⟫⟧ g) ⟦[&]⟧ ⟦done⟧ {V}) ≃ (f ⟦[&]⟧ ⟦done⟧ {V}) ⟦⟫⟧ (g ⟦[&]⟧ ⟦done⟧ {V}))
⟦[&]⟧-resp-⟦⟫⟧₁ {S} {T} {U} {V} f g f✓ as with front✓/back[] {S} {V} as
⟦[&]⟧-resp-⟦⟫⟧₁ {S} {T} {U} {V} f g f✓ as | inj₁ ✓bs =
  cong₂ _++_ 
    (cong g (sym (++-β₁ (f (front as)) (back {S} as)))) 
    (sym (++-β₂-✓ (f✓ ✓bs) (back {S} as)))
⟦[&]⟧-resp-⟦⟫⟧₁ {S} {T} {U} {V} f g f✓ as | inj₂ cs≡[] = 
  cong₂ _++_ 
    (cong g (sym (++-β₁ (f (front as)) (back {S} as)))) 
    (sym (++-β₂-[] (f (front as)) cs≡[])) 

-- & is a functor in its right argument

⟦[&]⟧-resp-⟦⟫⟧₂ : ∀ {S T U V} → 
  (f : Trace T → Trace U) → (g : Trace U → Trace V) →
    ((⟦done⟧ {S} ⟦[&]⟧ (f ⟦⟫⟧ g)) ≃ ((⟦done⟧ {S} ⟦[&]⟧ f) ⟦⟫⟧ (⟦done⟧ {S} ⟦[&]⟧ g)))
⟦[&]⟧-resp-⟦⟫⟧₂ {I}     f g as       = refl
⟦[&]⟧-resp-⟦⟫⟧₂ {Σ W F} f g []       = refl
⟦[&]⟧-resp-⟦⟫⟧₂ {Σ W F} f g (a ∷ as) = cong (_∷_ a) (⟦[&]⟧-resp-⟦⟫⟧₂ {♭ F a} f g as)

-- & is a functor if f₁ respects completion and f₂ respects emptiness

⟦[&]⟧-resp-⟦⟫⟧ : ∀ {S₁ S₂ T₁ T₂ U₁ U₂} → 
  (f₁ : Trace S₁ → Trace T₁) → (g₁ : Trace T₁ → Trace U₁) → 
  (f₂ : Trace S₂ → Trace T₂) → (g₂ : Trace T₂ → Trace U₂) → 
    (∀ {bs} → (✓ bs) → (✓ (f₁ bs))) → (∀ {bs} → (bs ≡ []) → (f₂ bs ≡ [])) → 
      (((f₁ ⟦⟫⟧ g₁) ⟦[&]⟧ (f₂ ⟦⟫⟧ g₂)) ≃ (f₁ ⟦[&]⟧ f₂) ⟦⟫⟧ (g₁ ⟦[&]⟧ g₂))
⟦[&]⟧-resp-⟦⟫⟧ {S₁} {S₂} {T₁} {T₂} f₁ g₁ f₂ g₂ f₁✓ f₂[] as with front✓/back[] {S₁} {S₂} as
⟦[&]⟧-resp-⟦⟫⟧ {S₁} {S₂} {T₁} {T₂} f₁ g₁ f₂ g₂ f₁✓ f₂[] as | inj₁ ✓as₁ =
  cong₂ _++_ 
    (cong g₁ (sym (++-β₁ (f₁ (front as)) (f₂ (back {S₁} as))))) 
    (cong g₂ (sym (++-β₂-✓ (f₁✓ ✓as₁) (f₂ (back {S₁} as))))) 
⟦[&]⟧-resp-⟦⟫⟧ {S₁} {S₂} {T₁} {T₂} f₁ g₁ f₂ g₂ f₁✓ f₂[] as | inj₂ as₂≡[] = 
  cong₂ _++_
    (cong g₁ (sym (++-β₁ (f₁ (front as)) (f₂ (back {S₁} as))))) 
    (cong g₂ (sym (++-β₂-[] (f₁ (front as)) (f₂[] as₂≡[]))))

-- -- Semantics of associativity

-- ⟦assoc⟧ : ∀ {S T U} → (Trace (S & (T & U)) → Trace ((S & T) & U))
-- ⟦assoc⟧ {[]}     as       = as
-- ⟦assoc⟧ {W ∷ Ss} []       = []
-- ⟦assoc⟧ {W ∷ Ss} (a ∷ as) = a ∷ ⟦assoc⟧ {♭ Ss a} as

-- assoc-semantics : ∀ {S T U} → (⟦ assoc {S} {T} {U} ⟧ ≃ ⟦assoc⟧ {S} {T} {U})
-- assoc-semantics {[]}     as       = refl
-- assoc-semantics {W ∷ Ss} []       = refl
-- assoc-semantics {W ∷ Ss} (a ∷ as) = cong (_∷_ a) (assoc-semantics {♭ Ss a} as)

-- -- Semantics of delay

-- ⟦delay⟧ : ∀ S {T U} → (Trace T → Trace U) → (Trace (S & T) → Trace U)
-- ⟦delay⟧ S f as = f (back {S} as)

-- delay-semantics : ∀ S {T U} → (P : T ⇒ U) → (⟦ delay S P ⟧ ≃ ⟦delay⟧ S ⟦ P ⟧)
-- delay-semantics []       P         as       = refl
-- delay-semantics (W ∷ Ss) (inp F)   []       = refl
-- delay-semantics (W ∷ Ss) (inp F)   (a ∷ as) = delay-semantics (♭ Ss a) (inp F) as
-- delay-semantics (W ∷ Ss) (out b P) as       = cong (_∷_ b) (delay-semantics (W ∷ Ss) P as)
-- delay-semantics (W ∷ Ss) done      []       = refl
-- delay-semantics (W ∷ Ss) done      (a ∷ as) = delay-semantics (♭ Ss a) done as

-- -- Semantics for tensor

-- _⟦[&]⟧_ : ∀ {S T U V} →
--   (f : Trace S → Trace T) → (g : Trace U → Trace V) → 
--     (Trace (S & U)) → (Trace (T & V))
-- _⟦[&]⟧_ {S} f g as = f (front as) ++ g (back {S} as)

-- [&]-semantics : ∀ {S T U V} →
--   (P : S ⇒ T) → (Q : U ⇒ V) → 
--     (⟦ P [&] Q ⟧ ≃ ⟦ P ⟧ ⟦[&]⟧ ⟦ Q ⟧)
-- [&]-semantics {S} {T = []} P         Q as with ⟦ P ⟧ (front as)
-- [&]-semantics {S} {T = []} P         Q as | []  = delay-semantics S Q as
-- [&]-semantics {T = V ∷ Ts} (inp F) Q []         = refl
-- [&]-semantics {T = V ∷ Ts} (inp F) Q (a ∷ as)   = [&]-semantics (♭ F a) Q as
-- [&]-semantics {T = V ∷ Ts} (out b P) Q as       = cong (_∷_ b) ([&]-semantics P Q as)
-- [&]-semantics {T = V ∷ Ts} done      Q []       = refl
-- [&]-semantics {T = V ∷ Ts} done      Q (a ∷ as) = cong (_∷_ a) ([&]-semantics {T = ♭ Ts a} done Q as)

-- -- Tensor is a functor -- it respects identity:

-- [&]-resp-done : ∀ {S T} → (⟦ done {S} [&] done {T} ⟧ ≃ ⟦ done ⟧)
-- [&]-resp-done {S} {T} as = 
--   begin
--     ⟦ done {S} [&] done {T} ⟧ as
--   ≡⟨ [&]-semantics (done {S}) (done {T}) as ⟩
--     front {S} as ++ back {S} as
--   ≡⟨ ++-η {S} as ⟩
--     as
--   ∎

-- -- and composition:

-- [&]-resp-⟫ : ∀ {S₁ T₁ U₁ S₂ T₂ U₂} → 
--   (P₁ : S₁ ⇒ T₁) → (P₂ : S₂ ⇒ T₂) → (Q₁ : T₁ ⇒ U₁) → (Q₂ : T₂ ⇒ U₂) →
--     (⟦ (P₁ ⟫ Q₁) [&] (P₂ ⟫ Q₂) ⟧ ≃ ⟦ (P₁ [&] P₂) ⟫ (Q₁ [&] Q₂) ⟧)
-- [&]-resp-⟫ {S₁} {T₁} P₁ P₂ Q₁ Q₂ as = 
--   begin
--     ⟦ (P₁ ⟫ Q₁) [&] (P₂ ⟫ Q₂) ⟧ as
--   ≡⟨ [&]-semantics (P₁ ⟫ Q₁) (P₂ ⟫ Q₂) as ⟩
--     ⟦ P₁ ⟫ Q₁ ⟧ (front as) ++ ⟦ P₂ ⟫ Q₂ ⟧ (back {S₁} as)
--   ≡⟨ cong₂ _++_ (⟫-semantics P₁ Q₁ (front as)) (⟫-semantics P₂ Q₂ (back {S₁} as)) ⟩
--     ⟦ Q₁ ⟧ (⟦ P₁ ⟧ (front as)) ++ ⟦ Q₂ ⟧ (⟦ P₂ ⟧ (back {S₁} as))
--   ≡⟨ cong₂ _++_ (cong ⟦ Q₁ ⟧ (sym (++-β₁ (⟦ P₁ ⟧ (front as)) (⟦ P₂ ⟧ (back {S₁} as))))) 
--        (cong ⟦ Q₂ ⟧ (sym (++-β₂ (⟦ P₁ ⟧ (front as)) (⟦ P₂ ⟧ (back {S₁} as))))) ⟩
--     ⟦ Q₁ ⟧ (front (⟦ P₁ ⟧ (front as) ++ ⟦ P₂ ⟧ (back {S₁} as))) ++
--       ⟦ Q₂ ⟧ (back {T₁} (⟦ P₁ ⟧ (front as) ++ ⟦ P₂ ⟧ (back {S₁} as)))
--   ≡⟨ sym ([&]-semantics Q₁ Q₂ (⟦ P₁ ⟧ (front as) ++ ⟦ P₂ ⟧ (back {S₁} as))) ⟩
--     ⟦ Q₁ [&] Q₂ ⟧ (⟦ P₁ ⟧ (front as) ++ ⟦ P₂ ⟧ (back {S₁} as))
--   ≡⟨ cong ⟦ Q₁ [&] Q₂ ⟧ (sym ([&]-semantics P₁ P₂ as)) ⟩
--     ⟦ Q₁ [&] Q₂ ⟧ (⟦ P₁ [&] P₂ ⟧ as)
--   ≡⟨ sym (⟫-semantics (P₁ [&] P₂) (Q₁ [&] Q₂) as) ⟩
--     ⟦ P₁ [&] P₂ ⟫ Q₁ [&] Q₂ ⟧ as
--   ∎