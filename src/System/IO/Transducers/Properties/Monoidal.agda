open import Coinduction using ( ♭ ; ♯_ )
open import Data.Empty using ( ⊥-elim )
open import Data.Sum using ( _⊎_ ; inj₁ ; inj₂ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; cong ; cong₂ )
open import Relation.Nullary using ( ¬_ ; Dec ; yes ; no )
open import System.IO.Transducers.Lazy using ( _⇒_ ; inp ; out ; id ; done ; _⟫_ ; equiv ; assoc ; assoc⁻¹ ; unit₁ ; unit₁⁻¹ ; unit₂ ; unit₂⁻¹ ; delay ; _[&]_ ; ⟦_⟧ ; _≃_ )
open import System.IO.Transducers.Strict using ( Strict )
open import System.IO.Transducers.Session using ( I ; Σ ; _∼_ ; ∼-refl ; ∼-trans ; ∼-sym ; _&_ )
  renaming ( unit₁ to ∼-unit₁ ; unit₂ to ∼-unit₂ ; assoc to ∼-assoc )
open import System.IO.Transducers.Trace using ( Trace ; ✓ ; [] ; _∷_ )
open import System.IO.Transducers.Properties.Category using ( ⟦done⟧ ; _⟦⟫⟧_ ; ⟫-semantics ; equiv-resp-done ; equiv-resp-⟫ ; equiv-is-iso )
open import System.IO.Transducers.Properties.Lemmas using ( ≃-refl ; ≃-sym ; ⟦⟧-resp-✓ ; ⟦⟧-resp-[] ; ⟦⟧-resp-∼ )

module System.IO.Transducers.Properties.Monoidal where

open Relation.Binary.PropositionalEquality.≡-Reasoning

-- & respects ∼

&-resp-∼ : ∀ {S T U V} → (S ∼ T) → (U ∼ V) → ((S & U) ∼ (T & V))
&-resp-∼ I       U∼V = U∼V
&-resp-∼ (Σ V F) U∼V = Σ V (♯ λ a → &-resp-∼ (♭ F a) U∼V)

-- Concatenation of traces

_++_ : ∀ {S T} → (Trace S) → (Trace T) → (Trace (S & T))
_++_ {I}     []        bs = bs
_++_ {I}     (() ∷ as) bs
_++_ {Σ V F} []        bs = []
_++_ {Σ V F} (a ∷ as ) bs = a ∷ (as ++ bs)

-- Projection of traces

front : ∀ {S T} → (Trace (S & T)) → (Trace S)
front {I}     as       = []
front {Σ V F} []       = []
front {Σ V F} (a ∷ as) = a ∷ front as

back : ∀ {S T} → (Trace (S & T)) → (Trace T)
back {I}     as       = as
back {Σ V F} []       = []
back {Σ V F} (a ∷ as) = back {♭ F a} as

-- Semantics of delay

⟦delay⟧ : ∀ S {T U} → (Trace T → Trace U) →
  (Trace (S & T) → Trace U)
⟦delay⟧ S f as = f (back {S} as)

delay-semantics : ∀ S {T U} → (P : T ⇒ U) → (⟦ delay S P ⟧ ≃ ⟦delay⟧ S ⟦ P ⟧)
delay-semantics I       P         as       = refl
delay-semantics (Σ V F) (inp P)   []       = refl
delay-semantics (Σ V F) (inp P)   (a ∷ as) = delay-semantics (♭ F a) (inp P) as
delay-semantics (Σ V F) (out b P) as       = cong (_∷_ b) (delay-semantics (Σ V F) P as)
delay-semantics (Σ V F) (id refl) []       = refl
delay-semantics (Σ V F) (id refl) (a ∷ as) = delay-semantics (♭ F a) done as

-- Semantics of tensor

_⟦[&]⟧_ : ∀ {S T U V} →
  (f : Trace S → Trace T) → (g : Trace U → Trace V) → 
    (Trace (S & U)) → (Trace (T & V))
_⟦[&]⟧_ {S} f g as = f (front as) ++ g (back {S} as)

[&]-semantics : ∀ {S T U V} (P : S ⇒ T) (Q : U ⇒ V) → 
  ⟦ P [&] Q ⟧ ≃ ⟦ P ⟧ ⟦[&]⟧ ⟦ Q ⟧
[&]-semantics {S}      {I}     P          Q as with ⟦ P ⟧ (front {S} as)
[&]-semantics {S}      {I}     P          Q as | []  = delay-semantics S Q as
[&]-semantics {S}      {I}     P          Q as | () ∷ bs
[&]-semantics {I}      {Σ W G} (inp {} P) Q as
[&]-semantics {Σ V F}  {Σ W G} (inp P)    Q []       = refl
[&]-semantics {Σ V F}  {Σ W G} (inp P)    Q (a ∷ as) = [&]-semantics (♭ P a) Q as
[&]-semantics {I}      {Σ W G} (out b P)  Q as       = cong (_∷_ b) ([&]-semantics P Q as)
[&]-semantics {Σ V F}  {Σ W G} (out b P)  Q as       = cong (_∷_ b) ([&]-semantics P Q as)
[&]-semantics .{Σ W G} {Σ W G} (id refl)  Q []       = refl
[&]-semantics .{Σ W G} {Σ W G} (id refl)  Q (a ∷ as) = cong (_∷_ a) ([&]-semantics (done {♭ G a}) Q as)

-- Beta and eta equivalence for concatenation
-- Note that β₂ only holds when as is completed or bs is empty.

++-β₁ : ∀ {S T} (as : Trace S) (bs : Trace T) → (front (as ++ bs) ≡ as)
++-β₁ {I}     []        bs = refl
++-β₁ {I}     (() ∷ as) bs
++-β₁ {Σ V F} []        bs = refl
++-β₁ {Σ V F} (a ∷ as)  bs = cong (_∷_ a) (++-β₁ as bs)

++-β₂-✓ : ∀ {S T} {as : Trace S} → (✓ as) → (bs : Trace T) → (back {S} (as ++ bs) ≡ bs)
++-β₂-✓ {I}     []        bs = refl
++-β₂-✓ {I}     (() ∷ as) bs
++-β₂-✓ {Σ V F} ([] {})   bs
++-β₂-✓ {Σ V F} (a ∷ as)  bs = ++-β₂-✓ as bs

++-β₂-[] : ∀ {S T} (as : Trace S) {bs : Trace T} → (bs ≡ []) → (back {S} (as ++ bs) ≡ bs)
++-β₂-[] {I}     []        refl  = refl
++-β₂-[] {I}     (() ∷ as) refl
++-β₂-[] {Σ V F} []        refl  = refl
++-β₂-[] {Σ V F} (a ∷ as)  refl = ++-β₂-[] as refl

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

-- Equivalence respects &

equiv-resp-⟦[&]⟧ : ∀ {S T U V} (S∼T : S ∼ T) (U∼V : U ∼ V) →
  ⟦ equiv (&-resp-∼ S∼T U∼V) ⟧ ≃ ⟦ equiv S∼T ⟧ ⟦[&]⟧ ⟦ equiv U∼V ⟧
equiv-resp-⟦[&]⟧ I       U∼V as       = refl
equiv-resp-⟦[&]⟧ (Σ V F) U∼V []       = refl
equiv-resp-⟦[&]⟧ (Σ V F) U∼V (a ∷ as) = cong (_∷_ a) (equiv-resp-⟦[&]⟧ (♭ F a) U∼V as)

equiv-resp-[&] : ∀ {S T U V} (S∼T : S ∼ T) (U∼V : U ∼ V) →
  ⟦ equiv (&-resp-∼ S∼T U∼V) ⟧ ≃ ⟦ equiv S∼T [&] equiv U∼V ⟧
equiv-resp-[&] S∼T U∼V as =
  begin
    ⟦ equiv (&-resp-∼ S∼T U∼V) ⟧ as
  ≡⟨ equiv-resp-⟦[&]⟧ S∼T U∼V as ⟩
    (⟦ equiv S∼T ⟧ ⟦[&]⟧ ⟦ equiv U∼V ⟧) as
  ≡⟨ sym ([&]-semantics (equiv S∼T) (equiv U∼V) as) ⟩
    ⟦ equiv S∼T [&] equiv U∼V ⟧ as
  ∎

-- Tensor respects ≃

[&]-resp-≃ : ∀ {S T U V} {P₁ P₂ : S ⇒ T} {Q₁ Q₂ : U ⇒ V} → 
  (⟦ P₁ ⟧ ≃ ⟦ P₂ ⟧) → (⟦ Q₁ ⟧ ≃ ⟦ Q₂ ⟧) →
    (⟦ P₁ [&] Q₁ ⟧ ≃ ⟦ P₂ [&] Q₂ ⟧)
[&]-resp-≃ {S} {T} {U} {V} {P₁} {P₂} {Q₁} {Q₂} P₁≃P₂ Q₁≃Q₂ as =
  begin
    ⟦ P₁ [&] Q₁ ⟧ as
  ≡⟨ [&]-semantics P₁ Q₁ as ⟩
    ⟦ P₁ ⟧ (front as) ++ ⟦ Q₁ ⟧ (back {S} as)
  ≡⟨ cong₂ _++_ (P₁≃P₂ (front as)) (Q₁≃Q₂ (back {S} as)) ⟩
    ⟦ P₂ ⟧ (front as) ++ ⟦ Q₂ ⟧ (back {S} as)
  ≡⟨ sym ([&]-semantics P₂ Q₂ as) ⟩
    ⟦ P₂ [&] Q₂ ⟧ as
  ∎

-- Tensor respects identity

[&]-resp-done : ∀ S T → ⟦ done {S} [&] done {T} ⟧ ≃ ⟦ done {S & T} ⟧
[&]-resp-done S T as =
  begin
    ⟦ done {S} [&] done {T} ⟧ as
  ≡⟨ [&]-semantics (done {S}) (done {T}) as ⟩
    front {S} as ++ back {S} as
  ≡⟨ ++-η {S} as ⟩
    as
  ∎

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

-- Category of lazy transducers is premonoidal

[&]-resp-⟫₁ : ∀ {S T U V} (P : S ⇒ T) → (Q : T ⇒ U) → 
  ⟦ (P ⟫ Q) [&] done {V} ⟧ ≃ ⟦ (P [&] done {V}) ⟫ (Q [&] done {V}) ⟧
[&]-resp-⟫₁ P Q as = 
  begin
    ⟦ (P ⟫ Q) [&] id refl ⟧ as
  ≡⟨ [&]-semantics (P ⟫ Q) (id refl) as ⟩
    (⟦ P ⟫ Q ⟧ ⟦[&]⟧ ⟦ id refl ⟧) as
  ≡⟨ cong₂ _++_ (⟫-semantics P Q (front as)) refl ⟩
    ((⟦ P ⟧ ⟦⟫⟧ ⟦ Q ⟧) ⟦[&]⟧ ⟦ id refl ⟧) as
  ≡⟨ ⟦[&]⟧-resp-⟦⟫⟧₁ ⟦ P ⟧ ⟦ Q ⟧ (⟦⟧-resp-✓ P) as ⟩
    ((⟦ P ⟧ ⟦[&]⟧ ⟦ id refl ⟧) ⟦⟫⟧ (⟦ Q ⟧ ⟦[&]⟧ ⟦ id refl ⟧)) as
  ≡⟨ sym ([&]-semantics Q (id refl) ((⟦ P ⟧ ⟦[&]⟧ ⟦ id refl ⟧) as)) ⟩
    ((⟦ P ⟧ ⟦[&]⟧ ⟦ id refl ⟧) ⟦⟫⟧ (⟦ Q [&] id refl ⟧)) as
  ≡⟨ sym (cong ⟦ Q [&] id refl ⟧ ([&]-semantics P (id refl) as)) ⟩
    ((⟦ P [&] id refl ⟧) ⟦⟫⟧ (⟦ Q [&] id refl ⟧)) as
  ≡⟨ sym (⟫-semantics (P [&] id refl) (Q [&] id refl) as) ⟩
    ⟦ P [&] id refl ⟫ Q [&] id refl ⟧ as
  ∎

[&]-resp-⟫₂ : ∀ {S T U V} (P : T ⇒ U) → (Q : U ⇒ V) → 
  ⟦ done {S} [&] (P ⟫ Q) ⟧ ≃ ⟦ (done {S} [&] P) ⟫ (done {S} [&] Q) ⟧
[&]-resp-⟫₂ {S} P Q as = 
  begin
    ⟦ done {S} [&] (P ⟫ Q) ⟧ as
  ≡⟨ [&]-semantics (done {S}) (P ⟫ Q) as ⟩
    (⟦ done {S} ⟧ ⟦[&]⟧ ⟦ P ⟫ Q ⟧) as
  ≡⟨ cong₂ (_++_ {S}) refl (⟫-semantics P Q (back {S} as)) ⟩
    (⟦ done {S} ⟧ ⟦[&]⟧ (⟦ P ⟧ ⟦⟫⟧ ⟦ Q ⟧)) as
  ≡⟨ ⟦[&]⟧-resp-⟦⟫⟧₂ {S} ⟦ P ⟧ ⟦ Q ⟧ as ⟩
    ((⟦ done {S} ⟧ ⟦[&]⟧ ⟦ P ⟧) ⟦⟫⟧ (⟦ done {S} ⟧ ⟦[&]⟧ ⟦ Q ⟧)) as
  ≡⟨ sym ([&]-semantics (done {S}) Q ((⟦ done {S} ⟧ ⟦[&]⟧ ⟦ P ⟧) as)) ⟩
    ((⟦ done {S} ⟧ ⟦[&]⟧ ⟦ P ⟧) ⟦⟫⟧ (⟦ done {S} [&] Q ⟧)) as
  ≡⟨ sym (cong ⟦ done {S} [&] Q ⟧ ([&]-semantics (done {S}) P as)) ⟩
    ((⟦ done {S} [&] P ⟧) ⟦⟫⟧ (⟦ done {S} [&] Q ⟧)) as
  ≡⟨ sym (⟫-semantics (done {S} [&] P) (done {S} [&] Q) as) ⟩
    ⟦ done {S} [&] P ⟫ done {S} [&] Q ⟧ as
  ∎
  
-- Category of strict transducers is monoidal

[&]-resp-⟫ : ∀ {S₁ S₂ T₁ T₂ U₁ U₂} 
  (P₁ : S₁ ⇒ T₁) (Q₁ : T₁ ⇒ U₁) (P₂ : S₂ ⇒ T₂) (Q₂ : T₂ ⇒ U₂) → (Strict P₂) →
    ⟦ (P₁ ⟫ Q₁) [&] (P₂ ⟫ Q₂) ⟧ ≃ ⟦ (P₁ [&] P₂) ⟫ (Q₁ [&] Q₂) ⟧
[&]-resp-⟫ P₁ Q₁ P₂ Q₂ #P₂ as = 
  begin
    ⟦ (P₁ ⟫ Q₁) [&] (P₂ ⟫ Q₂) ⟧ as
  ≡⟨ [&]-semantics (P₁ ⟫ Q₁) (P₂ ⟫ Q₂) as ⟩
    (⟦ P₁ ⟫ Q₁ ⟧ ⟦[&]⟧ ⟦ P₂ ⟫ Q₂ ⟧) as
  ≡⟨ cong₂ _++_ (⟫-semantics P₁ Q₁ _) (⟫-semantics P₂ Q₂ _) ⟩
    ((⟦ P₁ ⟧ ⟦⟫⟧ ⟦ Q₁ ⟧) ⟦[&]⟧ (⟦ P₂ ⟧ ⟦⟫⟧ ⟦ Q₂ ⟧)) as
  ≡⟨ ⟦[&]⟧-resp-⟦⟫⟧ ⟦ P₁ ⟧ ⟦ Q₁ ⟧ ⟦ P₂ ⟧ ⟦ Q₂ ⟧ (⟦⟧-resp-✓ P₁) (⟦⟧-resp-[] #P₂) as ⟩
    ((⟦ P₁ ⟧ ⟦[&]⟧ ⟦ P₂ ⟧) ⟦⟫⟧ (⟦ Q₁ ⟧ ⟦[&]⟧ ⟦ Q₂ ⟧)) as
  ≡⟨ sym ([&]-semantics Q₁ Q₂ ((⟦ P₁ ⟧ ⟦[&]⟧ ⟦ P₂ ⟧) as)) ⟩
    ((⟦ P₁ ⟧ ⟦[&]⟧ ⟦ P₂ ⟧) ⟦⟫⟧ (⟦ Q₁ [&] Q₂ ⟧)) as
  ≡⟨ sym (cong ⟦ Q₁ [&] Q₂ ⟧ ([&]-semantics P₁ P₂ as)) ⟩
    ((⟦ P₁ [&] P₂ ⟧) ⟦⟫⟧ (⟦ Q₁ [&] Q₂ ⟧)) as
  ≡⟨ sym (⟫-semantics (P₁ [&] P₂) (Q₁ [&] Q₂) as) ⟩
    ⟦ P₁ [&] P₂ ⟫ Q₁ [&] Q₂ ⟧ as
  ∎

-- Isomorphisms

unit₁-iso : ∀ {S} → ⟦ unit₁ {S} ⟫ unit₁⁻¹ {S} ⟧ ≃ ⟦ done ⟧
unit₁-iso = equiv-is-iso ∼-unit₁ (∼-sym ∼-unit₁)

unit₁⁻¹-iso : ∀ {S} → ⟦ unit₁⁻¹ {S} ⟫ unit₁ {S} ⟧ ≃ ⟦ done ⟧
unit₁⁻¹-iso = equiv-is-iso (∼-sym ∼-unit₁) ∼-unit₁

unit₂-iso : ∀ {S} → ⟦ unit₂ {S} ⟫ unit₂⁻¹ {S} ⟧ ≃ ⟦ done ⟧
unit₂-iso {S} = equiv-is-iso (∼-unit₂ {S}) (∼-sym (∼-unit₂ {S}))

unit₂⁻¹-iso : ∀ {S} → ⟦ unit₂⁻¹ {S} ⟫ unit₂ {S} ⟧ ≃ ⟦ done ⟧
unit₂⁻¹-iso {S} = equiv-is-iso (∼-sym (∼-unit₂ {S})) (∼-unit₂ {S})

assoc-iso : ∀ {S T U} → ⟦ assoc {S} {T} {U} ⟫ assoc⁻¹ {S} {T} {U} ⟧ ≃ ⟦ done ⟧
assoc-iso {S} {T} = equiv-is-iso (∼-assoc {S} {T}) (∼-sym (∼-assoc {S} {T}))

assoc⁻¹-iso : ∀ {S T U} → ⟦ assoc⁻¹ {S} {T} {U} ⟫ assoc {S} {T} {U} ⟧ ≃ ⟦ done ⟧
assoc⁻¹-iso {S} = equiv-is-iso (∼-sym (∼-assoc {S})) (∼-assoc {S})

-- Coherence conditions

assoc-unit₂ : ∀ {S T} → ⟦ done {S} [&] unit₂ {T} ⟧ ≃ ⟦ assoc {S} {T} {I} ⟫ unit₂ {S & T} ⟧
assoc-unit₂ {S} {T} as = 
  begin
    ⟦ done {S} [&] unit₂ {T} ⟧ as
  ≡⟨ [&]-resp-≃ {P₁ = done {S}} (≃-sym (equiv-resp-done)) ≃-refl as ⟩
    (⟦ equiv (∼-refl {S}) [&] unit₂ {T} ⟧) as
  ≡⟨ sym (equiv-resp-[&] (∼-refl {S}) (∼-unit₂ {T}) as) ⟩
    (⟦ equiv (&-resp-∼ (∼-refl {S}) (∼-unit₂ {T})) ⟧) as
  ≡⟨ ⟦⟧-resp-∼ (&-resp-∼ (∼-refl {S}) (∼-unit₂ {T})) (∼-trans (∼-assoc {S}) (∼-unit₂ {S & T})) as ⟩
    (⟦ equiv (∼-trans (∼-assoc {S}) (∼-unit₂ {S & T})) ⟧) as
  ≡⟨ equiv-resp-⟫ (∼-assoc {S}) ∼-unit₂ as ⟩
    ⟦ assoc {S} ⟫ unit₂ {S & T} ⟧ as
  ∎ 