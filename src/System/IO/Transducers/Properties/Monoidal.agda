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
open import System.IO.Transducers.Properties.Category using ( ⟦done⟧ ; done-semantics ; _⟦⟫⟧_ ; ⟫-semantics ; ⟫-≃-⟦⟫⟧ ; ⟫-resp-≃ ; done-isEquiv ; ⟫-isEquiv ; equiv-is-iso )
open import System.IO.Transducers.Properties.Lemmas using ( ≃-refl ; ≃-sym ; ⟦⟧-resp-✓ ; ⟦⟧-resp-[] ; ⟦⟧-resp-∼ ; IsEquiv ; isEquiv ; ≃-equiv )

module System.IO.Transducers.Properties.Monoidal where

open Relation.Binary.PropositionalEquality.≡-Reasoning

infixr 8 _++_ _⟦[&]⟧_

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

[&]-≃-⟦[&]⟧ : ∀ {S T U V} 
  {P : S ⇒ T} {f : Trace S → Trace T} {Q : U ⇒ V} {g : Trace U → Trace V} →
    (⟦ P ⟧ ≃ f) → (⟦ Q ⟧ ≃ g) → (⟦ P [&] Q ⟧ ≃ f ⟦[&]⟧ g)
[&]-≃-⟦[&]⟧ {S} {T} {U} {V} {P} {f} {Q} {g} P≃f Q≃g as =
  begin
    ⟦ P [&] Q ⟧ as
  ≡⟨ [&]-semantics P Q as ⟩
    (⟦ P ⟧ ⟦[&]⟧ ⟦ Q ⟧) as
  ≡⟨ cong₂ _++_ (P≃f (front as)) (Q≃g (back {S} as)) ⟩
    (f ⟦[&]⟧ g) as
  ∎

-- Semantics of units

⟦unit₁⟧ : ∀ {S} → (Trace (I & S)) → (Trace S)
⟦unit₁⟧ as = as

unit₁-semantics : ∀ {S} → ⟦ unit₁ {S} ⟧ ≃ ⟦unit₁⟧ {S}
unit₁-semantics {I}     [] = refl
unit₁-semantics {Σ V F} []        = refl
unit₁-semantics {I}     (() ∷ as)
unit₁-semantics {Σ V F} (a ∷ as)  = cong (_∷_ a) (unit₁-semantics as)

⟦unit₂⟧ : ∀ {S} → (Trace (S & I)) → (Trace S)
⟦unit₂⟧ = front

unit₂-semantics : ∀ {S} → ⟦ unit₂ {S} ⟧ ≃ ⟦unit₂⟧ {S}
unit₂-semantics {I}     [] = refl
unit₂-semantics {Σ V F} []        = refl
unit₂-semantics {I}     (() ∷ as)
unit₂-semantics {Σ V F} (a ∷ as)  = cong (_∷_ a) (unit₂-semantics as)

-- Semantics of associativity

⟦assoc⟧ : ∀ {S T U} → (Trace (S & (T & U))) → (Trace ((S & T) & U))
⟦assoc⟧ {S} {T} {U} as =
  (front {S} as ++ front {T} (back {S} as)) ++ back {T} (back {S} as)

assoc-semantics : ∀ {S T U} → ⟦ assoc {S} {T} {U} ⟧ ≃ ⟦assoc⟧ {S} {T} {U}
assoc-semantics {I}     {I}     {I}     []        = refl
assoc-semantics {I}     {I}     {Σ X H} []        = refl
assoc-semantics {I}     {Σ W G}         []        = refl
assoc-semantics {I}     {I}     {I}     (() ∷ as)
assoc-semantics {I}     {I}     {Σ X H} (a ∷ as)  = cong (_∷_ a) (assoc-semantics {I} {I} as)
assoc-semantics {I}     {Σ W G}         (a ∷ as)  = cong (_∷_ a) (assoc-semantics {I} {♭ G a} as)
assoc-semantics {Σ W F}                 []        = refl
assoc-semantics {Σ W F}                 (a ∷ as)  = cong (_∷_ a) (assoc-semantics {♭ F a} as)

-- Congruence for concatenation, where the rhs can assume the lhs has terminated

++-cong : ∀ {S T} {as₁ as₂ : Trace S} {bs₁ bs₂ : Trace T} →
  (as₁ ≡ as₂) → (✓ as₂ → bs₁ ≡ bs₂) → (as₁ ++ bs₁) ≡ (as₂ ++ bs₂)
++-cong {I}     {T} {[]}      refl bs₁≡bs₂ = bs₁≡bs₂ []
++-cong {I}     {T} {() ∷ as} refl bs₁≡bs₂
++-cong {Σ V F} {T} {[]}      refl bs₁≡bs₂ = refl
++-cong {Σ V F} {T} {a ∷ as}  refl bs₁≡bs₂ = cong (_∷_ a) (++-cong refl (λ ✓as → bs₁≡bs₂ (a ∷ ✓as)))

-- Concatenation reflects termination

++-✓₁ : ∀ {S T} {as : Trace S} {bs : Trace T} → (✓ (as ++ bs)) → (✓ as)
++-✓₁ {I}     {T} {[]}      _         = []
++-✓₁ {I}     {T} {() ∷ as} _
++-✓₁ {Σ W F} {T} {[]}      ([] {})
++-✓₁ {Σ W F} {T} {a ∷ as}  (.a ∷ bs) = a ∷ ++-✓₁ bs

++-✓₂ : ∀ {S T} {as : Trace S} {bs : Trace T} → (✓ (as ++ bs)) → (✓ bs)
++-✓₂ {I}     {T} {[]}      cs        = cs
++-✓₂ {I}     {T} {() ∷ as} cs
++-✓₂ {Σ W F} {T} {[]}      ([] {})
++-✓₂ {Σ W F} {T} {a ∷ as}  (.a ∷ cs) = ++-✓₂ {♭ F a} cs

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

-- Tensor respects ≃

[&]-resp-≃ : ∀ {S T U V} {P₁ P₂ : S ⇒ T} {Q₁ Q₂ : U ⇒ V} → 
  (⟦ P₁ ⟧ ≃ ⟦ P₂ ⟧) → (⟦ Q₁ ⟧ ≃ ⟦ Q₂ ⟧) →
    (⟦ P₁ [&] Q₁ ⟧ ≃ ⟦ P₂ [&] Q₂ ⟧)
[&]-resp-≃ {S} {T} {U} {V} {P₁} {P₂} {Q₁} {Q₂} P₁≃P₂ Q₁≃Q₂ as =
  begin
    ⟦ P₁ [&] Q₁ ⟧ as
  ≡⟨ [&]-≃-⟦[&]⟧ P₁≃P₂ Q₁≃Q₂ as ⟩
    (⟦ P₂ ⟧ ⟦[&]⟧ ⟦ Q₂ ⟧) as
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
    ⟦ (P ⟫ Q) [&] done ⟧ as
  ≡⟨ [&]-≃-⟦[&]⟧ (⟫-semantics P Q) ≃-refl as ⟩
    ((⟦ P ⟧ ⟦⟫⟧ ⟦ Q ⟧) ⟦[&]⟧ ⟦done⟧) as
  ≡⟨ ⟦[&]⟧-resp-⟦⟫⟧₁ ⟦ P ⟧ ⟦ Q ⟧ (⟦⟧-resp-✓ P) as ⟩
    ((⟦ P ⟧ ⟦[&]⟧ ⟦done⟧) ⟦⟫⟧ (⟦ Q ⟧ ⟦[&]⟧ ⟦done⟧)) as
  ≡⟨ sym (⟫-≃-⟦⟫⟧ ([&]-semantics P done) ([&]-semantics Q done) as) ⟩
    ⟦ P [&] done ⟫ Q [&] done ⟧ as
  ∎

[&]-resp-⟫₂ : ∀ {S T U V} (P : T ⇒ U) → (Q : U ⇒ V) → 
  ⟦ done {S} [&] (P ⟫ Q) ⟧ ≃ ⟦ (done {S} [&] P) ⟫ (done {S} [&] Q) ⟧
[&]-resp-⟫₂ {S} P Q as = 
  begin
    ⟦ done {S} [&] (P ⟫ Q) ⟧ as
  ≡⟨ [&]-≃-⟦[&]⟧ {P = done {S}} ≃-refl (⟫-semantics P Q) as ⟩
    (⟦done⟧ {S} ⟦[&]⟧ (⟦ P ⟧ ⟦⟫⟧ ⟦ Q ⟧)) as
  ≡⟨ ⟦[&]⟧-resp-⟦⟫⟧₂ {S} ⟦ P ⟧ ⟦ Q ⟧ as ⟩
    ((⟦done⟧ {S} ⟦[&]⟧ ⟦ P ⟧) ⟦⟫⟧ (⟦done⟧ {S} ⟦[&]⟧ ⟦ Q ⟧)) as
  ≡⟨ sym (⟫-≃-⟦⟫⟧ ([&]-semantics (done {S}) P) ([&]-semantics (done {S}) Q) as) ⟩
    ⟦ done {S} [&] P ⟫ done {S} [&] Q ⟧ as
  ∎
  
-- Category of strict transducers is monoidal

[&]-resp-⟫ : ∀ {S₁ S₂ T₁ T₂ U₁ U₂} 
  (P₁ : S₁ ⇒ T₁) (Q₁ : T₁ ⇒ U₁) (P₂ : S₂ ⇒ T₂) (Q₂ : T₂ ⇒ U₂) → (Strict P₂) →
    ⟦ (P₁ ⟫ Q₁) [&] (P₂ ⟫ Q₂) ⟧ ≃ ⟦ (P₁ [&] P₂) ⟫ (Q₁ [&] Q₂) ⟧
[&]-resp-⟫ P₁ Q₁ P₂ Q₂ #P₂ as = 
  begin
    ⟦ (P₁ ⟫ Q₁) [&] (P₂ ⟫ Q₂) ⟧ as
  ≡⟨ [&]-≃-⟦[&]⟧ (⟫-semantics P₁ Q₁) (⟫-semantics P₂ Q₂) as ⟩
    ((⟦ P₁ ⟧ ⟦⟫⟧ ⟦ Q₁ ⟧) ⟦[&]⟧ (⟦ P₂ ⟧ ⟦⟫⟧ ⟦ Q₂ ⟧)) as
  ≡⟨ ⟦[&]⟧-resp-⟦⟫⟧ ⟦ P₁ ⟧ ⟦ Q₁ ⟧ ⟦ P₂ ⟧ ⟦ Q₂ ⟧ (⟦⟧-resp-✓ P₁) (⟦⟧-resp-[] #P₂) as ⟩
    ((⟦ P₁ ⟧ ⟦[&]⟧ ⟦ P₂ ⟧) ⟦⟫⟧ (⟦ Q₁ ⟧ ⟦[&]⟧ ⟦ Q₂ ⟧)) as
  ≡⟨ sym (⟫-≃-⟦⟫⟧ ([&]-semantics P₁ P₂) ([&]-semantics Q₁ Q₂) as) ⟩
    ⟦ P₁ [&] P₂ ⟫ Q₁ [&] Q₂ ⟧ as
  ∎

-- Units and associator are equivalences

unit₁-isEquiv : ∀ {S} → IsEquiv (unit₁ {S})
unit₁-isEquiv = isEquiv ∼-unit₁ ≃-refl

unit₂-isEquiv : ∀ {S} → IsEquiv (unit₂ {S})
unit₂-isEquiv {S} = isEquiv (∼-unit₂ {S}) ≃-refl

assoc-isEquiv : ∀ {S T U} → IsEquiv (assoc {S} {T} {U})
assoc-isEquiv {S} {T} = isEquiv (∼-assoc {S} {T}) ≃-refl

unit₁⁻¹-isEquiv : ∀ {S} → IsEquiv (unit₁⁻¹ {S})
unit₁⁻¹-isEquiv = isEquiv (∼-sym ∼-unit₁) ≃-refl

unit₂⁻¹-isEquiv : ∀ {S} → IsEquiv (unit₂⁻¹ {S})
unit₂⁻¹-isEquiv = isEquiv (∼-sym ∼-unit₂) ≃-refl

assoc⁻¹-isEquiv : ∀ {S T U} → IsEquiv (assoc⁻¹ {S} {T} {U})
assoc⁻¹-isEquiv {S} = isEquiv (∼-sym (∼-assoc {S})) ≃-refl

-- Equivalence respects &

&-resp-∼ : ∀ {S T U V} → (S ∼ T) → (U ∼ V) → ((S & U) ∼ (T & V))
&-resp-∼ I       U∼V = U∼V
&-resp-∼ (Σ V F) U∼V = Σ V (♯ λ a → &-resp-∼ (♭ F a) U∼V)

equiv-resp-⟦[&]⟧ : ∀ {S T U V} (S∼T : S ∼ T) (U∼V : U ∼ V) →
  ⟦ equiv S∼T ⟧ ⟦[&]⟧ ⟦ equiv U∼V ⟧ ≃ ⟦ equiv (&-resp-∼ S∼T U∼V) ⟧
equiv-resp-⟦[&]⟧ I       U∼V as       = refl
equiv-resp-⟦[&]⟧ (Σ V F) U∼V []       = refl
equiv-resp-⟦[&]⟧ (Σ V F) U∼V (a ∷ as) = cong (_∷_ a) (equiv-resp-⟦[&]⟧ (♭ F a) U∼V as)

equiv-resp-[&] : ∀ {S T U V} (S∼T : S ∼ T) (U∼V : U ∼ V) →
  ⟦ equiv S∼T [&] equiv U∼V ⟧ ≃ ⟦ equiv (&-resp-∼ S∼T U∼V) ⟧
equiv-resp-[&] S∼T U∼V as =
  begin
    ⟦ equiv S∼T [&] equiv U∼V ⟧ as
  ≡⟨ [&]-semantics (equiv S∼T) (equiv U∼V) as ⟩
    (⟦ equiv S∼T ⟧ ⟦[&]⟧ ⟦ equiv U∼V ⟧) as
  ≡⟨ equiv-resp-⟦[&]⟧ S∼T U∼V as ⟩
    ⟦ equiv (&-resp-∼ S∼T U∼V) ⟧ as
  ∎

[&]-isEquiv : ∀ {S T U V} {P : S ⇒ T} {Q : U ⇒ V} →
  (IsEquiv P) → (IsEquiv Q) → (IsEquiv (P [&] Q))
[&]-isEquiv {S} {T} {U} {V} {P} {Q} (isEquiv S∼T P≃S∼T) (isEquiv U∼V Q≃U∼V) =
  isEquiv (&-resp-∼ S∼T U∼V) λ as →
    begin
      ⟦ P [&] Q ⟧ as
    ≡⟨ [&]-resp-≃ P≃S∼T Q≃U∼V as ⟩
      ⟦ equiv S∼T [&] equiv U∼V ⟧ as
    ≡⟨ equiv-resp-[&] S∼T U∼V as ⟩
      ⟦ equiv (&-resp-∼ S∼T U∼V) ⟧ as
    ∎

-- Isomorphisms

unit₁-iso : ∀ {S} → ⟦ unit₁ {S} ⟫ unit₁⁻¹ {S} ⟧ ≃ ⟦ done ⟧
unit₁-iso = equiv-is-iso unit₁-isEquiv unit₁⁻¹-isEquiv

unit₁⁻¹-iso : ∀ {S} → ⟦ unit₁⁻¹ {S} ⟫ unit₁ {S} ⟧ ≃ ⟦ done ⟧
unit₁⁻¹-iso = equiv-is-iso unit₁⁻¹-isEquiv unit₁-isEquiv

unit₂-iso : ∀ {S} → ⟦ unit₂ {S} ⟫ unit₂⁻¹ {S} ⟧ ≃ ⟦ done ⟧
unit₂-iso {S} = equiv-is-iso (unit₂-isEquiv {S}) unit₂⁻¹-isEquiv

unit₂⁻¹-iso : ∀ {S} → ⟦ unit₂⁻¹ {S} ⟫ unit₂ {S} ⟧ ≃ ⟦ done ⟧
unit₂⁻¹-iso {S} = equiv-is-iso unit₂⁻¹-isEquiv (unit₂-isEquiv {S})

assoc-iso : ∀ {S T U} → ⟦ assoc {S} {T} {U} ⟫ assoc⁻¹ {S} {T} {U} ⟧ ≃ ⟦ done ⟧
assoc-iso {S} {T} = equiv-is-iso (assoc-isEquiv {S} {T}) (assoc⁻¹-isEquiv {S} {T})

assoc⁻¹-iso : ∀ {S T U} → ⟦ assoc⁻¹ {S} {T} {U} ⟫ assoc {S} {T} {U} ⟧ ≃ ⟦ done ⟧
assoc⁻¹-iso {S} {T} = equiv-is-iso (assoc⁻¹-isEquiv {S} {T}) (assoc-isEquiv {S} {T})

-- Coherence conditions

assoc-unit₁ : ∀ {S T} →
  ⟦ unit₁ {S} [&] done {T} ⟧ ≃ ⟦ assoc⁻¹ {I} {S} {T} ⟫ unit₁ {S & T} ⟧
assoc-unit₁ {S} {T} = 
  ≃-equiv ([&]-isEquiv (unit₁-isEquiv {S}) (done-isEquiv {T})) 
    (⟫-isEquiv (assoc⁻¹-isEquiv {I} {S} {T}) unit₁-isEquiv)

assoc-unit₂ : ∀ {S T} →
  ⟦ done {S} [&] unit₂ {T} ⟧ ≃ ⟦ assoc {S} {T} {I} ⟫ unit₂ {S & T} ⟧
assoc-unit₂ {S} {T} = 
  ≃-equiv ([&]-isEquiv (done-isEquiv {S}) (unit₂-isEquiv {T})) 
    (⟫-isEquiv (assoc-isEquiv {S} {T} {I}) (unit₂-isEquiv {S & T}))

assoc-assoc : ∀ {S T U V} → 
  ⟦ done {S} [&] assoc {T} {U} {V} ⟫ 
      assoc {S} {T & U} {V} ⟫ 
        assoc {S} {T} {U} [&] done {V} ⟧ ≃
  ⟦ assoc {S} {T} {U & V} ⟫ assoc {S & T} {U} {V} ⟧
assoc-assoc {S} {T} {U} {V} = 
  ≃-equiv 
    (⟫-isEquiv ([&]-isEquiv (done-isEquiv {S}) (assoc-isEquiv {T} {U} {V})) 
      (⟫-isEquiv (assoc-isEquiv {S} {T & U} {V}) 
        ([&]-isEquiv (assoc-isEquiv {S} {T} {U}) done-isEquiv))) 
    (⟫-isEquiv (assoc-isEquiv {S} {T} {U & V}) (assoc-isEquiv {S & T} {U} {V}))

-- Front and back play well with associativity

front-⟦assoc⟧ : ∀ {S T U} (as : Trace (S & (T & U))) →
  (front {S} as ≡ front {S} (front {S & T} (⟦assoc⟧ {S} as)))
front-⟦assoc⟧ {I}     as       = refl
front-⟦assoc⟧ {Σ V F} []       = refl
front-⟦assoc⟧ {Σ V F} (a ∷ as) = cong (_∷_ a) (front-⟦assoc⟧ as)

mid-⟦assoc⟧ : ∀ {S T U} (as : Trace (S & (T & U))) →
  (front {T} (back {S} as) ≡ back {S} (front {S & T} (⟦assoc⟧ {S} as)))
mid-⟦assoc⟧ {I}     {T}     as       = cong front (sym (++-η {T} as))
mid-⟦assoc⟧ {Σ V F} {I}     []       = refl
mid-⟦assoc⟧ {Σ V F} {Σ W G} []       = refl
mid-⟦assoc⟧ {Σ V F}         (a ∷ as) = mid-⟦assoc⟧ {♭ F a} as

back-⟦assoc⟧ : ∀ {S T U} (as : Trace (S & (T & U))) →
  (back {T} (back {S} as) ≡ back {S & T} (⟦assoc⟧ {S} as))
back-⟦assoc⟧ {I}     {T}     as       = cong (back {T}) (sym (++-η {T} as))
back-⟦assoc⟧ {Σ V F} {I}     []       = refl
back-⟦assoc⟧ {Σ V F} {Σ W G} []       = refl
back-⟦assoc⟧ {Σ V F}         (a ∷ as) = back-⟦assoc⟧ {♭ F a} as

-- Units are natural

⟦unit₁⟧-natural : ∀ {S T} (f : Trace S → Trace T) →
  (⟦done⟧ {I} ⟦[&]⟧ f) ⟦⟫⟧ ⟦unit₁⟧ ≃ ⟦unit₁⟧ ⟦⟫⟧ f 
⟦unit₁⟧-natural f as = refl

unit₁-natural : ∀ {S T} (P : S ⇒ T) →
  ⟦ done {I} [&] P ⟫ unit₁ ⟧ ≃ ⟦ unit₁ ⟫ P ⟧ 
unit₁-natural P as = 
  begin
    ⟦ done {I} [&] P ⟫ unit₁ ⟧ as
  ≡⟨ ⟫-≃-⟦⟫⟧ ([&]-semantics (done {I}) P) unit₁-semantics as ⟩
    (⟦done⟧ {I} ⟦[&]⟧ ⟦ P ⟧ ⟦⟫⟧ ⟦unit₁⟧) as
  ≡⟨ ⟦unit₁⟧-natural ⟦ P ⟧ as ⟩
     (⟦unit₁⟧ ⟦⟫⟧ ⟦ P ⟧) as
  ≡⟨ sym (⟫-≃-⟦⟫⟧ unit₁-semantics ≃-refl as) ⟩
    ⟦ unit₁ ⟫ P ⟧ as
  ∎

⟦unit₂⟧-natural : ∀ {S T} (f : Trace S → Trace T) →
  (f ⟦[&]⟧ ⟦done⟧ {I}) ⟦⟫⟧ ⟦unit₂⟧ ≃ ⟦unit₂⟧ ⟦⟫⟧ f 
⟦unit₂⟧-natural {S} f as = ++-β₁ (f (front as)) (back {S} as)

unit₂-natural : ∀ {S T} (P : S ⇒ T) →
  ⟦ P [&] done {I} ⟫ unit₂ ⟧ ≃ ⟦ unit₂ ⟫ P ⟧ 
unit₂-natural {S} {T} P as = 
  begin
    ⟦ P [&] done {I} ⟫ unit₂ ⟧ as
  ≡⟨ ⟫-≃-⟦⟫⟧ ([&]-semantics P (done {I})) (unit₂-semantics {T}) as ⟩
    (⟦ P ⟧ ⟦[&]⟧ ⟦done⟧ {I} ⟦⟫⟧ ⟦unit₂⟧) as
  ≡⟨ ⟦unit₂⟧-natural ⟦ P ⟧ as ⟩
     (⟦unit₂⟧ ⟦⟫⟧ ⟦ P ⟧) as
  ≡⟨ sym (⟫-≃-⟦⟫⟧ (unit₂-semantics {S}) ≃-refl as) ⟩
    ⟦ unit₂ ⟫ P ⟧ as
  ∎

-- Associativity is natural

⟦assoc⟧-natural : ∀ {S S' T T' U U'} 
  (f : Trace S → Trace S') (g : Trace T → Trace T') (h : Trace U → Trace U') →
    ((f ⟦[&]⟧ (g ⟦[&]⟧ h)) ⟦⟫⟧ ⟦assoc⟧ {S'} {T'} {U'}) ≃ 
      (⟦assoc⟧ {S} {T} {U} ⟦⟫⟧ ((f ⟦[&]⟧ g) ⟦[&]⟧ h))
⟦assoc⟧-natural {S} {S'} {T} {T'} {U} {U'} f g h as =
  begin
    ((f ⟦[&]⟧ (g ⟦[&]⟧ h)) ⟦⟫⟧ ⟦assoc⟧ {S'} {T'} {U'}) as
  ≡⟨ ++-cong (++-cong lemma₁ lemma₂) lemma₃ ⟩
    (f (front as) ++ g (front (back {S} as))) ++ h (back {T} (back {S} as))
  ≡⟨ cong₂ _++_ (cong₂ _++_ (cong f (front-⟦assoc⟧ as)) (cong g (mid-⟦assoc⟧ {S} as))) (cong h (back-⟦assoc⟧ {S} as)) ⟩
    (⟦assoc⟧ {S} {T} {U} ⟦⟫⟧ ((f ⟦[&]⟧ g) ⟦[&]⟧ h)) as
  ∎ where
  lemma₁ : 
    front {S'} ((f ⟦[&]⟧ (g ⟦[&]⟧ h)) as) ≡ 
      f (front as)
  lemma₁ = 
    begin
      front {S'} ((f ⟦[&]⟧ (g ⟦[&]⟧ h)) as)
    ≡⟨ ++-β₁ ((f (front as))) ((g (front (back {S} as)) ++ h (back {T} (back {S} as)))) ⟩
      f (front as)
    ∎
  lemma₂ : (✓ (f (front as))) →
    front {T'} (back {S'} ((f ⟦[&]⟧ (g ⟦[&]⟧ h)) as)) ≡ 
      g (front {T} (back {S} as))
  lemma₂ ✓f = 
    begin
      front {T'} (back {S'} ((f ⟦[&]⟧ (g ⟦[&]⟧ h)) as))
    ≡⟨ cong (front {T'}) (++-β₂-✓ ✓f ((g ⟦[&]⟧ h) (back {S} as))) ⟩
      front {T'} ((g ⟦[&]⟧ h) (back {S} as))
    ≡⟨ ++-β₁ ((g (front (back {S} as)))) ((h (back {T} (back {S} as)))) ⟩
      g (front {T} (back {S} as))
    ∎
  lemma₃ : (✓ (f (front as) ++ g (front (back {S} as)))) →
    back {T'} (back {S'} ((f ⟦[&]⟧ (g ⟦[&]⟧ h)) as)) ≡
      h (back {T} (back {S} as))
  lemma₃ ✓fg = 
    begin
      back {T'} (back {S'} ((f ⟦[&]⟧ (g ⟦[&]⟧ h)) as))
    ≡⟨ cong (back {T'}) (++-β₂-✓ (++-✓₁ {as = f (front as)} ✓fg) ((g ⟦[&]⟧ h) (back {S} as))) ⟩
      back {T'} ((g ⟦[&]⟧ h) (back {S} as))
    ≡⟨ ++-β₂-✓ (++-✓₂ {as = f (front as)} ✓fg) (h (back {T} (back {S} as))) ⟩
      h (back {T} (back {S} as))
    ∎

assoc-natural : ∀ {S S' T T' U U'} (P : S ⇒ S') (Q : T ⇒ T') (R : U ⇒ U') →
  ⟦ P [&] (Q [&] R) ⟫ assoc {S'} {T'} {U'} ⟧ ≃
    ⟦ assoc {S} {T} {U} ⟫ (P [&] Q) [&] R ⟧
assoc-natural {S} {S'} {T} {T'} {U} {U'} P Q R as =
  begin
    ⟦ P [&] (Q [&] R) ⟫ assoc {S'} {T'} {U'} ⟧ as
  ≡⟨ ⟫-≃-⟦⟫⟧ ([&]-≃-⟦[&]⟧ {P = P} ≃-refl ([&]-semantics Q R)) (assoc-semantics {S'} {T'} {U'}) as ⟩
    ((⟦ P ⟧ ⟦[&]⟧ (⟦ Q ⟧ ⟦[&]⟧ ⟦ R ⟧)) ⟦⟫⟧ ⟦assoc⟧ {S'} {T'} {U'}) as
  ≡⟨ ⟦assoc⟧-natural ⟦ P ⟧ ⟦ Q ⟧ ⟦ R ⟧ as ⟩
    (⟦assoc⟧ {S} {T} {U} ⟦⟫⟧ ((⟦ P ⟧ ⟦[&]⟧ ⟦ Q ⟧) ⟦[&]⟧ ⟦ R ⟧)) as
  ≡⟨ sym (⟫-≃-⟦⟫⟧ (assoc-semantics {S} {T} {U}) ([&]-≃-⟦[&]⟧ ([&]-semantics P Q) ≃-refl) as) ⟩
    ⟦ assoc {S} {T} {U} ⟫ (P [&] Q) [&] R ⟧ as
  ∎
