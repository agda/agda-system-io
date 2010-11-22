open import Coinduction using ( ♭ ; ♯_ )
open import Data.Empty using ( ⊥-elim )
open import Data.Sum using ( _⊎_ ; inj₁ ; inj₂ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; _≢_ ; refl ; sym ; cong ; cong₂ )
open import Relation.Nullary using ( ¬_ ; Dec ; yes ; no )
open import System.IO.Transducers.Lazy using ( _⇒_ ; inp ; out ; id ; done ; _⟫_ ; equiv ; assoc ; assoc⁻¹ ; unit₁ ; unit₁⁻¹ ; unit₂ ; unit₂⁻¹ ; delay ; _[&]_ ; ⟦_⟧ ; _≃_ )
open import System.IO.Transducers.Strict using ( Strict )
open import System.IO.Transducers.Session using ( I ; Σ ; IsΣ ; _∼_ ; ∼-refl ; ∼-trans ; ∼-sym ; _&_ )
  renaming ( unit₁ to ∼-unit₁ ; unit₂ to ∼-unit₂ ; assoc to ∼-assoc )
open import System.IO.Transducers.Trace using ( Trace ; ✓ ; [] ; [✓] ; _∷_ )
open import System.IO.Transducers.Properties.Category using ( ⟦done⟧ ; done-semantics ; _⟦⟫⟧_ ; ⟫-semantics ; ⟫-≃-⟦⟫⟧ ; ⟫-resp-≃ ; done-isEquiv ; ⟫-isEquiv ; equiv-is-iso )
open import System.IO.Transducers.Properties.Lemmas using ( ≃-refl ; ≃-sym ; ↓ ; ↑ ; ✓-tl ; ✓? ; ↓-↑ ; ↑-✓ ; ⟦⟧-refl-✓ ; ⟦⟧-resp-[] ; ⟦⟧-resp-↓ ; IsEquiv ; isEquiv ; ≃-equiv ; I-¬✓-η ; I-✓-η)

module System.IO.Transducers.Properties.Monoidal where

open Relation.Binary.PropositionalEquality.≡-Reasoning

infixr 8 _++_ _⟦[&]⟧_

-- Concatenation of traces

_++_ : ∀ {S T} → (Trace S) → (Trace T) → (Trace (S & T))
_++_ {S}     []        bs = []
_++_ {I}     [✓]       bs = bs
_++_ {Σ V F} (a ∷ as)  bs = a ∷ (as ++ bs)
_++_ {Σ V F} ([✓] {})  bs
_++_ {I}     (() ∷ as) bs

-- Projection of traces

front : ∀ {S T} → (Trace (S & T)) → (Trace S)
front {I}     as       = [✓]
front {Σ V F} []       = []
front {Σ V F} (a ∷ as) = a ∷ front as
front {Σ V F} ([✓] {})

back : ∀ {S T} → (Trace (S & T)) → (Trace T)
back {I}     as       = as
back {Σ V F} []       = []
back {Σ V F} (a ∷ as) = back {♭ F a} as
back {Σ V F} ([✓] {})

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
delay-semantics (Σ V F) P         ([✓] {})

-- Semantics of tensor

_⟦[&]⟧_ : ∀ {S T U V} →
  (f : Trace S → Trace T) → (g : Trace U → Trace V) → 
    (Trace (S & U)) → (Trace (T & V))
_⟦[&]⟧_ {S} f g as = f (front as) ++ g (back {S} as)

[&]-semantics : ∀ {S T U V} (P : S ⇒ T) (Q : U ⇒ V) → 
  ⟦ P [&] Q ⟧ ≃ ⟦ P ⟧ ⟦[&]⟧ ⟦ Q ⟧
[&]-semantics {Σ V F}         (inp P)    Q []       = refl
[&]-semantics {Σ V F}         (inp P)    Q (a ∷ as) = [&]-semantics (♭ P a) Q as
[&]-semantics {I}     {Σ W G} (out b P)  Q as       = cong (_∷_ b) ([&]-semantics P Q as)
[&]-semantics {Σ V F} {Σ W G} (out b P)  Q as       = cong (_∷_ b) ([&]-semantics P Q as)
[&]-semantics {I}             (id refl)  Q as       = refl
[&]-semantics {Σ V F}         (id refl)  Q []       = refl
[&]-semantics {Σ V F}         (id refl)  Q (a ∷ as) = cong (_∷_ a) ([&]-semantics (done {♭ F a}) Q as)
[&]-semantics {I}             (inp {} P) Q as
[&]-semantics {S}     {I}     (out () P) Q as
[&]-semantics {Σ V F}         (inp P)    Q ([✓] {})
[&]-semantics {Σ V F}         (id refl)  Q ([✓] {})

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
unit₁-semantics {I}     as        = refl
unit₁-semantics {Σ V F} []        = refl
unit₁-semantics {Σ V F} (a ∷ as)  = cong (_∷_ a) (unit₁-semantics as)
unit₁-semantics {Σ V F} ([✓] {})

⟦unit₂⟧ : ∀ {S} → (Trace (S & I)) → (Trace S)
⟦unit₂⟧ {I}     as       = as
⟦unit₂⟧ {Σ V F} []       = []
⟦unit₂⟧ {Σ V F} (a ∷ as) = a ∷ ⟦unit₂⟧ as
⟦unit₂⟧ {Σ V F} ([✓] {})

unit₂-semantics : ∀ {S} → ⟦ unit₂ {S} ⟧ ≃ ⟦unit₂⟧ {S}
unit₂-semantics {I}     as        = refl
unit₂-semantics {Σ V F} []        = refl
unit₂-semantics {Σ V F} (a ∷ as)  = cong (_∷_ a) (unit₂-semantics as)
unit₂-semantics {Σ V F} ([✓] {})

-- Semantics of associativity

⟦assoc⟧ : ∀ {S T U} → (Trace (S & (T & U))) → (Trace ((S & T) & U))
⟦assoc⟧ {S} {T} {U} as =
  (front {S} as ++ front {T} (back {S} as)) ++ back {T} (back {S} as)

assoc-semantics : ∀ {S T U} → ⟦ assoc {S} {T} {U} ⟧ ≃ ⟦assoc⟧ {S} {T} {U}
assoc-semantics {I}     {I}     {I}     []        = refl
assoc-semantics {I}     {I}     {Σ X H} []        = refl
assoc-semantics {I}     {Σ W G}         []        = refl
assoc-semantics {I}     {I}     {I}     [✓]       = refl
assoc-semantics {I}     {I}     {Σ X H} (a ∷ as)  = cong (_∷_ a) (assoc-semantics {I} {I} as)
assoc-semantics {I}     {Σ W G}         (a ∷ as)  = cong (_∷_ a) (assoc-semantics {I} {♭ G a} as)
assoc-semantics {Σ W F}                 []        = refl
assoc-semantics {Σ W F}                 (a ∷ as)  = cong (_∷_ a) (assoc-semantics {♭ F a} as)
assoc-semantics {Σ V F}                 ([✓] {})
assoc-semantics {I}     {Σ W G}         ([✓] {})
assoc-semantics {I}     {I}     {Σ X H} ([✓] {})
assoc-semantics {I}     {I}     {I}     (() ∷ as)

-- Congruence for concatenation, where the rhs can assume the lhs has terminated

++-cong : ∀ {S T} {as₁ as₂ : Trace S} {bs₁ bs₂ : Trace T} →
  (as₁ ≡ as₂) → (✓ as₁ → bs₁ ≡ bs₂) → (as₁ ++ bs₁) ≡ (as₂ ++ bs₂)
++-cong {I}     {T} {[]}      refl bs₁≡bs₂ = refl
++-cong {I}     {T} {[✓]}     refl bs₁≡bs₂ = bs₁≡bs₂ [✓]
++-cong {Σ V F} {T} {[]}      refl bs₁≡bs₂ = refl
++-cong {Σ V F} {T} {a ∷ as}  refl bs₁≡bs₂ = cong (_∷_ a) (++-cong refl (λ ✓as → bs₁≡bs₂ (a ∷ ✓as)))
++-cong {I}     {T} {() ∷ as} refl bs₁≡bs₂
++-cong {Σ V F} {T} {[✓] {}}  refl bs₁≡bs₂

-- Incompleting a trace is irrelevant when concatenating with []

↓-++-[] : ∀ {S T} → (as : Trace S) → (↓ as ++ [] {T} ≡ as ++ [] {T})
↓-++-[]         []       = refl
↓-++-[] {I}     [✓]      = refl
↓-++-[] {Σ V F} (a ∷ as) = cong (_∷_ a) (↓-++-[] as)
↓-++-[] {Σ V F} ([✓] {})
↓-++-[] {I}     (() ∷ as)

-- Concatenation reflects termination

++-✓₁ : ∀ {S T} {as : Trace S} {bs : Trace T} → (✓ (as ++ bs)) → (✓ as)
++-✓₁ {I}     {T} {[✓]}     cs         = [✓]
++-✓₁ {Σ W F} {T} {a ∷ as}  (.a ∷ cs) = a ∷ ++-✓₁ cs
++-✓₁ {S}     {T} {[]}      ()
++-✓₁ {I}     {T} {() ∷ as} cs
++-✓₁ {Σ W F} {T} {[✓] {}}  cs

++-✓₂ : ∀ {S T} {as : Trace S} {bs : Trace T} → (✓ (as ++ bs)) → (✓ bs)
++-✓₂ {I}     {T} {[✓]}     cs        = cs
++-✓₂ {Σ W F} {T} {a ∷ as}  (.a ∷ cs) = ++-✓₂ {♭ F a} {T} {as} cs
++-✓₂ {S}     {T} {[]}      ()
++-✓₂ {I}     {T} {() ∷ as} cs
++-✓₂ {Σ W F} {T} {[✓] {}}  cs

-- Beta and eta equivalence for concatenation.  Note that β₁ may return a more complete trace than as,
-- and that β₂ only holds when as is complete.

++-β₁ : ∀ {S T} (as : Trace S) → (bs : Trace T) → (front (as ++ bs) ≡ ↑ as)
++-β₁ {I}     []        bs = refl
++-β₁ {I}     [✓]       bs = refl
++-β₁ {I}     (() ∷ as) bs
++-β₁ {Σ V F} []        bs = refl
++-β₁ {Σ V F} (a ∷ as)  bs = cong (_∷_ a) (++-β₁ as bs)
++-β₁ {Σ V F} ([✓] {})  bs

++-β₂ : ∀ {S T} {as : Trace S} → (✓ as) → (bs : Trace T) → (back {S} (as ++ bs) ≡ bs)
++-β₂ {I}     [✓]       bs = refl
++-β₂ {Σ V F} (a ∷ as)  bs = ++-β₂ as bs
++-β₂ {I}     (() ∷ as) bs
++-β₂ {Σ V F} ([✓] {})  bs

++-η : ∀ {S T} (as : Trace (S & T)) → (front {S} as ++ back {S} as ≡ as)
++-η {I}     []       = refl
++-η {I}     [✓]      = refl
++-η {I}     (a ∷ as) = refl
++-η {Σ V F} []       = refl
++-η {Σ V F} (a ∷ as) = cong (_∷_ a) (++-η {♭ F a} as)
++-η {Σ V F} ([✓] {})

-- Beta for concatenation with an incomplete trace

++-β₂-[] : ∀ {S T} {as : Trace S} → (¬ ✓ as) → (bs : Trace T) → (back {S} (as ++ bs) ≡ [])
++-β₂-[] {I}     {T} {[]}      ¬✓[]   bs = refl
++-β₂-[] {I}     {T} {[✓]}     ¬✓[✓]  bs = ⊥-elim (¬✓[✓] [✓])
++-β₂-[] {Σ V F} {T} {[]}      ¬✓[]   bs = refl
++-β₂-[] {Σ V F} {T} {a ∷ as}  ¬✓a∷as bs = ++-β₂-[] (λ ✓as → ¬✓a∷as (a ∷ ✓as)) bs
++-β₂-[] {I}     {T} {() ∷ as} ¬✓a∷as bs
++-β₂-[] {Σ V F} {T} {[✓] {}}  ¬✓[✓]  bs

-- Back reflects and respects completion

back-resp-✓ :  ∀ {S} {T} {as : Trace (S & T)} → (✓ as) → (✓ (back {S} as))
back-resp-✓ {I}     ✓as       = ✓as
back-resp-✓ {Σ W F} (a ∷ ✓as) = back-resp-✓ {♭ F a} ✓as
back-resp-✓ {Σ W F} ([✓] {})

back-refl-✓ :  ∀ {S} {T} {as : Trace (S & T)} → (✓ (back {S} as)) → (✓ as)
back-refl-✓ {I}                  ✓bs = ✓bs
back-refl-✓ {Σ W F} {T} {a ∷ as} ✓bs = a ∷ back-refl-✓ {♭ F a} {T} {as} ✓bs
back-refl-✓ {Σ W F} {T} {[]}     ()
back-refl-✓ {Σ W F} {T} {[✓] {}} ✓bs

-- Front returns a trace that is as complete as can be.

-- front-↑ : ∀ {S T} (as : Trace (S & T)) → (front {S} as ≡ ↑ (front {S} as))
-- front-↑ {I} as = refl
-- front-↑ {Σ W F} [] = refl
-- front-↑ {Σ W F} ([✓] {})
-- front-↑ {Σ W F} (a ∷ as) = cong (_∷_ a) (front-↑ as)

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

-- Tensor respects composition when g₁ reflects completion and respects ↓, and g₂ is strict.

⟦[&]⟧-resp-⟦⟫⟧ : ∀ {S₁ S₂ T₁ T₂ U₁ U₂} → 
  (f₁ : Trace S₁ → Trace T₁) → (g₁ : Trace T₁ → Trace U₁) → 
    (f₂ : Trace S₂ → Trace T₂) → (g₂ : Trace T₂ → Trace U₂) → 
      (∀ as → ✓ (g₁ as) → ✓ as) → (∀ as → g₁ (↓ as) ≡ ↓ (g₁ as)) → (g₂ [] ≡ []) →
        (((f₁ ⟦⟫⟧ g₁) ⟦[&]⟧ (f₂ ⟦⟫⟧ g₂)) ≃ (f₁ ⟦[&]⟧ f₂) ⟦⟫⟧ (g₁ ⟦[&]⟧ g₂))
⟦[&]⟧-resp-⟦⟫⟧ {S₁} {S₂} {T₁} {T₂} f₁ g₁ f₂ g₂ g₁-refl-✓ g₁-resp-↓ g₂-resp-[] as with ✓? (f₁ (front as))
⟦[&]⟧-resp-⟦⟫⟧ {S₁} {S₂} {T₁} {T₂} f₁ g₁ f₂ g₂ g₁-refl-✓ g₁-resp-↓ g₂-resp-[] as | yes ✓f₁as₁ =
  begin
    g₁ (f₁ (front {S₁} as))
      ++ g₂ (f₂ (back {S₁} as))
  ≡⟨ cong₂ _++_ (cong g₁ (sym (↑-✓ ✓f₁as₁))) refl ⟩
    g₁ (↑ (f₁ (front {S₁} as)))
      ++ g₂ (f₂ (back {S₁} as))
  ≡⟨ cong₂ _++_ (cong g₁ (sym (++-β₁ (f₁ (front {S₁} as)) (f₂ (back {S₁} as))))) (cong g₂ (sym (++-β₂ ✓f₁as₁ (f₂ (back {S₁} as))))) ⟩
    g₁ (front {T₁} (f₁ (front {S₁} as) ++ f₂ (back {S₁} as))) 
      ++ g₂ (back {T₁} (f₁ (front {S₁} as) ++ f₂ (back {S₁} as)))  
  ∎
⟦[&]⟧-resp-⟦⟫⟧ {S₁} {S₂} {T₁} {T₂} f₁ g₁ f₂ g₂ g₁-refl-✓ g₁-resp-↓ g₂-resp-[] as | no ¬✓f₁as₁ = 
  begin
    g₁ (f₁ (front {S₁} as))
      ++ g₂ (f₂ (back {S₁} as))
  ≡⟨ ++-cong refl (λ ✓g₁f₁as₁ → ⊥-elim (¬✓f₁as₁ (g₁-refl-✓ (f₁ (front as)) ✓g₁f₁as₁))) ⟩
    g₁ (f₁ (front {S₁} as))
      ++ []
  ≡⟨ sym (↓-++-[] (g₁ (f₁ (front {S₁} as)))) ⟩
    ↓ (g₁ (f₁ (front {S₁} as)))
      ++ []
  ≡⟨ cong₂ _++_ (sym (g₁-resp-↓ (f₁ (front {S₁} as)))) refl ⟩
    g₁ (↓ (f₁ (front {S₁} as)))
      ++ []
  ≡⟨ cong₂ _++_ (cong g₁ (sym (↓-↑ (f₁ (front {S₁} as))))) refl ⟩
    g₁ (↓ (↑ (f₁ (front {S₁} as))))
      ++ []
  ≡⟨ cong₂ _++_ (cong g₁ (cong ↓ (sym (++-β₁ (f₁ (front {S₁} as)) (f₂ (back {S₁} as)))))) refl ⟩
    g₁ (↓ (front {T₁} (f₁ (front {S₁} as) ++ f₂ (back {S₁} as))) )
      ++ []
  ≡⟨ cong₂ _++_ (g₁-resp-↓ (front {T₁} (f₁ (front {S₁} as) ++ f₂ (back {S₁} as)))) refl ⟩
    ↓ (g₁ (front {T₁} (f₁ (front {S₁} as) ++ f₂ (back {S₁} as))))
      ++ []
  ≡⟨ ↓-++-[] (g₁ (front {T₁} (f₁ (front {S₁} as) ++ f₂ (back {S₁} as)))) ⟩
    g₁ (front {T₁} (f₁ (front {S₁} as) ++ f₂ (back {S₁} as)))
      ++ []
  ≡⟨ cong₂ _++_ (refl {x = g₁ _}) (sym g₂-resp-[]) ⟩
    g₁ (front {T₁} (f₁ (front {S₁} as) ++ f₂ (back {S₁} as)))
      ++ g₂ []
  ≡⟨ cong₂ _++_ (refl {x = g₁ _}) (cong g₂ (sym (++-β₂-[] ¬✓f₁as₁ (f₂ (back {S₁} as))))) ⟩
    g₁ (front {T₁} (f₁ (front {S₁} as) ++ f₂ (back {S₁} as))) 
      ++ g₂ (back {T₁} (f₁ (front {S₁} as) ++ f₂ (back {S₁} as)))  
  ∎

-- Tensor respects composition when Q₂ is strict

[&]-resp-⟫ : ∀ {S₁ S₂ T₁ T₂ U₁ U₂} 
  (P₁ : S₁ ⇒ T₁) (Q₁ : T₁ ⇒ U₁) (P₂ : S₂ ⇒ T₂) {Q₂ : T₂ ⇒ U₂} → (Strict Q₂) →
    ⟦ (P₁ ⟫ Q₁) [&] (P₂ ⟫ Q₂) ⟧ ≃ ⟦ (P₁ [&] P₂) ⟫ (Q₁ [&] Q₂) ⟧
[&]-resp-⟫ P₁ Q₁ P₂ {Q₂} #Q₂ as = 
  begin
    ⟦ (P₁ ⟫ Q₁) [&] (P₂ ⟫ Q₂) ⟧ as
  ≡⟨ [&]-≃-⟦[&]⟧ (⟫-semantics P₁ Q₁) (⟫-semantics P₂ Q₂) as ⟩
    ((⟦ P₁ ⟧ ⟦⟫⟧ ⟦ Q₁ ⟧) ⟦[&]⟧ (⟦ P₂ ⟧ ⟦⟫⟧ ⟦ Q₂ ⟧)) as
  ≡⟨ ⟦[&]⟧-resp-⟦⟫⟧ ⟦ P₁ ⟧ ⟦ Q₁ ⟧ ⟦ P₂ ⟧ ⟦ Q₂ ⟧ (⟦⟧-refl-✓ Q₁) (⟦⟧-resp-↓ Q₁) (⟦⟧-resp-[] #Q₂) as ⟩
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
equiv-resp-⟦[&]⟧ (Σ V F) U∼V ([✓] {})

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

assoc-unit : ∀ {S T} →
  ⟦ done {S} [&] unit₁ {T} ⟧ ≃ ⟦ assoc {S} {I} {T} ⟫ unit₂ {S} [&] done {T} ⟧
assoc-unit {S} {T} = 
  ≃-equiv ([&]-isEquiv (done-isEquiv {S}) (unit₁-isEquiv {T}))
    (⟫-isEquiv (assoc-isEquiv {S} {I} {T}) ([&]-isEquiv (unit₂-isEquiv {S}) (done-isEquiv {T})))

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

-- Concatenation plays nicely with associativity

⟦assoc⟧-++ : ∀ {S T U} → (as : Trace S) (bs : Trace T) (cs : Trace U) →
  ⟦assoc⟧ {S} (as ++ (bs ++ cs)) ≡ ((as ++ bs) ++ cs)
⟦assoc⟧-++ {I} {I}     []        bs cs = refl
⟦assoc⟧-++ {I} {Σ W G} []        bs cs = refl
⟦assoc⟧-++ {I} {T}     [✓]       bs cs = ++-η {T} (bs ++ cs)
⟦assoc⟧-++ {Σ W F}     []        bs cs = refl
⟦assoc⟧-++ {Σ W F}     (a ∷ as)  bs cs = cong (_∷_ a) (⟦assoc⟧-++ as bs cs)
⟦assoc⟧-++ {I}         (() ∷ as) bs cs
⟦assoc⟧-++ {Σ W F}     ([✓] {})  bs cs

-- Front and back play well with associativity

front-⟦assoc⟧ : ∀ {S T U} (as : Trace (S & (T & U))) →
  (front {S} as ≡ front {S} (front {S & T} (⟦assoc⟧ {S} as)))
front-⟦assoc⟧ {I}     as = refl
front-⟦assoc⟧ {Σ V F} []       = refl
front-⟦assoc⟧ {Σ V F} (a ∷ as) = cong (_∷_ a) (front-⟦assoc⟧ as)
front-⟦assoc⟧ {Σ V F} ([✓] {})

mid-⟦assoc⟧ : ∀ {S T U} (as : Trace (S & (T & U))) →
  (✓ (front {S} as)) → (front {T} (back {S} as) ≡ back {S} (front {S & T} (⟦assoc⟧ {S} as)))
mid-⟦assoc⟧ {I}     {T}     as       ✓as₁ = cong (front {T}) (sym (++-η {T} as))
mid-⟦assoc⟧ {Σ V F} {I}     []       ()
mid-⟦assoc⟧ {Σ V F} {Σ W G} []       ✓as₁ = refl
mid-⟦assoc⟧ {Σ V F}         (a ∷ as) ✓as₁ = mid-⟦assoc⟧ {♭ F a} as (✓-tl ✓as₁)
mid-⟦assoc⟧ {Σ V F}         ([✓] {}) ✓as₁ 

back-⟦assoc⟧ : ∀ {S T U} (as : Trace (S & (T & U))) →
  (back {T} (back {S} as) ≡ back {S & T} (⟦assoc⟧ {S} as))
back-⟦assoc⟧ {I}     {T}     as       = cong (back {T}) (sym (++-η {T} as))
back-⟦assoc⟧ {Σ V F} {I}     []       = refl
back-⟦assoc⟧ {Σ V F} {Σ W G} []       = refl
back-⟦assoc⟧ {Σ V F}         (a ∷ as) = back-⟦assoc⟧ {♭ F a} as
back-⟦assoc⟧ {Σ V F}         ([✓] {})

-- Unit plays nicely with concatenation

⟦unit₂⟧-++-[✓] : ∀ {S} (as : Trace S) → ⟦unit₂⟧ {S} (as ++ [✓]) ≡ as
⟦unit₂⟧-++-[✓] {I}     []       = refl
⟦unit₂⟧-++-[✓] {I}     [✓]      = refl
⟦unit₂⟧-++-[✓] {Σ W F} []       = refl
⟦unit₂⟧-++-[✓] {Σ W F} (a ∷ as) = cong (_∷_ a) (⟦unit₂⟧-++-[✓] as)
⟦unit₂⟧-++-[✓] {I}     (() ∷ as)
⟦unit₂⟧-++-[✓] {Σ W F} ([✓] {})

⟦unit₂⟧-++-[] : ∀ {S} (as : Trace S) → ⟦unit₂⟧ {S} (as ++ []) ≡ ↓ as
⟦unit₂⟧-++-[] {I}     []       = refl
⟦unit₂⟧-++-[] {I}     [✓]      = refl
⟦unit₂⟧-++-[] {Σ W F} []       = refl
⟦unit₂⟧-++-[] {Σ W F} (a ∷ as) = cong (_∷_ a) (⟦unit₂⟧-++-[] as)
⟦unit₂⟧-++-[] {I}     (() ∷ as)
⟦unit₂⟧-++-[] {Σ W F} ([✓] {})

-- Unit is the same as front, modulo completion

⟦unit₂⟧≡front-✓ : ∀ {S} {as : Trace (S & I)} → (✓ as) → (⟦unit₂⟧ {S} as) ≡ front as
⟦unit₂⟧≡front-✓ {I}     [✓]       = refl
⟦unit₂⟧≡front-✓ {Σ W F} (a ∷ ✓as) = cong (_∷_ a) (⟦unit₂⟧≡front-✓ ✓as)
⟦unit₂⟧≡front-✓ {I}     (() ∷ ✓as)
⟦unit₂⟧≡front-✓ {Σ W F} ([✓] {})

⟦unit₂⟧≡front-¬✓ : ∀ {S} {as : Trace (S & I)} → (¬ ✓ as) → (⟦unit₂⟧ {S} as) ≡ ↓ (front as)
⟦unit₂⟧≡front-¬✓ {I}     {[]}      ¬✓as   = refl
⟦unit₂⟧≡front-¬✓ {I}     {[✓]}     ¬✓as   = ⊥-elim (¬✓as [✓])
⟦unit₂⟧≡front-¬✓ {Σ W F} {[]}      ¬✓as   = refl
⟦unit₂⟧≡front-¬✓ {Σ W F} {a ∷ as}  ¬✓a∷as = cong (_∷_ a) (⟦unit₂⟧≡front-¬✓ (λ ✓as → ¬✓a∷as (a ∷ ✓as)))
⟦unit₂⟧≡front-¬✓ {Σ W F} {[✓] {}}  ¬✓as
⟦unit₂⟧≡front-¬✓ {I}     {() ∷ as} ¬✓as

-- Units are natural

⟦unit₁⟧-natural : ∀ {S T} (f : Trace S → Trace T) →
  (⟦done⟧ {I} ⟦[&]⟧ f) ⟦⟫⟧ ⟦unit₁⟧ ≃ ⟦unit₁⟧ ⟦⟫⟧ f 
⟦unit₁⟧-natural f []       = refl
⟦unit₁⟧-natural f [✓]      = refl
⟦unit₁⟧-natural f (a ∷ as) = refl

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

⟦unit₂⟧-natural : ∀ {S T} (f : Trace S → Trace T) → (∀ as → f (↓ as) ≡ ↓ (f as)) →
  (f ⟦[&]⟧ ⟦done⟧ {I}) ⟦⟫⟧ ⟦unit₂⟧ ≃ ⟦unit₂⟧ ⟦⟫⟧ f 
⟦unit₂⟧-natural {S} {T} f f-resp-↓ as with ✓? as
⟦unit₂⟧-natural {S} {T} f f-resp-↓ as | no ¬✓as =
  begin
    ⟦unit₂⟧ (f (front {S} as) ++ (back {S} as))
  ≡⟨ cong ⟦unit₂⟧ (cong (_++_ (f (front {S} as))) (I-¬✓-η (λ ✓as₂ → ¬✓as (back-refl-✓ {S} ✓as₂)))) ⟩
    ⟦unit₂⟧ (f (front {S} as) ++ [])
  ≡⟨ ⟦unit₂⟧-++-[] (f (front {S} as)) ⟩
    ↓ (f (front {S} as))
  ≡⟨ sym (f-resp-↓ (front {S} as)) ⟩
    f (↓ (front {S} as))
  ≡⟨ cong f (sym (⟦unit₂⟧≡front-¬✓ ¬✓as)) ⟩
    f (⟦unit₂⟧ as)
  ∎
⟦unit₂⟧-natural {S} {T} f f-resp-↓ as | yes ✓as =
  begin
    ⟦unit₂⟧ (f (front {S} as) ++ (back {S} as))
  ≡⟨ cong ⟦unit₂⟧ (cong (_++_ (f (front {S} as))) (I-✓-η (back-resp-✓ {S} ✓as))) ⟩
    ⟦unit₂⟧ (f (front {S} as) ++ [✓])
  ≡⟨ ⟦unit₂⟧-++-[✓] (f (front {S} as)) ⟩
    f (front {S} as)
  ≡⟨ cong f (sym (⟦unit₂⟧≡front-✓ ✓as)) ⟩
    f (⟦unit₂⟧ as)
  ∎

unit₂-natural : ∀ {S T} (P : S ⇒ T) →
  ⟦ P [&] done {I} ⟫ unit₂ ⟧ ≃ ⟦ unit₂ ⟫ P ⟧ 
unit₂-natural {S} {T} P as = 
  begin
    ⟦ P [&] done {I} ⟫ unit₂ ⟧ as
  ≡⟨ ⟫-≃-⟦⟫⟧ ([&]-semantics P (done {I})) (unit₂-semantics {T}) as ⟩
    (⟦ P ⟧ ⟦[&]⟧ ⟦done⟧ {I} ⟦⟫⟧ ⟦unit₂⟧) as
  ≡⟨ ⟦unit₂⟧-natural ⟦ P ⟧ (⟦⟧-resp-↓ P) as ⟩
     (⟦unit₂⟧ ⟦⟫⟧ ⟦ P ⟧) as
  ≡⟨ sym (⟫-≃-⟦⟫⟧ (unit₂-semantics {S}) ≃-refl as) ⟩
    ⟦ unit₂ ⟫ P ⟧ as
  ∎

-- Associativity is natural

⟦assoc⟧-natural : ∀ {S S' T T' U U'} 
  (f : Trace S → Trace S') (g : Trace T → Trace T') (h : Trace U → Trace U') →
    (∀ bs → (✓ (f bs)) → (✓ bs)) → 
      ((f ⟦[&]⟧ (g ⟦[&]⟧ h)) ⟦⟫⟧ ⟦assoc⟧ {S'} {T'} {U'}) ≃ 
        (⟦assoc⟧ {S} {T} {U} ⟦⟫⟧ ((f ⟦[&]⟧ g) ⟦[&]⟧ h))
⟦assoc⟧-natural {S} {S'} {T} {T'} {U} {U'} f g h f-refl-✓ as = 
  begin
    ⟦assoc⟧ {S'} ((f ⟦[&]⟧ (g ⟦[&]⟧ h)) as)
  ≡⟨ ⟦assoc⟧-++ (f (front {S} as)) (g (front {T} (back {S} as))) (h (back {T} (back {S} as))) ⟩
    (f (front {S} as)
      ++ g (front {T} (back {S} as)))
        ++ h (back {T} (back {S} as))
  ≡⟨ cong₂ _++_ (++-cong (cong f (front-⟦assoc⟧ as)) 
       (λ ✓bs₁ → cong g (mid-⟦assoc⟧ {S} as (f-refl-✓ (front {S} as) ✓bs₁)))) 
         (cong h (back-⟦assoc⟧ {S} as)) ⟩
    (f (front {S} (front {S & T} (⟦assoc⟧ {S} as))) 
      ++ g (back {S} (front {S & T} (⟦assoc⟧ {S} as)))) 
        ++ h (back {S & T} (⟦assoc⟧ {S} as))
  ∎

assoc-natural : ∀ {S S' T T' U U'} (P : S ⇒ S') (Q : T ⇒ T') (R : U ⇒ U') →
  ⟦ P [&] (Q [&] R) ⟫ assoc {S'} {T'} {U'} ⟧ ≃
    ⟦ assoc {S} {T} {U} ⟫ (P [&] Q) [&] R ⟧
assoc-natural {S} {S'} {T} {T'} {U} {U'} P Q R as =
  begin
    ⟦ P [&] (Q [&] R) ⟫ assoc {S'} {T'} {U'} ⟧ as
  ≡⟨ ⟫-≃-⟦⟫⟧ ([&]-≃-⟦[&]⟧ {P = P} ≃-refl ([&]-semantics Q R)) (assoc-semantics {S'} {T'} {U'}) as ⟩
    ((⟦ P ⟧ ⟦[&]⟧ (⟦ Q ⟧ ⟦[&]⟧ ⟦ R ⟧)) ⟦⟫⟧ ⟦assoc⟧ {S'} {T'} {U'}) as
  ≡⟨ ⟦assoc⟧-natural ⟦ P ⟧ ⟦ Q ⟧ ⟦ R ⟧ (⟦⟧-refl-✓ P) as ⟩
    (⟦assoc⟧ {S} {T} {U} ⟦⟫⟧ ((⟦ P ⟧ ⟦[&]⟧ ⟦ Q ⟧) ⟦[&]⟧ ⟦ R ⟧)) as
  ≡⟨ sym (⟫-≃-⟦⟫⟧ (assoc-semantics {S} {T} {U}) ([&]-≃-⟦[&]⟧ ([&]-semantics P Q) ≃-refl) as) ⟩
    ⟦ assoc {S} {T} {U} ⟫ (P [&] Q) [&] R ⟧ as
  ∎
