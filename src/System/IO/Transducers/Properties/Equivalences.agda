open import Coinduction using ( ♯_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; cong ; subst )
open import System.IO.Transducers.Lazy using ( _⇒_ ; inp ; out ; done ; ⟦_⟧ ; _≃_ )
open import System.IO.Transducers.Strict using ( Strict )
open import System.IO.Transducers.Session using ( Session ; I ; Σ ; _/_ )
open import System.IO.Transducers.Trace using ( Trace ; [] ; _∷_ ; _✓ ; _⊑_ )
open import System.IO.Transducers.Properties.Lemmas using ( I-η ; ⟦⟧-mono ; ⟦⟧-resp-✓ ; ⟦⟧-resp-[] )
open import System.IO.Transducers.Properties.Category using ( _≣_ ; ⟦⟧-refl-≣ )

module System.IO.Transducers.Properties.Equivalences where

open Relation.Binary.PropositionalEquality.≡-Reasoning

_//_ : ∀ S → (Trace S) → Session
S // [] = S
S // (a ∷ as) = (S / a) // as

suffix : ∀ {S} {as bs : Trace S} → (as ⊑ bs) → (Trace (S // as))
suffix {bs = bs} [] = bs
suffix (a ∷ as⊑bs) = suffix as⊑bs

_+++_ : ∀ {S} (as : Trace S) (bs : Trace (S // as)) → (Trace S)
[]       +++ bs = bs
(a ∷ as) +++ bs = a ∷ (as +++ bs)

suffix-+++ : ∀ {S} {as : Trace S} {bs} (as⊑bs : as ⊑ bs) → 
  as +++ suffix as⊑bs ≡ bs
suffix-+++ []          = refl
suffix-+++ (a ∷ as⊑bs) = cong (_∷_ a) (suffix-+++ as⊑bs)

suffix-mono : ∀ {S} {as : Trace S} {bs cs} (as⊑bs : as ⊑ bs) (as⊑cs : as ⊑ cs) →
  (bs ⊑ cs) → (suffix as⊑bs ⊑ suffix as⊑cs)
suffix-mono []           []           bs⊑cs       = bs⊑cs
suffix-mono (.a ∷ as⊑bs) (.a ∷ as⊑cs) (a ∷ bs⊑cs) = suffix-mono as⊑bs as⊑cs bs⊑cs

suffix-resp-✓ : ∀ {S} {as : Trace S} {bs} (as⊑bs : as ⊑ bs) →
  (bs ✓) → (suffix as⊑bs ✓)
suffix-resp-✓ []           bs✓       = bs✓
suffix-resp-✓ (.a ∷ as⊑bs) (a ∷ bs✓) = suffix-resp-✓ as⊑bs bs✓

suffix-[] : ∀ {S} {as : Trace S} (as⊑as : as ⊑ as) → 
  (suffix as⊑as ≡ [])
suffix-[] [] = refl
suffix-[] (a ∷ as⊑as) = suffix-[] as⊑as

strictify : ∀ {S T} (f : Trace S → Trace T) →
  (∀ as bs → as ⊑ bs → f as ⊑ f bs) →
    (Trace S → Trace (T // f []))
strictify f f-mono as = suffix (f-mono [] as [])

lazify : ∀ {S T} (f : Trace S → Trace T) a → 
  (Trace (S / a) → Trace T) 
lazify f a as = f (a ∷ as)

strictify-mono : ∀ {S T} (f : Trace S → Trace T) f-mono →
  (∀ as bs → as ⊑ bs → strictify f f-mono as ⊑ strictify f f-mono bs)
strictify-mono f f-mono as bs as⊑bs = suffix-mono (f-mono [] as []) (f-mono [] bs []) (f-mono as bs as⊑bs)

strictify-resp-✓ : ∀ {S T} (f : Trace S → Trace T) f-mono →
  (∀ as → as ✓ → f as ✓) →
    (∀ as → as ✓ → strictify f f-mono as ✓)
strictify-resp-✓ f f-mono f-resp-✓ as as✓ = suffix-resp-✓ (f-mono [] as []) (f-resp-✓ as as✓)

strictify-strict : ∀ {S T} (f : Trace S → Trace T) f-mono →
  (strictify f f-mono [] ≡ [])
strictify-strict f f-mono = suffix-[] (f-mono [] [] [])

lazify-mono : ∀ {S T} (f : Trace S → Trace T) a →
  (∀ as bs → as ⊑ bs → f as ⊑ f bs) →
    (∀ as bs → as ⊑ bs → lazify f a as ⊑ lazify f a bs)
lazify-mono f a f-mono as bs as⊑bs = f-mono (a ∷ as) (a ∷ bs) (a ∷ as⊑bs)

lazify-resp-✓ : ∀ {S T} (f : Trace S → Trace T) a →
  (∀ as → as ✓ → f as ✓) →
    (∀ as → as ✓ → lazify f a as ✓) 
lazify-resp-✓ f a f-resp-✓ as as✓ = f-resp-✓ (a ∷ as) (a ∷ as✓)

mutual

  lazy' : ∀ {T S} bs (f : Trace S → Trace (T // bs)) →
    (∀ as bs → as ⊑ bs → f as ⊑ f bs) →
      (∀ as → as ✓ → f as ✓) → (f [] ≡ []) →
        (S ⇒ T)
  lazy' [] f f-mono f-resp-✓ f-strict = strict f f-mono f-resp-✓ f-strict 
  lazy' {Σ V F} (b ∷ bs) f f-mono f-resp-✓ f-strict = out b (lazy' bs f f-mono f-resp-✓ f-strict)
  lazy' {I} (() ∷ bs) f f-mono f-resp-✓ f-strict
   
  lazy : ∀ {T S} (f : Trace S → Trace T) →
    (∀ as bs → as ⊑ bs → f as ⊑ f bs) →
      (∀ as → as ✓ → f as ✓) →
        (S ⇒ T)
  lazy f f-mono f-resp-✓ = lazy' (f []) (strictify f f-mono) (strictify-mono f f-mono) (strictify-resp-✓ f f-mono f-resp-✓) (strictify-strict f f-mono)

  strict : ∀ {S T} (f : Trace S → Trace T) →
    (∀ as bs → as ⊑ bs → f as ⊑ f bs) →
      (∀ as → as ✓ → f as ✓) → (f [] ≡ []) →
        (S ⇒ T)
  strict {I} {I} f f-mono f-resp-✓ f-strict = done
  strict {Σ V F} f f-mono f-resp-✓ f-strict = inp (♯ λ a → lazy (lazify f a) (lazify-mono f a f-mono) (lazify-resp-✓ f a f-resp-✓))
  strict {I} {Σ W G} f f-mono f-resp-✓ f-strict with subst _✓ f-strict (f-resp-✓ [] [])
  strict {I} {Σ W G} f f-mono f-resp-✓ f-strict | ()

mutual

  lazy'-⟦⟧ : ∀ {T S} bs (f : Trace S → Trace (T // bs)) f-mono f-resp-✓ f-strict →
    ∀ as → ⟦ lazy' bs f f-mono f-resp-✓ f-strict ⟧ as ≡ bs +++ f as
  lazy'-⟦⟧ [] f f-mono f-resp-✓ f-strict as = strict-⟦⟧ f f-mono f-resp-✓ f-strict as
  lazy'-⟦⟧ {Σ W G} (b ∷ bs)  f f-mono f-resp-✓ f-strict as = cong (_∷_ b) (lazy'-⟦⟧ bs f f-mono f-resp-✓ f-strict as)
  lazy'-⟦⟧ {I}     (() ∷ bs) f f-mono f-resp-✓ f-strict as

  lazy-⟦⟧ : ∀ {S T} (f : Trace S → Trace T) f-mono f-resp-✓ →
    ⟦ lazy f f-mono f-resp-✓ ⟧ ≃ f
  lazy-⟦⟧ f f-mono f-resp-✓ as =
    begin
      ⟦ lazy f f-mono f-resp-✓ ⟧ as
    ≡⟨ lazy'-⟦⟧ (f []) (strictify f f-mono) (strictify-mono f f-mono) (strictify-resp-✓ f f-mono f-resp-✓) (strictify-strict f f-mono) as ⟩
      f [] +++ strictify f f-mono as
    ≡⟨ suffix-+++ (f-mono [] as []) ⟩
      f as
    ∎

  strict-⟦⟧ : ∀ {S T} (f : Trace S → Trace T) f-mono f-resp-✓ f-strict →
    ⟦ strict f f-mono f-resp-✓ f-strict ⟧ ≃ f
  strict-⟦⟧ {I} {I} f f-mono f-resp-✓ f-strict [] = sym (I-η (f []))
  strict-⟦⟧ {Σ V F} f f-mono f-resp-✓ f-strict [] = sym f-strict
  strict-⟦⟧ {Σ V F} f f-mono f-resp-✓ f-strict (a ∷ as) = lazy-⟦⟧ (lazify f a) (lazify-mono f a f-mono) (lazify-resp-✓ f a f-resp-✓) as
  strict-⟦⟧ {I} {Σ W G} f f-mono f-resp-✓ f-strict as with subst _✓ f-strict (f-resp-✓ [] [])
  strict-⟦⟧ {I} {Σ W G} f f-mono f-resp-✓ f-strict as | ()
  strict-⟦⟧ {I} f f-mono f-resp-✓ f-strict (() ∷ as)
  
⟦⟧-lazy : ∀ {S T} (P : S ⇒ T) →
  lazy ⟦ P ⟧ (⟦⟧-mono P) (⟦⟧-resp-✓ P) ≣ P
⟦⟧-lazy P = ⟦⟧-refl-≣ (lazy ⟦ P ⟧ (⟦⟧-mono P) (⟦⟧-resp-✓ P)) P (lazy-⟦⟧ ⟦ P ⟧ (⟦⟧-mono P) (⟦⟧-resp-✓ P))

⟦⟧-strict : ∀ {S T} (P : S ⇒ T) (#P : Strict P) →
  strict ⟦ P ⟧ (⟦⟧-mono P) (⟦⟧-resp-✓ P) (⟦⟧-resp-[] #P) ≣ P
⟦⟧-strict P #P = ⟦⟧-refl-≣ (strict ⟦ P ⟧ (⟦⟧-mono P) (⟦⟧-resp-✓ P) (⟦⟧-resp-[] #P)) P (strict-⟦⟧ ⟦ P ⟧ (⟦⟧-mono P) (⟦⟧-resp-✓ P) (⟦⟧-resp-[] #P))
