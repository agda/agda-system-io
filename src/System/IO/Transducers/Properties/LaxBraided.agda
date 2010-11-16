open import Coinduction using ( ♭ )
open import System.IO.Transducers.Lazy using ( _⇒_ ; inp ; out ; id ; done ; ⟦_⟧ ; _≃_ ; out* ; π₁ ; π₂ ; buffer ; _⟨&⟩_ ; swap )
open import System.IO.Transducers.Session using ( I ; Σ ; Γ ; _/_ ; _&_ )
open import System.IO.Transducers.Trace using ( Trace ; _≤_ ; [] ; _∷_ )
open import System.IO.Transducers.Properties.Monoidal using ( _++_ ; front ; back )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; sym ; refl ; cong ; cong₂ )

module System.IO.Transducers.Properties.LaxBraided where

open Relation.Binary.PropositionalEquality.≡-Reasoning

-- Semantics of out*

revApp : ∀ {S T} → (S ≤ T) → (Trace S) → (Trace T)
revApp []       bs = bs
revApp (a ∷ as) bs = revApp as (a ∷ bs)

⟦out*⟧ : ∀ {S T U} → (T ≤ U) → (Trace S → Trace T) → (Trace S → Trace U)
⟦out*⟧ cs f as = revApp cs (f as)

out*-semantics : ∀ {S T U} (cs : T ≤ U) (P : S ⇒ T) →
  ⟦ out* cs P ⟧ ≃ ⟦out*⟧ cs ⟦ P ⟧
out*-semantics [] P as = refl
out*-semantics (c ∷ cs) P as = out*-semantics cs (out c P) as

-- Eta conversion for session I

I-η : ∀ (as : Trace I) → (as ≡ [])
I-η [] = refl
I-η (() ∷ _)

-- Semantics of buffering

⟦buffer⟧ : ∀ {S T U V} → (Trace S → Trace T) → (Trace S → Trace U) → (U ≤ V) → (Trace S → Trace (T & V))
⟦buffer⟧ f g cs as = f as ++ revApp cs (g as)

buffer-semantics : ∀ {S T U V} (P : S ⇒ T) (Q : S ⇒ U) (cs : U ≤ V) →
  ⟦ buffer P Q cs ⟧ ≃ ⟦buffer⟧ ⟦ P ⟧ ⟦ Q ⟧ cs
buffer-semantics {I}             (inp {} P) Q         cs as
buffer-semantics {Σ V F} {I}     (inp P)    Q         cs as       = cong₂ _++_ (sym (I-η (⟦ inp P ⟧ as))) (out*-semantics cs Q as)
buffer-semantics {Σ V F} {Σ W G} (inp P)    (inp Q)   cs []       = refl
buffer-semantics {Σ V F} {Σ W G} (inp P)    (inp Q)   cs (a ∷ as) = buffer-semantics (♭ P a) (♭ Q a) cs as
buffer-semantics {Σ V F} {Σ W G} (inp P)    (out c Q) cs as       = buffer-semantics (inp P) Q (c ∷ cs) as
buffer-semantics {Σ V F} {Σ W G} (inp P)    (id refl) cs []       = refl
buffer-semantics {Σ V F} {Σ W G} (inp P)    (id refl) cs (a ∷ as) = buffer-semantics (♭ P a) (id refl) (a ∷ cs) as
buffer-semantics {S}     {I}     (out () P) Q         cs as
buffer-semantics {I}     {Σ W G} (out b P)  Q         cs as       = cong (_∷_ b) (buffer-semantics P Q cs as)
buffer-semantics {Σ V F} {Σ W G} (out b P)  Q         cs as       = cong (_∷_ b) (buffer-semantics P Q cs as)
buffer-semantics {I}             (id refl)  Q         cs as       = cong₂ _++_ (sym (I-η as)) (out*-semantics cs Q as)
buffer-semantics {Σ V F}         (id refl)  (inp Q)   cs []       = refl
buffer-semantics {Σ V F}         (id refl)  (inp Q)   cs (a ∷ as) = cong (_∷_ a) (buffer-semantics (id refl) (♭ Q a) cs as)
buffer-semantics {Σ V F}         (id refl)  (out c Q) cs as       = buffer-semantics (id refl) Q (c ∷ cs) as
buffer-semantics {Σ V F}         (id refl)  (id refl) cs []       = refl
buffer-semantics {Σ V F}         (id refl)  (id refl) cs (a ∷ as) = cong (_∷_ a) (buffer-semantics (id refl) (id refl) (a ∷ cs) as)

-- Semantics of pairing

_⟦⟨&⟩⟧_ : ∀ {S T U} → (Trace S → Trace T) → (Trace S → Trace U) → (Trace S → Trace (T & U))
(f ⟦⟨&⟩⟧ g) as = f as ++ g as

⟨&⟩-semantics : ∀ {S T U} → (P : S ⇒ T) (Q : S ⇒ U) →
  ⟦ P ⟨&⟩ Q ⟧ ≃ ⟦ P ⟧ ⟦⟨&⟩⟧ ⟦ Q ⟧
⟨&⟩-semantics P Q as = buffer-semantics P Q [] as

