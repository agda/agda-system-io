open import Coinduction using ( ♭ )
open import System.IO.Transducers.Lazy using ( _⇒_ ; inp ; out ; id ; done ; ⟦_⟧ ; _≃_ ; out* ; discard ; π₁ ; π₂ ; buffer ; _⟨&⟩_ ; swap )
open import System.IO.Transducers.Session using ( I ; Σ ; Γ ; _/_ ; _&_ )
open import System.IO.Transducers.Trace using ( Trace ; _≤_ ; [] ; _∷_ )
open import System.IO.Transducers.Properties.Category using ( _⟦⟫⟧_ )
open import System.IO.Transducers.Properties.Monoidal using ( _++_ ; front ; back ; _⟦[&]⟧_ ; ++-β₁ ; ++-β₂-✓ )
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

-- Semantics of projections

π₁-semantics : ∀ {S T} → ⟦ π₁ {S} {T} ⟧ ≃ front
π₁-semantics {I}     as       = I-η (⟦ discard ⟧ as)
π₁-semantics {Σ V F} []       = refl
π₁-semantics {Σ V F} (a ∷ as) = cong (_∷_ a) (π₁-semantics as)

π₂-semantics : ∀ {S T} → ⟦ π₂ {S} {T} ⟧ ≃ back {S}
π₂-semantics {I}     as       = refl
π₂-semantics {Σ V F} []       = refl
π₂-semantics {Σ V F} (a ∷ as) = π₂-semantics {♭ F a} as

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

⟨&⟩-≃-⟦⟨&⟩⟧ : ∀ {S T U} 
  {P : S ⇒ T} {f : Trace S → Trace T} {Q : S ⇒ U} {g : Trace S → Trace U} →
    (⟦ P ⟧ ≃ f) → (⟦ Q ⟧ ≃ g) → (⟦ P ⟨&⟩ Q ⟧ ≃ f ⟦⟨&⟩⟧ g)
⟨&⟩-≃-⟦⟨&⟩⟧ {S} {T} {U} {P} {f} {Q} {g} P≃f Q≃g as =
  begin
    ⟦ P ⟨&⟩ Q ⟧ as
  ≡⟨ ⟨&⟩-semantics P Q as ⟩
    (⟦ P ⟧ ⟦⟨&⟩⟧ ⟦ Q ⟧) as
  ≡⟨ cong₂ _++_ (P≃f as) (Q≃g as) ⟩
    (f ⟦⟨&⟩⟧ g) as
  ∎

-- Semantics of swap

⟦swap⟧ : ∀ {S T} → (Trace (S & T) → Trace (T & S))
⟦swap⟧ {S} as = back {S} as ++ front {S} as

swap-semantics : ∀ {S T} → ⟦ swap {S} {T} ⟧ ≃ ⟦swap⟧ {S} {T}
swap-semantics {S} = ⟨&⟩-≃-⟦⟨&⟩⟧ (π₂-semantics {S}) (π₁-semantics {S})
  