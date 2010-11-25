open import Coinduction using ( ♭ )
open import Data.Empty using ( ⊥-elim )
open import System.IO.Transducers.Lazy 
  using ( _⇒_ ; inp ; out ; id ; done ; ⟦_⟧ ; _≃_ ; out* ; π₁ ; π₂ ; buffer ; _⟨&⟩_ ; swap )
open import System.IO.Transducers.Session using ( I ; Σ ; IsΣ ; _&_ )
open import System.IO.Transducers.Trace using ( Trace ; ✓ ; _≤_ ; [] ; _∷_ )
open import System.IO.Transducers.Properties.Lemmas
  using ( ✓? ; ¬✓[] ; I-✓ ; I-η ; reflective )
open import System.IO.Transducers.Properties.Category using ( _⟦⟫⟧_ )
open import System.IO.Transducers.Properties.Monoidal 
  using ( _++_ ; front ; back ; _⟦[&]⟧_ ; ++-cong ; ++-β₁ ; ++-β₂ ; ++-β₂-[] ; ++-η )
open import Relation.Binary.PropositionalEquality 
  using ( _≡_ ; sym ; refl ; cong ; cong₂ )
open import Relation.Nullary using ( Dec ; yes ; no )

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

π₁-semantics : ∀ {S T isΣ} → ⟦ π₁ {S} {T} {isΣ} ⟧ ≃ reflective front
π₁-semantics as = {!!}

π₂-semantics : ∀ {S T isΣ} → ⟦ π₂ {S} {T} {isΣ} ⟧ ≃ back {S}
π₂-semantics {I}             as       = refl
π₂-semantics {Σ V F} {Σ W G} []       = refl
π₂-semantics {Σ V F} {Σ W G} (a ∷ as) = π₂-semantics {♭ F a} as
π₂-semantics {Σ V F} {I}  {} as

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

-- Semantics of delay'

⟦delay'⟧ : ∀ {S T} → (S ≤ T) → (Trace S) → (Trace T)
⟦delay'⟧ cs as with ✓? as
⟦delay'⟧ cs as | yes ✓as = revApp cs as
⟦delay'⟧ cs as | no ¬✓as = []

-- Semantics of delay

⟦delay⟧ : ∀ {S} → (Trace S) → (Trace S)
⟦delay⟧ as with ✓? as
⟦delay⟧ as | yes ✓as = as
⟦delay⟧ as | no ¬✓as = []

-- Semantics of swap

⟦swap⟧ : ∀ {S T} → (Trace (S & T) → Trace (T & S))
⟦swap⟧ {S} as = back {S} as ++ front {S} as

swap-semantics : ∀ {S T} → ⟦ swap {S} {T} ⟧ ≃ ⟦swap⟧ {S} {T}
swap-semantics {S} as = {!!}

-- Swap is natural

⟦swap⟧-natural : ∀ {S T U V} → (f : Trace S → Trace T) → (g : Trace U → Trace V) →
  (∀ as → (✓ (f as)) → (✓ as)) → (∀ as → (✓ as) → (✓ (f as))) → 
    (∀ as → (✓ (g as)) → (✓ as)) → (g [] ≡ []) →
      (f ⟦[&]⟧ g ⟦⟫⟧ ⟦swap⟧ {T} {V}) ≃ (⟦swap⟧ {S} {U} ⟦⟫⟧ g ⟦[&]⟧ f)
⟦swap⟧-natural {S} {T} {U} {V} f g f-refl-✓ f-resp-✓ g-refl-✓ g-resp-[] as with ✓? (front {S} as)
⟦swap⟧-natural {S} {T} {U} {V} f g f-refl-✓ f-resp-✓ g-refl-✓ g-resp-[] as | yes ✓as₁ =
  begin
    back {T} (f (front {S} as) ++ g (back {S} as))
      ++ front {T} (f (front {S} as) ++ g (back {S} as))
  ≡⟨ cong₂ _++_ (++-β₂ (f-resp-✓ (front {S} as) ✓as₁) (g (back {S} as))) 
       (++-β₁ (f (front {S} as)) (g (back {S} as))) ⟩
    g (back {S} as)
      ++ f (front {S} as)
  ≡⟨ ++-cong (cong g (sym (++-β₁ (back {S} as) (front {S} as))))
       (λ ✓gas₂ → cong f (sym (++-β₂ (g-refl-✓ (back {S} as) ✓gas₂) (front {S} as)))) ⟩
    g (front {U} (back {S} as ++ front {S} as))
      ++ f (back {U} (back {S} as ++ front {S} as))
  ∎
⟦swap⟧-natural {S} {T} {I} {I} f g f-refl-✓ f-resp-✓ g-refl-✓ g-resp-[] as | no ¬✓as₁ =
  begin
    back {T} (f (front {S} as) ++ g (back {S} as))
      ++ front {T} (f (front {S} as) ++ g (back {S} as))
  ≡⟨ cong₂ _++_ 
       (++-β₂-[] (λ ✓fas₁ → ¬✓as₁ (f-refl-✓ (front {S} as) ✓fas₁)) (g (back {S} as))) 
       refl ⟩
    [] {I}
      ++ front {T} (f (front {S} as) ++ g (back {S} as))
  ≡⟨ cong₂ _++_ (sym g-resp-[]) (++-β₁ (f (front {S} as)) (g (back {S} as))) ⟩
    g []
      ++ f (front {S} as)
  ≡⟨ cong₂ _++_ (cong g (sym (I-η (front {I} (back {S} as ++ front {S} as)))))
       (cong f (sym (++-β₂ (I-✓ (back {S} as)) (front {S} as)))) ⟩
    g (front {I} (back {S} as ++ front {S} as))
      ++ f (back {I} (back {S} as ++ front {S} as))
  ∎
⟦swap⟧-natural {S} {T} {U} {Σ W G} f g f-refl-✓ f-resp-✓ g-refl-✓ g-resp-[] as | no ¬✓as₁ = 
  begin
    back {T} (f (front {S} as) ++ g (back {S} as))
      ++ front {T} (f (front {S} as) ++ g (back {S} as))
  ≡⟨ cong₂ _++_ 
       (++-β₂-[] (λ ✓fas₁ → ¬✓as₁ (f-refl-✓ (front {S} as) ✓fas₁)) (g (back {S} as))) 
       refl ⟩
    [] {Σ W G}
      ++ front {T} (f (front {S} as) ++ g (back {S} as))
  ≡⟨ cong₂ _++_ (sym g-resp-[]) refl ⟩
    g []
      ++ f (back {U} (back {S} as ++ front {S} as))
  ≡⟨ cong₂ _++_ (cong g (sym (++-β₂-[] ¬✓as₁ (back {S} as)))) refl ⟩
    g (back {S} (front {S} as ++ back {S} as))
      ++ f (back {U} (back {S} as ++ front {S} as))
  ≡⟨ cong₂ _++_ (cong g (cong (back {S}) (++-η {S} as))) refl ⟩
    g (back {S} as)
      ++ f (back {U} (back {S} as ++ front {S} as))
  ≡⟨ cong₂ _++_ (cong g (sym (++-β₁ (back {S} as) (front {S} as)))) refl ⟩
    g (front {U} (back {S} as ++ front {S} as))
      ++ f (back {U} (back {S} as ++ front {S} as))
  ∎
⟦swap⟧-natural {S} {T} {Σ W G} {I} f g f-refl-✓ f-resp-✓ g-refl-✓ g-resp-[] as | no ¬✓as₁ =
   ⊥-elim (¬✓[] (g-refl-✓ [] (I-✓ (g []))))
