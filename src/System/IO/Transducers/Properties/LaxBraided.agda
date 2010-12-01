open import Coinduction using ( ♭ )
open import Data.Empty using ( ⊥-elim )
open import Data.Sum using ( _⊎_ ; inj₁ ; inj₂ )
open import System.IO.Transducers.Lazy 
  using ( _⇒_ ; inp ; out ; id ; done ; ⟦_⟧ ; _≃_ ; out* ;
     _⟫_ ;_[&]_ ; unit₁ ; unit₂ ; assoc ; assoc⁻¹ ; swap'' ; swap' ; swap )
open import System.IO.Transducers.Strict using ( Strict )
open import System.IO.Transducers.Session using ( I ; Σ ; IsΣ ; _&_ )
open import System.IO.Transducers.Trace using ( Trace ; ✓ ; _≤_ ; [] ; _∷_ )
open import System.IO.Transducers.Properties.Lemmas
  using ( ✓? ; ¬✓[] ; I-✓ ; I-η ; ⟦⟧-resp-✓ ; ⟦⟧-refl-✓ ; ⟦⟧-resp-[] )
open import System.IO.Transducers.Properties.Category 
  using ( ⟦done⟧ ; _⟦⟫⟧_ ; ⟫-≃-⟦⟫⟧ ; done-semantics )
open import System.IO.Transducers.Properties.Monoidal 
  using ( _++_ ; front ; back ; _⟦[&]⟧_ ; ⟦unit₁⟧ ; ⟦unit₂⟧ ; ⟦assoc⟧ ; ⟦assoc⁻¹⟧ ;
    ++-cong ; ++-β₁ ; ++-β₂ ; ++-β₂-[] ; ++-η ; back≡[] ; back-resp-[] ; ++-resp-[] ;
    ++-refl-✓₁ ; ++-refl-✓₂ ; front-refl-✓ ; back-refl-✓ ; ++-resp-✓ ; front-resp-✓ ;
    ⟦[&]⟧-++ ; ⟦assoc⟧-++ ; ⟦assoc⁻¹⟧-++ ; 
    [&]-≃-⟦[&]⟧ ; [&]-semantics ; 
    assoc-semantics ; assoc⁻¹-semantics ; 
    unit₁-semantics ; unit₂-semantics ; unit₂⁻¹-semantics )
open import Relation.Binary.PropositionalEquality 
  using ( _≡_ ; sym ; refl ; trans ; cong ; cong₂ )
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

-- Semantics of swap

⟦swap''⟧ : ∀ {T U} → (I ≤ U) → (Trace T) → (Trace (T & U))
⟦swap''⟧ cs as = as ++ revApp cs []

⟦swap'⟧ : ∀ {S T U} → (S ≤ U) → (Trace (S & T)) → (Trace (T & U))
⟦swap'⟧ {S} cs as = back {S} as ++ revApp cs (front {S} as)

⟦swap⟧ : ∀ {S T} → (Trace (S & T) → Trace (T & S))
⟦swap⟧ {S} as = back {S} as ++ front {S} as

swap''-semantics : ∀ {T U} cs → ⟦ swap'' {T} {U} cs ⟧ ≃ ⟦swap''⟧ cs
swap''-semantics {I}     cs []       = out*-semantics cs done []
swap''-semantics {Σ W G} cs []       = refl
swap''-semantics {Σ W G} cs (a ∷ as) = cong (_∷_ a) (swap''-semantics cs as)
swap''-semantics {I}     cs (() ∷ as)

swap'-semantics : ∀ {S T isΣ U} cs → ⟦ swap' {S} {T} {isΣ} {U} cs ⟧ ≃ ⟦swap'⟧ cs
swap'-semantics {I}             cs as       = swap''-semantics cs as
swap'-semantics {Σ V F} {Σ W G} cs []       = refl
swap'-semantics {Σ V F} {Σ W G} cs (a ∷ as) = swap'-semantics (a ∷ cs) as
swap'-semantics {Σ V F} {I}  {} cs as

swap-semantics : ∀ {S T} → ⟦ swap {S} {T} ⟧ ≃ ⟦swap⟧ {S} {T}
swap-semantics {I}             as = unit₂⁻¹-semantics as
swap-semantics {Σ V F} {I}     as = cong₂ _++_ (sym (I-η (back {Σ V F} as))) (unit₂-semantics as)
swap-semantics {Σ V F} {Σ W G} as = swap'-semantics {Σ V F} [] as

-- Swap reflects completion

⟦swap⟧-refl-✓ : ∀ {S T} as → (✓ (⟦swap⟧ {S} {T} as)) → (✓ as)
⟦swap⟧-refl-✓ {S} {I}     as ✓bs = front-refl-✓ {S} as (++-refl-✓₂ {I} {S} {back {S} as} ✓bs)
⟦swap⟧-refl-✓ {S} {Σ W G} as ✓bs = back-refl-✓ {S} as (++-refl-✓₁ {Σ W G} ✓bs)

-- Swap plays nicely with concatenation

⟦swap⟧-++ : ∀ {S T} (as : Trace S) (bs : Trace T) → (✓ as ⊎ bs ≡ []) →  
  ⟦swap⟧ {S} {T} (as ++ bs) ≡ bs ++ as
⟦swap⟧-++ as bs ✓as/bs≡[] with ✓? as
⟦swap⟧-++ as bs ✓as/bs≡[]    | yes ✓as = cong₂ _++_ (++-β₂ ✓as bs) (++-β₁ as bs)
⟦swap⟧-++ as bs (inj₁ ✓as)   | no ¬✓as = cong₂ _++_ (++-β₂ ✓as bs) (++-β₁ as bs)
⟦swap⟧-++ as bs (inj₂ bs≡[]) | no ¬✓as = cong₂ _++_ (trans (++-β₂-[] ¬✓as bs) (sym bs≡[])) (++-β₁ as bs)

-- Swap is natural when f respects completion, and g reflects completion and is strict

⟦swap⟧-natural : ∀ {S T U V} → (f : Trace S → Trace T) → (g : Trace U → Trace V) →
  (∀ as → (✓ as) → (✓ (f as))) → 
    (∀ as → (✓ (g as)) → (✓ as)) → (g [] ≡ []) →
      (f ⟦[&]⟧ g ⟦⟫⟧ ⟦swap⟧ {T} {V}) ≃ (⟦swap⟧ {S} {U} ⟦⟫⟧ g ⟦[&]⟧ f)
⟦swap⟧-natural {S} {T} {U} {V} f g f-resp-✓ g-refl-✓ g-resp-[] as =
  begin
    ⟦swap⟧ {T} {V} (f as₁ ++ g as₂)
  ≡⟨ ⟦swap⟧-++ (f as₁) (g as₂) ✓fas₁/gas₂≡[] ⟩
    g as₂ ++ f as₁
  ≡⟨ sym (⟦[&]⟧-++ g f g-refl-✓ as₂ as₁) ⟩
    (g ⟦[&]⟧ f) (as₂ ++ as₁)
  ∎ where
  as₁ = front {S} as
  as₂ = back {S} as
  ✓fas₁/gas₂≡[] : ✓ (f as₁) ⊎ g as₂ ≡ []
  ✓fas₁/gas₂≡[] with ✓? as₁
  ✓fas₁/gas₂≡[] | yes ✓as₁ = inj₁ (f-resp-✓ as₁ ✓as₁)
  ✓fas₁/gas₂≡[] | no ¬✓as₁ = inj₂ (trans (cong g (back≡[] ¬✓as₁)) g-resp-[])

swap-natural : ∀ {S T U V} (P : S ⇒ T) {Q : U ⇒ V} → (Strict Q) →
  ⟦ P [&] Q ⟫ swap {T} {V} ⟧ ≃ ⟦ swap {S} {U} ⟫ Q [&] P ⟧
swap-natural {S} {T} {U} {V} P {Q} #Q as =
  begin
    ⟦ P [&] Q ⟫ swap {T} {V} ⟧ as
  ≡⟨ ⟫-≃-⟦⟫⟧ ([&]-semantics P Q) (swap-semantics {T} {V}) as ⟩
    (⟦ P ⟧ ⟦[&]⟧ ⟦ Q ⟧ ⟦⟫⟧ ⟦swap⟧ {T} {V}) as
  ≡⟨ ⟦swap⟧-natural ⟦ P ⟧ ⟦ Q ⟧ (⟦⟧-resp-✓ P) (⟦⟧-refl-✓ Q) (⟦⟧-resp-[] #Q) as ⟩
    (⟦swap⟧ {S} {U} ⟦⟫⟧ ⟦ Q ⟧ ⟦[&]⟧ ⟦ P ⟧) as
  ≡⟨ sym (⟫-≃-⟦⟫⟧ (swap-semantics {S} {U}) ([&]-semantics Q P) as) ⟩
    ⟦ swap {S} {U} ⟫ Q [&] P ⟧ as
  ∎

-- Coherence of swap with units

⟦swap⟧-⟦unit₁⟧ : ∀ {S} →
  ⟦swap⟧ {S} {I} ⟦⟫⟧ ⟦unit₁⟧ ≃ ⟦unit₂⟧
⟦swap⟧-⟦unit₁⟧ {S} as = cong₂ _++_ (I-η (back {S} as)) refl

swap-unit₁ : ∀ {S} →
  ⟦ swap {S} {I} ⟫ unit₁ ⟧ ≃ ⟦ unit₂ ⟧
swap-unit₁ {S} as = 
  begin
    ⟦ swap {S} {I} ⟫ unit₁ ⟧ as
  ≡⟨ ⟫-≃-⟦⟫⟧ (swap-semantics {S}) unit₁-semantics as ⟩
    (⟦swap⟧ {S} {I} ⟦⟫⟧ ⟦unit₁⟧) as
  ≡⟨ ⟦swap⟧-⟦unit₁⟧ as ⟩
    ⟦unit₂⟧ as
  ≡⟨ sym (unit₂-semantics as) ⟩
    ⟦ unit₂ ⟧ as
  ∎
  
⟦swap⟧-⟦unit₂⟧ : ∀ {S} →
  ⟦swap⟧ {I} {S} ⟦⟫⟧ ⟦unit₂⟧ ≃ ⟦unit₁⟧
⟦swap⟧-⟦unit₂⟧ as = ++-β₁ as []

swap-unit₂ : ∀ {S} →
  ⟦ swap {I} {S} ⟫ unit₂ ⟧ ≃ ⟦ unit₁ ⟧
swap-unit₂ {S} as = 
  begin
    ⟦ swap {I} {S} ⟫ unit₂ ⟧ as
  ≡⟨ ⟫-≃-⟦⟫⟧ (swap-semantics {I}) (unit₂-semantics {S}) as ⟩
    (⟦swap⟧ {I} {S} ⟦⟫⟧ ⟦unit₂⟧) as
  ≡⟨ ⟦swap⟧-⟦unit₂⟧ as ⟩
    ⟦unit₁⟧ as
  ≡⟨ sym (unit₁-semantics as) ⟩
    ⟦ unit₁ ⟧ as
  ∎

-- Coherence of swap with associators

⟦swap⟧-⟦assoc⟧ : ∀ {S T U} →
  ⟦assoc⟧ {S} {T} {U} ⟦⟫⟧ ⟦swap⟧ {S & T} {U} ⟦⟫⟧ ⟦assoc⟧ {U} {S} {T} 
    ≃ ⟦done⟧ {S} ⟦[&]⟧ ⟦swap⟧ {T} {U} ⟦⟫⟧ 
        ⟦assoc⟧ {S} {U} {T} ⟦⟫⟧ ⟦swap⟧ {S} {U} ⟦[&]⟧ ⟦done⟧ {T}
⟦swap⟧-⟦assoc⟧ {S} {T} {U} as =
  begin
    ⟦assoc⟧ {U} {S} {T} (⟦swap⟧ {S & T} {U} ((as₁ ++ as₂) ++ as₃))
  ≡⟨ cong (⟦assoc⟧ {U} {S} {T}) (⟦swap⟧-++ (as₁ ++ as₂) as₃ ✓as₁₂/as₃≡[]) ⟩
    ⟦assoc⟧ {U} {S} {T} (as₃ ++ as₁ ++ as₂)
  ≡⟨ ⟦assoc⟧-++ as₃ as₁ as₂ ⟩
    (as₃ ++ as₁) ++ as₂
  ≡⟨ cong₂ _++_ (sym (⟦swap⟧-++ as₁ as₃ ✓as₁/as₃≡[])) refl ⟩
    ⟦swap⟧ {S} {U} (as₁ ++ as₃) ++ as₂
  ≡⟨ (sym (⟦[&]⟧-++ (⟦swap⟧ {S} {U}) ⟦done⟧ (⟦swap⟧-refl-✓ {S} {U}) (as₁ ++ as₃) as₂)) ⟩
    (⟦swap⟧ {S} {U} ⟦[&]⟧ ⟦done⟧ {T}) ((as₁ ++ as₃) ++ as₂)
  ≡⟨ cong (⟦swap⟧ {S} {U} ⟦[&]⟧ ⟦done⟧ {T}) (sym (⟦assoc⟧-++ as₁ as₃ as₂)) ⟩
    (⟦swap⟧ {S} {U} ⟦[&]⟧ ⟦done⟧ {T}) (⟦assoc⟧ {S} {U} {T} (as₁ ++ as₃ ++ as₂))
  ∎ where
  as₁ = front {S} as
  as₂ = front {T} (back {S} as)
  as₃ = back {T} (back {S} as)
  ✓as₁₂/as₃≡[] : ✓ (as₁ ++ as₂) ⊎ as₃ ≡ []
  ✓as₁₂/as₃≡[] with ✓? as₁ | ✓? as₂
  ✓as₁₂/as₃≡[] | yes ✓as₁ | yes ✓as₂ = inj₁ (++-resp-✓ ✓as₁ ✓as₂)
  ✓as₁₂/as₃≡[] | _        | no ¬✓as₂ = inj₂ (back≡[] ¬✓as₂)
  ✓as₁₂/as₃≡[] | no ¬✓as₁ | _        = inj₂ (back-resp-[] {T} (back≡[] ¬✓as₁))
  ✓as₁/as₃≡[] : ✓ as₁ ⊎ as₃ ≡ []
  ✓as₁/as₃≡[] with ✓? as₁
  ✓as₁/as₃≡[] | yes ✓as₁ = inj₁ ✓as₁
  ✓as₁/as₃≡[] | no ¬✓as₁ = inj₂ (back-resp-[] {T} (back≡[] ¬✓as₁))


swap-assoc : ∀ {S T U} →
  ⟦ assoc {S} {T} {U} ⟫ swap {S & T} {U} ⟫ assoc {U} {S} {T} ⟧
    ≃ ⟦ done {S} [&] swap {T} {U} ⟫ assoc {S} {U} {T} ⟫ swap {S} {U} [&] done {T} ⟧
swap-assoc {S} {T} {U} as =
  begin
    ⟦ assoc {S} {T} {U} ⟫ swap {S & T} {U} ⟫ assoc {U} {S} {T} ⟧ as
  ≡⟨ ⟫-≃-⟦⟫⟧ (assoc-semantics {S} {T} {U}) 
       (⟫-≃-⟦⟫⟧ (swap-semantics {S & T} {U}) (assoc-semantics {U} {S} {T})) as ⟩
    (⟦assoc⟧ {S} {T} {U} ⟦⟫⟧ ⟦swap⟧ {S & T} {U} ⟦⟫⟧ ⟦assoc⟧ {U} {S} {T}) as
  ≡⟨ ⟦swap⟧-⟦assoc⟧ {S} {T} {U} as ⟩
    (⟦done⟧ {S} ⟦[&]⟧ ⟦swap⟧ {T} {U} ⟦⟫⟧
       ⟦assoc⟧ {S} {U} {T} ⟦⟫⟧ ⟦swap⟧ {S} {U} ⟦[&]⟧ ⟦done⟧ {T}) as
  ≡⟨ sym (⟫-≃-⟦⟫⟧ ([&]-≃-⟦[&]⟧ {P = done} (done-semantics {S}) (swap-semantics {T} {U}))
       (⟫-≃-⟦⟫⟧ (assoc-semantics {S} {U} {T})
         ([&]-≃-⟦[&]⟧ {Q = done} (swap-semantics {S} {U}) (done-semantics {T}))) as) ⟩
    ⟦ done {S} [&] swap {T} {U} ⟫ assoc {S} {U} {T} ⟫ swap {S} {U} [&] done {T} ⟧ as
  ∎

⟦swap⟧-⟦assoc⁻¹⟧ : ∀ {S T U} →
  ⟦assoc⁻¹⟧ {S} {T} {U} ⟦⟫⟧ ⟦swap⟧ {S} {T & U} ⟦⟫⟧ ⟦assoc⁻¹⟧ {T} {U} {S} 
    ≃ ⟦swap⟧ {S} {T} ⟦[&]⟧ ⟦done⟧ {U} ⟦⟫⟧ 
        ⟦assoc⁻¹⟧ {T} {S} {U} ⟦⟫⟧ ⟦done⟧ {T} ⟦[&]⟧ ⟦swap⟧ {S} {U}
⟦swap⟧-⟦assoc⁻¹⟧ {S} {T} {U} as =
  begin
    ⟦assoc⁻¹⟧ {T} {U} {S} (⟦swap⟧ {S} {T & U} (as₁ ++ as₂ ++ as₃))
  ≡⟨ cong (⟦assoc⁻¹⟧ {T} {U} {S}) (⟦swap⟧-++ as₁ (as₂ ++ as₃) ✓as₁/as₂₃≡[]) ⟩
    ⟦assoc⁻¹⟧ {T} {U} {S} ((as₂ ++ as₃) ++ as₁)
  ≡⟨ ⟦assoc⁻¹⟧-++ as₂ as₃ as₁ ⟩
    as₂ ++ as₃ ++ as₁
  ≡⟨ cong (_++_ as₂) (sym (⟦swap⟧-++ as₁ as₃ ✓as₁/as₃≡[])) ⟩
    as₂ ++ ⟦swap⟧ {S} {U} (as₁ ++ as₃)
  ≡⟨ sym (⟦[&]⟧-++ (⟦done⟧ {T}) (⟦swap⟧ {S} {U}) (λ cs → λ ✓cs → ✓cs) as₂ (as₁ ++ as₃)) ⟩
    (⟦done⟧ {T} ⟦[&]⟧ ⟦swap⟧ {S} {U}) (as₂ ++ as₁ ++ as₃)
  ≡⟨ cong (⟦done⟧ {T} ⟦[&]⟧ ⟦swap⟧ {S} {U}) (sym (⟦assoc⁻¹⟧-++ as₂ as₁ as₃)) ⟩
    (⟦done⟧ {T} ⟦[&]⟧ ⟦swap⟧ {S} {U}) (⟦assoc⁻¹⟧ {T} {S} {U} ((as₂ ++ as₁) ++ as₃))
  ∎ where
  as₁ = front {S} (front {S & T} as)
  as₂ = back {S} (front {S & T} as)
  as₃ = back {S & T} as
  ✓as₁/as₂₃≡[] : ✓ as₁ ⊎ as₂ ++ as₃ ≡ []
  ✓as₁/as₂₃≡[] with ✓? as₁
  ✓as₁/as₂₃≡[] | yes ✓as₁ = inj₁ ✓as₁
  ✓as₁/as₂₃≡[] | no ¬✓as₁ = inj₂ (++-resp-[] (back≡[] ¬✓as₁) (back≡[] (λ ✓as₁₂ → ¬✓as₁ (front-resp-✓ ✓as₁₂))))
  ✓as₁/as₃≡[] : ✓ as₁ ⊎ as₃ ≡ []
  ✓as₁/as₃≡[] with ✓? as₁
  ✓as₁/as₃≡[] | yes ✓as₁ = inj₁ ✓as₁
  ✓as₁/as₃≡[] | no ¬✓as₁ = inj₂ (back≡[] (λ ✓as₁₂ → ¬✓as₁ (front-resp-✓ ✓as₁₂)))

swap-assoc⁻¹ : ∀ {S T U} →
  ⟦ assoc⁻¹ {S} {T} {U} ⟫ swap {S} {T & U} ⟫ assoc⁻¹ {T} {U} {S} ⟧
    ≃ ⟦ swap {S} {T} [&] done {U} ⟫ assoc⁻¹ {T} {S} {U} ⟫ done {T} [&] swap {S} {U} ⟧
swap-assoc⁻¹ {S} {T} {U} as =
  begin
    ⟦ assoc⁻¹ {S} {T} {U} ⟫ swap {S} {T & U} ⟫ assoc⁻¹ {T} {U} {S} ⟧ as
  ≡⟨ ⟫-≃-⟦⟫⟧ (assoc⁻¹-semantics {S} {T} {U}) 
       (⟫-≃-⟦⟫⟧ (swap-semantics {S} {T & U}) (assoc⁻¹-semantics {T} {U} {S})) as ⟩
    (⟦assoc⁻¹⟧ {S} {T} {U} ⟦⟫⟧ ⟦swap⟧ {S} {T & U} ⟦⟫⟧ ⟦assoc⁻¹⟧ {T} {U} {S}) as
  ≡⟨ ⟦swap⟧-⟦assoc⁻¹⟧ {S} {T} {U} as ⟩
    (⟦swap⟧ {S} {T} ⟦[&]⟧ ⟦done⟧ {U} ⟦⟫⟧ 
      ⟦assoc⁻¹⟧ {T} {S} {U} ⟦⟫⟧ ⟦done⟧ {T} ⟦[&]⟧ ⟦swap⟧ {S} {U}) as
  ≡⟨ sym (⟫-≃-⟦⟫⟧ ([&]-≃-⟦[&]⟧ {Q = done} (swap-semantics {S} {T}) (done-semantics {U}))
       (⟫-≃-⟦⟫⟧ (assoc⁻¹-semantics {T} {S} {U})
         ([&]-≃-⟦[&]⟧ {P = done} (done-semantics {T}) (swap-semantics {S} {U}))) as) ⟩
    ⟦ swap {S} {T} [&] done {U} ⟫ assoc⁻¹ {T} {S} {U} ⟫ done {T} [&] swap {S} {U} ⟧ as
  ∎
