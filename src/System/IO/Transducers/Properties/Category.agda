open import Coinduction using ( ∞ ; ♯_ ; ♭ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; cong )
open import System.IO.Transducers.Lazy using ( _⇒_ ; inp ; out ; done ; _⟫_ ; ⟦_⟧ ; _≃_ ; equiv )
open import System.IO.Transducers.Session using ( Session ; I ; Σ ; _∼_ ; ∼-refl ; ∼-trans )
open import System.IO.Transducers.Trace using ( Trace ; [] ; _∷_ )
open import System.IO.Transducers.Properties.Lemmas using ( ⟦⟧-resp-∼ ; ≃-refl ; ≃-sym ; IsEquiv ; isEquiv ; ≃-equiv ; ∷-refl-≡₁ ; ∷-refl-≡₂ )

module System.IO.Transducers.Properties.Category where

open Relation.Binary.PropositionalEquality.≡-Reasoning

infixr 6 _⟦⟫⟧_

-- Coinductive equivalence of programs, note that in the
-- case where done has type I ⇒ I, this is syntactic
-- identity.

data _⇒_⊨_≣_ : ∀ S T (P Q : S ⇒ T) → Set₁ where
  inp : ∀ {A V F T P Q} → ∞ (∀ a → ♭ F a ⇒ T ⊨ ♭ P a ≣ ♭ Q a) → 
    (Σ {A} V F ⇒ T ⊨ inp P ≣ inp Q)
  out : ∀ {B W G S} b {P Q} → (S ⇒ ♭ G b ⊨ P ≣ Q) →
    (S ⇒ Σ {B} W G ⊨ out b P ≣ out b Q)
  done : ∀ {S} → 
    (S ⇒ S ⊨ done ≣ done)
  inp-done : ∀ {A V F P} → ∞ (∀ a → ♭ F a ⇒ Σ V F ⊨ ♭ P a ≣ out a done) → 
    (Σ {A} V F ⇒ Σ V F ⊨ inp P ≣ done)
  done-inp : ∀ {A V F P} → ∞ (∀ a → ♭ F a ⇒ Σ V F ⊨ out a done ≣ ♭ P a) → 
    (Σ {A} V F ⇒ Σ V F ⊨ done ≣ inp P)

_≣_ : ∀ {S T} (P Q : S ⇒ T) → Set₁
P ≣ Q = _ ⇒ _ ⊨ P ≣ Q

-- Coinductive equivalence implies semantic equivalence

⟦⟧-resp-≣ : ∀ {S T} {P Q : S ⇒ T} → (P ≣ Q) → (⟦ P ⟧ ≃ ⟦ Q ⟧)
⟦⟧-resp-≣ (inp P≣Q) []                   = refl
⟦⟧-resp-≣ (inp P≣Q) (a ∷ as)             = ⟦⟧-resp-≣ (♭ P≣Q a) as
⟦⟧-resp-≣ (out b P≣Q) as                 = cong (_∷_ b) (⟦⟧-resp-≣ P≣Q as)
⟦⟧-resp-≣ done as                        = refl
⟦⟧-resp-≣ (inp-done P≣outadone) []       = refl
⟦⟧-resp-≣ (inp-done P≣outadone) (a ∷ as) = ⟦⟧-resp-≣ (♭ P≣outadone a) as
⟦⟧-resp-≣ (done-inp outadone≣P) []       = refl
⟦⟧-resp-≣ (done-inp outadone≣P) (a ∷ as) = ⟦⟧-resp-≣ (♭ outadone≣P a) as

-- Semantic equivalence implies coinductive equivalence

⟦⟧-refl-≣ : ∀ {S T} (P Q : S ⇒ T) → (⟦ P ⟧ ≃ ⟦ Q ⟧) → (P ≣ Q)
⟦⟧-refl-≣ (inp P)   (inp Q)    P≃Q        = inp (♯ λ a → ⟦⟧-refl-≣ (♭ P a) (♭ Q a) (λ as → P≃Q (a ∷ as)))
⟦⟧-refl-≣ (inp P)   done       P≃Q        = inp-done (♯ λ a → ⟦⟧-refl-≣ (♭ P a) (out a done) (λ as → P≃Q (a ∷ as)))
⟦⟧-refl-≣ (out b P) (out c Q)  P≃Q with ∷-refl-≡₁ refl refl (P≃Q [])
⟦⟧-refl-≣ (out b P) (out .b Q) P≃Q | refl = out b (⟦⟧-refl-≣ P Q (λ as → ∷-refl-≡₂ refl refl (P≃Q as)))
⟦⟧-refl-≣ done      (inp Q)    P≃Q        = done-inp (♯ λ a → ⟦⟧-refl-≣ (out a done) (♭ Q a) (λ as → P≃Q (a ∷ as)))
⟦⟧-refl-≣ done      done       P≃Q        = done
⟦⟧-refl-≣ (inp P)   (out b Q)  P≃Q with P≃Q []
⟦⟧-refl-≣ (inp P)   (out b Q)  P≃Q | ()
⟦⟧-refl-≣ (out b P) (inp Q)    P≃Q with P≃Q []
⟦⟧-refl-≣ (out b P) (inp Q)    P≃Q | ()
⟦⟧-refl-≣ (out b P) done       P≃Q with P≃Q []
⟦⟧-refl-≣ (out b P) done       P≃Q | ()
⟦⟧-refl-≣ done      (out b Q)  P≃Q with P≃Q []
⟦⟧-refl-≣ done      (out b Q)  P≃Q | ()

-- Trace semantics of identity

⟦done⟧ : ∀ {S} → (Trace S)  → (Trace S)
⟦done⟧ as = as

done-semantics : ∀ {S} → ⟦ done {S} ⟧ ≃ ⟦done⟧
done-semantics as = refl

-- Trace semantics of composition

_⟦⟫⟧_ : ∀ {S T U} → 
  (f : Trace S → Trace T) → (g : Trace T → Trace U) → 
    (Trace S) → (Trace U)
(f ⟦⟫⟧ g) as = g (f as)

⟫-semantics : ∀ {S T U} (P : S ⇒ T) (Q : T ⇒ U) →
    (⟦ P ⟫ Q ⟧ ≃ ⟦ P ⟧ ⟦⟫⟧ ⟦ Q ⟧)
⟫-semantics (inp P)   (inp Q)   []       = refl
⟫-semantics (inp P)   (inp Q)   (a ∷ as) = ⟫-semantics (♭ P a) (inp Q) as
⟫-semantics (inp P)   (out c Q) as       = cong (_∷_ c) (⟫-semantics (inp P) Q as)
⟫-semantics (inp P)   done      as       = refl
⟫-semantics (out b P) (inp Q)   as       = ⟫-semantics P (♭ Q b) as
⟫-semantics (out b P) (out c Q) as       = cong (_∷_ c) (⟫-semantics (out b P) Q as)
⟫-semantics (out b P) done      as       = refl
⟫-semantics done      Q         as       = refl

⟫-≃-⟦⟫⟧ : ∀ {S T U} 
  {P : S ⇒ T} {f : Trace S → Trace T} {Q : T ⇒ U} {g : Trace T → Trace U} →
    (⟦ P ⟧ ≃ f) → (⟦ Q ⟧ ≃ g) → (⟦ P ⟫ Q ⟧ ≃ f ⟦⟫⟧ g)
⟫-≃-⟦⟫⟧ {S} {T} {U} {P} {f} {Q} {g} P≃f Q≃g as =
  begin
    ⟦ P ⟫ Q ⟧ as
  ≡⟨ ⟫-semantics P Q as ⟩
    ⟦ Q ⟧ (⟦ P ⟧ as)
  ≡⟨ cong ⟦ Q ⟧ (P≃f as) ⟩
    ⟦ Q ⟧ (f as)
  ≡⟨ Q≃g (f as) ⟩
    g (f as)
  ∎

-- Composition respects ≃

⟫-resp-≃ : ∀ {S T U} {P₁ P₂ : S ⇒ T} {Q₁ Q₂ : T ⇒ U} → 
  (⟦ P₁ ⟧ ≃ ⟦ P₂ ⟧) → (⟦ Q₁ ⟧ ≃ ⟦ Q₂ ⟧) →
    (⟦ P₁ ⟫ Q₁ ⟧ ≃ ⟦ P₂ ⟫ Q₂ ⟧)
⟫-resp-≃ {S} {T} {U} {P₁} {P₂} {Q₁} {Q₂} P₁≃P₂ Q₁≃Q₂ as =
  begin
    ⟦ P₁ ⟫ Q₁ ⟧ as
  ≡⟨ ⟫-≃-⟦⟫⟧ P₁≃P₂ Q₁≃Q₂ as ⟩
    (⟦ P₂ ⟧ ⟦⟫⟧ ⟦ Q₂ ⟧) as
  ≡⟨ sym (⟫-semantics P₂ Q₂ as) ⟩
    ⟦ P₂ ⟫ Q₂ ⟧ as
  ∎

-- Left identity of composition

⟫-identity₁ : ∀ {S T} (P : S ⇒ T) → ⟦ done ⟫ P ⟧ ≃ ⟦ P ⟧
⟫-identity₁ P = ⟫-semantics done P

-- Right identity of composition

⟫-identity₂ : ∀ {S T} (P : S ⇒ T) → ⟦ P ⟫ done ⟧ ≃ ⟦ P ⟧
⟫-identity₂ P = ⟫-semantics P done

-- Associativity of composition

⟫-assoc : ∀ {S T U V} (P : S ⇒ T) (Q : T ⇒ U) (R : U ⇒ V) → 
    ⟦ (P ⟫ Q) ⟫ R ⟧ ≃ ⟦ P ⟫ (Q ⟫ R) ⟧
⟫-assoc P Q R as =
  begin
    ⟦ (P ⟫ Q) ⟫ R ⟧ as
  ≡⟨ ⟫-≃-⟦⟫⟧ (⟫-semantics P Q) ≃-refl as ⟩
    (⟦ P ⟧ ⟦⟫⟧ ⟦ Q ⟧ ⟦⟫⟧ ⟦ R ⟧) as
  ≡⟨ sym (⟫-≃-⟦⟫⟧ ≃-refl (⟫-semantics Q R) as) ⟩
    ⟦ P ⟫ (Q ⟫ R) ⟧ as
  ∎

-- Identity is an equivalence

equiv-resp-done : ∀ {S} → ⟦ done ⟧ ≃ ⟦ equiv (∼-refl {S}) ⟧
equiv-resp-done {I}     as = refl
equiv-resp-done {Σ V F} [] = refl
equiv-resp-done {Σ V F} (a ∷ as) = cong (_∷_ a) (equiv-resp-done as)

done-isEquiv : ∀ {S} → IsEquiv (done {S})
done-isEquiv = isEquiv {P = done} ∼-refl equiv-resp-done

-- Composition respects being an equivalence

equiv-resp-⟦⟫⟧ : ∀ {S T U} (S∼T : S ∼ T) (T∼U : T ∼ U) →
  ⟦ equiv S∼T ⟧ ⟦⟫⟧ ⟦ equiv T∼U ⟧ ≃ ⟦ equiv (∼-trans S∼T T∼U) ⟧
equiv-resp-⟦⟫⟧ I       I        as       = refl
equiv-resp-⟦⟫⟧ (Σ W F) (Σ .W G) []       = refl
equiv-resp-⟦⟫⟧ (Σ W F) (Σ .W G) (a ∷ as) = cong (_∷_ a) (equiv-resp-⟦⟫⟧ (♭ F a) (♭ G a) as)

equiv-resp-⟫ : ∀ {S T U} (S∼T : S ∼ T) (T∼U : T ∼ U) →
  ⟦ equiv S∼T ⟫ equiv T∼U ⟧ ≃ ⟦ equiv (∼-trans S∼T T∼U) ⟧
equiv-resp-⟫ S∼T T∼U as =
  begin
    ⟦ equiv S∼T ⟫ equiv T∼U ⟧ as
  ≡⟨ ⟫-semantics (equiv S∼T) (equiv T∼U) as ⟩
    (⟦ equiv S∼T ⟧ ⟦⟫⟧ ⟦ equiv T∼U ⟧) as
  ≡⟨ equiv-resp-⟦⟫⟧ S∼T T∼U as ⟩
    ⟦ equiv (∼-trans S∼T T∼U) ⟧ as
  ∎

⟫-isEquiv : ∀ {S T U} {P : S ⇒ T} {Q : T ⇒ U} →
  (IsEquiv P) → (IsEquiv Q) → (IsEquiv (P ⟫ Q))
⟫-isEquiv {S} {T} {U} {P} {Q} (isEquiv S∼T P≃S∼T) (isEquiv (T∼U) (Q≃T∼U)) =
  isEquiv (∼-trans S∼T T∼U) λ as →
    begin
      ⟦ P ⟫ Q ⟧ as
    ≡⟨ ⟫-resp-≃ P≃S∼T Q≃T∼U as ⟩
      ⟦ equiv S∼T ⟫ equiv T∼U ⟧ as
    ≡⟨ equiv-resp-⟫ S∼T T∼U as ⟩
      ⟦ equiv (∼-trans S∼T T∼U) ⟧ as
    ∎

-- Equivalences form isos

equiv-is-iso : ∀ {S T} {P : S ⇒ T} {Q : T ⇒ S} →
  (IsEquiv P) → (IsEquiv Q) → ⟦ P ⟫ Q ⟧ ≃ ⟦ done ⟧
equiv-is-iso PisEq QisEq =
  ≃-equiv (⟫-isEquiv PisEq QisEq) done-isEquiv