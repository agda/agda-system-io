{-# OPTIONS --universe-polymorphism #-}

open import System.IO.Transducers using ( _⇒_ ; inp ; out ; done ; _⟫_ ; out*' ; _≃_ )
open import System.IO.Transducers.Trace using ( _≤_ ; [] ; _∷_ ) 
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; cong )

module System.IO.Transducers.Properties.Lemmas where

open Relation.Binary.PropositionalEquality.≡-Reasoning

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x y u v r s} → x ≡ y → u ≡ v → r ≡ s → f x u r ≡ f y v s
cong₃ f refl refl refl = refl

≡-impl-≃ : ∀ {S T} {P Q : S ⇒ T} → (P ≡ Q) → (P ≃ Q)
≡-impl-≃ refl as = refl

⟫-identity₁ : ∀ {S T} → (P : S ⇒ T) → (done ⟫ P ≡ P)
⟫-identity₁ (inp F)   = refl
⟫-identity₁ (out b P) = cong (out b) (⟫-identity₁ P)
⟫-identity₁ done      = refl

⟫-identity₂ : ∀ {S T} → (P : S ⇒ T) → (P ⟫ done ≡ P)
⟫-identity₂ P = refl

out*'-comm-⟫ : ∀ {S T U V} →
  (P : S ⇒ T) → (Q : T ⇒ U) → (as : U ≤ V) → 
    ((P ⟫ (out*' as Q)) ≡ (out*' as (P ⟫ Q)))
out*'-comm-⟫ P Q []       = refl
out*'-comm-⟫ P Q (a ∷ as) = out*'-comm-⟫ P (out a Q) as
