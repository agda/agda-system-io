open import Coinduction
open import System.IO.Transducers
open import System.IO.Transducers.Trace
open import System.IO.Transducers.Session
open import System.IO.Transducers.Properties.LaxProduct.Lemmas
open import Relation.Binary.PropositionalEquality

module System.IO.Transducers.Properties.LaxProduct where

⟫-dist-⟨&⟩ : ∀ {S T U V} → 
  (P : T ⇒ U) → (Q : T ⇒ V) → (R : S ⇒ T) →
    ((R ⟫ (P ⟨&⟩ Q)) ≃ ((R ⟫ P) ⟨&⟩ (R ⟫ Q)))
⟫-dist-⟨&⟩ P Q R = ⟫-dist-⟨&⟩[] P Q R []
