open import System.IO.Transducers using ( _⇒_ ; _⟫_ ; _⟨&⟩_ ; _≃_ )
open import System.IO.Transducers.Trace using ( [] )
open import System.IO.Transducers.Properties.LaxProduct.Lemmas using ( ⟫-dist-⟨&⟩[] )

module System.IO.Transducers.Properties.LaxProduct where

⟫-dist-⟨&⟩ : ∀ {S T U V} → 
  (P : T ⇒ U) → (Q : T ⇒ V) → (R : S ⇒ T) →
    ((R ⟫ (P ⟨&⟩ Q)) ≃ ((R ⟫ P) ⟨&⟩ (R ⟫ Q)))
⟫-dist-⟨&⟩ P Q R = ⟫-dist-⟨&⟩[] P Q R []
