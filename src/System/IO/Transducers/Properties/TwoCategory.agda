open import Coinduction using ( ♭ )
open import Data.Product using ( _,_ )
open import Relation.Binary using ( Poset )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; trans ; cong ; subst₂ ) renaming ( setoid to ≡-setoid )
open import System.IO.Transducers using ( _⇒_ ; inp ; out ; done ; ⟦_⟧ ; _≃_ ; _≲_ ; _⟫_ )
open import System.IO.Transducers.Session using ( Session )
open import System.IO.Transducers.Trace using ( Trace ; [] ; _∷_ ; _⊑_ )
open import System.IO.Transducers.Properties.Category using ( ⟫-semantics )

import Relation.Binary.PartialOrderReasoning

module System.IO.Transducers.Properties.TwoCategory where

-- The category is poset-enriched, with order inherited from prefix order on traces.

-- Reflexivity

⊑-refl : ∀ {S} (as : Trace S) → (as ⊑ as)
⊑-refl [] = []
⊑-refl (a ∷ as) = (a ∷ ⊑-refl as)

≡-impl-⊑ : ∀ {S} {as bs : Trace S} → (as ≡ bs) → (as ⊑ bs)
≡-impl-⊑ refl = ⊑-refl _

≲-refl : ∀ {S T} (f : Trace S → Trace T) → (f ≲ f)
≲-refl f as = ⊑-refl (f as)

≃-impl-≲ : ∀ {S T} {f g : Trace S → Trace T} → (f ≃ g) → (f ≲ g)
≃-impl-≲ f≃g as = ≡-impl-⊑ (f≃g as)

-- Transitivity

⊑-trans : ∀ {S} {as bs cs : Trace S} → (as ⊑ bs) → (bs ⊑ cs) → (as ⊑ cs)
⊑-trans []       bs        = []
⊑-trans (a ∷ as) (.a ∷ bs) = (a ∷ ⊑-trans as bs)

≲-trans : ∀ {S T} {f g h : Trace S → Trace T} → (f ≲ g) → (g ≲ h) → (f ≲ h)
≲-trans f≲g g≲h as = ⊑-trans (f≲g as) (g≲h as)

-- Antisymmetry

⊑-antisym : ∀ {S} {as bs : Trace S} → (as ⊑ bs) → (bs ⊑ as) → (as ≡ bs)
⊑-antisym [] [] = refl
⊑-antisym (a ∷ as) (.a ∷ bs) = cong (_∷_ a) (⊑-antisym as bs)

≲-antisym : ∀ {S T} {f g : Trace S → Trace T} → (f ≲ g) → (g ≲ f) → (f ≃ g)
≲-antisym f≲g g≲f as = ⊑-antisym (f≲g as) (g≲f as)

-- ⊑ and ≲ form posets

⊑-poset : Session → Poset _ _ _ 
⊑-poset S = record 
  { Carrier = Trace S
  ; _≈_ = _≡_
  ; _≤_ = _⊑_
  ; isPartialOrder = record
    { antisym = ⊑-antisym
    ; isPreorder = record
      { reflexive = ≡-impl-⊑
      ; trans = ⊑-trans
      ; ∼-resp-≈ = ((λ bs≡cs → subst₂ _⊑_ refl bs≡cs) , (λ as≡bs → subst₂ _⊑_ as≡bs refl))
      ; isEquivalence = Relation.Binary.Setoid.isEquivalence (≡-setoid (Trace S))
      }
    }
  }

≲-poset : Session → Session → Poset _ _ _ 
≲-poset S T = record 
  { Carrier = (Trace S → Trace T)
  ; _≈_ = _≃_
  ; _≤_ = _≲_
  ; isPartialOrder = record
    { antisym = ≲-antisym
    ; isPreorder = record
      { reflexive = ≃-impl-≲
      ; trans = ≲-trans
      ; ∼-resp-≈ = (λ P≃Q P≲R as → subst₂ _⊑_ refl (P≃Q as) (P≲R as)) , λ Q≃R Q≲P as → subst₂ _⊑_ (Q≃R as) refl (Q≲P as)
      ; isEquivalence = record
        { refl = λ as → refl
        ; sym = λ P≃Q as → sym (P≃Q as)
        ; trans = λ P≃Q Q≃R as → trans (P≃Q as) (Q≃R as)
        }
      }
    }
  }

-- Inequational reasoning

module ⊑-Reasoning {S} where
  open Relation.Binary.PartialOrderReasoning (⊑-poset S) public renaming ( _≤⟨_⟩_ to _⊑⟨_⟩_ ; _≈⟨_⟩_ to _≡⟨_⟩_ )

module ≲-Reasoning {S T} where
  open Relation.Binary.PartialOrderReasoning (≲-poset S T) public renaming ( _≤⟨_⟩_ to _≲⟨_⟩_ ; _≈⟨_⟩_ to _≃⟨_⟩_ )

open ⊑-Reasoning

-- Processes are ⊑-monotone

P-monotone : ∀ {S T as bs} → (P : S ⇒ T) → (as ⊑ bs) → (⟦ P ⟧ as ⊑ ⟦ P ⟧ bs)
P-monotone (inp F)   []          = []
P-monotone (inp F)   (a ∷ as⊑bs) = P-monotone (♭ F a) as⊑bs
P-monotone (out b P) as⊑bs       = b ∷ P-monotone P as⊑bs
P-monotone done      as⊑bs       = as⊑bs

-- Composition is ≲-monotone

⟫-monotone : ∀ {S T U} (P₁ P₂ : S ⇒ T) (Q₁ Q₂ : T ⇒ U) → 
  (⟦ P₁ ⟧ ≲ ⟦ P₂ ⟧) → (⟦ Q₁ ⟧ ≲ ⟦ Q₂ ⟧) → 
    (⟦ P₁ ⟫ Q₁ ⟧ ≲ ⟦ P₂ ⟫ Q₂ ⟧)
⟫-monotone P₁ P₂ Q₁ Q₂ P₁≲P₂ Q₁≲Q₂ as = 
  begin
    ⟦ P₁ ⟫ Q₁ ⟧ as
  ≡⟨ ⟫-semantics P₁ Q₁ as ⟩
    ⟦ Q₁ ⟧ (⟦ P₁ ⟧ as)
  ⊑⟨ P-monotone Q₁ (P₁≲P₂ as) ⟩
    ⟦ Q₁ ⟧ (⟦ P₂ ⟧ as)
  ⊑⟨ Q₁≲Q₂ (⟦ P₂ ⟧ as) ⟩
    ⟦ Q₂ ⟧ (⟦ P₂ ⟧ as)
  ≡⟨ sym (⟫-semantics P₂ Q₂ as) ⟩
    ⟦ P₂ ⟫ Q₂ ⟧ as
  ∎