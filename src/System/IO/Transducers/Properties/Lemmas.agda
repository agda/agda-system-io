{-# OPTIONS --universe-polymorphism #-}

open import System.IO.Transducers using ( _⇒_ ; inp ; out ; done ; _⟫_ ; out*' ; I⟦_⟧ ; _≃_ )
open import System.IO.Transducers.Trace using ( Trace ; _≤_ ; [] ; _∷_ ) 
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; cong )

module System.IO.Transducers.Properties.Lemmas where

open Relation.Binary.PropositionalEquality.≡-Reasoning

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x y u v r s} → x ≡ y → u ≡ v → r ≡ s → f x u r ≡ f y v s
cong₃ f refl refl refl = refl

revApp : ∀ {S T} → (S ≤ T) → (Trace S) → (Trace T)
revApp []       bs = bs
revApp (a ∷ as) bs = revApp as (a ∷ bs)

out*'-semantics : ∀ {S T U} → 
  (cs : T ≤ U) →  (Q : S ⇒ T) →
    ∀ as → I⟦ out*' cs Q ⟧ as ≡ revApp cs (I⟦ Q ⟧ as)
out*'-semantics [] Q as       = refl
out*'-semantics (c ∷ cs) Q as = out*'-semantics cs (out c Q) as
