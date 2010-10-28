open import Coinduction using ( ♭ )
open import System.IO.Transducers using ( _⇒_ ; inp ; out ; done ; _⟫_ ;_⟨&⟩_ ; _⟨&⟩[_]_ ; out*' ; I⟦_⟧ ; _≃_ )
open import System.IO.Transducers.Trace using ( _≤_ ; [] ; _∷_ )
open import System.IO.Transducers.Session using ( [] ; _∷_ ; _&_ )
open import System.IO.Transducers.Properties.Lemmas using ( cong₃ ; ≡-impl-≃ ; ⟫-identity₁ ; ⟫-identity₂ ; out*'-comm-⟫ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; cong ; cong₂ )

module System.IO.Transducers.Properties.LaxProduct.Lemmas where

open Relation.Binary.PropositionalEquality.≡-Reasoning
 
⟨&⟩[]-push : ∀ {C S T Us V W} → 
  (P : S ⇒ T) → (c : C) → (Q : S ⇒ (♭ Us c)) → (cs : (W ∷ Us) ≤ V) →
    ((P ⟨&⟩[ cs ] out c Q) ≡ (P ⟨&⟩[ c ∷ cs ] Q))
⟨&⟩[]-push (inp {T = []} F)    c Q cs = refl
⟨&⟩[]-push (inp {T = _ ∷ _} F) c Q cs = refl
⟨&⟩[]-push (out b P)           c Q cs = cong (out b) (⟨&⟩[]-push P c Q cs)
⟨&⟩[]-push (done {[]})         c Q cs = refl
⟨&⟩[]-push (done {_ ∷ _})      c Q cs = refl

⟨&⟩[]-discard : ∀ {S U V} → 
  (P : S ⇒ []) → (Q : S ⇒ U) → (cs : U ≤ V) →
    ((P ⟨&⟩[ cs ] Q) ≡ (out*' cs Q))
⟨&⟩[]-discard (inp F) Q cs = refl
⟨&⟩[]-discard done    Q cs = refl

⟫-dist-⟨&⟩[] : ∀ {S T U V W} → 
  (P : T ⇒ U) → (Q : T ⇒ V) → (R : S ⇒ T) → (cs : V ≤ W) → 
    ((R ⟫ (P ⟨&⟩[ cs ] Q)) ≃ ((R ⟫ P) ⟨&⟩[ cs ] (R ⟫ Q)))
⟫-dist-⟨&⟩[] (out b P) Q R cs as = 
  cong (_∷_ b) (⟫-dist-⟨&⟩[] P Q R cs as)
⟫-dist-⟨&⟩[] P (out c Q) R cs as = 
  begin
    I⟦ R ⟫ P ⟨&⟩[ cs ] out c Q ⟧ as
  ≡⟨ ≡-impl-≃ (cong₂ _⟫_ refl (⟨&⟩[]-push P c Q cs)) as ⟩
    I⟦ R ⟫ P ⟨&⟩[ c ∷ cs ] Q ⟧ as
  ≡⟨ ⟫-dist-⟨&⟩[] P Q R (c ∷ cs) as ⟩
    I⟦ (R ⟫ P) ⟨&⟩[ c ∷ cs ] (R ⟫ Q) ⟧ as
  ≡⟨ ≡-impl-≃ (sym (⟨&⟩[]-push (R ⟫ P) c (R ⟫ Q) cs)) as ⟩
    I⟦ (R ⟫ P) ⟨&⟩[ cs ] out c (R ⟫ Q) ⟧ as
  ∎
⟫-dist-⟨&⟩[] P Q done cs as =
  begin
    I⟦ done ⟫ P ⟨&⟩[ cs ] Q ⟧ as
  ≡⟨ ≡-impl-≃ (⟫-identity₁ (P ⟨&⟩[ cs ] Q)) as ⟩
    I⟦ P ⟨&⟩[ cs ] Q ⟧ as
  ≡⟨ ≡-impl-≃ (cong₃ _⟨&⟩[_]_ (sym (⟫-identity₁ P)) refl (sym (⟫-identity₁ Q))) as ⟩
    I⟦ (done ⟫ P) ⟨&⟩[ cs ] (done ⟫ Q) ⟧ as
  ∎
⟫-dist-⟨&⟩[] (inp {T = []} F) Q R cs as = 
  begin
    I⟦ R ⟫ out*' cs Q ⟧ as
  ≡⟨ ≡-impl-≃ (out*'-comm-⟫ R Q cs) as ⟩
    I⟦ out*' cs (R ⟫ Q) ⟧ as
  ≡⟨ ≡-impl-≃ (sym (⟨&⟩[]-discard (R ⟫ inp F) (R ⟫ Q) cs)) as ⟩
    I⟦ (R ⟫ inp F) ⟨&⟩[ cs ] (R ⟫ Q) ⟧ as
  ∎
⟫-dist-⟨&⟩[] (inp {T = _ ∷ _} F) (inp G) (inp H) cs [] = 
  refl
⟫-dist-⟨&⟩[] (inp {T = _ ∷ _} F) (inp G) (inp H) cs (a ∷ as) =
  ⟫-dist-⟨&⟩[] (inp F) (inp G) (♭ H a) cs as
⟫-dist-⟨&⟩[] (inp {T = _ ∷ _} F) (inp G) (out a R) cs as =
  ⟫-dist-⟨&⟩[] (♭ F a) (♭ G a) R cs as
⟫-dist-⟨&⟩[] (inp {T = _ ∷ _} F) done (inp H) cs [] =
  refl
⟫-dist-⟨&⟩[] (inp {T = _ ∷ _} F) done (inp H) cs (a ∷ as) =
  ⟫-dist-⟨&⟩[] (inp F) done (♭ H a) cs as
⟫-dist-⟨&⟩[] (inp {T = _ ∷ _} F) done (out c R) cs as =
  begin
    I⟦ R ⟫ ♭ F c ⟨&⟩[ c ∷ cs ] done ⟧ as
  ≡⟨ ⟫-dist-⟨&⟩[] (♭ F c) done R (c ∷ cs) as ⟩
    I⟦ (R ⟫ ♭ F c) ⟨&⟩[ c ∷ cs ] (R ⟫ done) ⟧ as
  ≡⟨ ≡-impl-≃ ((cong₃ _⟨&⟩[_]_ (refl {x = R ⟫ ♭ F c}) refl (⟫-identity₂ R))) as ⟩
    I⟦ (R ⟫ ♭ F c) ⟨&⟩[ c ∷ cs ] R ⟧ as
  ≡⟨ ≡-impl-≃ (sym (⟨&⟩[]-push (R ⟫ ♭ F c) c R cs)) as ⟩
    I⟦ (R ⟫ ♭ F c) ⟨&⟩[ cs ] out c R ⟧ as
  ∎
⟫-dist-⟨&⟩[] (done {[]}) Q R cs as = 
  begin
    I⟦ R ⟫ out*' cs Q ⟧ as
  ≡⟨ ≡-impl-≃ (out*'-comm-⟫ R Q cs) as ⟩
    I⟦ out*' cs (R ⟫ Q) ⟧ as
  ≡⟨ ≡-impl-≃ (sym (⟨&⟩[]-discard (R ⟫ done) (R ⟫ Q) cs)) as ⟩
    I⟦ (R ⟫ done) ⟨&⟩[ cs ] (R ⟫ Q) ⟧ as
  ∎
⟫-dist-⟨&⟩[] (done {_ ∷ _}) (inp G) (inp H) cs [] =
  refl
⟫-dist-⟨&⟩[] (done {_ ∷ _}) (inp G) (inp H) cs (a ∷ as) =
   ⟫-dist-⟨&⟩[] done (inp G) (♭ H a) cs as
⟫-dist-⟨&⟩[] (done {_ ∷ _}) (inp G) (out a R) cs as =
  begin
    a ∷ I⟦ R ⟫ done ⟨&⟩[ cs ] ♭ G a ⟧ as
  ≡⟨ cong (_∷_ a) (⟫-dist-⟨&⟩[] done (♭ G a) R cs as) ⟩
    a ∷ I⟦ (R ⟫ done) ⟨&⟩[ cs ] (R ⟫ ♭ G a) ⟧ as
  ≡⟨ cong (_∷_ a) (≡-impl-≃ (cong₃ _⟨&⟩[_]_ (⟫-identity₂ R) refl refl) as) ⟩
    a ∷ I⟦ R ⟨&⟩[ cs ] (R ⟫ ♭ G a) ⟧ as
  ∎
⟫-dist-⟨&⟩[] (done {_ ∷ _}) done (inp H) cs [] =
  refl
⟫-dist-⟨&⟩[] (done {_ ∷ _}) done (inp H) cs (a ∷ as) =
  ⟫-dist-⟨&⟩[] done done (♭ H a) cs as
⟫-dist-⟨&⟩[] (done {_ ∷ _}) done (out a R) cs as =
  begin
    a ∷ I⟦ R ⟫ done ⟨&⟩[ a ∷ cs ] done ⟧ as
  ≡⟨ cong (_∷_ a) (⟫-dist-⟨&⟩[] done done R (a ∷ cs) as) ⟩
    a ∷ I⟦ (R ⟫ done) ⟨&⟩[ a ∷ cs ] (R ⟫ done) ⟧ as
  ≡⟨ cong (_∷_ a) (≡-impl-≃ (cong₃ _⟨&⟩[_]_ (⟫-identity₂ R) refl (⟫-identity₂ R)) as) ⟩
    a ∷ I⟦ R ⟨&⟩[ a ∷ cs ] R ⟧ as
  ≡⟨ cong (_∷_ a) (≡-impl-≃ (sym (⟨&⟩[]-push R a R cs)) as) ⟩
    a ∷ I⟦ R ⟨&⟩[ cs ] out a R ⟧ as
  ∎
