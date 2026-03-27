{-# OPTIONS --cubical --safe --guardedness -WnoUnsupportedIndexedMatch #-}

module Talks.Introduction where







------------------------------------------------------------------------------
--
--                         Programming with Cubes
--
--          Vikraman Choudhury    <vikraman.choudhury@strath.ac.uk>
--               Rin Liu          <rin.liu@strath.ac.uk>
--
--               Mathematically Structured Programming group
--                   Computer and Information Sciences
--                       University of Strathclyde
--
------------------------------------------------------------------------------


















------------------------------------------------------------------------------

open import Cubical.Foundations.Prelude
  renaming ( congS to ap
           ; cong to apd
           ; congP to apP
           ; J to base-J
           ) hiding (funExt ; subst)
import Cubical.Foundations.Prelude as Lib renaming (subst to tpt)
open import Cubical.Foundations.Univalence hiding (ua)
import Cubical.Foundations.Univalence as Lib using (ua)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Unit renaming (Unit to 𝟙 ; tt to ⋆)
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Nat

variable
  ℓ ℓ' ℓ'' : Level
  A B C : Type ℓ

J : {A : Type ℓ} → (P : (x y : A) → x ≡ y → Type ℓ') →
  (c : (x : A) → P x x refl) →
  (x y : A) → (p : x ≡ y) →
  P x y p
J P c x y p = base-J (λ y p → P x y p) (c x) p

------------------------------------------------------------------------------

















------------------------------------------------------------------------------
-- Dependent Types
------------------------------------------------------------------------------

module Lists where

  data List {ℓ} (A : Type ℓ) : Type ℓ where
    []  : List A
    _∷_ : A → List A → List A

  head : {A : Type ℓ} → List A → 𝟙 ⊎ A
  head [] = inl ⋆
  head (x ∷ xs) = inr x



module Vectors where

  data Vec {ℓ} (A : Type ℓ) : ℕ → Type ℓ where
    []  : Vec A zero
    _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

  head : {A : Type ℓ} {n : ℕ} → Vec A (suc n) → A
  head (x ∷ xs) = x



-- example =
-- example = {!!}





{-

Π-type:   (x : A) → B x       "for all x : A, a term of B x"
Σ-type:   Σ (x : A), B x      "some x : A, together with a term of B x"

=-type:   x ≡ y               "given x, y : A, a proof that x equals y"

-}



------------------------------------------------------------------------------
-- Equality types
------------------------------------------------------------------------------


{-

Formation              a b : A    ⊢    a ≡ b : Type

Introduction             a : A    ⊢    refl : a ≡ a

Elimination                       J



J : (P : (x y : A) → x ≡ y → Type)    -- Method P of transforming equality into target type
  → (d : (x : A) → P x x refl)        -- Proof that P holds for refl
  → (p : a ≡ b) → P a b p             -- Returns a function that eliminates from equality types

To prove something (P) about a general equality (p : a ≡ b), it suffices to prove it for the reflexivity case.

-}


sym' : {a b : A} → a ≡ b → b ≡ a
sym' {a = a} {b} = J (λ x y p → y ≡ x) (λ x → refl) a b

trans' : ∀ {ℓ} {A : Type ℓ} → {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans' {A = A} {a = a} {b} {c} p = J (λ x y q → (c : A) → y ≡ c → x ≡ c) (λ x c p → p) a b p c




sym'' : {a b : A} → a ≡ b → b ≡ a
sym'' p i = p (~ i)

trans'' : {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans'' p q i = (p ∙ q) i




------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Homotopy Type Theory
------------------------------------------------------------------------------

{-

The Homotopy Interpretation:


 A : Type         <->        Topological space
 a : A            <->        Points in A
 p : a ≡ b        <->        Paths from a to b
 α : p ≡ q        <->        Homotopies between paths
...               <->        Higher homotopies

-}


funExt : {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g
funExt α i = λ x → α x i

ua : A ≃ B → A ≡ B
ua = Lib.ua

tpt : {a b : A} → (P : A → Type ℓ) → (p : a ≡ b) → P a → P b
tpt = Lib.tpt

ua-β : (e : A ≃ B) → tpt (λ X → X) (ua e) ≡ equivFun e
ua-β e = funExt (λ x → transportRefl (equivFun e x))

------------------------------------------------------------------------------

















------------------------------------------------------------------------------
-- The Interval Type
------------------------------------------------------------------------------

_ : {A : Type} {a b : A} → Path A a b → a ≡ b
_ = λ p → p












------------------------------------------------------------------------------
