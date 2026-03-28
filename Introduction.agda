{-# OPTIONS --cubical --safe --guardedness -WnoUnsupportedIndexedMatch #-}

module Introduction where







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

import Cubical.Foundations.Prelude as Lib renaming (subst to tpt)

open import Cubical.Core.Primitives
import Cubical.Data.Equality renaming (_≡_ to Id ; refl to idp)
open Cubical.Data.Equality using (Id ; idp)

variable
  ℓ ℓ' ℓ'' : Level
  A B C : Type ℓ

-- J : {A : Type ℓ} → (P : (x y : A) → x ≡ y → Type ℓ') →
--   (c : (x : A) → P x x
--   refl) →
--   (x y : A) → (p : x ≡ y) →
--   P x y p
-- J P c x y p = based-J (λ y p → P x y p) (c x) p

------------------------------------------------------------------------------

















------------------------------------------------------------------------------
-- Dependent Types
------------------------------------------------------------------------------

module _ where
  open import Cubical.Data.Unit renaming (Unit to 𝟙 ; tt to ⋆)
  open import Cubical.Data.Sum
  open import Cubical.Data.Nat

  module Lists where

    data List {ℓ } (A : Type ℓ) : Type ℓ where
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






{-

Π-type:   (x : A) → B x       "for all x : A, a term of B x"
Σ-type:   Σ (x : A), B x      "some x : A, together with a term of B x"
=-type:   x ≡ y               "given x, y : A, an identification of x with y"

-}



------------------------------------------------------------------------------
-- Equality types
------------------------------------------------------------------------------

{-

Formation              a b : A    ⊢    Id a b : Type

Introduction             a : A    ⊢    refl : Id a a

Elimination                       J

J : (P : (x y : A) → x ≡ y → Type)    -- Motive P transforming equality into target type
  → (d : (x : A) → P x x refl)        -- Proof that P holds for refl
  → (p : a ≡ b) → P a b p             -- Returns a function that eliminates from equality types

To prove something (P) about a general equality (p : a ≡ b),
it suffices to prove it for the reflexivity case.

-}

sym' : {a b : A} → Id a b → Id b a
sym' idp = idp
-- sym' {a = a} {b} = J (λ x y p → y ≡ x) (λ x → refl) a b

trans' : ∀ {ℓ} {A : Type ℓ} → {a b c : A} → Id a b → Id b c → Id a c
trans' idp p = p
-- trans' {A = A} {a = a} {b} {c} p = J (λ x y q → (c : A) → y ≡ c → x ≡ c) (λ x c p → p) a b p c

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

Types are infinity groupoids:

-}

module _ {a b c d : A} where

  assoc' : (p : Id a b) (q : Id b c) (r : Id c d)
    → Id (trans' p (trans' q r)) (trans' (trans' p q ) r)
  assoc' idp q r = idp

  sym² : (p : Id a b) → Id (sym' (sym' p)) p
  sym² idp = idp

------------------------------------------------------------------------------













------------------------------------------------------------------------------
-- The Interval Type
------------------------------------------------------------------------------
{-

Paths in A between
    (a : A) and (b : A)
are maps
    p : I → A
with:
- p i0 = a
- p i1 = b

Paths over (A : I → Type) between
    (a : A i0) and (b : A i1)
are maps
    p : (i : I) → A i
with:
- p i0 = a
- p i1 = b

-}

-- refl {a} is the constant path I → A at a
refl : (a : A) → a ≡ a
refl a = λ i → a

-- sym p is the path p in reverse
sym : {a b : A} → a ≡ b → b ≡ a
sym p i = p (~ i)





funExt : {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g
funExt α i x = α x i

ap : {a b : A} → (f : A → B) → (p : a ≡ b) → f a ≡ f b
ap f p i = f (p i)

apd : {B : A → Type ℓ}
  → (f : (x : A) → B x)
  → {a b : A} → (p : a ≡ b)
  → PathP (λ i → B (p i)) (f a) (f b)
apd f p i = f (p i)



------------------------------------------------------------------------------
-- Squares, Cubes, ...
------------------------------------------------------------------------------
{-

A square in A with vertices
    (a b c d : A)
is a map
    p : I × I → A
with

-  p i0 i0 = a
-  p i0 i1 = b
-  p i1 i0 = c
-  p i1 i1 = d

    b --------> d
    ∧           ∧
    |           |
    |           |
    |           |
    |           |
j   a --------> c
∧
|
+-> i

-}

module Squares where

  private variable
    a b c d : A

  Square : ∀ {ℓ} {A : Type ℓ}
    {a b : A} (p : a ≡ b)
    {c d : A} (q : c ≡ d)
    (r : a ≡ c) (s : b ≡ d)
    → Type _
  Square {A = A} p q r s = PathP (λ i → Path A (r i) (s i)) p q

  const-i : (p : a ≡ b) → Square p p (refl a) (refl b)
  const-i p i j = p j

  lower : (p : a ≡ b) → Square p (refl b) p (refl b)
  lower p i j = p (i ∨ j)

  upper : (p : a ≡ b) → Square (refl a) p (refl a) p
  upper p i j = p (i ∧ j)

  left : (p : a ≡ b) → Square (refl a) (sym p) p (refl a)
  left p i j = p (i ∧ ~ j)

  right : (p : a ≡ b) → Square p (refl a) (refl a) (sym p)
  right p i j = p (~ i ∧ j)

  symmetricSquare : (p : a ≡ b) → (q : b ≡ c) → Square p q p q
  symmetricSquare p q i j =
    hcomp (λ k →
      λ { (i = i0) → p (j ∨ ~ k)
      ; (i = i1) → q j
      ; (j = i0) → p (i ∨ ~ k)
      ; (j = i1) → q i
    })
    (q (i ∧ j))

{-

A cube in A with vertices
    (a b c d e f g h : A)
is a map
    p : I × I × I → A
with
- p i0 i0 i0 = a
- p i0 i0 i1 = b
- ...

But we'll stick to squares for now...
-}

















------------------------------------------------------------------------------
-- Composition
------------------------------------------------------------------------------

module Composition where
  variable
    a b c d : A

  open Squares

  lid : (p : a ≡ b) (q : c ≡ d) (r : a ≡ c)
    → b ≡ d
  lid p q r i =
    hcomp (λ j → λ { (i = i0) → p j
                   ; (i = i1) → q j })
          (r i)

  filler : (p : a ≡ b) (q : c ≡ d) (r : a ≡ c)
    → Square p q r (lid p q r)
  filler p q r i j =
    hcomp (λ k → (λ { (i = i0) → p (j ∧ k)
                    ; (i = i1) → q (j ∧ k)
                    ; (j = i0) → r i
                    -- ; (j = i1) → {!!} -- recursive sorcery
                    }))
          (r i)

  infixr 5 _∙_

  _∙_ : a ≡ b → b ≡ c → a ≡ c
  p ∙ q = lid (refl _) q p



------------------------------------------------------------------------------
