module Paths where

------------------------------------------------------------------------------

import Cubical.Foundations.Prelude as Lib renaming (subst to tpt)

open import Cubical.Core.Primitives

variable
  ℓ ℓ' ℓ'' : Level
  A B C : Type ℓ

------------------------------------------------------------------------------














------------------------------------------------------------------------------
-- The Interval Type
------------------------------------------------------------------------------
{-

I : Type

i0 i1 : I

~ : I → I
_∧_ _∨_ : I → I → I



Paths in A between
    (a : A) and (b : A)
are maps
    p : I → A
with:
- p i0 = a
- p i1 = b

Path : {ℓ : Level} (A : Type ℓ) → A → A → Type ℓ



Paths over (A : I → Type) between
    (a : A i0) and (b : A i1)
are maps
    p : (i : I) → A i
with:
- p i0 = a
- p i1 = b

PathP : {ℓ : Level} (A : I → Type ℓ) → A i0 → A i1 → Type ℓ

-}




-- `refl a` is the constant path I → A at a
refl : (a : A) → a ≡ a
refl a i = a

-- sym p is the path p in reverse
sym : {a b : A} → a ≡ b → b ≡ a
sym p i = p (~ i)

-- what about transitivity?


-- funExt is pointwise equality of functions
funExt : {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g
funExt α i x = α x i

-- ap applies a path to a function
ap : {a b : A} → (f : A → B) → (p : a ≡ b) → f a ≡ f b
ap f p i = f (p i)

-- apd applies a dependent path to a function
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
j   a --------> c
∧
|
+-> i





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

module Squares where

  private variable
    a b c d : A

  Square : ∀ {ℓ} {A : Type ℓ}
    {a b : A} (p : a ≡ b)
    {c d : A} (q : c ≡ d)
    (r : a ≡ c) (s : b ≡ d)
    → Type _
  Square {A = A} p q r s = PathP (λ i → Path A (r i) (s i)) p q

  lid : (p : a ≡ b) (q : c ≡ d) (r : a ≡ c)
    → b ≡ d
  lid p q r i =
    hcomp (λ j → λ { (i = i0) → p j
                   ; (i = i1) → q j })
          (r i)






------------------------------------------------------------------------------
-- Connections and Composition
------------------------------------------------------------------------------

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




  filler : (p : a ≡ b) (q : c ≡ d) (r : a ≡ c)
    → Square p q r (lid p q r)
  filler p q r i j =
    hcomp (λ k → (λ { (i = i0) → p (j ∧ k)
                    ; (i = i1) → q (j ∧ k)
                    ; (j = i0) → r i
                    -- ; (j = i1) → filler p q r i k -- recursive sorcery
                    }))
          (r i)

  infixr 5 _∙_

  _∙_ : a ≡ b → b ≡ c → a ≡ c
  r ∙ q = lid (refl (r i0)) q r



------------------------------------------------------------------------------
