module Intro where

------------------------------------------------------------------------------

open import Cubical.Data.Equality hiding (sym ; _∙_ ; assoc)

variable
  ℓ ℓ' ℓ'' : Level
  A B C : Type ℓ
infixr 30 _∙_

------------------------------------------------------------------------------

















------------------------------------------------------------------------------
-- Dependent Types
------------------------------------------------------------------------------

module _ where
  open import Cubical.Data.Unit renaming (Unit to 𝟙 ; tt to ⋆)
  open import Cubical.Data.Sum
  open import Cubical.Data.Nat
  open import Cubical.Data.Bool

  f : ℕ → Bool
  f n = true

  g : (n : ℕ) → if isEven n then ℕ else Bool
  g zero = zero
  g (suc zero) = true
  g (suc (suc n)) = g n

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


{-

Π-type:   (x : A) → B x       "for all x : A, a term of B x"
Σ-type:   Σ (x : A) B x       "an x : A, together with a term of B x"
=-type:   x ≡ y               "given x, y : A, an identification of x with y"

-}













------------------------------------------------------------------------------
-- Equality types
------------------------------------------------------------------------------

{-

Formation              a b : A    ⊢    a ≡ b : Type

Introduction             a : A    ⊢    refl : a ≡ a

Elimination                       J

J : (P : (x y : A) → x ≡ y → Type)    -- Motive P transforming equality into target type
  → (d : (x : A) → P x x refl)        -- Proof that P holds for refl
  → (p : a ≡ b) → P a b p             -- Returns a function that eliminates from equality types

To prove something (P) about a general equality (p : a ≡ b),
it suffices to prove it for the reflexivity case.

-}

reflexivity : {a : A} → a ≡ a
reflexivity = refl

sym : {a b : A} → a ≡ b → b ≡ a
sym refl = refl
-- sym {a = a} {b} = J (λ x y p → y ≡ x) (λ x → refl) a b

_∙_ : ∀ {ℓ} {A : Type ℓ} → {a b c : A} → a ≡ b → b ≡ c → a ≡ c
refl ∙ p = p
-- trans {A = A} {a = a} {b} {c} p = J (λ x y q → (c : A) → y ≡ c → x ≡ c) (λ x c p → p) a b p c

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

module _ {a b : A} where

  unitr : (p : a ≡ b) → (p ∙ refl) ≡ p
  unitr refl = refl

  sym² : (p : a ≡ b) → sym (sym p) ≡ p
  sym² refl = refl

module _ {a b c d : A} where

  assoc : (p : a ≡ b) (q : b ≡ c) (r : c ≡ d)
        → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r
  assoc refl q r = refl

module _ {a b c d e : A} where

  pentagon : (p : a ≡ b) → (q : b ≡ c) → (r : c ≡ d) → (s : d ≡ e) →
            (assoc p q (r ∙ s) ∙ assoc (p ∙ q) r s)
                              ≡
    (ap (p ∙_) (assoc q r s)) ∙ assoc p (q ∙ r) s ∙ ap (_∙ s) (assoc p q r)
  pentagon refl refl r s = refl


------------------------------------------------------------------------------
