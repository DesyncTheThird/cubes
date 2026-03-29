module HITs where

------------------------------------------------------------------------------
-- We'll be using the Cubical Agda standard Library:

open import Cubical.Foundations.Prelude
  renaming ( congS to ap
           ; cong to apd
           ; congP to apP
           ; subst to tpt
           )
open import Cubical.Foundations.Transport
  renaming ( substComposite to tptComp )
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_^_)

variable
  ℓ ℓ' ℓ'' : Level
  A B C : Type ℓ



------------------------------------------------------------------------------
-- HITs
------------------------------------------------------------------------------

module Int where

  data ℤ : Type where
    pos : ℕ → ℤ
    neg : ℕ → ℤ
    zero : pos 0 ≡ neg 0






  succ : ℤ → ℤ
  succ (pos n) = pos (suc n)
  succ (neg 0) = pos 1
  succ (neg (suc n)) = neg n
  succ (zero i) = pos 1

  pred : ℤ → ℤ
  pred (pos 0) = neg 1
  pred (pos (suc n)) = pos n
  pred (neg n) = neg (suc n)
  pred (zero i) = neg 1





  predSucc : (n : ℤ) → pred (succ n) ≡ n
  predSucc (pos n) = refl
  predSucc (neg 0) = zero
  predSucc (neg (suc x)) = refl
  predSucc (zero i) j = zero (i ∧ j)

  succPred : (n : ℤ) → succ (pred n) ≡ n
  succPred (pos 0) = sym zero
  succPred (pos (suc n)) = refl
  succPred (neg n) = refl
  succPred (zero i) j = zero (i ∨ ~ j)





  succEquiv : ℤ ≃ ℤ
  succEquiv = isoToEquiv (iso succ pred succPred predSucc)








------------------------------------------------------------------------------
-- Some shapes
------------------------------------------------------------------------------

module Circle where
  open Int

  data S¹ : Type where
    base : S¹
    loop : base ≡ base

  module S¹Elim where

    module _ (P : S¹ → Type ℓ')
      (base* : P base)
      (loop* : PathP (λ i → P (loop i)) base* base*) where

      ind : (x : S¹) → P x
      ind base = base*
      ind (loop i) = loop* i

    module _ (P : Type ℓ')
      (base* : P)
      (loop* : base* ≡ base*) where

      rec : (x : S¹) → P
      rec = ind (λ _ → P) base* loop*





  twist : S¹ → S¹
  twist base = base
  twist (loop i) = loop (~ i)

  twist² : (x : S¹) → twist (twist x) ≡ x
  twist² base = refl
  twist² (loop i) = refl





  cover : ℤ → (base ≡ base)
  cover (pos zero) = refl
  cover (pos (suc x)) = loop ∙ cover (pos x)
  cover (neg zero) = refl
  cover (neg (suc x)) = loop ⁻¹ ∙ cover (neg x)
  cover (zero i) = refl

  code : S¹ → Type
  code base = ℤ
  code (loop i) = ua succEquiv i

  encode : (x : S¹) → (base ≡ x) → code x
  encode x p = tpt code p (pos 0)

  winding : (base ≡ base) → ℤ
  winding = encode base

  _^_ : ∀ {a : A} → (p : a ≡ a) → ℤ → a ≡ a
  p ^ (pos 0) = refl
  p ^ (pos (suc x)) = (p ^ (pos x)) ∙ p
  p ^ (neg 0) = refl
  p ^ (neg (suc x)) = (p ^ (neg x)) ∙ sym p
  p ^ (zero i) = refl



  _ : winding (loop ^ (pos 4)) ≡ pos 4
  _ = refl







  windingCount : (n : ℤ) → encode base (loop ^ n) ≡ n
  windingCount (pos 0) = refl
  windingCount (pos (suc x)) = tptComp code (loop ^ (pos x)) loop (pos 0) ∙ ap succ (windingCount (pos x))
  windingCount (neg 0) = zero
  windingCount (neg (suc x)) = tptComp code (loop ^ (neg x)) (sym loop) (pos 0) ∙ ap pred (windingCount (neg x))
  windingCount (zero i) j = zero (i ∧ j)










module CW where

  open Circle

  data T² : Type where
    base : T²
    loop1 : base ≡ base
    loop2 : base ≡ base
    filler : Square loop1 loop1 loop2 loop2
        -- loop1 ∙ loop2 ≡ loop2 ∙ loop1

  data K² : Type where
    base : K²
    loop1 : base ≡ base
    loop2 : base ≡ base
    filler : Square loop1 loop2 (sym loop1) loop2
        -- loop1 ∙ loop2 ∙ loop1 ≡ loop2

  data RP² : Type where
    base : RP²
    loop : base ≡ base
    loop² : Square loop refl refl loop
        -- loop ∙ loop = refl





  -- S¹ × S¹ ≃ T²

  c2t : (S¹ × S¹) → T²
  c2t (base , base) = base
  c2t (loop i , base) = loop1 i
  c2t (base , loop j) = loop2 j
  c2t (loop i , loop j) = filler j i

  t2c : T² → (S¹ × S¹)
  t2c base = (base , base)
  t2c (loop1 i) = (loop i , base)
  t2c (loop2 i) = (base , loop i)
  t2c (filler i j) = (loop j) , (loop i)

  c2t2c : (x : S¹ × S¹) → t2c (c2t x) ≡ x
  c2t2c (base , base) = refl
  c2t2c (base , loop j) = refl
  c2t2c (loop i , base) = refl
  c2t2c (loop i , loop j) = refl

  t2c2t : (x : T²) → c2t (t2c x) ≡ x
  t2c2t base = refl
  t2c2t (loop1 i) = refl
  t2c2t (loop2 i) = refl
  t2c2t (filler i j) = refl

  t=c : S¹ × S¹ ≃ T²
  t=c = isoToEquiv (iso c2t t2c t2c2t c2t2c)





  Ω : Σ (Type ℓ) (λ X → X) → Type ℓ
  Ω (X , x) = x ≡ x

  S¹Univ : (X : Type ℓ) → (S¹ → X) ≃ Σ X (λ x → Ω (X , x))
  S¹Univ X = isoToEquiv (iso f2l l2f f2l2f l2f2l)
    where
      f2l : (S¹ → X) → Σ X (λ x → Ω (X , x))
      f2l f = (f base) , ap f loop
      l2f : Σ X (λ x → Ω (X , x)) → S¹ → X
      l2f (x , p) base = x
      l2f (x , p) (loop i) = p i
      f2l2f : ∀ x → f2l (l2f x) ≡ x
      f2l2f (x , p) = refl
      l2f2l : ∀ f → l2f (f2l f) ≡ f
      l2f2l f i base = f base
      l2f2l f i (loop j) = f (loop j)
