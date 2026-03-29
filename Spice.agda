module Spice where

------------------------------------------------------------------------------
-- We'll be using the Cubical Agda standard Library:

open import Cubical.Foundations.Prelude
  renaming ( congS to ap
           ; cong to apd
           ; congP to apP
           ; subst to tpt
           )
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Relation.Binary.Order.Toset
import Cubical.HITs.PropositionalTruncation as PTrunc
import Cubical.Functions.Logic as L
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
import Cubical.Data.Nat.Order as Nat
open import Cubical.Data.Unit renaming (Unit to 𝟙 ; tt to ⋆)
open import Cubical.Data.Empty hiding (rec)
open import Cubical.Data.Sum hiding (rec)
import Cubical.Data.Sum as ⊎ using (rec)

variable
  ℓ ℓ' ℓ'' : Level
  A B C : Type ℓ

------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- Spicy Lists
------------------------------------------------------------------------------

module SLists where

  infixr 10 _∷_

  data SList {ℓ} (A : Type ℓ) : Type ℓ where
    []  : SList A
    _∷_ : A → SList A → SList A
    swap : (x y : A) (xs : SList A) → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
    trunc : isSet (SList A)

  {- eliminators -}
  module SListElim where
    module _ (P : SList A → Type ℓ')
         ([]* : P [])
         (_∷*_ : (x : A) {xs : SList A} → P xs → P (x ∷ xs))
         (swap* : (x y : A) {xs : SList A} (p : P xs) → PathP (λ i → P (swap x y xs i)) (x ∷* (y ∷* p)) (y ∷* (x ∷* p)))
         (trunc* : (xs : SList A) → isSet (P xs)) where

      ind : (xs : SList A) → P xs
      ind [] = []*
      ind (x ∷ xs) = x ∷* ind xs
      ind (swap x y xs i) = swap* x y (ind xs) i
      ind (trunc x y p q i j) =
             isSet→SquareP (λ i j → trunc* (trunc x y p q i j)) (apd ind p) (apd ind q) refl refl i j

    module _ {A : Type ℓ} (P : SList A → Type ℓ')
         ([]* : P [])
         (_∷*_ : (x : A) {xs : SList A} → P xs → P (x ∷ xs))
         (trunc* : (xs : SList A) → isProp (P xs)) where

      private
        swap* : (x y : A) {xs : SList A} (p : P xs) → PathP (λ i → P (swap x y xs i)) (x ∷* (y ∷* p)) (y ∷* (x ∷* p))
        swap* x y {xs} p = isProp→PathP (λ i → trunc* (swap x y xs i)) (x ∷* (y ∷* p)) (y ∷* (x ∷* p))

      indProp : (xs : SList A) → P xs
      indProp = ind P []* _∷*_ swap* (λ xs → isProp→isSet (trunc* xs))

    module _ {A : Type ℓ} (P : Type ℓ')
         ([]* : P)
         (_∷*_ : A → P → P)
         (swap* : (x y : A) → (p : P) → Path P (x ∷* (y ∷* p)) (y ∷* (x ∷* p)))
         (trunc* : isSet P) where

      rec : SList A → P
      rec = ind (λ _ → P) []* (λ x {xs} → x ∷*_) (λ x y {xs} → swap* x y) (λ _ → trunc*)






  {- permutations -}
  as : SList ℕ
  as = 1 ∷ 2 ∷ 3 ∷ []

  bs : SList ℕ
  bs = 3 ∷ 2 ∷ 1 ∷ []

  p : as ≡ bs
  p = swap 1 2 _ ∙ ap (2 ∷_) (swap 1 3 _) ∙ swap 2 3 _

  q : as ≡ bs
  q = ap (1 ∷_) (swap 2 3 _) ∙ swap 1 3 _ ∙ ap (3 ∷_) (swap 1 2 _)

  _ : p ≡ q
  _ = trunc as bs p q

  -- head : ∀ {a} {A : Type a} → SList A → 𝟙 ⊎ A
  -- head [] = inl ⋆
  -- head (x ∷ xs) = inr x
  -- head (swap x y xs i) = inr {!!}
  -- head (trunc x xs p q i j) = {!!}











module Monoid where

  open import Cubical.Data.List

  pattern [_∶_]       a b         = a ∷ b ∷ []
  pattern [_∶_∶_]     a b c       = a ∷ b ∷ c ∷ []
  pattern [_∶_∶_∶_]   a b c d     = a ∷ b ∷ c ∷ d ∷ []
  pattern [_∶_∶_∶_∶_] a b c d e   = a ∷ b ∷ c ∷ d ∷ e ∷ []

  record Mon {a} (A : Type a) : Type a where
    infixr 10 _⊕_
    field
      e : A
      _⊕_ : A → A → A
      unitl : ∀ x → e ⊕ x ≡ x
      unitr : ∀ x → x ⊕ e ≡ x
      assocr : ∀ x y z → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
  open Mon

  record MonHom {a b} {A : Type a} {B : Type b} (M : Mon A) (N : Mon B) : Type (ℓ-max a b) where
    private
      module M = Mon M
      module N = Mon N
    field
      ϕ : A → B
      preserves-e : ϕ M.e ≡ N.e
      preserves-⊕ : ∀ x y → ϕ (x M.⊕ y) ≡ ϕ x N.⊕ ϕ y
  open MonHom

  ListMon : ∀ {a} {A : Type a} → Mon (List A)
  ListMon .e = []
  ListMon ._⊕_ = _++_
  ListMon .unitl xs = refl
  ListMon .unitr = ++-unit-r
  ListMon .assocr = ++-assoc

  η : ∀ {a} {A : Type a} → A → List A
  η a = [ a ]

  module _ {a m} {A : Type a} {M : Type m} (M* : Mon M) where
    private
      module M = Mon M*
      eval : (A → M) → List A → M
      eval f [] = M.e
      eval f (x ∷ xs) = f x M.⊕ eval f xs

    [_]_♯ = eval

    module _ (h* : MonHom ListMon M*) (f : A → M) where
      private
        module h = MonHom h*
        eval-uniq : h.ϕ ∘ η ≡ f → ∀ xs → h.ϕ xs ≡ eval f xs
        eval-uniq p [] =
          h.preserves-e
        eval-uniq p (x ∷ xs) =
            h.preserves-⊕ [ x ] xs
          ∙ ap (M._⊕ h.ϕ xs) (funExt⁻ p x)
          ∙ ap (f x M.⊕_) (eval-uniq p xs)

      [_]_♯-uniq = eval-uniq

  𝟙+⟨_⟩-Mon : ∀ {a} (A : Type a) → Mon (𝟙 ⊎ A)
  𝟙+⟨ A ⟩-Mon .e = inl ⋆
  𝟙+⟨ A ⟩-Mon ._⊕_ (inl ⋆) y = y
  𝟙+⟨ A ⟩-Mon ._⊕_ (inr x) y = inr x
  𝟙+⟨ A ⟩-Mon .unitl x = refl
  𝟙+⟨ A ⟩-Mon .unitr (inl ⋆) = refl
  𝟙+⟨ A ⟩-Mon .unitr (inr x) = refl
  𝟙+⟨ A ⟩-Mon .assocr (inl ⋆) y z = refl
  𝟙+⟨ A ⟩-Mon .assocr (inr x) (inl ⋆) z = refl
  𝟙+⟨ A ⟩-Mon .assocr (inr x) (inr y) z = refl

  head : ∀ {a} {A : Type a} → List A → 𝟙 ⊎ A
  head {A = A} = [ 𝟙+⟨ A ⟩-Mon ] inr ♯

  _ : head {A = ℕ} [] ≡ inl ⋆
  _ = refl

  _ : head {A = ℕ} [ 2 ∶ 1 ∶ 3 ] ≡ inr 2
  _ = refl











module CMonoid where

  open SLists

  pattern [_]         a           = a ∷ []
  pattern [_∶_]       a b         = a ∷ b ∷ []
  pattern [_∶_∶_]     a b c       = a ∷ b ∷ c ∷ []
  pattern [_∶_∶_∶_]   a b c d     = a ∷ b ∷ c ∷ d ∷ []
  pattern [_∶_∶_∶_∶_] a b c d e   = a ∷ b ∷ c ∷ d ∷ e ∷ []

  module _ {ℓ} {A : Type ℓ} where

    infixr 5 _++_

    _++_ : SList A → SList A → SList A
    _++_ = SListElim.rec (SList A → SList A)
      (λ ys → ys)
      (λ x h ys → x ∷ h ys)
      (λ x y h i → λ ys → swap x y (h ys) i)
      (isSet→ trunc)






    ++-unit-r : (xs : SList A) → xs ++ [] ≡ xs
    ++-unit-r = SListElim.indProp (λ xs → xs ++ [] ≡ xs)
      refl
      (λ x {xs} h i → x ∷ h i)
      (λ xs → trunc (xs ++ []) xs)

    ++-assoc : (xs ys zs : SList A) → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
    ++-assoc = SListElim.indProp (λ xs → (ys zs : SList A) → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs)
      (λ ys zs → refl)
      (λ x {xs} h ys zs i → x ∷ h ys zs i)
      (λ xs → isPropΠ2 λ x y → trunc ((xs ++ x) ++ y) (xs ++ x ++ y))

    ∷-comm : (x : A) (xs : SList A) → x ∷ xs ≡ xs ++ [ x ]
    ∷-comm x = SListElim.indProp (λ xs → x ∷ xs ≡ xs ++ [ x ])
      refl
      (λ y {xs} h → swap x y xs ∙ ap (y ∷_) h)
      (λ xs → trunc (x ∷ xs) (xs ++ [ x ]))

    ++-comm : (xs ys : SList A) → xs ++ ys ≡ ys ++ xs
    ++-comm = SListElim.indProp (λ xs → (ys : SList A) → xs ++ ys ≡ ys ++ xs)
      (λ ys → sym (++-unit-r ys))
      (λ x {xs} h ys i →
        hcomp (λ j → λ { (i = i0) → x ∷ h ys (~ j)
                       ; (i = i1) → ++-assoc ys [ x ] xs j })
              (∷-comm x ys i ++ xs))
      (λ xs → isPropΠ (λ ys → trunc (xs ++ ys) (ys ++ xs)))









  record CMon {a} (A : Type a) : Type a where
    infixr 10 _⊕_
    field
      e : A
      _⊕_ : A → A → A
      unitl : ∀ x → e ⊕ x ≡ x
      assocr : ∀ x y z → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
      comm : ∀ x y → x ⊕ y ≡ y ⊕ x
      hLevel : isSet A
  open CMon

  record CMonHom {a b} {A : Type a} {B : Type b} (M : CMon A) (N : CMon B) : Type (ℓ-max a b) where
    private
      module M = CMon M
      module N = CMon N
    field
      ϕ : A → B
      preserves-e : ϕ M.e ≡ N.e
      preserves-⊕ : ∀ x y → ϕ (x M.⊕ y) ≡ ϕ x N.⊕ ϕ y
  open CMonHom

  SListCMon : ∀ {a} {A : Type a} → CMon (SList A)
  SListCMon .e = []
  SListCMon ._⊕_ = _++_
  SListCMon .unitl xs = refl
  SListCMon .assocr = ++-assoc
  SListCMon .comm = ++-comm
  SListCMon .hLevel = trunc



  η : ∀ {a} {A : Type a} → A → SList A
  η a = [ a ]



  hPropCMon : ∀ {ℓ} → CMon (hProp ℓ)
  hPropCMon .e = (⊥* , isProp⊥*)
  hPropCMon ._⊕_ = L._⊔_
  hPropCMon .unitl x =
    L.⇒∶ PTrunc.rec (x .snd) (λ { (inr x) → x ; (inl ()) })
      ⇐∶ λ x → PTrunc.∣ (inr x) ∣₁
  hPropCMon .assocr = λ x y z → (sym (L.⊔-assoc x y z))
  hPropCMon .comm = L.⊔-comm
  hPropCMon .hLevel = isSetHProp





  module _ {a m} {A : Type a} {M : Type m} (M* : CMon M) where
    private
      module M = CMon M*
      eval : (A → M) → SList A → M
      eval f = SListElim.rec M
        M.e
        (λ a h → f a M.⊕ h)
        (λ x y h → sym (M.assocr (f x) (f y) h) ∙∙ ap (M._⊕ h) (M.comm (f x) (f y)) ∙∙ M.assocr (f y) (f x) h)
        M.hLevel

    [_]_♯ = eval

    eval-cons : ∀ x xs → {f : A → M} → eval f (x ∷ xs) ≡ f x M.⊕ eval f xs
    eval-cons x xs = refl

    module _ (h* : CMonHom SListCMon M*) (f : A → M) where
      private
        module h = CMonHom h*
        eval-uniq : h.ϕ ∘ η ≡ f → ∀ xs → h.ϕ xs ≡ eval f xs
        eval-uniq p = SListElim.indProp (λ xs → h.ϕ xs ≡ eval f xs)
          h.preserves-e
          (λ x {xs} H → h.preserves-⊕ [ x ] xs ∙ ap (M._⊕ h.ϕ xs) (funExt⁻ p x) ∙ ap (f x M.⊕_) H)
          (λ xs → M.hLevel (h.ϕ xs) (eval f xs))

      [_]_♯-uniq = eval-uniq




  module SymHead (T@(A , A*) : Toset ℓ ℓ') where
    private
      _≤_ = TosetStr._≤_ A*
      isPropValued = TosetStr.is-prop-valued A*
      antisym = TosetStr.is-antisym A*
      trans = TosetStr.is-trans A*
      totality = TosetStr.is-total A*
      reflexivity = TosetStr.is-refl A*
      isSetA = TosetStr.is-set A*

    infixr 20 _⊓_
    ⊓-min : (a b : A) → (a ≤ b) ⊎ (b ≤ a) → A
    ⊓-min a b = ⊎.rec (λ p → a) (λ q → b)

    ⊓-2Const : (a b : A) → 2-Constant (⊓-min a b)
    ⊓-2Const a b =
      ⊎.elim (λ a≤b -> ⊎.elim (λ _ -> refl) (λ b≤a -> antisym a b a≤b b≤a))
             (λ b≤a -> ⊎.elim (λ a≤b -> antisym b a b≤a a≤b) (λ _ -> refl))

    _⊓_ : A → A → A
    _⊓_ a b =
      PTrunc.rec→Set (IsToset.is-set (TosetStr.isToset A*))
      (⊓-min a b) (⊓-2Const a b) (totality a b)

    ⊓-a≤b : (a b : A) → (a ≤ b) → (a ⊓ b) ≡ a
    ⊓-a≤b a b p = PTrunc.SetElim.helper
      isSetA
      (⊓-min a b)
      (⊓-2Const a b)
      (totality a b)
      PTrunc.∣ (inl p) ∣₁

    ⊓-b≤a : (a b : A) → (b ≤ a) → (a ⊓ b) ≡ b
    ⊓-b≤a a b q = PTrunc.SetElim.helper
      isSetA
      (⊓-min a b)
      (⊓-2Const a b)
      (totality a b)
      PTrunc.∣ inr q ∣₁

    ⊓-meet : (a b : A) → (a ⊓ b) ≤ a × (a ⊓ b) ≤ b
    ⊓-meet a b =
      ( PTrunc.rec (isPropValued (a ⊓ b) a)
      (⊎.rec (λ p → tpt (_≤ a) (sym (⊓-a≤b a b p)) (reflexivity a))
              λ q → tpt (_≤ a) (sym (⊓-b≤a a b q)) q)
             (totality a b)
      , PTrunc.rec (isPropValued (a ⊓ b) b)
      (⊎.rec (λ p → tpt (_≤ b) (sym (⊓-a≤b a b p)) p)
              λ q → tpt (_≤ b) (sym (⊓-b≤a a b q)) (reflexivity b))
             (totality a b))

    ⊓-univ₁ : (a b x : A) → x ≤ (a ⊓ b) → (x ≤ a) × (x ≤ b)
    ⊓-univ₁ a b x p =
      ( trans x (a ⊓ b) a p (⊓-meet a b .fst)
      , trans x (a ⊓ b) b p (⊓-meet a b .snd))

    ⊓-univ₂ : (a b x : A) → (x ≤ a) × (x ≤ b) → x ≤ (a ⊓ b)
    ⊓-univ₂ a b x (p , q) =
      PTrunc.rec (isPropValued x (a ⊓ b))
      (⊎.rec (λ r → tpt (x ≤_) (sym (⊓-a≤b a b r)) p)
             (λ s → tpt (x ≤_) (sym (⊓-b≤a a b s)) q))
      (totality a b)

    ⊓-univ : (a b x : A) → (x ≤ (a ⊓ b)) ≃ ((x ≤ a) × (x ≤ b))
    ⊓-univ a b x =
      propBiimpl→Equiv (isPropValued x (a ⊓ b))
      (isProp× (isPropValued x a) (isPropValued x b))
      (⊓-univ₁ a b x) (⊓-univ₂ a b x)

    よ≡ : (a b : A) → ((x : A) → x ≤ a ≃ x ≤ b) → a ≡ b
    よ≡ a b f = antisym a b (f a .fst (reflexivity a)) (invEq (f b) (reflexivity b))

    ⊓-assoc : (a b c : A) → (a ⊓ b) ⊓ c ≡ a ⊓ (b ⊓ c)
    ⊓-assoc a b c =
      よ≡ ((a ⊓ b) ⊓ c) (a ⊓ b ⊓ c)
        λ x → compEquiv (⊓-univ (a ⊓ b) c x)
          (compEquiv (Σ-cong-equiv (⊓-univ a b x) (λ _ → idEquiv (x ≤ c)))
            (compEquiv Σ-assoc-≃ (compEquiv (Σ-cong-equiv (idEquiv (x ≤ a))
              (λ _ → invEquiv (⊓-univ b c x))) (invEquiv (⊓-univ a (b ⊓ c) x)))))

    ⊓-comm : (a b : A) → a ⊓ b ≡ b ⊓ a
    ⊓-comm a b = よ≡ (a ⊓ b) (b ⊓ a)
      λ x → compEquiv (⊓-univ a b x) (compEquiv Σ-swap-≃ (invEquiv (⊓-univ b a x)))





    infixr 20 _⊗_
    _⊗_ : 𝟙 ⊎ A → 𝟙 ⊎ A → 𝟙 ⊎ A
    inl ⋆ ⊗ b = b
    inr x ⊗ inl ⋆ = inr x
    inr x ⊗ inr y = inr (x ⊓ y)

    ⊗-unitl : (x : 𝟙 ⊎ A) → x ≡ x
    ⊗-unitl (inl ⋆) = refl
    ⊗-unitl (inr x) = refl

    ⊗-assoc : (a b c : 𝟙 ⊎ A) → (a ⊗ b) ⊗ c ≡ a ⊗ (b ⊗ c)
    ⊗-assoc (inl ⋆) b c = refl
    ⊗-assoc (inr a) (inl ⋆) c = refl
    ⊗-assoc (inr a) (inr b) (inl ⋆) = refl
    ⊗-assoc (inr a) (inr b) (inr c) = ap inr (⊓-assoc a b c)

    ⊗-comm : (a b : 𝟙 ⊎ A) → a ⊗ b ≡ b ⊗ a
    ⊗-comm (inl ⋆) (inl ⋆) = refl
    ⊗-comm (inl ⋆) (inr b) = refl
    ⊗-comm (inr a) (inl ⋆) = refl
    ⊗-comm (inr a) (inr b) = ap inr (⊓-comm a b)






    MaybeCMon : CMon (𝟙 ⊎ A)
    MaybeCMon .e = inl ⋆
    MaybeCMon ._⊕_ = _⊗_
    MaybeCMon .unitl = λ _ → refl
    MaybeCMon .assocr = ⊗-assoc
    MaybeCMon .comm = ⊗-comm
    MaybeCMon .hLevel = isSet⊎ isSetUnit (IsToset.is-set (TosetStr.isToset A*))





    head : SList A → 𝟙 ⊎ A
    head = [ MaybeCMon ] inr ♯

  ℕ* : IsToset {ℓ = ℓ-zero} {ℓ' = ℓ-zero} {A = ℕ} Nat._≤_
  ℕ* .IsToset.is-set = isSetℕ
  ℕ* .IsToset.is-prop-valued a b = Nat.isProp≤
  ℕ* .IsToset.is-refl a = Nat.≤-refl
  ℕ* .IsToset.is-trans a b c = Nat.≤-trans
  ℕ* .IsToset.is-antisym a b = Nat.≤-antisym
  ℕ* .IsToset.is-total a b with (Nat._≟_ a b)
  ... | Nat.lt x = PTrunc.∣ (inl (Nat.<-weaken x)) ∣₁
  ... | Nat.eq x = PTrunc.∣ (inl (tpt (λ y → (y Nat.≤ b)) (sym x) Nat.≤-refl)) ∣₁
  ... | Nat.gt x = PTrunc.∣ (inr (Nat.<-weaken x)) ∣₁


  open SymHead (ℕ , (tosetstr Nat._≤_ ℕ*))

  _ : head [] ≡ inl ⋆
  _ = refl

  _ : head [ 4 ∶ 6 ∶ 9 ∶ 6 ∶ 7 ] ≡ inr 4
  _ = refl
