{-# OPTIONS --cubical --safe --guardedness -WnoUnsupportedIndexedMatch #-}

module Prelude where

open import Cubical.Foundations.Prelude
  renaming ( congS to ap
           ; cong to apd
           ; congP to apP
           ; subst to tpt
           )
  hiding ( funExt ) public
import Cubical.Foundations.Prelude as P using ( funExt )
open import Cubical.Foundations.Univalence hiding ( ua ) public
import Cubical.Foundations.Univalence as P using ( ua )
open import Cubical.Foundations.HLevels public
open import Cubical.Foundations.Path public
open import Cubical.Foundations.GroupoidLaws public
open import Cubical.Foundations.Function public
open import Cubical.Foundations.Equiv public
open import Cubical.Foundations.Isomorphism public
open import Cubical.Foundations.Function public
open import Cubical.Foundations.Structure public
open import Cubical.Functions.Embedding public
import Cubical.Functions.Logic as L
import Cubical.Data.Sigma

open import Cubical.Data.Nat hiding (elim) public
open import Cubical.Data.Maybe hiding (elim ; rec) public
open import Cubical.Data.Unit renaming (Unit to 𝟙 ; tt to ⋆) public
open import Cubical.Data.Empty hiding (elim ; rec) public
open import Cubical.Data.Sum hiding (elim ; rec) public
