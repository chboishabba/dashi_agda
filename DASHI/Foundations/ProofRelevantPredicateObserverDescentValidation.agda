module DASHI.Foundations.ProofRelevantPredicateObserverDescentValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Unit using (⊤; tt)

import DASHI.Foundations.HyperformChartGluingExact as Glue
import DASHI.Foundations.ProofRelevantPredicateObserverDescentExact as Descent

data Fine : Set where left right : Fine
data Coarse : Set where same : Coarse

observer : Glue.ObserverWithFibre Fine Coarse
observer = record
  { Glue.observe = λ _ → same
  }

predicate : Fine → Set
predicate _ = ⊤

predicateFactors :
  Descent.PredicateFactorsThroughObserver observer predicate
predicateFactors = record
  { Descent.coarsePredicate = λ _ → ⊤
  ; Descent.forward = λ _ _ → tt
  ; Descent.backward = λ _ _ → tt
  }

sameFibreTransportsPredicate :
  predicate left →
  predicate right
sameFibreTransportsPredicate =
  Descent.predicateTransportAcrossObserverFibre
    predicateFactors left right refl
