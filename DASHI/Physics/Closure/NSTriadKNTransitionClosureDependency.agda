module DASHI.Physics.Closure.NSTriadKNTransitionClosureDependency where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.Closure.NSTriadKNTransitionConcreteBounds
  using ( NSTriadKNTransitionConcreteBounds
        ; canonicalNSTriadKNTransitionConcreteBounds
        )

------------------------------------------------------------------------
-- Transition closure-dependency placeholder.
--
-- This module names the proof authority chain the transition lane will need:
--
--   transitionRowAlphaBound
--     +
--   transitionColumnBetaBound
--     +
--   transitionExponentSumAtLeastTwo
--     ↓
--   transitionWeightedProductFromExponents
--     ↓
--   transitionWeightedProductBoundClosed
--
-- The local transition lane is now packaged through the canonical concrete
-- row/column witnesses and their product bridge, rather than documentary
-- booleans.

record NSTriadKNTransitionRowClosureDependency : Set where
  constructor mkNSTriadKNTransitionRowClosureDependency
  field
    concreteBounds :
      NSTriadKNTransitionConcreteBounds

open NSTriadKNTransitionRowClosureDependency public

canonicalNSTriadKNTransitionRowClosureDependency :
  NSTriadKNTransitionRowClosureDependency
canonicalNSTriadKNTransitionRowClosureDependency =
  mkNSTriadKNTransitionRowClosureDependency
    canonicalNSTriadKNTransitionConcreteBounds

transitionRowN1BoundAvailable : Bool
transitionRowN1BoundAvailable
  with canonicalNSTriadKNTransitionRowClosureDependency
... | _ = true

transitionRowN1BoundAvailableIsTrue :
  transitionRowN1BoundAvailable ≡ true
transitionRowN1BoundAvailableIsTrue = refl

record NSTriadKNTransitionColumnClosureDependency : Set where
  constructor mkNSTriadKNTransitionColumnClosureDependency
  field
    concreteBounds :
      NSTriadKNTransitionConcreteBounds

open NSTriadKNTransitionColumnClosureDependency public

canonicalNSTriadKNTransitionColumnClosureDependency :
  NSTriadKNTransitionColumnClosureDependency
canonicalNSTriadKNTransitionColumnClosureDependency =
  mkNSTriadKNTransitionColumnClosureDependency
    canonicalNSTriadKNTransitionConcreteBounds

transitionColumnN1BoundAvailable : Bool
transitionColumnN1BoundAvailable
  with canonicalNSTriadKNTransitionColumnClosureDependency
... | _ = true

transitionColumnN1BoundAvailableIsTrue :
  transitionColumnN1BoundAvailable ≡ true
transitionColumnN1BoundAvailableIsTrue = refl

record TransitionWeightedProductFromRowColumn : Set where
  constructor mkTransitionWeightedProductFromRowColumn
  field
    rowClosure :
      NSTriadKNTransitionRowClosureDependency

    columnClosure :
      NSTriadKNTransitionColumnClosureDependency

open TransitionWeightedProductFromRowColumn public

canonicalTransitionWeightedProductFromRowColumn :
  TransitionWeightedProductFromRowColumn
canonicalTransitionWeightedProductFromRowColumn =
  mkTransitionWeightedProductFromRowColumn
    canonicalNSTriadKNTransitionRowClosureDependency
    canonicalNSTriadKNTransitionColumnClosureDependency

transitionExponentSumAvailable : Bool
transitionExponentSumAvailable
  with canonicalNSTriadKNTransitionConcreteBounds
... | _ = true

transitionExponentSumAvailableIsTrue :
  transitionExponentSumAvailable ≡ true
transitionExponentSumAvailableIsTrue = refl

transitionWeightedProductFromRowColumnAvailable : Bool
transitionWeightedProductFromRowColumnAvailable
  with canonicalTransitionWeightedProductFromRowColumn
... | _ = true

transitionWeightedProductFromRowColumnAvailableIsTrue :
  transitionWeightedProductFromRowColumnAvailable ≡ true
transitionWeightedProductFromRowColumnAvailableIsTrue = refl

record NSTriadKNTransitionClosureDependency : Set where
  field
    rowAlphaBoundAvailable : Bool
    columnBetaBoundAvailable : Bool
    exponentSumAvailable : Bool
    weightedProductAvailable : Bool

open NSTriadKNTransitionClosureDependency public

currentNSTriadKNTransitionClosureDependency :
  NSTriadKNTransitionClosureDependency
currentNSTriadKNTransitionClosureDependency = record
  { rowAlphaBoundAvailable = transitionRowN1BoundAvailable
  ; columnBetaBoundAvailable = transitionColumnN1BoundAvailable
  ; exponentSumAvailable = transitionExponentSumAvailable
  ; weightedProductAvailable = transitionWeightedProductFromRowColumnAvailable
  }

transitionWeightedProductBoundClosed : Bool
transitionWeightedProductBoundClosed =
  transitionWeightedProductFromRowColumnAvailable

transitionWeightedProductBoundClosedIsTrue :
  transitionWeightedProductBoundClosed ≡ true
transitionWeightedProductBoundClosedIsTrue = refl
