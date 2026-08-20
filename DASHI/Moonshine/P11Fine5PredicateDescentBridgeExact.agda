module DASHI.Moonshine.P11Fine5PredicateDescentBridgeExact where

------------------------------------------------------------------------
-- Predicate descent on the actual p=11 marked/coarse quotient.
-- Coarse j-predicates are fibre-constant; a marked-sheet predicate is not.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Core.PredicatePullbackLatticeExact as Predicate

import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as Geo

isJZero : Predicate.Predicate Geo.P11SupersingularJ
isJZero Geo.jZeroSS = true
isJZero Geo.j1728SS = false

coarseJZeroPredicate : Predicate.Predicate Fine.P11Fine5
coarseJZeroPredicate = Predicate.pullbackPredicate Fine.projectFine5 isJZero

coarseJZeroPredicateFibreConstant :
  Predicate.FibreConstantPredicate Fine.projectFine5 coarseJZeroPredicate
coarseJZeroPredicateFibreConstant =
  Predicate.pulledBackPredicateIsFibreConstant Fine.projectFine5 isJZero

isMarkedA0 : Predicate.Predicate Fine.P11Fine5
isMarkedA0 Fine.a0 = true
isMarkedA0 Fine.a1 = false
isMarkedA0 Fine.b0 = false
isMarkedA0 Fine.b1 = false
isMarkedA0 Fine.b2 = false

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

markedA0PredicateNotFibreConstant :
  Predicate.FibreConstantPredicate Fine.projectFine5 isMarkedA0 → ⊥
markedA0PredicateNotFibreConstant constant =
  trueNotFalse (constant Fine.a0 Fine.a1 refl)

record P11Fine5PredicateDescentBoundary : Set where
  constructor p11Fine5PredicateDescentBoundary
  field
    coarseJPredicateDescends : Bool
    coarseJPredicateDescendsIsTrue : coarseJPredicateDescends ≡ true
    markedSheetPredicateDescendsToCoarseJ : Bool
    markedSheetPredicateDescendsToCoarseJIsFalse :
      markedSheetPredicateDescendsToCoarseJ ≡ false

canonicalP11Fine5PredicateDescentBoundary : P11Fine5PredicateDescentBoundary
canonicalP11Fine5PredicateDescentBoundary =
  p11Fine5PredicateDescentBoundary true refl false refl
