module DASHI.Physics.Chemistry.AtomicPeriodicTable369GraphMaxCutValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369FillingGraphExact as F
import DASHI.Physics.Chemistry.AtomicPeriodicTable369TernaryRealizationIntertwinerExact as R

fillingGraphPaidRegression :
  F.AtomicFillingGraphBoundary.directedStructuralFillingGraphPaid
    F.canonicalAtomicFillingGraphBoundary
  ≡ true
fillingGraphPaidRegression = refl

closureObserverRegression :
  F.closureObserver F.c2 ≡ F.heliumClosure
  × F.closureObserver F.c10 ≡ F.neonClosure
  × F.closureObserver F.c18 ≡ F.argonClosure
closureObserverRegression = refl , (refl , refl)

realizationNonPromotionRegression :
  R.TernaryAtomicRealizationBoundary.sameCardinalityConstructsRealization
    R.canonicalTernaryAtomicRealizationBoundary
  ≡ false
  ×
  R.TernaryAtomicRealizationBoundary.graphSimilarityConstructsRealization
    R.canonicalTernaryAtomicRealizationBoundary
  ≡ false
realizationNonPromotionRegression = refl , refl
