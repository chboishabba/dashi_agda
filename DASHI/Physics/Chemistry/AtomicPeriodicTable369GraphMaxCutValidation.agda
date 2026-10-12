module DASHI.Physics.Chemistry.AtomicPeriodicTable369GraphMaxCutValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369FillingGraphExact as F
import DASHI.Physics.Chemistry.AtomicPeriodicTable369TernaryRealizationIntertwinerExact as R
import DASHI.Physics.Chemistry.AtomicPeriodicTable369MagneticC3PhysicalRealizationExact as C3

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

pShellC3SectorRegression :
  C3.magneticSector C3.mNegOne ≡ C3.sectorNegative
  × C3.magneticSector C3.mZero ≡ C3.sectorZero
  × C3.magneticSector C3.mPosOne ≡ C3.sectorPositive
pShellC3SectorRegression = refl , (refl , refl)

pShellRotationOrderThreeRegression :
  C3.rotateMagneticState
    (C3.rotateMagneticState (C3.rotateMagneticState C3.mNegOne))
  ≡ C3.mNegOne
pShellRotationOrderThreeRegression = C3.rotateMagneticStateOrderThree C3.mNegOne

pShellRealizationIntertwinerRegression :
  (x : C3.DepthOneKernel) ->
  R.realize C3.pShellC3Realization
    (R.ternaryStep C3.pShellC3Realization x)
  ≡
  R.physicalStep C3.pShellC3Realization
    (R.realize C3.pShellC3Realization x)
pShellRealizationIntertwinerRegression =
  R.intertwines C3.pShellC3Realization

selectionRuleRegression :
  C3.transitionAllowed C3.sectorNegative C3.chargePositive C3.sectorZero
  ≡ true
  ×
  C3.transitionAllowed C3.sectorNegative C3.chargeZero C3.sectorZero
  ≡ false
selectionRuleRegression = refl , refl
