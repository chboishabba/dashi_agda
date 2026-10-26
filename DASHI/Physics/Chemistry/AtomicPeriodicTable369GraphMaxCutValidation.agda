module DASHI.Physics.Chemistry.AtomicPeriodicTable369GraphMaxCutValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369FillingGraphExact as F
import DASHI.Physics.Chemistry.AtomicPeriodicTable369TernaryRealizationIntertwinerExact as R
import DASHI.Physics.Chemistry.AtomicPeriodicTable369MagneticC3PhysicalRealizationExact as C3
import DASHI.Physics.Chemistry.AtomicPeriodicTable369MagneticC3SameActionExact as Same
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AnalyticQuantumExecutionExact as AQ
import DASHI.Physics.Chemistry.AtomicPeriodicTable369LiBeMinimalBasisHFExecutionExact as LiBe

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

pShellRotationCharacterRegression :
  C3.rotationPhase C3.mNegOne ≡ C3.phaseNegative
  × C3.rotationPhase C3.mZero ≡ C3.phaseNeutral
  × C3.rotationPhase C3.mPosOne ≡ C3.phasePositive
pShellRotationCharacterRegression = refl , (refl , refl)

rotationCharacterReusesExistingFourierRegression :
  (m : C3.MagneticState) ->
  C3.rotationPhaseViaExistingCharacter m ≡ C3.rotationPhase m
rotationCharacterReusesExistingFourierRegression =
  C3.rotationPhaseIsExistingPositiveCharacter

pShellChargeStepOrderThreeRegression :
  C3.chargePositiveStep
    (C3.chargePositiveStep (C3.chargePositiveStep C3.mNegOne))
  ≡ C3.mNegOne
pShellChargeStepOrderThreeRegression = C3.chargePositiveStepOrderThree C3.mNegOne

pShellRealizationIntertwinerRegression :
  (x : C3.DepthOneKernel) ->
  R.realize C3.pShellC3Realization
    (R.ternaryStep C3.pShellC3Realization x)
  ≡
  R.physicalStep C3.pShellC3Realization
    (R.realize C3.pShellC3Realization x)
pShellRealizationIntertwinerRegression =
  R.intertwines C3.pShellC3Realization

residueSameObjectWeldRegression :
  (x : C3.DepthOneKernel) ->
  C3.sectorResidue (C3.magneticSector (C3.realizeMagneticState x))
  ≡ C3.kernelResidue x
residueSameObjectWeldRegression = C3.realizationPreservesC3Residue

sameActionRecognitionRegression :
  (x : C3.DepthOneKernel) ->
  C3.kernelResidue (C3.ternaryChargePositiveStep x)
  ≡ Same.translatePositive (C3.kernelResidue x)
sameActionRecognitionRegression = Same.ternaryStepIsPositiveTranslation

selectionRuleRegression :
  C3.transitionAllowed C3.sectorNegative C3.chargePositive C3.sectorZero
  ≡ true
  ×
  C3.transitionAllowed C3.sectorNegative C3.chargeZero C3.sectorZero
  ≡ false
selectionRuleRegression = refl , refl

analyticSpatialChargeNoncollapseRegression :
  AQ.basisStateAction AQ.spatialRotation120 C3.mZero ≡ C3.mZero
  ×
  AQ.basisStateAction AQ.positiveChargeTransport C3.mZero ≡ C3.mPosOne
analyticSpatialChargeNoncollapseRegression = refl , refl

analyticExecutionBoundaryRegression :
  AQ.AnalyticQuantumExecutionBoundary.analyticHydrogenicWavefunctionsExecuted
    AQ.canonicalAnalyticQuantumExecutionBoundary
  ≡ true
  ×
  AQ.AnalyticQuantumExecutionBoundary.weightedHydrogenicE1GraphExecuted
    AQ.canonicalAnalyticQuantumExecutionBoundary
  ≡ true
  ×
  AQ.AnalyticQuantumExecutionBoundary.lithiumBerylliumMinimalBasisSCFExecuted
    AQ.canonicalAnalyticQuantumExecutionBoundary
  ≡ true
  ×
  AQ.AnalyticQuantumExecutionBoundary.lithiumBerylliumCompleteBasisRecoveryPaid
    AQ.canonicalAnalyticQuantumExecutionBoundary
  ≡ false
analyticExecutionBoundaryRegression = refl , (refl , (refl , refl))

liBeExecutionBoundaryRegression :
  LiBe.LiBeMinimalBasisExecutionBoundary.lithiumOneSAndTwoSTrackedSimultaneously
    LiBe.canonicalLiBeMinimalBasisExecutionBoundary
  ≡ true
  ×
  LiBe.LiBeMinimalBasisExecutionBoundary.berylliumOneSAndTwoSTrackedSimultaneously
    LiBe.canonicalLiBeMinimalBasisExecutionBoundary
  ≡ true
  ×
  LiBe.LiBeMinimalBasisExecutionBoundary.completeBasisLimitPaid
    LiBe.canonicalLiBeMinimalBasisExecutionBoundary
  ≡ false
liBeExecutionBoundaryRegression = refl , (refl , refl)
