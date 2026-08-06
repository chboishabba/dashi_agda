module DASHI.Physics.Foundations.Round5AttachedCompletionRegression where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.FiniteHistoryFunctionalExact as History
import DASHI.Physics.Foundations.FiniteResidueCycleReachabilityExact as Residue
import DASHI.Physics.Foundations.FiniteMultiscaleKernelCompatibilityExact as Multiscale
import DASHI.Physics.Foundations.FiniteUltrametricReebFlowExact as Ultrametric
import DASHI.Physics.Foundations.ProbabilityDecoratedReebExact as Reeb
import DASHI.Physics.Foundations.Round5AttachedCompletionBoundary as Boundary

completionBoundaryExists : Boundary.Round5AttachedCompletionBoundary
completionBoundaryExists = Boundary.canonicalRound5AttachedCompletionBoundary

nondeterministicHistoryRegression :
  History.classifyHistory History.historyABC ≡ History.admissibleHistory
  ×
  History.classifyHistory History.historyACB ≡ History.admissibleHistory
nondeterministicHistoryRegression = refl , refl

actionFunctionalRegression :
  History.historyAction History.historyABC ≡ 2
  ×
  History.historyAction History.historyACB ≡ 4
actionFunctionalRegression = refl , refl

stationaryCandidateRegression :
  History.variationAction History.leftVariation
  ≡
  History.variationAction History.stationaryVariation + 2
  ×
  History.variationAction History.rightVariation
  ≡
  History.variationAction History.stationaryVariation + 3
stationaryCandidateRegression = refl , refl

residueCycleRegression :
  Residue.successor6Six Residue.residue6Four ≡ Residue.residue6Four
  ×
  Residue.successor9Nine Residue.residue9Seven ≡ Residue.residue9Seven
residueCycleRegression = refl , refl

boundedReachabilityRegression :
  Residue.reachStepTwo Residue.reachStart ≡ Residue.reachTerminal
boundedReachabilityRegression = refl

finiteGeometricSeriesRegression :
  Residue.partialSum3 ≡ 40
  ×
  (2 * Residue.partialSum3 + 1 ≡ 81)
finiteGeometricSeriesRegression = refl , refl

exactCompatibilityRegression :
  Multiscale.coarseProjection
    (Multiscale.fineKernelExact Multiscale.fineRightLow)
  ≡
  Multiscale.coarseKernelExact
    (Multiscale.coarseProjection Multiscale.fineRightLow)
exactCompatibilityRegression = refl

compatibilityDefectRegression :
  Multiscale.compatibilityDefect Multiscale.fineLeftLow ≡ 1
  ×
  Multiscale.compatibilityDefect Multiscale.fineLeftHigh ≡ 0
compatibilityDefectRegression = refl , refl

ultrametricRegression :
  Ultrametric.addressDistance Ultrametric.addressA Ultrametric.addressB
  ≡
  Ultrametric.distanceNear
  ×
  Ultrametric.addressDistance Ultrametric.addressA Ultrametric.addressC
  ≡
  Ultrametric.distanceFar
ultrametricRegression = refl , refl

stochasticFlowRegression :
  Ultrametric.transitionWeight Reeb.sourceToLeft
  +
  Ultrametric.transitionWeight Reeb.sourceToRight
  ≡
  6
stochasticFlowRegression = refl

historyMeasureRegression :
  Ultrametric.historyWeight Ultrametric.leftHistory ≡ 12
  ×
  Ultrametric.historyWeight Ultrametric.rightHistory ≡ 24
historyMeasureRegression = refl , refl
