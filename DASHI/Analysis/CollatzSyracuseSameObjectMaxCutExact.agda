module DASHI.Analysis.CollatzSyracuseSameObjectMaxCutExact where

------------------------------------------------------------------------
-- COLLATZ / SYRACUSE SAME-OBJECT MAX-CUT AUDIT
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.NumberTheory.Collatz.SyracuseExact
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderExact
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderCandidateExact
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderCompilerExact
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderLeanCrossProverWeldExact
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact
import DASHI.NumberTheory.Collatz.SyracuseLogDriftBoundaryExact
import DASHI.NumberTheory.Collatz.SyracuseLogDriftExact
import DASHI.Analysis.CollatzSyracuseParityObserverExact
import DASHI.Analysis.CollatzSyracuseFiniteTransferSameObjectWeldExact
import DASHI.Analysis.CollatzSyracuseCylinderInterfaceMatchExact
import DASHI.Analysis.CollatzSyracuseSamplingPushforwardExact
import DASHI.Analysis.CollatzSyracuseParityBernoulliExact
import DASHI.Analysis.CollatzSyracusePrefixAbsorptionWeldExact
import DASHI.Analysis.CollatzSyracuseUniformHittingBlockExact
import DASHI.Analysis.CollatzSyracuseGeometricSurvivalExact
import DASHI.Analysis.CollatzSyracuseCylinderCorrelationExact
import DASHI.Analysis.CollatzSyracuseMixingConcentrationCompilerExact
import DASHI.Analysis.CollatzSyracuseStoppingConcentrationExact

data MaxCutStatus : Set where
  proved : MaxCutStatus
  compiledFromRepo : MaxCutStatus
  conditionalOnHypothesis : MaxCutStatus
  sourceSpecificOpen : MaxCutStatus
  refutedRoute : MaxCutStatus

data CollatzCut : Set where
  C1-literalSyracuse : CollatzCut
  C2-parityObserver : CollatzCut
  C3-residueCylinderForward : CollatzCut
  C3a-oneStepCylinderArithmetic : CollatzCut
  C4-itineraryShift : CollatzCut
  C5-residueCylinderReverse : CollatzCut
  C6-affineIterate : CollatzCut
  C7-stoppedLogRemainder : CollatzCut
  C8-finiteTransferIntertwiner : CollatzCut
  C9-fullCylinderSeam : CollatzCut
  C10-repairedFiniteMixing : CollatzCut
  C11-samplingPushforward : CollatzCut
  C12a-directParityBernoulli : CollatzCut
  C12a-oldSpectralConcentration : CollatzCut
  C12b-prefixAbsorption : CollatzCut
  C13-integerStoppingTransport : CollatzCut
  C14-promotionFirewall : CollatzCut
  oldUnitPrefactorRoute : CollatzCut
  oldFiniteEqualsIntegerRoute : CollatzCut

cutStatus : CollatzCut → MaxCutStatus
cutStatus C1-literalSyracuse = proved
cutStatus C2-parityObserver = proved
cutStatus C3-residueCylinderForward = conditionalOnHypothesis
cutStatus C3a-oneStepCylinderArithmetic = sourceSpecificOpen
cutStatus C4-itineraryShift = proved
cutStatus C5-residueCylinderReverse = conditionalOnHypothesis
cutStatus C6-affineIterate = conditionalOnHypothesis
cutStatus C7-stoppedLogRemainder = conditionalOnHypothesis
cutStatus C8-finiteTransferIntertwiner = refutedRoute
cutStatus C9-fullCylinderSeam = conditionalOnHypothesis
cutStatus C10-repairedFiniteMixing = compiledFromRepo
cutStatus C11-samplingPushforward = sourceSpecificOpen
cutStatus C12a-directParityBernoulli = conditionalOnHypothesis
cutStatus C12a-oldSpectralConcentration = refutedRoute
cutStatus C12b-prefixAbsorption = conditionalOnHypothesis
cutStatus C13-integerStoppingTransport = conditionalOnHypothesis
cutStatus C14-promotionFirewall = proved
cutStatus oldUnitPrefactorRoute = refutedRoute
cutStatus oldFiniteEqualsIntegerRoute = refutedRoute

unitPrefactorStillRefuted :
  cutStatus oldUnitPrefactorRoute ≡ refutedRoute
unitPrefactorStillRefuted = refl

finiteChainStillNotIntegerSyracuse :
  cutStatus oldFiniteEqualsIntegerRoute ≡ refutedRoute
finiteChainStillNotIntegerSyracuse = refl

spectralIntertwinerRejected :
  cutStatus C8-finiteTransferIntertwiner ≡ refutedRoute
spectralIntertwinerRejected = refl

oldSpectralConcentrationNotCriticalPath :
  cutStatus C12a-oldSpectralConcentration ≡ refutedRoute
oldSpectralConcentrationNotCriticalPath = refl

cylinderForwardCompilerClosed :
  cutStatus C3-residueCylinderForward ≡ conditionalOnHypothesis
cylinderForwardCompilerClosed = refl

cylinderReverseCompilerClosed :
  cutStatus C5-residueCylinderReverse ≡ conditionalOnHypothesis
cylinderReverseCompilerClosed = refl

oneStepCylinderArithmeticIsTheLiveWall :
  cutStatus C3a-oneStepCylinderArithmetic ≡ sourceSpecificOpen
oneStepCylinderArithmeticIsTheLiveWall = refl

record MaxCutBoundary : Set where
  constructor maxCutBoundary
  field
    finiteMixingImpliesUniversalStopping : Nat
    interfaceRecordCountsAsSourceProof : Nat
    exhaustiveSpecimensCountAsGeneralProof : Nat
    openSourcesRemainVisible : Nat
    completeBlockBernoulliNeedsSpectralMixing : Nat
    directCylinderBijectionCanReplaceSpectralRoute : Nat
    arbitraryLengthCylinderInductionAlreadyCompiled : Nat

canonicalMaxCutBoundary : MaxCutBoundary
canonicalMaxCutBoundary = maxCutBoundary 0 0 0 1 0 1 1
