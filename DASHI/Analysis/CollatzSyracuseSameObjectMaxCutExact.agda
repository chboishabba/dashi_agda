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
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderEvenBranchExact
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderOddBranchExact
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderRepresentativeExact
import DASHI.NumberTheory.Collatz.SyracuseInv3Pow2Exact
import DASHI.NumberTheory.Collatz.SyracuseNatModCongruenceExact
import DASHI.NumberTheory.Collatz.SyracuseOneStepArithmeticExact
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderLeanCrossProverWeldExact
import DASHI.NumberTheory.Collatz.SyracuseZ2InverseBranchSourceExact
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact
import DASHI.NumberTheory.Collatz.SyracuseLogDriftBoundaryExact
import DASHI.NumberTheory.Collatz.SyracuseLogDriftExact
import DASHI.Analysis.CollatzSyracuseParityObserverExact
import DASHI.Analysis.CollatzSyracuseFiniteTransferSameObjectWeldExact
import DASHI.Analysis.CollatzSyracuseCylinderInterfaceMatchExact
import DASHI.Analysis.CollatzSyracuseCompleteBlockBijectionExact
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
  C3a-evenCylinderArithmetic : CollatzCut
  C3b-inv3Pow2Arithmetic : CollatzCut
  C3c-oddCylinderArithmetic : CollatzCut
  C4-itineraryShift : CollatzCut
  C5-residueCylinderReverse : CollatzCut
  C5a-residueCodeInjective : CollatzCut
  C6-affineIterate : CollatzCut
  C7-stoppedLogRemainder : CollatzCut
  C8a-relationMatrixTransfer : CollatzCut
  C8b-finiteInverseBranchWeld : CollatzCut
  C8c-z2TransferOperatorIntertwiner : CollatzCut
  C9-fullCylinderSeam : CollatzCut
  C10-repairedRelationMixing : CollatzCut
  C11a-completeBlockBijection : CollatzCut
  C11b-completeBlockUniformPushforward : CollatzCut
  C11c-arbitraryIntervalBoundary : CollatzCut
  C11d-logWeightedSampling : CollatzCut
  C12a-directParityBernoulliLaw : CollatzCut
  C12b-BernoulliConcentration : CollatzCut
  C12c-prefixAbsorption : CollatzCut
  C13-integerStoppingTransport : CollatzCut
  C14-promotionFirewall : CollatzCut
  oldUnitPrefactorRoute : CollatzCut
  oldFiniteEqualsIntegerRoute : CollatzCut

cutStatus : CollatzCut → MaxCutStatus
cutStatus C1-literalSyracuse = proved
cutStatus C2-parityObserver = proved
cutStatus C3-residueCylinderForward = proved
cutStatus C3a-evenCylinderArithmetic = proved
cutStatus C3b-inv3Pow2Arithmetic = proved
cutStatus C3c-oddCylinderArithmetic = proved
cutStatus C4-itineraryShift = proved
cutStatus C5-residueCylinderReverse = proved
cutStatus C5a-residueCodeInjective = proved
cutStatus C6-affineIterate = proved
cutStatus C7-stoppedLogRemainder = conditionalOnHypothesis
cutStatus C8a-relationMatrixTransfer = refutedRoute
cutStatus C8b-finiteInverseBranchWeld = proved
cutStatus C8c-z2TransferOperatorIntertwiner = sourceSpecificOpen
cutStatus C9-fullCylinderSeam = compiledFromRepo
cutStatus C10-repairedRelationMixing = compiledFromRepo
cutStatus C11a-completeBlockBijection = proved
cutStatus C11b-completeBlockUniformPushforward = proved
cutStatus C11c-arbitraryIntervalBoundary = conditionalOnHypothesis
cutStatus C11d-logWeightedSampling = sourceSpecificOpen
cutStatus C12a-directParityBernoulliLaw = proved
cutStatus C12b-BernoulliConcentration = conditionalOnHypothesis
cutStatus C12c-prefixAbsorption = conditionalOnHypothesis
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

relationMatrixIntertwinerRejected :
  cutStatus C8a-relationMatrixTransfer ≡ refutedRoute
relationMatrixIntertwinerRejected = refl

cylinderForwardPaid :
  cutStatus C3-residueCylinderForward ≡ proved
cylinderForwardPaid = refl

cylinderReversePaid :
  cutStatus C5-residueCylinderReverse ≡ proved
cylinderReversePaid = refl

oneStepCylinderArithmeticPaid :
  cutStatus C3c-oddCylinderArithmetic ≡ proved
oneStepCylinderArithmeticPaid = refl

completeBlockUniformityPaid :
  cutStatus C11b-completeBlockUniformPushforward ≡ proved
completeBlockUniformityPaid = refl

directBernoulliLawPaid :
  cutStatus C12a-directParityBernoulliLaw ≡ proved
directBernoulliLawPaid = refl

oldRelationSpectralConcentrationNotCriticalPath :
  cutStatus C8a-relationMatrixTransfer ≡ refutedRoute
oldRelationSpectralConcentrationNotCriticalPath = refl

record MaxCutBoundary : Set where
  constructor maxCutBoundary
  field
    relationMixingImpliesUniversalStopping : Nat
    interfaceRecordCountsAsSourceProof : Nat
    exhaustiveSpecimensCountAsGeneralProof : Nat
    openSourcesRemainVisible : Nat
    completeBlockBernoulliNeedsSpectralMixing : Nat
    directCylinderBijectionReplacesRelationSpectralRoute : Nat
    arbitraryLengthCylinderInductionPaid : Nat
    agdaNativeInv3Paid : Nat
    completeBlockUniformityPaidHere : Nat
    arbitrarySamplingStillSeparate : Nat
    realConcentrationStillSeparate : Nat
    universalStoppingStillSeparate : Nat

canonicalMaxCutBoundary : MaxCutBoundary
canonicalMaxCutBoundary =
  maxCutBoundary 0 0 0 1 0 1 1 1 1 1 1 1
