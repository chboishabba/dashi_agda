module DASHI.Physics.YangMills.YangMillsSubmissionRound9ExactCutset where

open import Agda.Builtin.String using (String)

import DASHI.Physics.YangMills.BalabanBishopFactorialPowerRecurrenceExact as BishopRecurrence
import DASHI.Physics.YangMills.BalabanBishopSeriesParityAndLimitExact as BishopLimit
import DASHI.Physics.YangMills.BalabanP06PhysicalModelLeafExact as P06
import DASHI.Physics.YangMills.BalabanP11PhysicalPrefixTailEntropyExact as P11
import DASHI.Physics.YangMills.BalabanStepVFiniteGeometricBackendExact as StepV
import DASHI.Physics.YangMills.BalabanP10P33PhysicalCutsetExact as P10P33
import DASHI.Physics.YangMills.BalabanGate4ParityIntegrationExact as Gate4
import DASHI.Physics.YangMills.YangMillsRGParitySISpineExact as Endpoint
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- One typed cutset for every lane requested in the round-nine attachment.
-- Inhabiting this record is not identified with the final Clay theorem: it is
-- the exact local-to-global evidence package still required after the owned
-- generic reductions.
------------------------------------------------------------------------

record Round9LocalAnalyticCutset : Set₁ where
  field
    bishopFactorialCoefficientSteps :
      BishopRecurrence.ConcreteFactorialCoefficientStepBounds

    bishopAlternatingBrackets :
      BishopLimit.ConcreteBishopAlternatingBrackets

    bishopOrderClosedLimitPassage : Set
    bishopOrderClosedLimitPassageEvidence :
      bishopOrderClosedLimitPassage

    bishopTransformedSeriesConvergence : Set
    bishopTransformedSeriesConvergenceEvidence :
      bishopTransformedSeriesConvergence

    p06PhysicalModelLeaf : P06.P06PhysicalModelLeafInputs
    p11PhysicalPrefixTail : P11.P11PhysicalPrefixTailInputs

    p10PhysicalSuppression : P10P33.P10LargeFieldPhysicalChain
    p33PhysicalEllipticity : P10P33.P33LinkEllipticityPhysicalChain

    gate4Parity : Gate4.Gate4ParityPackage

open Round9LocalAnalyticCutset public

record Round9StepVScalarCutset : Set₁ where
  field
    Scalar : Set
    scalarBackend : StepV.StepVScalarBackend Scalar
    finiteSumBackend :
      StepV.CompleteStepVFiniteSumBackend Scalar scalarBackend

    physicalOscillationShells : Set
    physicalOscillationShellsEvidence : physicalOscillationShells

    shellDecompositionMatchesActualKPNeighbourhood : Set
    shellDecompositionMatchesActualKPNeighbourhoodEvidence :
      shellDecompositionMatchesActualKPNeighbourhood

    weightedActivityDecayUsesP10AndP33 : Set
    weightedActivityDecayUsesP10AndP33Evidence :
      weightedActivityDecayUsesP10AndP33

open Round9StepVScalarCutset public

record Round9GlobalEndpointCutset : Set₁ where
  field
    Scalar : Set
    parityAndSI : Endpoint.YangMillsParitySISpine Scalar

    dlrSmallnessFromStepV : Set
    dlrSmallnessFromStepVEvidence : dlrSmallnessFromStepV

    crossScaleInfluenceSummability : Set
    crossScaleInfluenceSummabilityEvidence :
      crossScaleInfluenceSummability

    uniformLogSobolevInequality : Set
    uniformLogSobolevInequalityEvidence :
      uniformLogSobolevInequality

    fixedLatticeSpectralGap : Set
    fixedLatticeSpectralGapEvidence : fixedLatticeSpectralGap

    thermodynamicLimitExistsAndIsUnique : Set
    thermodynamicLimitExistsAndIsUniqueEvidence :
      thermodynamicLimitExistsAndIsUnique

    cutoffRemovalExistsAndIsSchemeIndependent : Set
    cutoffRemovalExistsAndIsSchemeIndependentEvidence :
      cutoffRemovalExistsAndIsSchemeIndependent

    osReconstructionHypothesesVerified : Set
    osReconstructionHypothesesVerifiedEvidence :
      osReconstructionHypothesesVerified

    positivePhysicalSIMassGap : Set
    positivePhysicalSIMassGapEvidence :
      positivePhysicalSIMassGap

open Round9GlobalEndpointCutset public

record Round9CompleteCutset : Set₁ where
  field
    local : Round9LocalAnalyticCutset
    stepV : Round9StepVScalarCutset
    global : Round9GlobalEndpointCutset

    localStepVTypesAgree : Set
    localStepVTypesAgreeEvidence : localStepVTypesAgree

    stepVGlobalTypesAgree : Set
    stepVGlobalTypesAgreeEvidence : stepVGlobalTypesAgree

    theoremBoundary : String

open Round9CompleteCutset public

round9ExactCutsetDefinitionLevel : ProofLevel
round9ExactCutsetDefinitionLevel = machineChecked

round9LocalAnalyticInhabitantsLevel : ProofLevel
round9LocalAnalyticInhabitantsLevel = conditional

round9StepVPhysicalInhabitantsLevel : ProofLevel
round9StepVPhysicalInhabitantsLevel = conditional

round9GlobalEndpointInhabitantsLevel : ProofLevel
round9GlobalEndpointInhabitantsLevel = conditional
