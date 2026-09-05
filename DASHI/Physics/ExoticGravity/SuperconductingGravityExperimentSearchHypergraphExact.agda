module DASHI.Physics.ExoticGravity.SuperconductingGravityExperimentSearchHypergraphExact where

open import DASHI.Core.Prelude

import DASHI.Reasoning.AristotleMCGSHypergraphExact as Aristotle
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Least
import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Physics.ExoticGravity.SuperconductingGravityExperimentDesignProofSearchCrossPollinationExact as Design

------------------------------------------------------------------------
-- SUPERCONDUCTING-GRAVITY EXPERIMENT PROOF-SEARCH HYPERGRAPH
--
-- The promotion root is an AND cut.  Unresolved empirical leaves are encoded
-- as self-blocking actions, not empty-target actions, because an empty target
-- list would manufacture a successful proof leaf in the generic search graph.
------------------------------------------------------------------------

data SearchState : Set where
  sourceNormalisedConstitutiveFinding
  sourceCurrentLeaf
  sourceStressEnergyLeaf
  geometryLeaf
  transitionLockLeaf
  externalProbeLeaf
  backgroundClosureLeaf
  replicationLeaf
  constitutiveResidualLeaf
  : SearchState

data SearchAction : Set where
  assembleConstitutiveFinding
  inspectSourceCurrent
  inspectSourceStressEnergy
  inspectGeometry
  inspectTransitionLock
  inspectExternalProbe
  inspectBackgroundClosure
  inspectReplication
  inspectConstitutiveResidual
  : SearchAction

actionSource : SearchAction → SearchState
actionSource assembleConstitutiveFinding = sourceNormalisedConstitutiveFinding
actionSource inspectSourceCurrent = sourceCurrentLeaf
actionSource inspectSourceStressEnergy = sourceStressEnergyLeaf
actionSource inspectGeometry = geometryLeaf
actionSource inspectTransitionLock = transitionLockLeaf
actionSource inspectExternalProbe = externalProbeLeaf
actionSource inspectBackgroundClosure = backgroundClosureLeaf
actionSource inspectReplication = replicationLeaf
actionSource inspectConstitutiveResidual = constitutiveResidualLeaf

actionTargets : SearchAction → List SearchState
actionTargets assembleConstitutiveFinding =
  sourceCurrentLeaf ∷
  sourceStressEnergyLeaf ∷
  geometryLeaf ∷
  transitionLockLeaf ∷
  externalProbeLeaf ∷
  backgroundClosureLeaf ∷
  replicationLeaf ∷
  constitutiveResidualLeaf ∷ []
actionTargets inspectSourceCurrent = sourceCurrentLeaf ∷ []
actionTargets inspectSourceStressEnergy = sourceStressEnergyLeaf ∷ []
actionTargets inspectGeometry = geometryLeaf ∷ []
actionTargets inspectTransitionLock = transitionLockLeaf ∷ []
actionTargets inspectExternalProbe = externalProbeLeaf ∷ []
actionTargets inspectBackgroundClosure = backgroundClosureLeaf ∷ []
actionTargets inspectReplication = replicationLeaf ∷ []
actionTargets inspectConstitutiveResidual = constitutiveResidualLeaf ∷ []

experimentSearchGraph : Aristotle.SearchHypergraph
experimentSearchGraph = record
  { State = SearchState
  ; Action = SearchAction
  ; source = actionSource
  ; targets = actionTargets
  }

constitutiveFindingRequiresEightLeaves :
  Aristotle.targets experimentSearchGraph assembleConstitutiveFinding ≡
    sourceCurrentLeaf ∷ sourceStressEnergyLeaf ∷ geometryLeaf ∷
    transitionLockLeaf ∷ externalProbeLeaf ∷ backgroundClosureLeaf ∷
    replicationLeaf ∷ constitutiveResidualLeaf ∷ []
constitutiveFindingRequiresEightLeaves = refl

------------------------------------------------------------------------
-- Search modalities and route dispositions.
------------------------------------------------------------------------

data SearchModality : Set where
  repositoryProofReuse
  publicSourceReconstruction
  calibrationExperiment
  physicalMeasurement
  perturbAndMeasure
  independentReplication
  : SearchModality

routeDisposition : SearchModality → Least.RouteDisposition
routeDisposition repositoryProofReuse = Least.redirectedReuse
routeDisposition publicSourceReconstruction = Least.admitted
routeDisposition calibrationExperiment = Least.admitted
routeDisposition physicalMeasurement = Least.admitted
routeDisposition perturbAndMeasure = Least.admitted
routeDisposition independentReplication = Least.admitted

phaseSignalAlonePromotesEtaC : Least.RouteDisposition
phaseSignalAlonePromotesEtaC = Least.rejected Least.strengthMismatch

externalSignalAlonePromotesEtaC : Least.RouteDisposition
externalSignalAlonePromotesEtaC = Least.rejected Least.consumerMismatch

oneNullGeometryProvesUniversalEtaCOne : Least.RouteDisposition
oneNullGeometryProvesUniversalEtaCOne = Least.rejected Least.scopeMismatch

microscopicGeometrySubstitutedForProbeGeometry : Least.RouteDisposition
microscopicGeometrySubstitutedForProbeGeometry = Least.rejected Least.carrierMismatch

------------------------------------------------------------------------
-- Empirical measurements may discharge empirical leaves through an explicit
-- adapter, but they are not kernel proof authority by themselves.
------------------------------------------------------------------------

rawExperimentAuthority : Least.TheoremAuthority
rawExperimentAuthority = Least.analogyOnly

rawExperimentCannotDirectlyCloseKernelLeaf :
  Least.ClosedLeafCapability rawExperimentAuthority → ⊥
rawExperimentCannotDirectlyCloseKernelLeaf = Least.analogyCannotCloseLeaf

------------------------------------------------------------------------
-- Declared information moves reuse the generic actionability owner.
------------------------------------------------------------------------

characteriseSourceMove : Choice.InformationMove
characteriseSourceMove = Choice.informationMove
  Choice.takeMeasurement 1
  "measure/reconstruct superconducting mass-current and stress-energy source"
  "requires calibrated electrical, rotational, thermal and geometry observables"
  "same-apparatus source-characterisation protocol"

crossTcMove : Choice.InformationMove
crossTcMove = Choice.informationMove
  Choice.perturbAndMeasure 2
  "cross the superconducting phase boundary while recording source and probe"
  "requires calibrated temperature/phase and matched drive/source observables"
  "controlled phase-transition protocol"

closeBackgroundMove : Choice.InformationMove
closeBackgroundMove = Choice.informationMove
  Choice.increaseFidelity 3
  "increase fidelity of magnetic, mechanical, thermal and sensor background closure"
  "requires nuisance-channel calibration and geometry-matched null controls"
  "background-closure protocol"

replicateMove : Choice.InformationMove
replicateMove = Choice.informationMove
  Choice.replicateMeasurement 4
  "independent source-normalised replication"
  "requires declared same-object comparison and reproducibility protocol"
  "replication protocol"

------------------------------------------------------------------------
-- Cross-pollination boundary.
------------------------------------------------------------------------

record ExperimentSearchHypergraphBoundary : Set where
  constructor experiment-search-hypergraph-boundary
  field
    constitutivePromotionIsANDCut : Bool
    constitutivePromotionIsANDCutIsTrue :
      constitutivePromotionIsANDCut ≡ true

    unresolvedLeafMayBeEncodedAsSuccessfulEmptyTarget : Bool
    unresolvedLeafMayBeEncodedAsSuccessfulEmptyTargetIsFalse :
      unresolvedLeafMayBeEncodedAsSuccessfulEmptyTarget ≡ false

    measurementMayResolveEmpiricalObstruction : Bool
    measurementMayResolveEmpiricalObstructionIsTrue :
      measurementMayResolveEmpiricalObstruction ≡ true

    rawExperimentAutomaticallyClosesKernelProofLeaf : Bool
    rawExperimentAutomaticallyClosesKernelProofLeafIsFalse :
      rawExperimentAutomaticallyClosesKernelProofLeaf ≡ false

    routeErrorsRemainFirstClass : Bool
    routeErrorsRemainFirstClassIsTrue :
      routeErrorsRemainFirstClass ≡ true

    designBundleRemainsCanonicalDiscriminator : Bool
    designBundleRemainsCanonicalDiscriminatorIsTrue :
      designBundleRemainsCanonicalDiscriminator ≡ true

canonicalExperimentSearchHypergraphBoundary : ExperimentSearchHypergraphBoundary
canonicalExperimentSearchHypergraphBoundary =
  experiment-search-hypergraph-boundary
    true refl
    false refl
    true refl
    false refl
    true refl
    true refl
