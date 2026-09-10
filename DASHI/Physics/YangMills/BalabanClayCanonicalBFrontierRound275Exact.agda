{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound275Exact where

------------------------------------------------------------------------
-- ROUND275 / CANONICAL B FRONTIER, RE-MINIMIZED THROUGH R277
--
-- Primitive theorem content is defined by the lowest consumer, not by a
-- currently preferred proof architecture.
--
-- The live T5 clustering->gap owner contains a later least-privilege reduction:
-- the contradiction only evaluates clustering on the observable selected by a
-- hypothetical positive subgap mode.  Therefore the canonical B clustering
-- payment is now `SubgapModeClusteringUpper`, not the stronger global
-- `ClusteringUpperBound`.
--
-- Canonical B content:
--   * quantitative clustering upper on subgap-selected reconstructed observables;
--   * positivity of the selected gap threshold.
--
-- Stronger optional producers include:
--   * global all-observable continuum clustering;
--   * Heat/Doob -> Langevin -> weighted Dyson -> clustering;
--   * unified polymer/Schwinger norm -> correlation-decay trajectory;
--   * source-native Step-V / multiscale cluster expansion;
--   * uniform finite-cutoff spectral gaps + continuum survival.
--
-- STEP-V ARCHAEOLOGY
-- ------------------
-- The historical Step-V chain
--
--   KP -> cluster expansion -> cluster-weight decay -> connected correlations
--
-- is not itself a completed physical proof: the final analytic arrows are stored
-- as theorem fields in the Step-V estimate packages.  The new two-mark audit
-- sharpens the source-native producer further.  Its physical leaves are:
--
--   (1) a same-carrier two-source connected-cluster expansion / support bridge;
--   (2) an absolute connecting-cluster weight sum bounded by the configured
--       rooted tail;
--   (3) terminal lattice-to-physical scale/rate transport;
--   (4) same-family continuum/OS transport.
--
-- The 8/16 -> 1/2 rooted-shell arithmetic is already compiler-owned.  None of
-- these optional producer details are promoted into the canonical B consumer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Interop.IntrospectiveProofLoopExact as Introspective
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanClayDirectQuantitativeClusteringRound274Exact as R274
import DASHI.Physics.YangMills.BalabanClayCanonicalMassGapConsumerRound270Exact as R270
import DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormExact as Unified
import DASHI.Physics.YangMills.BalabanMassGapSurvival as Survival
import DASHI.Physics.YangMills.BalabanLangevinDirectInfluencePaymentRound271Exact as RowC
import DASHI.Physics.YangMills.BalabanLargeFieldStepV as StepV
import DASHI.Physics.YangMills.BalabanTerminalScalePhysicalClustering as Terminal
import DASHI.Physics.YangMills.BalabanClayT5TwoMarkedConnectedClusterTailExact as TwoMark
import DASHI.Physics.YangMills.BalabanMarkedLogPartitionConnectedCorrelationCompilerExact as Marked


data BSearchObject275 : Set where
  subgapModeQuantitativeClusteringUpper : BSearchObject275
  positiveGapCandidate : BSearchObject275
  globalAllObservableClusteringUpper : BSearchObject275
  heatDoobLangevinDysonRoute : BSearchObject275
  unifiedPolymerNormRoute : BSearchObject275
  sourceNativeStepVRoute : BSearchObject275
  stepVTwoMarkedConnectedExpansionLeaf : BSearchObject275
  stepVConnectingWeightTailLeaf : BSearchObject275
  terminalPhysicalScaleComparisonLeaf : BSearchObject275
  continuumSameFamilyTransportLeaf : BSearchObject275
  finiteCutoffGapSurvivalRoute : BSearchObject275
  genericT5ClusteredField : BSearchObject275
  positiveTransferGapObject : BSearchObject275

searchRole275 : BSearchObject275 → Introspective.ProofSearchTargetRole
searchRole275 subgapModeQuantitativeClusteringUpper =
  Introspective.canonicalConsumerResidual
searchRole275 positiveGapCandidate =
  Introspective.canonicalConsumerResidual
searchRole275 globalAllObservableClusteringUpper =
  Introspective.optionalProducerTactic
searchRole275 heatDoobLangevinDysonRoute =
  Introspective.optionalProducerTactic
searchRole275 unifiedPolymerNormRoute =
  Introspective.optionalProducerTactic
searchRole275 sourceNativeStepVRoute =
  Introspective.optionalProducerTactic
searchRole275 stepVTwoMarkedConnectedExpansionLeaf =
  Introspective.optionalProducerTactic
searchRole275 stepVConnectingWeightTailLeaf =
  Introspective.optionalProducerTactic
searchRole275 terminalPhysicalScaleComparisonLeaf =
  Introspective.optionalProducerTactic
searchRole275 continuumSameFamilyTransportLeaf =
  Introspective.optionalProducerTactic
searchRole275 finiteCutoffGapSurvivalRoute =
  Introspective.optionalProducerTactic
searchRole275 genericT5ClusteredField =
  Introspective.compilerConsequence
searchRole275 positiveTransferGapObject =
  Introspective.compilerConsequence

record CanonicalBPayment275
    {Observable Energy Bound : Set}
    (spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound) : Set₁ where
  field
    subgapClusteringUpper : Gap.SubgapModeClusteringUpper spectrum
    candidatePositive : Gap.PositiveEnergy spectrum (Gap.gapCandidate spectrum)

open CanonicalBPayment275 public

compileCanonicalBPaymentCore :
  ∀ {Observable Energy Bound}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound} →
  CanonicalBPayment275 spectrum → Gap.PositiveTransferGapCore spectrum
compileCanonicalBPaymentCore {spectrum = spectrum} payment =
  Gap.positiveTransferGapCoreFromModeTests spectrum
    (subgapClusteringUpper payment)
    (candidatePositive payment)

-- Stronger global clustering is retained as a compatibility producer, not as
-- canonical theorem debt.
globalUpperBuildsCanonicalSubgapPayment :
  ∀ {Observable Energy Bound}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound} →
  Gap.ClusteringUpperBound spectrum →
  Gap.PositiveEnergy spectrum (Gap.gapCandidate spectrum) →
  CanonicalBPayment275 spectrum
globalUpperBuildsCanonicalSubgapPayment {spectrum = spectrum} upper positive = record
  { subgapClusteringUpper = Gap.globalClusteringUpperImpliesSubgapModeUpper spectrum upper
  ; candidatePositive = positive
  }

-- Historical Step-V assembly is compiler output from stored analytic theorem
-- fields.  Keeping this visible prevents the function name from being mistaken
-- for a new proof of connected-correlation decay.
stepVConnectedCorrelationsFromStoredProducer :
  ∀ {Site Polymer Configuration Bound : Set}
    (estimates : StepV.LargeFieldStepVEstimates Site Polymer Configuration Bound) →
  StepV.LargeFieldStepVEstimates.ConnectedCorrelationsClusterBound estimates
stepVConnectedCorrelationsFromStoredProducer =
  StepV.connectedCorrelationsClusterBound

record Round275Boundary : Set where
  constructor round275-boundary
  field
    globalAllObservableClusteringMandatory : Bool
    globalAllObservableClusteringMandatoryIsFalse :
      globalAllObservableClusteringMandatory ≡ false

    subgapModeClusteringIsCanonical : Bool
    subgapModeClusteringIsCanonicalIsTrue :
      subgapModeClusteringIsCanonical ≡ true

    rowCRouteMandatory : Bool
    rowCRouteMandatoryIsFalse : rowCRouteMandatory ≡ false

    unifiedNormRouteMandatory : Bool
    unifiedNormRouteMandatoryIsFalse : unifiedNormRouteMandatory ≡ false

    sourceNativeStepVRouteMandatory : Bool
    sourceNativeStepVRouteMandatoryIsFalse :
      sourceNativeStepVRouteMandatory ≡ false

    stepVKPAssemblyNeedsReproof : Bool
    stepVKPAssemblyNeedsReproofIsFalse : stepVKPAssemblyNeedsReproof ≡ false

    stepVTwoMarkedConnectedExpansionOpen : Bool
    stepVTwoMarkedConnectedExpansionOpenIsTrue :
      stepVTwoMarkedConnectedExpansionOpen ≡ true

    stepVConnectingWeightTailOpen : Bool
    stepVConnectingWeightTailOpenIsTrue :
      stepVConnectingWeightTailOpen ≡ true

    terminalPhysicalScaleComparisonOpen : Bool
    terminalPhysicalScaleComparisonOpenIsTrue :
      terminalPhysicalScaleComparisonOpen ≡ true

    continuumSameFamilyTransportOpen : Bool
    continuumSameFamilyTransportOpenIsTrue :
      continuumSameFamilyTransportOpen ≡ true

    finiteCutoffGapRouteMandatory : Bool
    finiteCutoffGapRouteMandatoryIsFalse : finiteCutoffGapRouteMandatory ≡ false

    opaqueT5ClusteredPaysQuantitativeB : Bool
    opaqueT5ClusteredPaysQuantitativeBIsFalse :
      opaqueT5ClusteredPaysQuantitativeB ≡ false

    subgapQuantitativeClusteringOpen : Bool
    subgapQuantitativeClusteringOpenIsTrue :
      subgapQuantitativeClusteringOpen ≡ true

    positiveGapCandidateOpen : Bool
    positiveGapCandidateOpenIsTrue : positiveGapCandidateOpen ≡ true

canonicalRound275Boundary : Round275Boundary
canonicalRound275Boundary =
  round275-boundary
    false refl
    true refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    true refl
    true refl

round275CanonicalBCompilerLevel : ProofLevel
round275CanonicalBCompilerLevel = machineChecked

round275QuantitativeClusteringLevel : ProofLevel
round275QuantitativeClusteringLevel = R274.round274PhysicalQuantitativeClusteringLevel

round275PositiveGapCandidateLevel : ProofLevel
round275PositiveGapCandidateLevel = conditional

round275StepVHistoricalAssemblyLevel : ProofLevel
round275StepVHistoricalAssemblyLevel = StepV.largeFieldStepVBridgeLevel

round275StepVPhysicalProducerLevel : ProofLevel
round275StepVPhysicalProducerLevel = StepV.largeFieldStepVAnalyticEstimatesLevel

round275TerminalPhysicalScaleProducerLevel : ProofLevel
round275TerminalPhysicalScaleProducerLevel = Terminal.terminalPhysicalScaleComparisonInputLevel
