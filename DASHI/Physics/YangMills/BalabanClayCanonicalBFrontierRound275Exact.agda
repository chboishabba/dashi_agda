{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound275Exact where

------------------------------------------------------------------------
-- ROUND275 / CANONICAL B FRONTIER AFTER NS-R592 NORMALIZATION
--
-- Primitive theorem content is defined by the lowest consumer, not by a
-- currently preferred proof architecture.
--
-- Canonical B content:
--   * quantitative clustering upper on the reconstructed continuum spectrum;
--   * positivity of the selected gap candidate.
--
-- Optional producer tactics:
--   * Heat/Doob -> Langevin -> weighted Dyson -> clustering;
--   * unified polymer/Schwinger norm -> correlation-decay trajectory;
--   * source-native multiscale cluster expansion;
--   * uniform finite-cutoff spectral gaps + continuum survival.
--
-- Generic T5 `continuumClustered` is packaging only unless it is bound to the
-- exact quantitative clustering consumer.  PositiveTransferGap is compiler
-- output once the two canonical B payments are present.
--
-- ARCHAEOLOGICAL STEP-V REFINEMENT
-- --------------------------------
-- The older Step-V lane already contains the exact producer topology
--
--   KP -> cluster expansion -> cluster-weight decay -> connected correlations.
--
-- But this must not be misread as a completed physical clustering proof.
-- `BalabanLargeFieldStepV` derives KP, convergence, weight decay and then the
-- connected-correlation object only because its `LargeFieldStepVEstimates`
-- input already stores the source-facing theorem fields
-- `clusterWeightDecayTheorem` and `connectedCorrelationTheorem`.
--
-- Consequently the first Step-V theorem-bearing physical leaf is not "do KP"
-- again.  It is the SAME-CARRIER source/physical inhabitant of
--
--   ClusterWeightsExponentiallyDecay -> ConnectedCorrelationsClusterBound,
--
-- followed separately by the terminal lattice-to-physical decay comparison
-- and the same-family continuum/OS identification.  This makes the buried
-- July/August donor explicit while keeping Step V an optional producer tactic
-- rather than promoting it to canonical B content.
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


data BSearchObject275 : Set where
  quantitativeContinuumClusteringUpper : BSearchObject275
  positiveGapCandidate : BSearchObject275
  heatDoobLangevinDysonRoute : BSearchObject275
  unifiedPolymerNormRoute : BSearchObject275
  sourceNativeStepVRoute : BSearchObject275
  stepVWeightDecayToConnectedCorrelationLeaf : BSearchObject275
  terminalPhysicalScaleComparisonLeaf : BSearchObject275
  finiteCutoffGapSurvivalRoute : BSearchObject275
  genericT5ClusteredField : BSearchObject275
  positiveTransferGapObject : BSearchObject275

searchRole275 : BSearchObject275 → Introspective.ProofSearchTargetRole
searchRole275 quantitativeContinuumClusteringUpper =
  Introspective.canonicalConsumerResidual
searchRole275 positiveGapCandidate =
  Introspective.canonicalConsumerResidual
searchRole275 heatDoobLangevinDysonRoute =
  Introspective.optionalProducerTactic
searchRole275 unifiedPolymerNormRoute =
  Introspective.optionalProducerTactic
searchRole275 sourceNativeStepVRoute =
  Introspective.optionalProducerTactic
searchRole275 stepVWeightDecayToConnectedCorrelationLeaf =
  Introspective.optionalProducerTactic
searchRole275 terminalPhysicalScaleComparisonLeaf =
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
    clusteringUpper : Gap.ClusteringUpperBound spectrum
    candidatePositive : Gap.PositiveEnergy spectrum (Gap.gapCandidate spectrum)

open CanonicalBPayment275 public

compileCanonicalBPayment :
  ∀ {Observable Energy Bound}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound} →
  CanonicalBPayment275 spectrum → Gap.PositiveTransferGap spectrum
compileCanonicalBPayment {spectrum = spectrum} payment =
  Gap.positiveTransferGapFromClusteringCutset spectrum
    (clusteringUpper payment)
    (candidatePositive payment)

-- Exact Step-V compiler already present in the historical lane.  This theorem
-- is intentionally exposed here to show what is compiler output and what is
-- still source/physical theorem content: the final application consumes the
-- `connectedCorrelationTheorem` field already stored in `estimates`.
stepVConnectedCorrelationsFromStoredProducer :
  ∀ {Site Polymer Configuration Bound : Set}
    (estimates : StepV.LargeFieldStepVEstimates Site Polymer Configuration Bound) →
  StepV.LargeFieldStepVEstimates.ConnectedCorrelationsClusterBound estimates
stepVConnectedCorrelationsFromStoredProducer =
  StepV.connectedCorrelationsClusterBound

record Round275Boundary : Set where
  constructor round275-boundary
  field
    rowCRouteMandatory : Bool
    rowCRouteMandatoryIsFalse : rowCRouteMandatory ≡ false

    unifiedNormRouteMandatory : Bool
    unifiedNormRouteMandatoryIsFalse : unifiedNormRouteMandatory ≡ false

    sourceNativeStepVRouteMandatory : Bool
    sourceNativeStepVRouteMandatoryIsFalse :
      sourceNativeStepVRouteMandatory ≡ false

    stepVKPAssemblyNeedsReproof : Bool
    stepVKPAssemblyNeedsReproofIsFalse : stepVKPAssemblyNeedsReproof ≡ false

    stepVWeightDecayToConnectedCorrelationPhysicalProducerOpen : Bool
    stepVWeightDecayToConnectedCorrelationPhysicalProducerOpenIsTrue :
      stepVWeightDecayToConnectedCorrelationPhysicalProducerOpen ≡ true

    terminalPhysicalScaleComparisonOpen : Bool
    terminalPhysicalScaleComparisonOpenIsTrue :
      terminalPhysicalScaleComparisonOpen ≡ true

    finiteCutoffGapRouteMandatory : Bool
    finiteCutoffGapRouteMandatoryIsFalse : finiteCutoffGapRouteMandatory ≡ false

    opaqueT5ClusteredPaysQuantitativeB : Bool
    opaqueT5ClusteredPaysQuantitativeBIsFalse :
      opaqueT5ClusteredPaysQuantitativeB ≡ false

    quantitativeClusteringUpperOpen : Bool
    quantitativeClusteringUpperOpenIsTrue :
      quantitativeClusteringUpperOpen ≡ true

    positiveGapCandidateOpen : Bool
    positiveGapCandidateOpenIsTrue : positiveGapCandidateOpen ≡ true

canonicalRound275Boundary : Round275Boundary
canonicalRound275Boundary =
  round275-boundary
    false refl
    false refl
    false refl
    false refl
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
