{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCanonicalMassGapConsumerRound270Exact where

------------------------------------------------------------------------
-- ROUND270 / NS-R592 INTROSPECTION APPLIED TO YANG--MILLS
--
-- The proof-search error exposed by NS R592 was promoting a successful proof
-- tactic/decomposition into a mandatory residual.  Yang--Mills had the same
-- risk in Row C: Heat/Doob -> Langevin Hessian -> weighted Dyson -> balanced
-- finite speed is a useful constructive route, but the Clay-facing mass-gap
-- endpoint does not mention that route.
--
-- The literal top-down B endpoint is exactly
--
--     CutoffUniformPhysicalMassGap Y.
--
-- The existing OS spectral compiler sharpens the hard physical input further:
-- uniform exponential clustering of the SAME continuum Schwinger family is
-- sufficient for the positive transfer/Hamiltonian gap once the standard OS
-- spectral interpretation is supplied.
--
-- Therefore:
--   * direct same-family physical exponential clustering is canonical target B;
--   * Heat/Doob/Langevin/Dyson is an optional producer tactic for clustering;
--   * source-native multiscale cluster expansion is another optional tactic;
--   * typecheck/submission/review status remains orthogonal to theorem content.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Interop.IntrospectiveProofLoopExact as Introspective
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound78TopDownThreeAnalyticFrontierExact as R78
import DASHI.Physics.YangMills.BalabanOSExponentialClusteringImpliesHamiltonianGapExact as OSGap
import DASHI.Physics.YangMills.BalabanStochasticFiniteSpeedSpatialClusteringExact as Stochastic
import DASHI.Physics.YangMills.BalabanClayT5ConditionalClusteringCutsetExact as Cluster

------------------------------------------------------------------------
-- Canonical endpoint adapter: no producer tactic appears in this type.
------------------------------------------------------------------------

canonicalMassGapEndpoint :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  Five.CutoffUniformPhysicalMassGap Y →
  R78.SameHamiltonianPhysicalMassGap Y
canonicalMassGapEndpoint gap = record
  { R78.SameHamiltonianPhysicalMassGap.physicalGap = gap }

------------------------------------------------------------------------
-- Search-role classification.
------------------------------------------------------------------------

data MassGapProducerTactic270 : Set where
  heatDoobLangevinDysonBalancedTime : MassGapProducerTactic270
  sourceNativeMultiscaleClusterExpansion : MassGapProducerTactic270
  directSameFamilyClusteringTheorem : MassGapProducerTactic270
  directSameHamiltonianSpectralTheorem : MassGapProducerTactic270

producerRole270 : MassGapProducerTactic270 → Introspective.ProofSearchTargetRole
producerRole270 heatDoobLangevinDysonBalancedTime = Introspective.optionalProducerTactic
producerRole270 sourceNativeMultiscaleClusterExpansion = Introspective.optionalProducerTactic
producerRole270 directSameFamilyClusteringTheorem = Introspective.canonicalConsumerResidual
producerRole270 directSameHamiltonianSpectralTheorem = Introspective.canonicalConsumerResidual

round270HeatDoobLangevinDysonMandatory : Bool
round270HeatDoobLangevinDysonMandatory = false

round270SourceNativeClusterExpansionMandatory : Bool
round270SourceNativeClusterExpansionMandatory = false

round270CanonicalPhysicalClusteringOpen : Bool
round270CanonicalPhysicalClusteringOpen = true

round270CanonicalMassGapEndpointOpen : Bool
round270CanonicalMassGapEndpointOpen = true

------------------------------------------------------------------------
-- Closure/status ledger.  This deliberately does not infer theorem completion
-- from typechecking, submission, review or acceptance metadata.
------------------------------------------------------------------------

round270MassGapClosureLedger : Introspective.ClosureLedger
round270MassGapClosureLedger =
  Introspective.closure-ledger false false false false false

------------------------------------------------------------------------
-- Existing consequences / tactics.
------------------------------------------------------------------------

osClusteringToHamiltonianGapCompilerLevel : ProofLevel
osClusteringToHamiltonianGapCompilerLevel =
  OSGap.osExponentialClusteringImpliesHamiltonianGapAdapterLevel

canonicalPhysicalUniformExponentialClusteringLevel : ProofLevel
canonicalPhysicalUniformExponentialClusteringLevel =
  OSGap.physicalUniformExponentialClusteringLevel

heatDoobBalancedFiniteSpeedTacticLevel : ProofLevel
heatDoobBalancedFiniteSpeedTacticLevel =
  Stochastic.physicalYMStochasticFiniteSpeedClusteringLevel

sourceNativeConditionalClusterExpansionTacticLevel : ProofLevel
sourceNativeConditionalClusterExpansionTacticLevel =
  Cluster.perScaleClusterWithHolesInputsLevel

round270CanonicalMassGapEndpointAdapterLevel : ProofLevel
round270CanonicalMassGapEndpointAdapterLevel = machineChecked

round270HeatDoobLangevinDysonMandatoryIsFalse :
  round270HeatDoobLangevinDysonMandatory ≡ false
round270HeatDoobLangevinDysonMandatoryIsFalse = refl

round270SourceNativeClusterExpansionMandatoryIsFalse :
  round270SourceNativeClusterExpansionMandatory ≡ false
round270SourceNativeClusterExpansionMandatoryIsFalse = refl
