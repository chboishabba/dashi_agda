module DASHI.Environment.PlanningLoopRegression where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using ([]; _∷_)

import DASHI.Core.ConsumerIndexedGovernedTransitionExact as Governed
import DASHI.Core.ReopenableConsumerInterventionCrossDomainRegression as CrossDomain
import DASHI.Environment.DepthTruncation as Depth
import DASHI.Environment.EcologicalEvidenceGates as Evidence
import DASHI.Environment.EcologicalKnowledge as Knowledge
import DASHI.Environment.LESResearchCrossPollinationExact as Research
import DASHI.Environment.LESResearchCrossPollinationRound2Exact as Research2
import DASHI.Environment.LESResearchCrossPollinationRound3Exact as Research3
import DASHI.Environment.LESResearchCrossPollinationRound4Exact as Research4
import DASHI.Environment.LESRuntimeBoundary as Runtime
import DASHI.Environment.ParetoPlanning as Pareto
import DASHI.Environment.QuantitiesConservation as Q
import DASHI.Environment.SpatialTransport as Spatial
import DASHI.Environment.SpringfieldPondGoldenScenario as Pond
import DASHI.Environment.SurrogateCalibration as Surrogate
import DASHI.Environment.ValidationGovernance as Governance
import DASHI.Foundations.SSPTritCarrier as SSP

one : Nat
one = suc zero

two : Nat
two = suc one

stream : Depth.EffectStream
stream = SSP.sspNegOne ∷ SSP.sspZero ∷ SSP.sspPosOne ∷ []

truncateOne : Depth.truncate one stream ≡ SSP.sspNegOne ∷ []
truncateOne = refl

truncateTwo :
  Depth.truncate two stream ≡ SSP.sspNegOne ∷ SSP.sspZero ∷ []
truncateTwo = refl

truncateOneIsPrefix :
  Depth.Prefix (Depth.truncate one stream) (Depth.truncate two stream)
truncateOneIsPrefix = Depth.shallowerPrefixOfDeeper one one stream

pondPathRecorded : Spatial.Path Pond.upperCatchment Pond.pond
pondPathRecorded = Pond.phosphorusPath

pondPolicyEscalates : Pond.policyEscalates ≡ Pond.policyEscalates
pondPolicyEscalates = refl

zeroNitrogenReceipt : Q.NitrogenBalance
zeroNitrogenReceipt = Q.exactZeroBalance "regression nitrogen balance"

runtimeBoundaryRecorded : Runtime.RuntimeBoundary
runtimeBoundaryRecorded = Runtime.canonicalRuntimeBoundary

evidenceBoundaryRecorded : Evidence.EvidenceGateBoundary
evidenceBoundaryRecorded = Evidence.canonicalEvidenceGateBoundary

knowledgeBoundaryRecorded : Knowledge.KnowledgeBoundary
knowledgeBoundaryRecorded = Knowledge.canonicalKnowledgeBoundary

paretoBoundaryRecorded : Pareto.SelectionSeparationBoundary
paretoBoundaryRecorded = Pareto.canonicalSelectionSeparationBoundary

surrogateBoundaryRecorded : Surrogate.SurrogateBoundary
surrogateBoundaryRecorded = Surrogate.canonicalSurrogateBoundary

governanceBoundaryRecorded : Governance.ValidationGovernanceBoundary
governanceBoundaryRecorded = Governance.canonicalValidationGovernanceBoundary

researchGapBoundaryRecorded : Research.LESResearchGapBoundary
researchGapBoundaryRecorded = Research.canonicalLESResearchGapBoundary

researchCrossPollinationBoundaryRecorded :
  Research.LESResearchCrossPollinationBoundary
researchCrossPollinationBoundaryRecorded =
  Research.canonicalLESResearchCrossPollinationBoundary

researchRound2StatusRecorded : Research2.LESRound2ResearchStatus
researchRound2StatusRecorded = Research2.canonicalLESRound2ResearchStatus

causalAbstractionBoundaryRecorded : Research2.CausalAbstractionBoundary
causalAbstractionBoundaryRecorded = Research2.canonicalCausalAbstractionBoundary

deepUncertaintyBoundaryRecorded : Research2.DeepUncertaintyBoundary
deepUncertaintyBoundaryRecorded = Research2.canonicalDeepUncertaintyBoundary

spatialAggregationBoundaryRecorded : Research2.SpatialAggregationBoundary
spatialAggregationBoundaryRecorded = Research2.canonicalSpatialAggregationBoundary

assimilationBoundaryRecorded : Research2.AssimilationBoundary
assimilationBoundaryRecorded = Research2.canonicalAssimilationBoundary

hybridDynamicsBoundaryRecorded : Research2.HybridDynamicsBoundary
hybridDynamicsBoundaryRecorded = Research2.canonicalHybridDynamicsBoundary

researchRound3StatusRecorded : Research3.LESRound3CrossProjectReuseStatus
researchRound3StatusRecorded = Research3.canonicalLESRound3CrossProjectReuseStatus

crossProjectFeedbackBoundaryRecorded : Research3.CrossProjectFeedbackBoundary
crossProjectFeedbackBoundaryRecorded = Research3.canonicalCrossProjectFeedbackBoundary

uncertaintyConstitutionRecorded : Research3.LESUncertaintyConstitution
uncertaintyConstitutionRecorded = Research3.canonicalLESUncertaintyConstitution

researchRound3BoundaryRecorded : Research3.LESRound3Boundary
researchRound3BoundaryRecorded = Research3.canonicalLESRound3Boundary

round4ConsumerRelativityStillTheoremBearing :
  (depth : Nat) →
  Governed.FutureEquivalent
    CrossDomain.publicSystem CrossDomain.public depth CrossDomain.left CrossDomain.right
round4ConsumerRelativityStillTheoremBearing =
  Research4.consumerRelativityRegression

springfieldScenarioRecorded : Pond.SpringfieldPondGoldenScenario
springfieldScenarioRecorded = Pond.canonicalSpringfieldPondGoldenScenario
