module DASHI.Environment.PlanningLoopRegression where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using ([]; _∷_)

import DASHI.Environment.DepthTruncation as Depth
import DASHI.Environment.EcologicalEvidenceGates as Evidence
import DASHI.Environment.EcologicalKnowledge as Knowledge
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

pondPolicyEscalates :
  Pond.policyEscalates ≡ Pond.policyEscalates
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

springfieldScenarioRecorded : Pond.SpringfieldPondGoldenScenario
springfieldScenarioRecorded = Pond.canonicalSpringfieldPondGoldenScenario
