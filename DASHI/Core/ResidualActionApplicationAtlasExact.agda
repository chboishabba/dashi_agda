module DASHI.Core.ResidualActionApplicationAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.MechanismDiscriminationApplicationAtlasExact as Atlas
import DASHI.Core.ResidualActionPolicyExact as Action

record CircumstanceActionTemplate : Set where
  constructor circumstanceActionTemplate
  field
    circumstance : Atlas.CircumstanceClass
    preferredAction : Action.ResidualActionKind
    triggerShape : String
    targetCarrier : String
    requiredAdmission : String
    authorityBoundary : String

open CircumstanceActionTemplate public

biochemicalTemplate : CircumstanceActionTemplate
biochemicalTemplate = circumstanceActionTemplate
  Atlas.biochemicalMechanism Action.measure
  "matched residual localises uncertainty to chemical species, molecular target, recovery, regulation or phenotype mediation"
  "dependency-reachable biochemical carrier"
  "same-preparation / same-organism measurement or perturbation receipt"
  "laboratory feasibility, biosafety and causal authority remain domain-specific"

engineeringTemplate : CircumstanceActionTemplate
engineeringTemplate = circumstanceActionTemplate
  Atlas.engineeringFaultDiagnosis Action.measure
  "same alarm remains compatible with multiple fault worlds"
  "vibration/current/thermal/calibration/control carrier"
  "instrument-calibration and safe-access receipt"
  "diagnostic evidence does not automatically authorise repair or shutdown"

softwareTemplate : CircumstanceActionTemplate
softwareTemplate = circumstanceActionTemplate
  Atlas.softwareFailureDiagnosis Action.measure
  "same exception/log signature remains compatible with dependency, configuration, data, concurrency or environment causes"
  "instrumentation/reproduction carrier"
  "reproducibility and scope receipt"
  "debugging evidence does not automatically authorise production mutation"

ecologicalTemplate : CircumstanceActionTemplate
ecologicalTemplate = circumstanceActionTemplate
  Atlas.ecologicalCausalAttribution Action.hold
  "population trend is underdetermined by habitat, predation, disease, climate, nutrient or sampling models"
  "driver-specific evidence carrier"
  "sampling adequacy / ethical intervention / temporal-context receipt"
  "absence of discrimination is not evidence for a preferred ecological cause"

financialTemplate : CircumstanceActionTemplate
financialTemplate = circumstanceActionTemplate
  Atlas.financialModelDiscrimination Action.measure
  "same P&L is compatible with exposure, liquidity, volatility, concentration, execution or data-model causes"
  "risk/exposure/data-quality carrier"
  "data lineage, valuation and model-governance receipt"
  "diagnostic residual does not itself authorise trading or capital allocation"

legalTemplate : CircumstanceActionTemplate
legalTemplate = circumstanceActionTemplate
  Atlas.legalCausalExplanation Action.hold
  "same legal outcome remains compatible with different doctrinal, evidentiary, procedural or implementation paths"
  "doctrine/evidence/procedure/authority carrier"
  "jurisdiction-specific authority and admissible-evidence receipt"
  "generic causal discrimination does not transfer legal authority"

historicalTemplate : CircumstanceActionTemplate
historicalTemplate = circumstanceActionTemplate
  Atlas.historicalProvenanceExplanation Action.reopen
  "observed discontinuity is compatible with source loss, custody, reorganisation, succession, codification or access change"
  "dependency-reachable provenance/custody carrier"
  "source chain / custody / event-time receipt"
  "reopening a historical explanation is not refutation and does not establish motive"

sensorFusionTemplate : CircumstanceActionTemplate
sensorFusionTemplate = circumstanceActionTemplate
  Atlas.sensorFusionDiagnosis Action.measure
  "fused estimate remains compatible with calibration, dropout, bias, latency or environment-induced error"
  "sensor/calibration/timing carrier"
  "cross-sensor calibration and timestamp-alignment receipt"
  "one agreeing sensor does not establish fused-state correctness"

record ResidualActionApplicationBoundary : Set where
  constructor residualActionApplicationBoundary
  field
    genericActionShapeTransfersDomainAuthority : Bool
    genericActionShapeTransfersDomainAuthorityIsFalse :
      genericActionShapeTransfersDomainAuthority ≡ false
    sameResidualClassRequiresSameActionInEveryDomain : Bool
    sameResidualClassRequiresSameActionInEveryDomainIsFalse :
      sameResidualClassRequiresSameActionInEveryDomain ≡ false
    holdMayBeCorrectWhenAuthorityOrDiscriminationIsIncomplete : Bool
    holdMayBeCorrectWhenAuthorityOrDiscriminationIsIncompleteIsTrue :
      holdMayBeCorrectWhenAuthorityOrDiscriminationIsIncomplete ≡ true
    reopenNeedNotMeanRefute : Bool
    reopenNeedNotMeanRefuteIsTrue : reopenNeedNotMeanRefute ≡ true

canonicalResidualActionApplicationBoundary : ResidualActionApplicationBoundary
canonicalResidualActionApplicationBoundary =
  residualActionApplicationBoundary false refl false refl true refl true refl
