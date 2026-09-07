module DASHI.Economics.AICriticalInfrastructurePoliticsCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Economics.PolicyBackstopCommercialDisciplineExact as Policy
import DASHI.Law.HerzogPoliceCountryColonialityCrossPollinationExact as Herzog

------------------------------------------------------------------------
-- CRITICAL-INFRASTRUCTURE POLITICS CROSS-POLLINATION
--
-- Pattern taken from the Mabo/Herzog audit architecture: a broad public-order
-- or security label may be locally useful while erasing decisive coordinates.
-- Likewise, "critical infrastructure" may support a strategic-policy case but
-- does not exhaust commercial, beneficiary, dependency, sovereignty or
-- distributional analysis.
------------------------------------------------------------------------

data CriticalInfrastructureCoordinate : Set where
  commercialReturn
  strategicValue
  securityValue
  industrialPolicyValue
  directBeneficiary
  ultimateCapitalProvider
  foreignTechnologyDependency
  domesticManufacturingDependency
  energyAndWaterDependency
  geographicConcentration
  supplyChainSovereignty
  distributionalIncidence
  exitOrRetrenchmentPath
  : CriticalInfrastructureCoordinate

record CriticalInfrastructureCoordinateReceipt : Set where
  constructor criticalInfrastructureCoordinateReceipt
  field
    coordinate : CriticalInfrastructureCoordinate
    sourceReference : String
    empiricallyClosed : Bool

open CriticalInfrastructureCoordinateReceipt public

openCriticalInfrastructureCoordinate :
  CriticalInfrastructureCoordinate → CriticalInfrastructureCoordinateReceipt
openCriticalInfrastructureCoordinate c =
  criticalInfrastructureCoordinateReceipt c
    "requires jurisdiction/project-specific source and authority receipt"
    false

record CriticalInfrastructureAudit : Set where
  constructor criticalInfrastructureAudit
  field
    coordinateReference : CriticalInfrastructureCoordinate → String
    policyProject : Policy.PolicySupportedProject
    criticalInfrastructureLabelLocallyUseful : Bool
    commercialReturnExhaustedByStrategicLabel : Bool
    commercialReturnExhaustedByStrategicLabelIsFalse :
      commercialReturnExhaustedByStrategicLabel ≡ false
    securityValueProvesCommercialViability : Bool
    securityValueProvesCommercialViabilityIsFalse :
      securityValueProvesCommercialViability ≡ false
    policyBackingProvesIndependentPrivateDemand : Bool
    policyBackingProvesIndependentPrivateDemandIsFalse :
      policyBackingProvesIndependentPrivateDemand ≡ false

open CriticalInfrastructureAudit public

-- Reverse producer calculus: stronger political-economic claims require the
-- coordinate that would otherwise have been erased by the umbrella label.
data CriticalInfrastructureClaim : Set where
  projectCommerciallySelfSustaining
  projectStrategicallyNecessary
  domesticSovereigntyImproved
  foreignDependencyReduced
  publicSupportBenefitsDomesticPublic
  policyBackingRevealsIndependentDemand
  : CriticalInfrastructureClaim

data CriticalInfrastructureProducer : Set where
  commercialReturnProducer
  strategicNecessityProducer
  sovereigntyDependencyProducer
  foreignDependencyProducer
  beneficiaryDistributionProducer
  terminalPayerProducer
  : CriticalInfrastructureProducer

reverseCriticalInfrastructure :
  CriticalInfrastructureClaim → CriticalInfrastructureProducer
reverseCriticalInfrastructure projectCommerciallySelfSustaining = commercialReturnProducer
reverseCriticalInfrastructure projectStrategicallyNecessary = strategicNecessityProducer
reverseCriticalInfrastructure domesticSovereigntyImproved = sovereigntyDependencyProducer
reverseCriticalInfrastructure foreignDependencyReduced = foreignDependencyProducer
reverseCriticalInfrastructure publicSupportBenefitsDomesticPublic = beneficiaryDistributionProducer
reverseCriticalInfrastructure policyBackingRevealsIndependentDemand = terminalPayerProducer

-- Herzog/Mabo direction is reused as an audit discipline, not as a claim that
-- semiconductor industrial policy and policing/native-title history are one
-- mechanism.
data PoliticsCrossPollinationImpliesHistoricalIdentityPermission : Set where

politicsCrossPollinationDoesNotAutoPromoteToHistoricalIdentity :
  PoliticsCrossPollinationImpliesHistoricalIdentityPermission → ⊥
politicsCrossPollinationDoesNotAutoPromoteToHistoricalIdentity ()

herzogDirectionReference : Herzog.CountryRecognitionBoundary
herzogDirectionReference = Herzog.canonicalCountryRecognitionBoundary

policySupportDoesNotCloseCommercialViability :
  Policy.PolicySupportImpliesCommercialViabilityPermission → ⊥
policySupportDoesNotCloseCommercialViability =
  Policy.policySupportDoesNotAutoPromoteToCommercialViability
