module DASHI.Cognition.OracleEllisonCapabilityPromotionExact where

------------------------------------------------------------------------
-- CLAIM PROMOTION LATTICE
--
-- L0 relationship observed
-- L1 capability supplied
-- L2 operational integration
-- L3 system architecture/control
-- L4 intent/motive
--
-- Payment is monotone only when an explicit stronger source receipt exists.
-- No lower level silently promotes to a higher one.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.OracleEllisonTranscriptClaimAtlasExact as Claims

data PromotionLevel : Set where
  relationshipObserved : PromotionLevel
  capabilitySupplied : PromotionLevel
  operationalIntegration : PromotionLevel
  systemArchitectureControl : PromotionLevel
  intentMotive : PromotionLevel

------------------------------------------------------------------------
-- Case-specific highest paid levels from the acquired evidence.
------------------------------------------------------------------------

ellisonFIDFHighestPaidLevel : PromotionLevel
ellisonFIDFHighestPaidLevel = relationshipObserved

oracleChinaHighestPaidLevel : PromotionLevel
oracleChinaHighestPaidLevel = operationalIntegration

oracleRafaelHighestPaidLevel : PromotionLevel
oracleRafaelHighestPaidLevel = operationalIntegration

oracleNimbusHighestPaidLevel : PromotionLevel
oracleNimbusHighestPaidLevel = relationshipObserved

------------------------------------------------------------------------
-- Explicit failed promotions.
------------------------------------------------------------------------

ellisonDonationPaysIsraeliPolicyAuthorship : Bool
ellisonDonationPaysIsraeliPolicyAuthorship = false

ellisonDonationPaysMotive : Bool
ellisonDonationPaysMotive = false

oracleChinaDeploymentPaysPRCPoliticalObjectiveAuthorship : Bool
oracleChinaDeploymentPaysPRCPoliticalObjectiveAuthorship = false

oracleChinaDeploymentPaysCommonController : Bool
oracleChinaDeploymentPaysCommonController = false

oracleRafaelPaysIsraeliSecuritySystemControl : Bool
oracleRafaelPaysIsraeliSecuritySystemControl = false

oracleRafaelPaysEllisonMotive : Bool
oracleRafaelPaysEllisonMotive = false

oracleNimbusPrimeProviderPaid : Bool
oracleNimbusPrimeProviderPaid = false

oracleNimbusArchitecturalAuthorshipPaid : Bool
oracleNimbusArchitecturalAuthorshipPaid = false

netanyahuServicePaysControlWorldview : Bool
netanyahuServicePaysControlWorldview = false

netanyahuServicePaysPermanentThreatMotive : Bool
netanyahuServicePaysPermanentThreatMotive = false

------------------------------------------------------------------------
-- Generic non-collapse receipt.
------------------------------------------------------------------------

record PromotionFirewall : Set where
  constructor promotion-firewall
  field
    relationshipToCapabilityAutomatic : Bool
    capabilityToOperationalAutomatic : Bool
    operationalToArchitectureAutomatic : Bool
    architectureToMotiveAutomatic : Bool
    sameVendorToCommonControllerAutomatic : Bool

canonicalPromotionFirewall : PromotionFirewall
canonicalPromotionFirewall =
  promotion-firewall false false false false false

------------------------------------------------------------------------
-- Positive pins: the case does pay more than a merely commercial-contact
-- story in China and the RAFAEL integration, while stopping before sovereign
-- architecture/control and motive.
------------------------------------------------------------------------

chinaAboveRelationship :
  oracleChinaHighestPaidLevel ≡ operationalIntegration
chinaAboveRelationship = refl

rafaelAboveRelationship :
  oracleRafaelHighestPaidLevel ≡ operationalIntegration
rafaelAboveRelationship = refl
