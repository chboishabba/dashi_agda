module DASHI.Law.GenocideFascismAnalyticalDefinitionBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.FascismAtrocitySourceCrossPollinationExact as Fascism
import DASHI.Law.GazaGenocideHerzogZionismSourceReceiptsExact as Source

------------------------------------------------------------------------
-- DASHI analytical definition bridge.
--
-- User-specified analytical stance: genocide is treated as a paradigmatic
-- fascistic elimination/terminalisation mechanism.  This theorem is DASHI-owned
-- unless an external source independently applies the political label.
------------------------------------------------------------------------

data DASHIFascismCriterion : Set where
  genocidalElimination
  terminalisingEnemyConstruction
  collectiveGuiltTransfer
  coerciveDistinctionErasure
  asymmetricExclusionaryRouting : DASHIFascismCriterion

data DASHIFascismClassification : Set where
  fascisticMechanism : DASHIFascismClassification

criterionClassifiesAsFascistic : DASHIFascismCriterion → DASHIFascismClassification
criterionClassifiesAsFascistic genocidalElimination = fascisticMechanism
criterionClassifiesAsFascistic terminalisingEnemyConstruction = fascisticMechanism
criterionClassifiesAsFascistic collectiveGuiltTransfer = fascisticMechanism
criterionClassifiesAsFascistic coerciveDistinctionErasure = fascisticMechanism
criterionClassifiesAsFascistic asymmetricExclusionaryRouting = fascisticMechanism

genocideIsFascisticMechanism :
  criterionClassifiesAsFascistic genocidalElimination ≡ fascisticMechanism
genocideIsFascisticMechanism = refl

------------------------------------------------------------------------
-- Mapping into the existing fascism feature vocabulary.
------------------------------------------------------------------------

genocidePrimaryFeature : Fascism.FascismFeature
genocidePrimaryFeature = Fascism.terminalisation

genocideSecondaryFeature : Fascism.FascismFeature
genocideSecondaryFeature = Fascism.collectiveGuiltTransport

------------------------------------------------------------------------
-- Source attribution firewall.
------------------------------------------------------------------------

data AttributionRole : Set where
  externalGenocideFinding
  externalFascismClassification
  dashiAnalyticalClassification : AttributionRole

record GenocideFascismReceipt : Set where
  constructor genocideFascismReceipt
  field
    genocideSourceReference : String
    genocideSourceRole : AttributionRole
    fascismClassificationRole : AttributionRole
    externalSourceItselfUsedFascismLabel : Bool
    boundedDescription : String

open GenocideFascismReceipt public

gazaCommissionToDASHIFascismReceipt : GenocideFascismReceipt
gazaCommissionToDASHIFascismReceipt = genocideFascismReceipt
  "UN Independent International Commission of Inquiry genocide finding, September 2025 and June 2026 continuation"
  externalGenocideFinding
  dashiAnalyticalClassification
  false
  "The Commission genocide finding is external; the statement that genocide is fascism/fascistic terminalisation is the DASHI analytical bridge unless separately sourced."

record GenocideFascismAttributionBoundary : Set where
  constructor genocideFascismAttributionBoundary
  field
    unGenocideFindingAutomaticallyAttributedAsUNFascismFinding : Bool
    unGenocideFindingAutomaticallyAttributedAsUNFascismFindingIsFalse : unGenocideFindingAutomaticallyAttributedAsUNFascismFinding ≡ false
    dashiDefinitionMayStateGenocideIsFascistic : Bool
    dashiDefinitionMayStateGenocideIsFascisticIsTrue : dashiDefinitionMayStateGenocideIsFascistic ≡ true
    fascisticMechanismClassificationAutomaticallyProvesEveryInstitutionFascist : Bool
    fascisticMechanismClassificationAutomaticallyProvesEveryInstitutionFascistIsFalse : fascisticMechanismClassificationAutomaticallyProvesEveryInstitutionFascist ≡ false

canonicalGenocideFascismAttributionBoundary : GenocideFascismAttributionBoundary
canonicalGenocideFascismAttributionBoundary =
  genocideFascismAttributionBoundary false refl true refl false refl
