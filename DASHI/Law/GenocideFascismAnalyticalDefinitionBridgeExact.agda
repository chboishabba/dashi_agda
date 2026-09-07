module DASHI.Law.GenocideFascismAnalyticalDefinitionBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.FascismAtrocitySourceCrossPollinationExact as Fascism
import DASHI.Law.GazaGenocideHerzogZionismSourceReceiptsExact as Source
import DASHI.Law.GenocideFascismSourceGenealogyExact as Genealogy

------------------------------------------------------------------------
-- Genocide / fascism analytical bridge.
--
-- The exact formal classifier is DASHI-owned, but it is not merely a
-- conversation-supplied preference.  Its source genealogy is separately owned
-- in GenocideFascismSourceGenealogyExact: Trainin/Penn's historical
-- "genocide is fascism in action" formulation, USHMM evidence on exclusionary
-- fascism/purifying violence and Nazi elimination, plus a comparative-scholarship
-- boundary noting that the exact relation is debated rather than a universal
-- definitional identity.
------------------------------------------------------------------------

data DASHIFascismCriterion : Set where
  genocidalElimination : DASHIFascismCriterion
  terminalisingEnemyConstruction : DASHIFascismCriterion
  collectiveGuiltTransfer : DASHIFascismCriterion
  coerciveDistinctionErasure : DASHIFascismCriterion
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

sourceGenealogyClassification :
  Genealogy.genocideMechanismClassification
  ≡ Genealogy.fascisticTerminalisationMechanism
sourceGenealogyClassification = Genealogy.genocideToFascisticTerminalisation

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
  externalGenocideFinding : AttributionRole
  externalFascismGenealogy : AttributionRole
  dashiAnalyticalSynthesis : AttributionRole

record GenocideFascismReceipt : Set where
  constructor genocideFascismReceipt
  field
    genocideSourceReference : String
    genocideSourceRole : AttributionRole
    fascismGenealogyReference : String
    fascismGenealogyRole : AttributionRole
    exactFormalSynthesisRole : AttributionRole
    externalGenocideSourceItselfUsedFascismLabel : Bool
    boundedDescription : String

open GenocideFascismReceipt public

gazaCommissionToSourcedFascismReceipt : GenocideFascismReceipt
gazaCommissionToSourcedFascismReceipt = genocideFascismReceipt
  "UN Independent International Commission of Inquiry genocide finding, September 2025 and June 2026 continuation"
  externalGenocideFinding
  "Michelle Penn 2020 on Aron Trainin; USHMM fascism and Nazi-elimination sources; comparative fascism/extermination scholarship"
  externalFascismGenealogy
  dashiAnalyticalSynthesis
  false
  "The UN Commission supplies the genocide finding. External scholarship supplies the genocide/fascism genealogy. DASHI owns the exact typed synthesis: established genocidal elimination instantiates fascistic terminalisation."

record GenocideFascismAttributionBoundary : Set where
  constructor genocideFascismAttributionBoundary
  field
    unGenocideFindingAutomaticallyAttributedAsUNFascismFinding : Bool
    unGenocideFindingAutomaticallyAttributedAsUNFascismFindingIsFalse : unGenocideFindingAutomaticallyAttributedAsUNFascismFinding ≡ false
    sourceGenealogyMaySupportDASHISynthesis : Bool
    sourceGenealogyMaySupportDASHISynthesisIsTrue : sourceGenealogyMaySupportDASHISynthesis ≡ true
    traininPennFormulationIsUniversalConsensus : Bool
    traininPennFormulationIsUniversalConsensusIsFalse : traininPennFormulationIsUniversalConsensus ≡ false
    fascisticMechanismClassificationAutomaticallyProvesEveryInstitutionFascist : Bool
    fascisticMechanismClassificationAutomaticallyProvesEveryInstitutionFascistIsFalse : fascisticMechanismClassificationAutomaticallyProvesEveryInstitutionFascist ≡ false

canonicalGenocideFascismAttributionBoundary : GenocideFascismAttributionBoundary
canonicalGenocideFascismAttributionBoundary =
  genocideFascismAttributionBoundary false refl true refl false refl false refl
