module DASHI.Governance.MontefioreRothschildAustralianGoldNetworkExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Governance.EvidenceGradedGenealogyCore as Genealogy
import DASHI.Governance.MontefioreRothschildAustralianGoldSourceAtlasExact as Sources

------------------------------------------------------------------------
-- FINITE CASE NETWORK
--
-- Case relations refine, but never strengthen, the canonical genealogy spine.
------------------------------------------------------------------------

data HistoricalNode : Set where
  jacobBarrowMontefiore : HistoricalNode
  josephBarrowMontefiore : HistoricalNode
  mosesMontefiore : HistoricalNode
  judithBarentCohen : HistoricalNode
  hannahCohen : HistoricalNode
  nathanMayerRothschild : HistoricalNode
  nmRothschildAndSons : HistoricalNode
  bankOfAustralasia : HistoricalNode
  southAustralianColonisation : HistoricalNode
  montefioreMercantileHouse : HistoricalNode
  victorianGoldMarket : HistoricalNode
  australianGoldConsignment : HistoricalNode

data CaseRelation : Set where
  kinship : CaseRelation
  marriageBridge : CaseRelation
  businessCorrespondence : CaseRelation
  commercialAgency : CaseRelation
  bankDirectorship : CaseRelation
  institutionalFounding : CaseRelation
  colonialOffice : CaseRelation
  commodityPurchase : CaseRelation
  commodityShipment : CaseRelation
  creditProvision : CaseRelation
  landFinance : CaseRelation

-- The canonical core has no kinship relation. Mapping kinship/marriage to the
-- weakest non-promoting canonical relation prevents family metadata from being
-- mistaken for institutional continuity while the case relation remains exact.
canonicalRelation : CaseRelation → Genealogy.PathwayRelation
canonicalRelation kinship = Genealogy.analogyOnly
canonicalRelation marriageBridge = Genealogy.analogyOnly
canonicalRelation businessCorrespondence = Genealogy.directDocumentedTransfer
canonicalRelation commercialAgency = Genealogy.fundingOrganisationalLink
canonicalRelation bankDirectorship = Genealogy.personnelInstitutionalContinuity
canonicalRelation institutionalFounding = Genealogy.personnelInstitutionalContinuity
canonicalRelation colonialOffice = Genealogy.personnelInstitutionalContinuity
canonicalRelation commodityPurchase = Genealogy.directDocumentedTransfer
canonicalRelation commodityShipment = Genealogy.directDocumentedTransfer
canonicalRelation creditProvision = Genealogy.fundingOrganisationalLink
canonicalRelation landFinance = Genealogy.fundingOrganisationalLink

record HistoricalEdge : Set where
  constructor historical-edge
  field
    source target : HistoricalNode
    relation : CaseRelation
    grade : Genealogy.EvidenceGrade
    sourceIdentity : Sources.SourceIdentity
    boundedFinding : String
    paid : Bool
open HistoricalEdge public

jacobMosesKinship : HistoricalEdge
jacobMosesKinship = historical-edge jacobBarrowMontefiore mosesMontefiore kinship Genealogy.gradeB
  Sources.adbPeopleAustraliaMontefiore
  "Biographical sources place Jacob Barrow Montefiore in the wider family of Sir Moses Montefiore; this kinship is not business agency."
  true

josephMosesKinship : HistoricalEdge
josephMosesKinship = historical-edge josephBarrowMontefiore mosesMontefiore kinship Genealogy.gradeB
  Sources.adbPeopleAustraliaMontefiore
  "Biographical sources place Joseph Barrow Montefiore in the wider family of Sir Moses Montefiore; this kinship is not business agency."
  true

mosesJudithMarriage : HistoricalEdge
mosesJudithMarriage = historical-edge mosesMontefiore judithBarentCohen marriageBridge Genealogy.gradeB
  Sources.adbPeopleAustraliaMontefiore
  "Moses Montefiore married Judith Barent Cohen."
  true

hannahNathanMarriage : HistoricalEdge
hannahNathanMarriage = historical-edge hannahCohen nathanMayerRothschild marriageBridge Genealogy.gradeB
  Sources.adbPeopleAustraliaMontefiore
  "Judith Cohen's sister Hannah married Nathan Mayer Rothschild, providing a specific kinship bridge rather than a generic family-finance edge."
  true

montefioreRothschildCorrespondence : HistoricalEdge
montefioreRothschildCorrespondence = historical-edge montefioreMercantileHouse nmRothschildAndSons businessCorrespondence Genealogy.gradeA
  Sources.npgMontefioreRothschildGoldRush
  "Surviving correspondence documents Montefiore-Rothschild gold-rush business communication."
  true

jacobRothschildAgency : HistoricalEdge
jacobRothschildAgency = historical-edge jacobBarrowMontefiore nmRothschildAndSons commercialAgency Genealogy.gradeB
  Sources.adbPeopleAustraliaMontefiore
  "Biographical evidence describes Jacob's Rothschild-linked mercantile/agency role; exact transaction-level agency mandates remain separately acquirable."
  true

montefioreBankRole : HistoricalEdge
montefioreBankRole = historical-edge josephBarrowMontefiore bankOfAustralasia institutionalFounding Genealogy.gradeB
  Sources.adbPeopleAustraliaMontefiore
  "Joseph and Jacob were involved in the founding/directorial history of the Bank of Australasia."
  true

jacobColonialOffice : HistoricalEdge
jacobColonialOffice = historical-edge jacobBarrowMontefiore southAustralianColonisation colonialOffice Genealogy.gradeB
  Sources.adbPeopleAustraliaMontefiore
  "Jacob served in South Australian colonisation machinery; office does not imply private financial control of the colony."
  true

goldPurchaseEdge : HistoricalEdge
goldPurchaseEdge = historical-edge montefioreMercantileHouse victorianGoldMarket commodityPurchase Genealogy.gradeB
  Sources.npgMontefioreRothschildGoldRush
  "Historical sources place Montefiore mercantile activity in Victorian gold purchasing; this does not establish mine ownership or gold production."
  true

goldShipmentEdge : HistoricalEdge
goldShipmentEdge = historical-edge nmRothschildAndSons australianGoldConsignment commodityShipment Genealogy.gradeB
  Sources.rothschildArchiveAustralianGold
  "Rothschild archival material documents Australian gold purchasing/shipping activity through agents; exact consignment identifiers remain open."
  true

------------------------------------------------------------------------
-- Explicit non-collapse / anti-antisemitic promotion firewall.
------------------------------------------------------------------------

data FamilyConnectionCreatesBusinessAgency : Set where
data KinshipCreatesCoordination : Set where
data JewishIdentityCreatesFinancialNetworkEdge : Set where
data GoldPurchaseCreatesMineOwnership : Set where
data MerchantIntermediationCreatesGoldProduction : Set where
data ColonialOfficeCreatesPrivateFinancialControl : Set where
data OneFamilyRelationCreatesUniversalCommand : Set where

familyConnectionDoesNotCreateBusinessAgency : FamilyConnectionCreatesBusinessAgency → ⊥
familyConnectionDoesNotCreateBusinessAgency ()

kinshipDoesNotCreateCoordination : KinshipCreatesCoordination → ⊥
kinshipDoesNotCreateCoordination ()

jewishIdentityDoesNotCreateFinancialNetworkEdge : JewishIdentityCreatesFinancialNetworkEdge → ⊥
jewishIdentityDoesNotCreateFinancialNetworkEdge ()

goldPurchaseDoesNotCreateMineOwnership : GoldPurchaseCreatesMineOwnership → ⊥
goldPurchaseDoesNotCreateMineOwnership ()

merchantIntermediationDoesNotCreateGoldProduction : MerchantIntermediationCreatesGoldProduction → ⊥
merchantIntermediationDoesNotCreateGoldProduction ()

colonialOfficeDoesNotCreatePrivateFinancialControl : ColonialOfficeCreatesPrivateFinancialControl → ⊥
colonialOfficeDoesNotCreatePrivateFinancialControl ()

oneFamilyRelationDoesNotCreateUniversalCommand : OneFamilyRelationCreatesUniversalCommand → ⊥
oneFamilyRelationDoesNotCreateUniversalCommand ()

record NetworkBoundary : Set where
  constructor network-boundary
  field
    familyConnectionEqualsBusinessAgency : Bool
    kinshipEqualsCoordination : Bool
    jewishIdentityCreatesNetworkContinuity : Bool
    goldPurchaseEqualsMineOwnership : Bool
    merchantIntermediationEqualsGoldProduction : Bool
    oneFamilyRelationEqualsUniversalCommand : Bool
    canonicalGenealogyReused : Bool
open NetworkBoundary public

canonicalNetworkBoundary : NetworkBoundary
canonicalNetworkBoundary = network-boundary false false false false false false true
