module DASHI.Law.ZionistInstitutionalCarrierGraphBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.ZionistPoliticalCultureSecurityRepertoireExact as Culture
import DASHI.Law.IsraeliAmalekContemporaryRoleBindingSourceReceiptsExact as Amalek
import DASHI.Law.AustraliaIsraelMilitarySecurityProvenanceExact as AUIsrael
import DASHI.Law.ZionismGlobalJewryExternalitySourceReceiptsExact as Jewry
import DASHI.Law.SecurityClassificationProvenanceBidiExact as Security

------------------------------------------------------------------------
-- Institutional carrier graph.
--
-- A political-cultural repertoire coordinate may be activated by an individual
-- speaker, reproduced by an institution, transmitted through a channel, and
-- then reach an operational consumer.  Those are distinct evidence-bearing
-- edges.  Material/security links are not silently promoted into ideological
-- transmission links.
------------------------------------------------------------------------

data InstitutionalCarrier : Set where
  israeliExecutive : InstitutionalCarrier
  knesset : InstitutionalCarrier
  idf : InstitutionalCarrier
  israeliDefenceIndustry : InstitutionalCarrier
  settlerInstitution : InstitutionalCarrier
  diasporaPoliticalAdvocacy : InstitutionalCarrier
  diasporaJewishCorrectionCarrier : InstitutionalCarrier
  privateSecurityOrganisation : InstitutionalCarrier
  australianGovernment : InstitutionalCarrier
  australianDefenceIndustry : InstitutionalCarrier
  nswPolice : InstitutionalCarrier
  foreignSecurityPartner : InstitutionalCarrier
  publicNarrativeCarrier : InstitutionalCarrier

data TransmissionChannel : Set where
  officialSpeech : TransmissionChannel
  soldierMessage : TransmissionChannel
  parliamentaryRecord : TransmissionChannel
  militaryEcho : TransmissionChannel
  doctrineOrTraining : TransmissionChannel
  procurement : TransmissionChannel
  exportSupplyChain : TransmissionChannel
  liaison : TransmissionChannel
  advocacy : TransmissionChannel
  publicStatement : TransmissionChannel
  privateSecurityCoordination : TransmissionChannel
  mediaNarrative : TransmissionChannel

data OperationalOutput : Set where
  militaryAudience : OperationalOutput
  securityClassification : OperationalOutput
  targetClassification : OperationalOutput
  publicThreatNarrative : OperationalOutput
  procurementIntegration : OperationalOutput
  securityProtectionRouting : OperationalOutput
  securityCoerciveRouting : OperationalOutput
  settlementOrTerritorialPolicy : OperationalOutput
  foreignSecurityInput : OperationalOutput
  correctionWarning : OperationalOutput

data EdgeClosure : Set where
  directReceipt : EdgeClosure
  echoReceipt : EdgeClosure
  contextualReceipt : EdgeClosure
  allegationOnly : EdgeClosure
  edgeOpen : EdgeClosure
  edgeConflict : EdgeClosure

record RepertoireCarrierEdge : Set where
  constructor repertoireCarrierEdge
  field
    repertoireReceipt : Culture.RepertoireReceipt
    sourceCarrier : InstitutionalCarrier
    targetCarrier : InstitutionalCarrier
    channel : TransmissionChannel
    output : OperationalOutput
    closure : EdgeClosure
    sourceReference : String
    sameContentTransportClosed : Bool

open RepertoireCarrierEdge public

------------------------------------------------------------------------
-- Positive contemporary carrier receipts.
------------------------------------------------------------------------

netanyahuExecutiveToMilitary : RepertoireCarrierEdge
netanyahuExecutiveToMilitary = repertoireCarrierEdge
  Culture.netanyahuAmalekRepertoireReceipt
  israeliExecutive idf soldierMessage militaryAudience directReceipt
  "Netanyahu public missive to IDF soldiers and commanders, 3 November 2023"
  true

knessetEnemyFrameToPublic : RepertoireCarrierEdge
knessetEnemyFrameToPublic = repertoireCarrierEdge
  Culture.netanyahuAmalekRepertoireReceipt
  knesset publicNarrativeCarrier parliamentaryRecord publicThreatNarrative contextualReceipt
  "Knesset official records containing Amalek/light-dark enemy framing; current-specific content remains separately attributed"
  false

militaryEchoOfInflammatoryRhetoric : RepertoireCarrierEdge
militaryEchoOfInflammatoryRhetoric = repertoireCarrierEdge
  Culture.netanyahuAmalekRepertoireReceipt
  israeliExecutive idf militaryEcho militaryAudience echoReceipt
  "ICJ Declaration of Judge Nolte, 26 January 2024: inflammatory parts of relevant statements were evidenced as echoed threateningly by members of the armed forces"
  false

------------------------------------------------------------------------
-- Material/security graph is separate from ideological-content graph.
------------------------------------------------------------------------

record MaterialSecurityCarrierEdge : Set where
  constructor materialSecurityCarrierEdge
  field
    sourceCarrier : InstitutionalCarrier
    targetCarrier : InstitutionalCarrier
    channel : TransmissionChannel
    output : OperationalOutput
    sourceReference : String
    materialOrInstitutionalLinkClosed : Bool
    ideologicalContentTransportClosed : Bool

open MaterialSecurityCarrierEdge public

f35MaterialCarrier : MaterialSecurityCarrierEdge
f35MaterialCarrier = materialSecurityCarrierEdge
  australianDefenceIndustry israeliDefenceIndustry exportSupplyChain procurementIntegration
  (AUIsrael.sourceReference AUIsrael.f35SupplyChainReceipt)
  true false

elbitProcurementCarrier : MaterialSecurityCarrierEdge
elbitProcurementCarrier = materialSecurityCarrierEdge
  israeliDefenceIndustry australianDefenceIndustry procurement procurementIntegration
  (AUIsrael.sourceReference AUIsrael.elbitIndustryReceipt)
  true false

csgPoliceCoordinationCarrier : MaterialSecurityCarrierEdge
csgPoliceCoordinationCarrier = materialSecurityCarrierEdge
  privateSecurityOrganisation nswPolice privateSecurityCoordination securityProtectionRouting
  (AUIsrael.sourceReference AUIsrael.csgCoordinationReceipt)
  true false

israelTrainingAllegationCarrier : MaterialSecurityCarrierEdge
israelTrainingAllegationCarrier = materialSecurityCarrierEdge
  foreignSecurityPartner privateSecurityOrganisation doctrineOrTraining foreignSecurityInput
  (AUIsrael.sourceReference AUIsrael.israelTrainingAllegationReceipt)
  false false

------------------------------------------------------------------------
-- Correction is an institutional carrier too.  Diaspora Jewish critique is not
-- Zionist transmission and must not be erased from the graph.
------------------------------------------------------------------------

record CorrectionCarrierEdge : Set where
  constructor correctionCarrierEdge
  field
    sourceCarrier : InstitutionalCarrier
    targetCarrier : InstitutionalCarrier
    output : OperationalOutput
    sourceReference : String
    warningClosed : Bool
    collectiveJewishResponsibilityAsserted : Bool

open CorrectionCarrierEdge public

diasporaWarningToExecutive : CorrectionCarrierEdge
diasporaWarningToExecutive = correctionCarrierEdge
  diasporaJewishCorrectionCarrier israeliExecutive correctionWarning
  (Jewry.sourceReference Jewry.globalJewishLeadersWarningReceipt)
  true false

------------------------------------------------------------------------
-- Cross-border security-classification bridge.
------------------------------------------------------------------------

data CarrierClaim : Set where
  repertoireReachedMilitaryAudience : CarrierClaim
  repertoireInstitutionallyReproduced : CarrierClaim
  materialSecurityLinkExists : CarrierClaim
  materialSecurityLinkCarriedIdeologicalContent : CarrierClaim
  privateSecurityLinkReachedNSWPolice : CarrierClaim
  zionistRepertoireReachedNSWPoliceClassification : CarrierClaim
  diasporaJewishCritiqueExists : CarrierClaim
  institutionalCarrierProvesPopulationBelief : CarrierClaim

data CarrierProducer : Set where
  directMilitaryAudienceProducer : CarrierProducer
  multiInstitutionReproductionProducer : CarrierProducer
  materialLinkProducer : CarrierProducer
  ideologicalContentTransportProducer : CarrierProducer
  policeCoordinationProducer : CarrierProducer
  nswClassificationContentAndForeignLiaisonProducer : CarrierProducer
  diasporaCorrectionProducer : CarrierProducer
  populationBeliefProducer : CarrierProducer

reverseCarrier : CarrierClaim → CarrierProducer
reverseCarrier repertoireReachedMilitaryAudience = directMilitaryAudienceProducer
reverseCarrier repertoireInstitutionallyReproduced = multiInstitutionReproductionProducer
reverseCarrier materialSecurityLinkExists = materialLinkProducer
reverseCarrier materialSecurityLinkCarriedIdeologicalContent = ideologicalContentTransportProducer
reverseCarrier privateSecurityLinkReachedNSWPolice = policeCoordinationProducer
reverseCarrier zionistRepertoireReachedNSWPoliceClassification = nswClassificationContentAndForeignLiaisonProducer
reverseCarrier diasporaJewishCritiqueExists = diasporaCorrectionProducer
reverseCarrier institutionalCarrierProvesPopulationBelief = populationBeliefProducer

record CarrierCutset : Set where
  constructor carrierCutset
  field
    militaryAudienceClosed : Bool
    multiInstitutionClosed : Bool
    materialLinkClosed : Bool
    ideologicalContentClosed : Bool
    policeCoordinationClosed : Bool
    nswClassificationContentClosed : Bool
    foreignLiaisonClosed : Bool
    correctionClosed : Bool
    cutsetReference : String

open CarrierCutset public

data CarrierResidual : Set where
  militaryAudienceResidual : CarrierResidual
  institutionalReproductionResidual : CarrierResidual
  materialLinkResidual : CarrierResidual
  ideologicalContentResidual : CarrierResidual
  policeCoordinationResidual : CarrierResidual
  nswClassificationContentResidual : CarrierResidual
  foreignLiaisonResidual : CarrierResidual
  correctionResidual : CarrierResidual
  carrierClosed : CarrierResidual

firstCarrierResidual : CarrierClaim → CarrierCutset → CarrierResidual
firstCarrierResidual repertoireReachedMilitaryAudience c with militaryAudienceClosed c
... | false = militaryAudienceResidual
... | true = carrierClosed
firstCarrierResidual repertoireInstitutionallyReproduced c with multiInstitutionClosed c
... | false = institutionalReproductionResidual
... | true = carrierClosed
firstCarrierResidual materialSecurityLinkExists c with materialLinkClosed c
... | false = materialLinkResidual
... | true = carrierClosed
firstCarrierResidual materialSecurityLinkCarriedIdeologicalContent c with ideologicalContentClosed c
... | false = ideologicalContentResidual
... | true = carrierClosed
firstCarrierResidual privateSecurityLinkReachedNSWPolice c with policeCoordinationClosed c
... | false = policeCoordinationResidual
... | true = carrierClosed
firstCarrierResidual zionistRepertoireReachedNSWPoliceClassification c with nswClassificationContentClosed c
... | false = nswClassificationContentResidual
... | true with foreignLiaisonClosed c
...   | false = foreignLiaisonResidual
...   | true = carrierClosed
firstCarrierResidual diasporaJewishCritiqueExists c with correctionClosed c
... | false = correctionResidual
... | true = carrierClosed
firstCarrierResidual institutionalCarrierProvesPopulationBelief c = institutionalReproductionResidual

canonicalCurrentCarrierCutset : CarrierCutset
canonicalCurrentCarrierCutset = carrierCutset
  true true true false true false false true
  "executive->military rhetoric, institutional repetition, material links, CSG-police coordination and diaspora correction are observed; ideological content transfer into NSW classification remains open"

nswIdeologyClaimStopsAtClassificationContent :
  firstCarrierResidual zionistRepertoireReachedNSWPoliceClassification canonicalCurrentCarrierCutset
  ≡ nswClassificationContentResidual
nswIdeologyClaimStopsAtClassificationContent = refl

materialLinkDoesNotCloseIdeologicalContent :
  firstCarrierResidual materialSecurityLinkCarriedIdeologicalContent canonicalCurrentCarrierCutset
  ≡ ideologicalContentResidual
materialLinkDoesNotCloseIdeologicalContent = refl

------------------------------------------------------------------------
-- Source-attribution and non-essentialisation firewalls.
------------------------------------------------------------------------

record InstitutionalCarrierBoundary : Set where
  constructor institutionalCarrierBoundary
  field
    procurementLinkEqualsIdeologicalTransmission : Bool
    procurementLinkEqualsIdeologicalTransmissionIsFalse : procurementLinkEqualsIdeologicalTransmission ≡ false
    privateSecurityCoordinationEqualsForeignControl : Bool
    privateSecurityCoordinationEqualsForeignControlIsFalse : privateSecurityCoordinationEqualsForeignControl ≡ false
    institutionalRepetitionEqualsUniversalZionistBelief : Bool
    institutionalRepetitionEqualsUniversalZionistBeliefIsFalse : institutionalRepetitionEqualsUniversalZionistBelief ≡ false
    zionistInstitutionEqualsJewishPopulation : Bool
    zionistInstitutionEqualsJewishPopulationIsFalse : zionistInstitutionEqualsJewishPopulation ≡ false
    correctionCarrierMayBeErasedAsOutlier : Bool
    correctionCarrierMayBeErasedAsOutlierIsFalse : correctionCarrierMayBeErasedAsOutlier ≡ false
    foreignSecurityContextProvesNSWClassificationMotive : Bool
    foreignSecurityContextProvesNSWClassificationMotiveIsFalse : foreignSecurityContextProvesNSWClassificationMotive ≡ false

canonicalInstitutionalCarrierBoundary : InstitutionalCarrierBoundary
canonicalInstitutionalCarrierBoundary =
  institutionalCarrierBoundary false refl false refl false refl false refl false refl false refl

------------------------------------------------------------------------
-- Adapter target into existing security-classification owner.
------------------------------------------------------------------------

nswForeignClassificationProducer : Security.SecurityClassificationProducer
nswForeignClassificationProducer = Security.foreignLiaisonProducer

nswIdeologicalClassificationProducer : Security.SecurityClassificationProducer
nswIdeologicalClassificationProducer = Security.motiveProducer
