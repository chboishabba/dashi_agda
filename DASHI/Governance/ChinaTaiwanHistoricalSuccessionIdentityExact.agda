module DASHI.Governance.ChinaTaiwanHistoricalSuccessionIdentityExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- CHINA / TAIWAN HISTORICAL SUCCESSION AND IDENTITY
--
-- The civil-war, state-succession, colonial-history, authoritarian-rule,
-- democratisation, national-identity and present-sovereignty questions are
-- separately typed.  No historical succession claim here settles a present
-- normative or legal sovereignty dispute.
------------------------------------------------------------------------

taiwanWhiteTerrorMuseum : Source.AttributedSource
taiwanWhiteTerrorMuseum = Source.mkNoDOISource
  "National Human Rights Museum, Taiwan"
  "White Terror Period"
  "National Human Rights Museum"
  "current institutional history page"
  "https://www.nhrm.gov.tw/w/nhrmEN/White_Terror_Period"
  Source.governmentSource
  "Taiwan institutional source for ROC takeover after Japan's defeat, the 1947 February 28 Incident, KMT retreat after civil-war defeat, martial-law authoritarian consolidation, and the White Terror period"
  Source.publicAttribution

taiwanDemocracyPresidentOffice : Source.AttributedSource
taiwanDemocracyPresidentOffice = Source.mkNoDOISource
  "Office of the President, Republic of China (Taiwan)"
  "Taiwan's Vibrant Democracy, Moving Forward with the World"
  "Office of the President"
  "current institutional history page"
  "https://www.president.gov.tw/qrcode/19e"
  Source.governmentSource
  "Taiwan institutional source for 38 years of martial law from 1949, lifting in 1987, subsequent liberalisation, and the first direct presidential election in 1996"
  Source.publicAttribution

prcAntiSecessionLaw2005 : Source.AttributedSource
prcAntiSecessionLaw2005 = Source.mkNoDOISource
  "National People's Congress / Government of the People's Republic of China"
  "Anti-Secession Law"
  "PRC statutory text"
  "2005"
  "https://www.gov.cn/flfg/2005-06/21/content_8265.htm"
  Source.governmentSource
  "primary PRC legal source for the PRC position that Taiwan is part of China, that the Taiwan question is a civil-war legacy, and for statutory conditions concerning non-peaceful means"
  Source.publicAttribution

data HistoricalLayer : Set where
  qingImperialPeriod : HistoricalLayer
  japaneseColonialPeriod : HistoricalLayer
  rocPostwarTakeover : HistoricalLayer
  chineseCivilWarSuccession : HistoricalLayer
  rocTaiwanAuthoritarianPeriod : HistoricalLayer
  taiwanDemocratisationPeriod : HistoricalLayer
  contemporaryCrossStraitPeriod : HistoricalLayer

data PoliticalEntity : Set where
  qingState : PoliticalEntity
  republicOfChina : PoliticalEntity
  chineseCommunistParty : PoliticalEntity
  peoplesRepublicOfChina : PoliticalEntity
  rocGovernmentOnTaiwan : PoliticalEntity
  democraticTaiwanPolity : PoliticalEntity

data SuccessionRelation : Set where
  colonialTransferRelation : SuccessionRelation
  civilWarRivalGovernmentRelation : SuccessionRelation
  authoritarianContinuityRelation : SuccessionRelation
  democratisationTransformationRelation : SuccessionRelation
  presentContestedSovereigntyRelation : SuccessionRelation

record HistoricalTransition : Set where
  constructor historical-transition
  field
    from : PoliticalEntity
    to : PoliticalEntity
    relation : SuccessionRelation
    sourceReceipt : String
    sameInstitutionalSystem : Bool
    settlesPresentSovereignty : Bool
    determinesPresentPopulationIdentity : Bool

open HistoricalTransition public

rocCivilWarRetreat : HistoricalTransition
rocCivilWarRetreat = historical-transition
  republicOfChina rocGovernmentOnTaiwan
  civilWarRivalGovernmentRelation
  "1949 KMT/ROC retreat to Taiwan after defeat by the CCP in the Chinese Civil War"
  false false false

rocAuthoritarianToDemocraticTaiwan : HistoricalTransition
rocAuthoritarianToDemocraticTaiwan = historical-transition
  rocGovernmentOnTaiwan democraticTaiwanPolity
  democratisationTransformationRelation
  "martial law lifted 1987; liberalisation followed; first direct presidential election 1996"
  false false false

data CivilWarSuccessionSettlesPresentSovereignty : Set where
data ROCContinuityMeansUnchangedPoliticalSystem : Set where
data ChineseHistoricalConnectionDeterminesTaiwaneseIdentity : Set where
data DemocratisationErasesAuthoritarianHistory : Set where

civilWarSuccessionDoesNotSettlePresentSovereignty :
  CivilWarSuccessionSettlesPresentSovereignty → ⊥
civilWarSuccessionDoesNotSettlePresentSovereignty ()

rocContinuityDoesNotMeanUnchangedPoliticalSystem :
  ROCContinuityMeansUnchangedPoliticalSystem → ⊥
rocContinuityDoesNotMeanUnchangedPoliticalSystem ()

historicalConnectionDoesNotDeterminePresentIdentity :
  ChineseHistoricalConnectionDeterminesTaiwaneseIdentity → ⊥
historicalConnectionDoesNotDeterminePresentIdentity ()

democratisationDoesNotEraseAuthoritarianHistory :
  DemocratisationErasesAuthoritarianHistory → ⊥
democratisationDoesNotEraseAuthoritarianHistory ()

whiteTerrorSnowball : Snowball.SourceRoleSnowballReceipt taiwanWhiteTerrorMuseum
whiteTerrorSnowball = Snowball.canonicalSourceRoleSnowballReceipt taiwanWhiteTerrorMuseum
