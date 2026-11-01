module DASHI.Governance.IranContraCovertFlowHistoricalMechanismExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Core.SnowballHistoricalProgrammeNameCollisionExact as SnowballName

------------------------------------------------------------------------
-- IRAN/CONTRA: HISTORICAL COVERT-FLOW MECHANISM
--
-- This owner is deliberately historical and source-bounded.
-- It records documented transaction / logistics / flow-of-funds structure.
------------------------------------------------------------------------

walshArchives : Source.AttributedSource
walshArchives = Source.mkNoDOISource
  "National Archives and Records Administration"
  "Records of Lawrence Walsh relating to Iran/Contra"
  "U.S. National Archives"
  ""
  "https://www.archives.gov/research/investigations/walsh.html"
  Source.governmentSource
  "archival administrative history: secret arms sales to Iran, prohibited Contra assistance, diversion of some arms-sale proceeds to the Contras, and an Independent Counsel Flow-of-Funds/DoD investigative team"
  Source.publicAttribution

walshReport : Source.AttributedSource
walshReport = Source.mkNoDOISource
  "Office of Independent Counsel Lawrence E. Walsh"
  "Final Report of the Independent Counsel for Iran/Contra Matters"
  "Independent Counsel report"
  "1993"
  "https://irp.fas.org/offdocs/walsh/execsum.htm"
  (Source.namedSourceKind "independent-counsel report")
  "historical report on off-the-books Enterprise financing, foreign/private donations, Swiss accounts and diversion of Iran arms-sale proceeds; legal findings remain proposition-specific"
  Source.publicAttribution

data HistoricalFlowLayer : Set where
  publicPolicyLayer : HistoricalFlowLayer
  armsSaleLayer : HistoricalFlowLayer
  logisticsProgrammeLayer : HistoricalFlowLayer
  intermediaryEnterpriseLayer : HistoricalFlowLayer
  flowOfFundsLayer : HistoricalFlowLayer
  downstreamContraSupportLayer : HistoricalFlowLayer
  oversightLayer : HistoricalFlowLayer

record HistoricalFlowReceipt : Set where
  constructor historical-flow-receipt
  field
    source : Source.AttributedSource
    boundedReading : String
    secretOperationsDocumented : Bool
    secretOperationsDocumentedIsTrue :
      secretOperationsDocumented ≡ true
    flowOfFundsInvestigationDocumented : Bool
    flowOfFundsInvestigationDocumentedIsTrue :
      flowOfFundsInvestigationDocumented ≡ true
    diversionOfSomeIranArmsProceedsDocumented : Bool
    diversionOfSomeIranArmsProceedsDocumentedIsTrue :
      diversionOfSomeIranArmsProceedsDocumented ≡ true
    everyTransactionIllegal : Bool
    everyTransactionIllegalIsFalse :
      everyTransactionIllegal ≡ false
    everyActorSharedIntent : Bool
    everyActorSharedIntentIsFalse :
      everyActorSharedIntent ≡ false

open HistoricalFlowReceipt public

canonicalIranContraFlow : HistoricalFlowReceipt
canonicalIranContraFlow =
  historical-flow-receipt
    walshArchives
    "Two secret U.S. operations were exposed in 1986; NARA records diversion of some Iran arms-sale proceeds to the Contras and a dedicated Flow-of-Funds/DoD investigative team."
    true refl
    true refl
    true refl
    false refl
    false refl

operationSnowballHistorical :
  SnowballName.NamedSnowballProgramme
operationSnowballHistorical =
  SnowballName.iranContra1986

record HistoricalRoutingTopology : Set where
  constructor historical-routing-topology
  field
    publicPolicyRef : String
    transactionRef : String
    logisticsRef : String
    intermediaryRef : String
    fundsRoutingRef : String
    downstreamUseRef : String
    oversightRef : String
    offBooksRoutingDocumented : Bool
    offBooksRoutingDocumentedIsTrue :
      offBooksRoutingDocumented ≡ true
    publicPolicyAndOperationalPracticeDiverged : Bool
    publicPolicyAndOperationalPracticeDivergedIsTrue :
      publicPolicyAndOperationalPracticeDiverged ≡ true

open HistoricalRoutingTopology public

iranContraTopology : HistoricalRoutingTopology
iranContraTopology =
  historical-routing-topology
    "stated U.S. public policy restricting arms relationship with Iran / statutory constraints on Contra aid"
    "U.S. arms sales to Iran"
    "Operation Snowball / Operation Crocus TOW-missile procurement-transfer logistics"
    "North/Secord/Hakim Enterprise"
    "Swiss-account / corporate flow-of-funds network"
    "Contra resupply / weapons support"
    "Congressional investigation + Independent Counsel"
    true refl
    true refl

data HistoricalFlowMeansCurrentAnalogy : Set where
data SimilarRoutingTopologyMeansSameActors : Set where
data SimilarRoutingTopologyMeansSameLegality : Set where
data CovertRoutingMeansEveryParticipantKnowsWholeScheme : Set where

historicalFlowDoesNotCreateCurrentAnalogy :
  HistoricalFlowMeansCurrentAnalogy → ⊥
historicalFlowDoesNotCreateCurrentAnalogy ()

topologyDoesNotIdentifyActors :
  SimilarRoutingTopologyMeansSameActors → ⊥
topologyDoesNotIdentifyActors ()

topologyDoesNotDetermineLegality :
  SimilarRoutingTopologyMeansSameLegality → ⊥
topologyDoesNotDetermineLegality ()

covertRoutingDoesNotCreateSharedKnowledge :
  CovertRoutingMeansEveryParticipantKnowsWholeScheme → ⊥
covertRoutingDoesNotCreateSharedKnowledge ()

walshSnowball :
  Snowball.SourceRoleSnowballReceipt walshArchives
walshSnowball = Snowball.canonicalSourceRoleSnowballReceipt walshArchives
