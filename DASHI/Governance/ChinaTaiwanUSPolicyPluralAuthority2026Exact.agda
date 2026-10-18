module DASHI.Governance.ChinaTaiwanUSPolicyPluralAuthority2026Exact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)
import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- U.S. CHINA / TAIWAN POLICY: PLURAL AUTHORITY, 2026
--
-- U.S. recognition policy, the U.S. "one China policy", the PRC "one China
-- principle", Taiwan Relations Act obligations/capabilities, presidential
-- bargaining posture, congressional positions and party coalitions are not one
-- object.
------------------------------------------------------------------------

archivedStateTaiwanFactSheet : Source.AttributedSource
archivedStateTaiwanFactSheet = Source.mkNoDOISource
  "United States Department of State"
  "U.S. Relations With Taiwan"
  "archived State Department fact sheet, 2021-2025 administration"
  "archived 2025"
  "https://2021-2025.state.gov/u-s-relations-with-taiwan/"
  Source.governmentSource
  "official archived description of longstanding U.S. one China policy, unofficial Taiwan relations, peaceful-resolution preference and Taiwan Relations Act self-defense framework; not current-administration evidence by itself"
  Source.publicAttribution

reutersTaiwanIndependence2026 : Source.AttributedSource
reutersTaiwanIndependence2026 = Source.mkNoDOISource
  "Reuters"
  "What is 'Taiwan independence' and what does that mean for Trump and Xi?"
  "Reuters"
  "2026-09-25"
  "https://www.reuters.com/world/china/what-is-taiwan-independence-is-taiwan-already-independent-2026-09-25/"
  Source.newsSource
  "current secondary source reporting that the Trump administration describes U.S. Taiwan policy as unchanged and retains strategic ambiguity while the U.S. lacks formal diplomatic recognition of Taiwan"
  Source.publicAttribution

reutersWicker2026 : Source.AttributedSource
reutersWicker2026 = Source.mkNoDOISource
  "Reuters"
  "Republican Senator Wicker says US security commitments to Taiwan must be upheld"
  "Reuters"
  "2026-09-30"
  "https://www.reuters.com/world/us/republican-senator-wicker-says-us-security-commitments-taiwan-must-be-upheld-2026-09-30/"
  Source.newsSource
  "current secondary source for Senate Armed Services Chair Roger Wicker and other Republican senators pressing the Trump administration over delayed Taiwan security assistance"
  Source.publicAttribution

data USPolicyLayer : Set where
  diplomaticRecognitionLayer : USPolicyLayer
  oneChinaPolicyLayer : USPolicyLayer
  taiwanRelationsActLayer : USPolicyLayer
  executiveBargainingLayer : USPolicyLayer
  congressionalSecurityLayer : USPolicyLayer
  partyCoalitionLayer : USPolicyLayer
  semiconductorIndustrialLayer : USPolicyLayer

data ChinaPolicyConcept : Set where
  usOneChinaPolicy : ChinaPolicyConcept
  prcOneChinaPrinciple : ChinaPolicyConcept
  formalDiplomaticRecognition : ChinaPolicyConcept
  unofficialTaiwanRelationship : ChinaPolicyConcept
  strategicAmbiguity : ChinaPolicyConcept
  selfDefenseAssistance : ChinaPolicyConcept

data USActor : Set where
  usExecutive : USActor
  usCongress : USActor
  republicanSenators : USActor
  democraticLegislators : USActor
  usStateDepartment : USActor
  usDefenseDepartment : USActor

record PolicyPosition : Set where
  constructor policy-position
  field
    actor : USActor
    layer : USPolicyLayer
    proposition : String
    sourceReceipt : String
    speaksForWholeUnitedStates : Bool
    speaksForWholeParty : Bool
    settlesTaiwanSovereignty : Bool

open PolicyPosition public

trumpAdministrationUnchangedPolicy : PolicyPosition
trumpAdministrationUnchangedPolicy = policy-position
  usExecutive oneChinaPolicyLayer
  "current administration representatives report no change in longstanding U.S. Taiwan policy"
  "Reuters, 2026-09-25 and subsequent reporting"
  false false false

wickerSecurityPressure : PolicyPosition
wickerSecurityPressure = policy-position
  republicanSenators congressionalSecurityLayer
  "Wicker and other Republican senators press the administration to release delayed Taiwan security assistance and uphold security commitments"
  "Reuters, 2026-09-30"
  false false false

data USOneChinaPolicyEqualsPRCOneChinaPrinciple : Set where
data ExecutivePositionEqualsCongressionalPosition : Set where
data RepublicanSenatorsSpeakForWholeRepublicanParty : Set where
data ArmsSupportSettlesTaiwanSovereignty : Set where
data DiplomaticNonrecognitionMeansNoTaiwanPolity : Set where

usPolicyDoesNotDefinitionallyEqualPRCPrinciple :
  USOneChinaPolicyEqualsPRCOneChinaPrinciple → ⊥
usPolicyDoesNotDefinitionallyEqualPRCPrinciple ()

executivePositionDoesNotEqualCongressionalPosition :
  ExecutivePositionEqualsCongressionalPosition → ⊥
executivePositionDoesNotEqualCongressionalPosition ()

namedRepublicanSenatorsDoNotSpeakForWholeParty :
  RepublicanSenatorsSpeakForWholeRepublicanParty → ⊥
namedRepublicanSenatorsDoNotSpeakForWholeParty ()

armsSupportDoesNotSettleSovereignty :
  ArmsSupportSettlesTaiwanSovereignty → ⊥
armsSupportDoesNotSettleSovereignty ()

diplomaticNonrecognitionDoesNotErasePolity :
  DiplomaticNonrecognitionMeansNoTaiwanPolity → ⊥
diplomaticNonrecognitionDoesNotErasePolity ()
