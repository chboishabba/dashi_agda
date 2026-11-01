module DASHI.Governance.IRISDenaSenateEstimatesDutyNarrowingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Governance.IRISDenaAustralianCommandStatementReceiptExact as Existing

------------------------------------------------------------------------
-- IRIS DENA / SENATE ESTIMATES DUTY NARROWING
--
-- Primary parliamentary index:
--   confirms that 3 June 2026 Senate Estimates examined ADF activities on
--   US submarines under AUKUS at Hansard pp. 49-52.
--
-- Secondary partisan summary:
--   attributes to Defence leadership the statement that the three personnel
--   performed defensive and platform-maintenance duties during the sinking.
--
-- Until the proof Hansard text itself is reviewed, the duty content remains
-- secondary-attributed rather than promoted to primary transcript fact.
------------------------------------------------------------------------

parliamentCommitteeIndex : Source.AttributedSource
parliamentCommitteeIndex = Source.mkNoDOISource
  "Senate Foreign Affairs, Defence and Trade Legislation Committee"
  "2026-27 Budget Estimates - Chapter 2: Key issues"
  "Parliament of Australia"
  "2026"
  "https://www.aph.gov.au/Parliamentary_Business/Committees/Senate/Foreign_Affairs_Defence_and_Trade/Budget_Estimates_2026-27/Chapter_2_-_Key_issues"
  Source.governmentSource
  "primary parliamentary index confirming the hearing topic and proof-Hansard page range; does not itself reproduce the detailed duty evidence"
  Source.publicAttribution

liberalPartySummary : Source.AttributedSource
liberalPartySummary = Source.mkNoDOISource
  "Liberal Party of Australia"
  "2026-27 Senate Estimates, Week Two"
  "Liberal Party of Australia"
  "2026-06-07"
  "https://www.liberal.org.au/2026/06/07/2026-27-senate-estimates-week-two"
  (Source.namedSourceKind "partisan political summary of parliamentary hearing")
  "secondary partisan summary attributing defensive and platform-maintenance duties to Defence leadership; requires proof-Hansard verification before primary promotion"
  Source.publicAttribution

data DutyClass : Set where
  defensiveDuty : DutyClass
  platformMaintenanceDuty : DutyClass
  offensiveWeaponEmployment : DutyClass
  exactWatchstationOrTask : DutyClass

record DutyNarrowingReceipt : Set where
  constructor duty-narrowing-receipt
  field
    parliamentaryTopicSource : Source.AttributedSource
    contentSource : Source.AttributedSource
    boundedReading : String
    defensiveDutyAttributed : Bool
    defensiveDutyAttributedIsTrue :
      defensiveDutyAttributed ≡ true
    platformMaintenanceAttributed : Bool
    platformMaintenanceAttributedIsTrue :
      platformMaintenanceAttributed ≡ true
    primaryHansardContentVerified : Bool
    primaryHansardContentVerifiedIsFalse :
      primaryHansardContentVerified ≡ false
    exactWatchstationKnown : Bool
    exactWatchstationKnownIsFalse :
      exactWatchstationKnown ≡ false
    offensiveWeaponEmploymentAttributed : Bool
    offensiveWeaponEmploymentAttributedIsFalse :
      offensiveWeaponEmploymentAttributed ≡ false

open DutyNarrowingReceipt public

senateDutyNarrowing : DutyNarrowingReceipt
senateDutyNarrowing =
  duty-narrowing-receipt
    parliamentCommitteeIndex
    liberalPartySummary
    "Parliament confirms the topic/page range; the Liberal Party summary attributes defensive and platform-maintenance duties to Defence leadership."
    true refl
    true refl
    false refl
    false refl
    false refl

record PrimaryTranscriptResidual : Set where
  constructor primary-transcript-residual
  field
    residualRef : String
    requiredObject : String
    currentFibre : String
    exactTaskStillOpen : Bool
    exactTaskStillOpenIsTrue :
      exactTaskStillOpen ≡ true
    secondarySummaryMayPromotePrimaryFact : Bool
    secondarySummaryMayPromotePrimaryFactIsFalse :
      secondarySummaryMayPromotePrimaryFact ≡ false

open PrimaryTranscriptResidual public

proofHansardResidual : PrimaryTranscriptResidual
proofHansardResidual =
  primary-transcript-residual
    "residual:iris-dena:proof-hansard-duty-content"
    "3 June 2026 proof Committee Hansard pp. 49-52, or an equivalent primary transcript/Defence record reproducing the duty evidence"
    "defensive duty OR platform-maintenance duty at secondary-attributed level; exact watchstation/task/protocol remains unknown"
    true refl
    false refl

existingOperationalResidual : Existing.OperationalResidual
existingOperationalResidual = Existing.exactDutyResidual

data PartisanSummaryEqualsPrimaryTranscript : Set where
data DefensiveDutyMeansNoCombatContribution : Set where
data PlatformMaintenanceMeansNoOperationalContribution : Set where
data DutyClassDeterminesExactWatchstation : Set where

partisanSummaryDoesNotEqualPrimaryTranscript :
  PartisanSummaryEqualsPrimaryTranscript → ⊥
partisanSummaryDoesNotEqualPrimaryTranscript ()

defensiveDutyDoesNotMeanNoCombatContribution :
  DefensiveDutyMeansNoCombatContribution → ⊥
defensiveDutyDoesNotMeanNoCombatContribution ()

maintenanceDoesNotMeanNoOperationalContribution :
  PlatformMaintenanceMeansNoOperationalContribution → ⊥
maintenanceDoesNotMeanNoOperationalContribution ()

dutyClassDoesNotDetermineExactWatchstation :
  DutyClassDeterminesExactWatchstation → ⊥
dutyClassDoesNotDetermineExactWatchstation ()

parliamentSnowball :
  Snowball.SourceRoleSnowballReceipt parliamentCommitteeIndex
parliamentSnowball =
  Snowball.canonicalSourceRoleSnowballReceipt parliamentCommitteeIndex

secondarySnowball :
  Snowball.SourceRoleSnowballReceipt liberalPartySummary
secondarySnowball =
  Snowball.canonicalSourceRoleSnowballReceipt liberalPartySummary
