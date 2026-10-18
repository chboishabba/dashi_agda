module DASHI.Governance.IRISDenaAustralianCommandStatementReceiptExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- IRIS DENA / AUSTRALIAN EMBEDDED SUBMARINERS
-- COMMAND-LEVEL PUBLIC STATEMENT RECEIPTS
------------------------------------------------------------------------

pmTranscript : Source.AttributedSource
pmTranscript = Source.mkNoDOISource
  "Prime Minister Anthony Albanese"
  "Television interview - Sky Newsday"
  "Prime Minister of Australia transcript"
  "2026-03-06"
  "https://www.pm.gov.au/media/television-interview-sky-newsday-0"
  Source.governmentSource
  "primary government statement confirming three Australian personnel aboard the vessel and stating that no Australian personnel participated in offensive action; not an operational action log"
  Source.publicAttribution

navyDefenceTranscript : Source.AttributedSource
navyDefenceTranscript = Source.mkNoDOISource
  "Vice Admiral Mark Hammond and Richard Marles"
  "Press Conference, Sydney"
  "Defence Ministers transcript"
  "2026-03-21"
  "https://www.minister.defence.gov.au/transcripts/2026-03-21/press-conference-sydney"
  Source.governmentSource
  "primary command/ministerial statement: sailors were not ordered to bunks; Chief of Navy says they performed duties under the bilateral agreement and were not engaged in offensive operations; operational details were withheld"
  Source.publicAttribution

data CommandClaimKind : Set where
  personnelPresent : CommandClaimKind
  noOffensiveParticipation : CommandClaimKind
  notOrderedToBunks : CommandClaimKind
  dutiesUnderEmbeddingAgreement : CommandClaimKind
  exactDutyReconstruction : CommandClaimKind

record CommandStatementReceipt : Set where
  constructor command-statement-receipt
  field
    claimKind : CommandClaimKind
    source : Source.AttributedSource
    boundedReading : String
    commandLevelPrimarySource : Bool
    commandLevelPrimarySourceIsTrue :
      commandLevelPrimarySource ≡ true
    independentlyReconstructsOperationalLog : Bool
    independentlyReconstructsOperationalLogIsFalse :
      independentlyReconstructsOperationalLog ≡ false

open CommandStatementReceipt public

presenceReceipt : CommandStatementReceipt
presenceReceipt =
  command-statement-receipt
    personnelPresent
    pmTranscript
    "Albanese confirms three Australian personnel were aboard the U.S. submarine."
    true refl
    false refl

nonParticipationReceipt : CommandStatementReceipt
nonParticipationReceipt =
  command-statement-receipt
    noOffensiveParticipation
    pmTranscript
    "Albanese states no Australian personnel participated in offensive action against Iran."
    true refl
    false refl

notBunksReceipt : CommandStatementReceipt
notBunksReceipt =
  command-statement-receipt
    notOrderedToBunks
    navyDefenceTranscript
    "Chief of Navy rejects the claim that the Australian submariners were ordered to their bunks."
    true refl
    false refl

embeddingProtocolReceipt : CommandStatementReceipt
embeddingProtocolReceipt =
  command-statement-receipt
    dutiesUnderEmbeddingAgreement
    navyDefenceTranscript
    "Chief of Navy and Defence Minister state the sailors operated under embedding protocols aligned with Australian policy."
    true refl
    false refl

record OperationalResidual : Set where
  constructor operational-residual
  field
    residualRef : String
    requiredObject : String
    reason : String
    publicCommandStatementsInsufficient : Bool
    publicCommandStatementsInsufficientIsTrue :
      publicCommandStatementsInsufficient ≡ true

open OperationalResidual public

exactDutyResidual : OperationalResidual
exactDutyResidual =
  operational-residual
    "residual:iris-dena:exact-duty-reconstruction"
    "operational action log, watch/duty record, embedding protocol text, or another independently reviewable same-object record"
    "public command statements narrow presence/participation claims but explicitly withhold operational detail"
    true refl

pmSnowball : Snowball.SourceRoleSnowballReceipt pmTranscript
pmSnowball = Snowball.canonicalSourceRoleSnowballReceipt pmTranscript

navySnowball : Snowball.SourceRoleSnowballReceipt navyDefenceTranscript
navySnowball = Snowball.canonicalSourceRoleSnowballReceipt navyDefenceTranscript

data CommandStatementEqualsOperationalLog : Set where
data NoOffensiveParticipationMeansNoDutiesPerformed : Set where
data NotOrderedToBunksMeansOffensiveParticipation : Set where

commandStatementDoesNotEqualOperationalLog :
  CommandStatementEqualsOperationalLog → ⊥
commandStatementDoesNotEqualOperationalLog ()

nonParticipationDoesNotMeanNoDuties :
  NoOffensiveParticipationMeansNoDutiesPerformed → ⊥
nonParticipationDoesNotMeanNoDutiesPerformed ()

notBunksDoesNotMeanOffensiveParticipation :
  NotOrderedToBunksMeansOffensiveParticipation → ⊥
notBunksDoesNotMeanOffensiveParticipation ()
