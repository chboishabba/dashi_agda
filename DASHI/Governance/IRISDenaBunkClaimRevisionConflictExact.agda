module DASHI.Governance.IRISDenaBunkClaimRevisionConflictExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Governance.IRISDenaAustralianCommandStatementReceiptExact as Command

------------------------------------------------------------------------
-- SOURCE-REVISION / COMPETING-CLAIM CASE
--
-- An early secondary report attributed an "ordered to bunks/cabins" claim to
-- an unnamed military source.  A later primary, named Chief-of-Navy answer said
-- "No" to that proposition, while declining to reveal the exact same-episode
-- duty.  Resolve only the bunk proposition; do not promote exact-duty closure.
------------------------------------------------------------------------

earlyBunkReport : Source.AttributedSource
earlyBunkReport = Source.mkNoDOISource
  "The West Australian / The Nightly reporting lineage"
  "Australian submariners reportedly kept in cabins during US attack on Iranian frigate"
  "The West Australian"
  "2026-03-11"
  "https://thewest.com.au/politics/defence/australian-submariners-reportedly-kept-in-cabins-during-us-attack-on-iranian-frigate-c-21941158"
  Source.newsSource
  "secondary report attributing an ordered-to-bunks/cabins claim to an unnamed military source; this is attribution evidence, not a primary operational record"
  Source.publicAttribution

primaryDenial : Source.AttributedSource
primaryDenial = Source.mkNoDOISource
  "Vice Admiral Mark Hammond AO RAN / Richard Marles"
  "Press Conference, Sydney"
  "Australian Department of Defence"
  "2026-03-21"
  "https://www.minister.defence.gov.au/transcripts/2026-03-21/press-conference-sydney"
  Source.governmentSource
  "primary named statement: Chief of Navy answered 'No' when asked whether the Australian submariners were ordered to their bunks; he separately said they performed duties under the US agreement and were not engaged in offensive operations, without disclosing exact duties"
  Source.publicAttribution

data ClaimStatus : Set where
  attributedSecondary : ClaimStatus
  deniedPrimaryNamed : ClaimStatus
  exactDutyUnresolved : ClaimStatus

record BunkClaimRevisionReceipt : Set where
  constructor bunk-claim-revision-receipt
  field
    earlyStatus : ClaimStatus
    laterStatus : ClaimStatus
    earlyPublicationDate : String
    laterPublicationDate : String
    earlySourceAnonymous : Bool
    earlySourceAnonymousIsTrue : earlySourceAnonymous ≡ true
    laterSpeakerNamed : Bool
    laterSpeakerNamedIsTrue : laterSpeakerNamed ≡ true
    bunkPropositionPrimaryDenied : Bool
    bunkPropositionPrimaryDeniedIsTrue : bunkPropositionPrimaryDenied ≡ true
    exactDutyDisclosedByDenial : Bool
    exactDutyDisclosedByDenialIsFalse : exactDutyDisclosedByDenial ≡ false
    historicalEventChangedByLaterSource : Bool
    historicalEventChangedByLaterSourceIsFalse : historicalEventChangedByLaterSource ≡ false

open BunkClaimRevisionReceipt public

canonicalRevision : BunkClaimRevisionReceipt
canonicalRevision =
  bunk-claim-revision-receipt
    attributedSecondary
    deniedPrimaryNamed
    "2026-03-11"
    "2026-03-21"
    true refl
    true refl
    true refl
    false refl
    false refl

-- Reuse the existing primary command owner for the operational residual rather
-- than inventing a second exact-duty representation.
exactDutyResidual : Command.OperationalResidual
exactDutyResidual = Command.exactDutyResidual

data AnonymousSecondaryClaimEqualsPrimaryFact : Set where
data PrimaryBunkDenialDeterminesExactDuty : Set where
data OneResolvedPropositionClosesOperationalEpisode : Set where
data LaterKnowledgeRevisionChangesEarlierWorldEvent : Set where
data RepetitionOfEarlyClaimCreatesIndependentCorroboration : Set where

anonymousSecondaryDoesNotEqualPrimaryFact :
  AnonymousSecondaryClaimEqualsPrimaryFact → ⊥
anonymousSecondaryDoesNotEqualPrimaryFact ()

bunkDenialDoesNotDetermineExactDuty :
  PrimaryBunkDenialDeterminesExactDuty → ⊥
bunkDenialDoesNotDetermineExactDuty ()

resolvedBunkClaimDoesNotCloseEpisode :
  OneResolvedPropositionClosesOperationalEpisode → ⊥
resolvedBunkClaimDoesNotCloseEpisode ()

knowledgeRevisionDoesNotChangeWorldEvent :
  LaterKnowledgeRevisionChangesEarlierWorldEvent → ⊥
knowledgeRevisionDoesNotChangeWorldEvent ()

repetitionDoesNotCreateIndependentCorroboration :
  RepetitionOfEarlyClaimCreatesIndependentCorroboration → ⊥
repetitionDoesNotCreateIndependentCorroboration ()

earlySnowball : Snowball.SourceRoleSnowballReceipt earlyBunkReport
earlySnowball = Snowball.canonicalSourceRoleSnowballReceipt earlyBunkReport

primarySnowball : Snowball.SourceRoleSnowballReceipt primaryDenial
primarySnowball = Snowball.canonicalSourceRoleSnowballReceipt primaryDenial
