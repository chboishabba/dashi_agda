module DASHI.Governance.AUKUSEmbeddedAuthorityCommandNoncollapseExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Governance.AUKUSOnboardConductSovereigntyBoundaryExact as Sovereignty

------------------------------------------------------------------------
-- EMBEDDED RAN AUTHORITY / COMMAND NONCOLLAPSE
--
-- The available public evidence is secondary reporting reproducing excerpts
-- from a leaked non-public 2024 Chief of Navy directive and describing a
-- September 2023 bilateral MOU.  The directive/MOU themselves are not in hand.
------------------------------------------------------------------------

theNightlyDirectiveReport : Source.AttributedSource
theNightlyDirectiveReport = Source.mkNoDOISource
  "Andrew Greene"
  "Australian naval personnel on board US subs instructed to comply with all directions from American commanders"
  "The Nightly"
  "2026-05-04"
  "https://thenightly.com.au/politics/australian-naval-personnel-on-board-us-subs-instructed-to-comply-with-all-directions-from-american-commanders-c-22231198"
  Source.newsSource
  "secondary reporting reproducing excerpts from a leaked December 2024 Chief of Navy directive; report says embedded RAN personnel must comply with lawful/reasonable directions from superior corresponding-rank USN personnel, while the same directive says this does not grant USN personnel command over RAN members"
  Source.publicAttribution

michaelWestDirectiveMOUReport : Source.AttributedSource
michaelWestDirectiveMOUReport = Source.mkNoDOISource
  "Rex Patrick"
  "Disingenuous. Minister blindsided as Australia stumbled into Iran war"
  "Michael West Media"
  "2026-05-12"
  "https://michaelwest.com.au/disingenuous-minister-blindsided-as-australia-stumbled-into-iran-war/"
  Source.newsSource
  "secondary investigative report: embedding followed a September 2023 MOU that is not public; reproduces the lawful/reasonable-direction clause from the leaked 2024 Chief of Navy directive"
  Source.publicAttribution

data DocumentaryAuthorityLevel : Set where
  publicPrimaryDocument : DocumentaryAuthorityLevel
  secondaryReproductionOfNonPublicPrimary : DocumentaryAuthorityLevel
  secondaryCharacterisationOnly : DocumentaryAuthorityLevel

record EmbeddedAuthorityReceipt : Set where
  constructor embedded-authority-receipt
  field
    documentaryLevel : DocumentaryAuthorityLevel
    source : Source.AttributedSource
    clauseRef : String
    lawfulReasonableDirectionsAttributed : Bool
    lawfulReasonableDirectionsAttributedIsTrue :
      lawfulReasonableDirectionsAttributed ≡ true
    disciplinaryConsequenceAttributed : Bool
    disciplinaryConsequenceAttributedIsTrue :
      disciplinaryConsequenceAttributed ≡ true
    explicitNoCommandClauseAttributed : Bool
    explicitNoCommandClauseAttributedIsTrue :
      explicitNoCommandClauseAttributed ≡ true
    primaryDirectiveAcquired : Bool
    primaryDirectiveAcquiredIsFalse :
      primaryDirectiveAcquired ≡ false
    primaryMOUAcquired : Bool
    primaryMOUAcquiredIsFalse :
      primaryMOUAcquired ≡ false
    appliesToIRISSameEpisodeTask : Bool
    appliesToIRISSameEpisodeTaskIsFalse :
      appliesToIRISSameEpisodeTask ≡ false

open EmbeddedAuthorityReceipt public

canonicalAuthorityReceipt : EmbeddedAuthorityReceipt
canonicalAuthorityReceipt =
  embedded-authority-receipt
    secondaryReproductionOfNonPublicPrimary
    theNightlyDirectiveReport
    "leaked Chief of Navy directive: lawful/reasonable superior-rank directions + explicit no-command clause"
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl

record DirectionCommandBoundary : Set where
  constructor direction-command-boundary
  field
    additionalDirectionAuthorityAttributed : Bool
    additionalDirectionAuthorityAttributedIsTrue :
      additionalDirectionAuthorityAttributed ≡ true
    formalCommandDelegationAttributed : Bool
    formalCommandDelegationAttributedIsFalse :
      formalCommandDelegationAttributed ≡ false
    authorityEqualsCommand : Bool
    authorityEqualsCommandIsFalse :
      authorityEqualsCommand ≡ false
    commandStatusSettlesSovereignty : Bool
    commandStatusSettlesSovereigntyIsFalse :
      commandStatusSettlesSovereignty ≡ false
    protocolRuleSettlesActualDuty : Bool
    protocolRuleSettlesActualDutyIsFalse :
      protocolRuleSettlesActualDuty ≡ false

open DirectionCommandBoundary public

canonicalBoundary : DirectionCommandBoundary
canonicalBoundary =
  direction-command-boundary
    true refl
    false refl
    false refl
    false refl
    false refl

record PrimaryDocumentResidual : Set where
  constructor primary-document-residual
  field
    residualRef : String
    requiredObject : String
    currentKnowledge : String
    secondaryExcerptMayPromotePrimaryDocument : Bool
    secondaryExcerptMayPromotePrimaryDocumentIsFalse :
      secondaryExcerptMayPromotePrimaryDocument ≡ false

open PrimaryDocumentResidual public

directiveResidual : PrimaryDocumentResidual
directiveResidual =
  primary-document-residual
    "residual:aukus:embedded-authority-directive-primary"
    "December 2024 Chief of Navy directive, complete and authentic primary document"
    "secondary reports reproduce both a mandatory lawful/reasonable-directions clause and an explicit no-command clause"
    false refl

mouResidual : PrimaryDocumentResidual
mouResidual =
  primary-document-residual
    "residual:aukus:2023-exchange-personnel-mou-primary"
    "September 2023 Australia-US exchange-of-defence-personnel MOU and any operative annexes for submarine embeds"
    "secondary reporting says the MOU exists and is not public"
    false refl

data DirectionAuthorityMeansFormalCommand : Set where
data NoCommandClauseMeansNoUSOperationalAuthority : Set where
data DirectiveRuleDeterminesMarch2026ActualTask : Set where
data LeakedExcerptEqualsCompletePrimaryDocument : Set where

directionAuthorityDoesNotEqualFormalCommand :
  DirectionAuthorityMeansFormalCommand → ⊥
directionAuthorityDoesNotEqualFormalCommand ()

noCommandClauseDoesNotEraseOperationalAuthority :
  NoCommandClauseMeansNoUSOperationalAuthority → ⊥
noCommandClauseDoesNotEraseOperationalAuthority ()

directiveDoesNotDetermineActualTask :
  DirectiveRuleDeterminesMarch2026ActualTask → ⊥
directiveDoesNotDetermineActualTask ()

secondaryExcerptDoesNotEqualPrimaryDocument :
  LeakedExcerptEqualsCompletePrimaryDocument → ⊥
secondaryExcerptDoesNotEqualPrimaryDocument ()

sovereigntyBoundary : Sovereignty.AUKUSCommandSovereigntyBoundary
sovereigntyBoundary = Sovereignty.canonicalBoundary

nightlySnowball : Snowball.SourceRoleSnowballReceipt theNightlyDirectiveReport
nightlySnowball = Snowball.canonicalSourceRoleSnowballReceipt theNightlyDirectiveReport

mwmSnowball : Snowball.SourceRoleSnowballReceipt michaelWestDirectiveMOUReport
mwmSnowball = Snowball.canonicalSourceRoleSnowballReceipt michaelWestDirectiveMOUReport
