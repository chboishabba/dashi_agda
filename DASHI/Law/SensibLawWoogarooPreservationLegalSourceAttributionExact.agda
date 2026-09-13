module DASHI.Law.SensibLawWoogarooPreservationLegalSourceAttributionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawWoogarooPreservationLegalCutsetExact as Cutset

------------------------------------------------------------------------
-- SOURCE ATTRIBUTION SEAM FOR THE WOOGAROO PRESERVATION CUTSET
--
-- This owner makes explicit what the legal cutset may report from a source and
-- what remains a DASHI reconstruction/application.  It deliberately does not
-- promote a source proposition into a legal finding about Woogaroo.
------------------------------------------------------------------------

data ClaimStage : Set where
  externalClaim : ClaimStage
  dashiFormalReconstruction : ClaimStage
  dashiCrossSourceApplication : ClaimStage
  externalAdjudicatedFinding : ClaimStage
  realisedProtectiveOutcome : ClaimStage

record AttributedLegalClaim : Set where
  constructor attributed-legal-claim
  field
    stage : ClaimStage
    source : Cutset.LegalSourceAttribution
    claim : String
    exactSameAsSourceBoundedProposition : Bool
    adjudicationReceiptPresent : Bool
    realisedOutcomeReceiptPresent : Bool

open AttributedLegalClaim public

ncaS13SourceClaim : AttributedLegalClaim
ncaS13SourceClaim = attributed-legal-claim
  externalClaim
  Cutset.ncaCriticalHabitatDefinition
  "Queensland legislation defines critical habitat by reference to habitat essential for conservation of a viable protected-wildlife population or native-wildlife community."
  true false false

woogarooS13Application : AttributedLegalClaim
woogarooS13Application = attributed-legal-claim
  dashiCrossSourceApplication
  Cutset.ncaCriticalHabitatDefinition
  "Woogaroo habitat should be tested against the Queensland s 13 critical-habitat elements using exact parcel, species/community and habitat-function evidence."
  false false false

ncaS49SourceClaim : AttributedLegalClaim
ncaS49SourceClaim = attributed-legal-claim
  externalClaim
  Cutset.ncaCompulsoryNatureRefugeAuthority
  "Queensland legislation provides a compulsory nature-refuge route where its statutory conditions are satisfied."
  true false false

woogarooS49Application : AttributedLegalClaim
woogarooS49Application = attributed-legal-claim
  dashiCrossSourceApplication
  Cutset.ncaCompulsoryNatureRefugeAuthority
  "If Woogaroo's exact land and ecology satisfy the statutory predicates, s 49 is a candidate permanent-protection mechanism to pursue."
  false false false

epbcSourceClaim : AttributedLegalClaim
epbcSourceClaim = attributed-legal-claim
  externalClaim
  Cutset.epbcThreatenedSpeciesAuthority
  "The EPBC Act regulates actions likely to have significant impacts on listed threatened species or ecological communities through the controlled-action and approval regime."
  true false false

woogarooEPBCApplication : AttributedLegalClaim
woogarooEPBCApplication = attributed-legal-claim
  dashiCrossSourceApplication
  Cutset.epbcThreatenedSpeciesAuthority
  "The existing Woogaroo-area federal project records can be assembled into a project x controlling-matter x impact matrix for the refusal/conditions argument."
  false false false

------------------------------------------------------------------------
-- No-promotion laws.
------------------------------------------------------------------------

data SourceClaimEqualsWoogarooFinding : Set where
data DASHIApplicationEqualsCourtFinding : Set where
data DelayEqualsProtectiveOutcome : Set where
data MinisterialPowerEqualsMinisterialExercise : Set where

sourceClaimDoesNotBecomeWoogarooFinding : SourceClaimEqualsWoogarooFinding → ⊥
sourceClaimDoesNotBecomeWoogarooFinding ()

dashIApplicationDoesNotBecomeCourtFinding : DASHIApplicationEqualsCourtFinding → ⊥
dashIApplicationDoesNotBecomeCourtFinding ()

delayDoesNotBecomeProtectiveOutcome : DelayEqualsProtectiveOutcome → ⊥
delayDoesNotBecomeProtectiveOutcome ()

powerDoesNotEqualExercise : MinisterialPowerEqualsMinisterialExercise → ⊥
powerDoesNotEqualExercise ()

------------------------------------------------------------------------
-- Reporting boundary.
------------------------------------------------------------------------

record WoogarooLegalReportingBoundary : Set where
  constructor woogaroo-legal-reporting-boundary
  field
    maySayMechanismExistsWhenStatutePaysIt : Bool
    maySayMechanismExistsWhenStatutePaysItIsTrue :
      maySayMechanismExistsWhenStatutePaysIt ≡ true
    maySayWoogarooQualifiesWithoutApplicationReceipt : Bool
    maySayWoogarooQualifiesWithoutApplicationReceiptIsFalse :
      maySayWoogarooQualifiesWithoutApplicationReceipt ≡ false
    maySayMinisterMustExerciseDiscretionWithoutDutyReceipt : Bool
    maySayMinisterMustExerciseDiscretionWithoutDutyReceiptIsFalse :
      maySayMinisterMustExerciseDiscretionWithoutDutyReceipt ≡ false
    maySayDelayIsProtection : Bool
    maySayDelayIsProtectionIsFalse : maySayDelayIsProtection ≡ false

canonicalWoogarooLegalReportingBoundary : WoogarooLegalReportingBoundary
canonicalWoogarooLegalReportingBoundary =
  woogaroo-legal-reporting-boundary
    true refl
    false refl
    false refl
    false refl
