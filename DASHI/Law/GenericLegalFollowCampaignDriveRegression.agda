module DASHI.Law.GenericLegalFollowCampaignDriveRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.GenericLegalFollowCampaignDriveExact as Drive

boundary : Drive.GenericLegalFollowCampaignDriveBoundary
boundary = Drive.canonicalGenericLegalFollowCampaignDriveBoundary

deterministicAcquisitionMayRun :
  Drive.deterministicAcquisitionMayBeDriven boundary ≡ true
deterministicAcquisitionMayRun =
  Drive.deterministicAcquisitionMayBeDrivenIsTrue boundary

identityReviewStops :
  Drive.identityReviewMayBeBypassedByDriver boundary ≡ false
identityReviewStops =
  Drive.identityReviewMayBeBypassedByDriverIsFalse boundary

treatmentReviewStops :
  Drive.treatmentReviewMayBeBypassedByDriver boundary ≡ false
treatmentReviewStops =
  Drive.treatmentReviewMayBeBypassedByDriverIsFalse boundary

terminalInventsNoWork :
  Drive.terminalGateMayInventFurtherWork boundary ≡ false
terminalInventsNoWork =
  Drive.terminalGateMayInventFurtherWorkIsFalse boundary
