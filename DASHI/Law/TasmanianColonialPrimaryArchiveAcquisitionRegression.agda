module DASHI.Law.TasmanianColonialPrimaryArchiveAcquisitionRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.TasmanianColonialPrimaryArchiveAcquisitionExact as Archive

parentGenocideBoundaryReusedRegression :
  Archive.parentGenocideSourceBoundaryReused
    Archive.canonicalTasmanianPrimaryArchiveAcquisitionBoundary
  ≡ true
parentGenocideBoundaryReusedRegression = refl

arthurAboriginalFileLocatedRegression :
  Archive.governorArthurAboriginalFile7578Located
    Archive.canonicalTasmanianPrimaryArchiveAcquisitionBoundary
  ≡ true
arthurAboriginalFileLocatedRegression = refl

campaignItineraryLocatedRegression :
  Archive.arthur1830CampaignItineraryLocated
    Archive.canonicalTasmanianPrimaryArchiveAcquisitionBoundary
  ≡ true
campaignItineraryLocatedRegression = refl

capturedAboriginesMinutesLocatedRegression :
  Archive.capturedAboriginesCommitteeMinutesLocated
    Archive.canonicalTasmanianPrimaryArchiveAcquisitionBoundary
  ≡ true
capturedAboriginesMinutesLocatedRegression = refl

colonialDespatchSeriesLocatedRegression :
  Archive.colonialDespatchSeriesLocated
    Archive.canonicalTasmanianPrimaryArchiveAcquisitionBoundary
  ≡ true
colonialDespatchSeriesLocatedRegression = refl

primaryArchiveReplayPaidRegression :
  Archive.primaryArchivePageLevelReplayPaid
    Archive.canonicalTasmanianPrimaryArchiveAcquisitionBoundary
  ≡ false
primaryArchiveReplayPaidRegression = refl

archiveLocatorAutomaticallyClaimProofRegression :
  Archive.archiveLocatorAutomaticallyPaysHistoricalClaim
    Archive.canonicalTasmanianPrimaryArchiveAcquisitionBoundary
  ≡ false
archiveLocatorAutomaticallyClaimProofRegression = refl

digitisationAutomaticallyCompleteRegression :
  Archive.archiveGuideAutomaticallyMeansCompleteDigitisation
    Archive.canonicalTasmanianPrimaryArchiveAcquisitionBoundary
  ≡ false
digitisationAutomaticallyCompleteRegression = refl
