module DASHI.Governance.BoloBoloOWSArchivesWorkingGroupLocatorRegression where

open import DASHI.Core.Prelude
import DASHI.Governance.BoloBoloOWSArchivesWorkingGroupLocatorExact as Locator

nov8ThreadLocatorPinned :
  Locator.nov8ForwardedSpokesDocumentsLocatorPaid
    Locator.canonicalOWSArchivesWorkingGroupLocatorBoundary ≡ true
nov8ThreadLocatorPinned = refl

nov8AttachmentStillUnrecovered :
  Locator.nov8ForwardedAttachmentRecovered
    Locator.canonicalOWSArchivesWorkingGroupLocatorBoundary ≡ false
nov8AttachmentStillUnrecovered = refl

nov11ThreadLocatorPinned :
  Locator.nov11SpokescouncilThreadLocatorPaid
    Locator.canonicalOWSArchivesWorkingGroupLocatorBoundary ≡ true
nov11ThreadLocatorPinned = refl

nov11ThreadContentStillUnrecovered :
  Locator.nov11ThreadContentRecovered
    Locator.canonicalOWSArchivesWorkingGroupLocatorBoundary ≡ false
nov11ThreadContentStillUnrecovered = refl

tamimentCoordinatesDoNotPaySpokesMinutes :
  Locator.tamimentCoordinatesProveSpokesMinuteContent
    Locator.canonicalOWSArchivesWorkingGroupLocatorBoundary ≡ false
tamimentCoordinatesDoNotPaySpokesMinutes = refl

secondaryLocatorDoesNotBecomePrimaryContent :
  Locator.secondaryLocatorEqualsPrimaryContent
    Locator.canonicalOWSArchivesWorkingGroupLocatorBoundary ≡ false
secondaryLocatorDoesNotBecomePrimaryContent = refl
