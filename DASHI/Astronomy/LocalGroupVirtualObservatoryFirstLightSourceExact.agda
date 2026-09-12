module DASHI.Astronomy.LocalGroupVirtualObservatoryFirstLightSourceExact where

open import DASHI.Core.Prelude
open import DASHI.Core.AttributedSourceCore
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Controlled attribution for the originating first-light social post.
--
-- The post was supplied from a private server.  The display identity, visible
-- timestamp, attached artefact name, and project relationship are retained;
-- the private server locator is deliberately not published here.
------------------------------------------------------------------------

firstLightPostSource : AttributedSource
firstLightPostSource =
  mkNoDOISource
    "Poppie / NOUS"
    "Virtual Observatory first-light Local Group rendering and summary"
    "private community/social post, displayed 2026-09-07 23:38; timezone not asserted"
    "2026"
    ""
    communitySource
    "originating Virtual Observatory first-light post; attached artefact first-light.png; project/model authorship attribution only, not authorship of cited astronomy sources"
    controlledAttribution

firstLightAttribution : AttributionProjection firstLightPostSource
firstLightAttribution =
  mkControlledAttributionProjection
    firstLightPostSource
    "Poppie / NOUS — private post, displayed 2026-09-07 23:38"

record FirstLightPrivateSourceReceipt : Set where
  constructor firstLightPrivateSourceReceipt
  field
    displayIdentity : String
    visibleDate : String
    visibleTime : String
    visibleTimezoneKnown : Bool
    visibleTimezoneKnownIsFalse : visibleTimezoneKnown ≡ false
    attachedArtifact : String
    privateServerKnownToContributor : Bool
    privateServerLocatorPublished : Bool
    privateServerLocatorPublishedIsFalse : privateServerLocatorPublished ≡ false
    cdnAttachmentIsCanonicalPostLocator : Bool
    cdnAttachmentIsCanonicalPostLocatorIsFalse : cdnAttachmentIsCanonicalPostLocator ≡ false
    visibleDisplayNameIsVerifiedLegalIdentity : Bool
    visibleDisplayNameIsVerifiedLegalIdentityIsFalse : visibleDisplayNameIsVerifiedLegalIdentity ≡ false

originReceipt : FirstLightPrivateSourceReceipt
originReceipt =
  firstLightPrivateSourceReceipt
    "Poppie / NOUS"
    "2026-09-07"
    "23:38"
    false
    refl
    "first-light.png"
    true
    false
    refl
    false
    refl
    false
    refl

postImportsPaperAuthorship : Bool
postImportsPaperAuthorship = false

postImportsPaperAuthorshipIsFalse : postImportsPaperAuthorship ≡ false
postImportsPaperAuthorshipIsFalse = refl

postImportsIndependentVerification : Bool
postImportsIndependentVerification = false

postImportsIndependentVerificationIsFalse : postImportsIndependentVerification ≡ false
postImportsIndependentVerificationIsFalse = refl

privateSourceAttributionImpliesPermissionToPublishLocator : Bool
privateSourceAttributionImpliesPermissionToPublishLocator = false

privateSourceAttributionImpliesPermissionToPublishLocatorIsFalse :
  privateSourceAttributionImpliesPermissionToPublishLocator ≡ false
privateSourceAttributionImpliesPermissionToPublishLocatorIsFalse = refl
