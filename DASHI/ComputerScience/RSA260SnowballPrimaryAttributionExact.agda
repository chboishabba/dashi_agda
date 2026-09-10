module DASHI.ComputerScience.RSA260SnowballPrimaryAttributionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as SnowballAttribution
import DASHI.Core.SnowballOSINTAcquisitionInvariantExact as OSINT
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as ExternalIdentity
import DASHI.ComputerScience.FactorProducerReceiptExact as Factor

------------------------------------------------------------------------
-- RSA-260 PRIMARY-SOURCE / SNOWBALL ATTRIBUTION OWNER
--
-- Keep distinct:
--   * the 2026-09-03 X disclosure event;
--   * Eric Lu's 2026-09-09 first-party technical account;
--   * arithmetic verification of the published factors;
--   * method attribution (GNFS / modified CADO-NFS / GPU implementation);
--   * independent reproduction;
--   * DASHI kernel certification.
--
-- The X carrier is retained as the publication-event locator, but the current
-- acquisition path cannot directly inspect its body.  The Cognition article is
-- the strongest presently available primary carrier for method/run/cost claims.
------------------------------------------------------------------------

rsa260XDisclosureSource : Attribution.AttributedSource
rsa260XDisclosureSource =
  Attribution.mkNoDOISource
    "Eric Lu (@penlume)"
    "RSA-260 factor disclosure on X"
    "X"
    "2026"
    "https://x.com/penlume/status/2095372672356212876"
    Attribution.practitionerSource
    "publication-event source: discloses a factor of RSA-260; does not by itself establish the production method, execution path, cost, independent reproduction, or kernel certification"
    Attribution.publicAttribution

rsa260CognitionTechnicalSource : Attribution.AttributedSource
rsa260CognitionTechnicalSource =
  Attribution.mkNoDOISource
    "Eric Lu"
    "Factoring RSA-260"
    "Cognition"
    "2026"
    "https://cognition.com/blog/factoring-rsa-260"
    Attribution.practitionerSource
    "first-party technical account for the RSA-260 factorization, GNFS/CADO-NFS implementation history, run chronology, hardware context, and author-estimated resource cost"
    Attribution.publicAttribution

rsa260SourceAtlas : Attribution.AttributedSourceAtlas
rsa260SourceAtlas =
  Attribution.mkSourceAtlas
    "RSA-260 publication and technical attribution"
    "DASHI.ComputerScience.RSA260SnowballPrimaryAttributionExact"
    (rsa260XDisclosureSource ∷ rsa260CognitionTechnicalSource ∷ [])
    "retains publication-event identity separately from first-party technical/method attribution; neither source imports proof authority or independent reproduction"

rsa260XDisclosureSnowball : SnowballAttribution.SourceRoleSnowballReceipt rsa260XDisclosureSource
rsa260XDisclosureSnowball =
  SnowballAttribution.canonicalSourceRoleSnowballReceipt rsa260XDisclosureSource

rsa260TechnicalSnowball : SnowballAttribution.SourceRoleSnowballReceipt rsa260CognitionTechnicalSource
rsa260TechnicalSnowball =
  SnowballAttribution.canonicalSourceRoleSnowballReceipt rsa260CognitionTechnicalSource

------------------------------------------------------------------------
-- OSINT carrier states.
------------------------------------------------------------------------

rsa260XObservation : OSINT.OSINTObservation
rsa260XObservation =
  OSINT.osint-observation
    "https://x.com/penlume/status/2095372672356212876"
    ""
    "current acquisition path receives HTTP 403 for the native X body; stable exact post locator retained and content claims require a source-of-source or later direct inspection receipt"
    OSINT.publicFirstPersonStatement
    OSINT.identityUnresolved
    "Eric Lu publicly disclosed a factor of RSA-260 on 2026-09-03"
    "publication event only; no method/runtime/cost inference from this carrier"
    "native-body digest unresolved"
    false
    true
    true

rsa260TechnicalObservation : OSINT.OSINTObservation
rsa260TechnicalObservation =
  OSINT.osint-observation
    "https://cognition.com/blog/factoring-rsa-260"
    ""
    "directly inspected first-party technical article, 2026-09-09"
    OSINT.publicFirstPersonStatement
    OSINT.exactNativeCarrier
    "Eric Lu reports RSA-260 was factored using a new GPU implementation of GNFS based on a significantly modified CADO-NFS pipeline, with detailed run chronology and estimated resource cost"
    "method/run/cost attribution to the author account; not independent reproduction or DASHI kernel certification"
    "content digest not yet bound in this source-written owner"
    true
    true
    true

------------------------------------------------------------------------
-- External-identity snowball.  No DOI is claimed for either web source.
------------------------------------------------------------------------

rsa260XCannonicalURLDemand : ExternalIdentity.ExternalIdentityDemand
rsa260XCannonicalURLDemand =
  ExternalIdentity.mkOptionalIdentityDemand
    "RSA-260 publication event"
    "Eric Lu penlume RSA-260 2026-09-03"
    "Eric Lu RSA-260 X disclosure"
    ExternalIdentity.canonicalURL
    (ExternalIdentity.verified
      "canonical X post URL"
      "https://x.com/penlume/status/2095372672356212876")

rsa260TechnicalCanonicalURLDemand : ExternalIdentity.ExternalIdentityDemand
rsa260TechnicalCanonicalURLDemand =
  ExternalIdentity.mkOptionalIdentityDemand
    "RSA-260 technical account"
    "Eric Lu Factoring RSA-260 Cognition 2026-09-09"
    "Factoring RSA-260"
    ExternalIdentity.canonicalURL
    (ExternalIdentity.verified
      "canonical first-party technical article"
      "https://cognition.com/blog/factoring-rsa-260")

------------------------------------------------------------------------
-- Producer/evidence refinement.
--
-- Preserve the existing externally-announced receipt as the disclosure object.
-- The later first-party account permits a SECOND receipt with producer class
-- number-field sieve and named method, without rewriting history or claiming
-- independent reproduction.
------------------------------------------------------------------------

rsa260GNFSAttributedReceipt : Factor.FactorProducerReceipt
rsa260GNFSAttributedReceipt =
  Factor.factorProducerReceipt
    (Factor.externalFactorIdentityEvidence
      "RSA-260 (260 decimal digits / 862 bits)"
      "4397328654844826923795068102505872571721883526553349659561256924505973939597593482272505698004801207988043088656411102133523080581"
      "5028695206842569864686141618253083416610081090075366674776775706538324961364412200138116378509733307971876652984898985905923678379"
      "published factorization reconstructs RSA-260 under external arbitrary-precision arithmetic verification; dedicated DASHI big-integer kernel certificate remains separate")
    Factor.numberFieldSieveProducer
    Factor.externallyCheckedArithmeticIdentity
    Factor.executionMethodNamedButPathUnknown
    Factor.partialCostReceipt
    "Eric Lu, Factoring RSA-260, Cognition, 2026-09-09; publication event separately retained at X status 2095372672356212876"
    "author reports GNFS using a significantly modified CADO-NFS implementation with GPU polyselect/lattice-sieving/Block-Wiedemann/sqrt components"
    "author estimates 4,900 GPU-days / 13.5 GPU-years and about USD 400k at then-current market prices; estimate is source-attributed, not an independently reproduced cost receipt"

------------------------------------------------------------------------
-- WrongType / promotion firewalls.
------------------------------------------------------------------------

data PublicationEventImpliesMethod : Set where
data AuthorMethodAccountImpliesIndependentReproduction : Set where
data AIAssistedImplementationImpliesAIOriginatedAlgorithm : Set where
data SameFactorImpliesSameProducerHistory : Set where
data SourceCostEstimateIsIndependentCostReceipt : Set where
data SourceAttributionIsKernelCertification : Set where

publicationEventDoesNotIdentifyMethod : PublicationEventImpliesMethod → ⊥
publicationEventDoesNotIdentifyMethod ()

authorAccountDoesNotCreateIndependentReproduction :
  AuthorMethodAccountImpliesIndependentReproduction → ⊥
authorAccountDoesNotCreateIndependentReproduction ()

aiAssistanceDoesNotCreateAlgorithmOrigin :
  AIAssistedImplementationImpliesAIOriginatedAlgorithm → ⊥
aiAssistanceDoesNotCreateAlgorithmOrigin ()

sameFactorDoesNotIdentifyHistory : SameFactorImpliesSameProducerHistory → ⊥
sameFactorDoesNotIdentifyHistory ()

sourceCostEstimateDoesNotBecomeIndependentReceipt :
  SourceCostEstimateIsIndependentCostReceipt → ⊥
sourceCostEstimateDoesNotBecomeIndependentReceipt ()

sourceAttributionDoesNotBecomeKernelCertification :
  SourceAttributionIsKernelCertification → ⊥
sourceAttributionDoesNotBecomeKernelCertification ()

------------------------------------------------------------------------
-- Current snowball boundary.
------------------------------------------------------------------------

record RSA260SnowballBoundary : Set where
  constructor rsa260-snowball-boundary
  field
    publicationEventRetainedSeparately : Bool
    primaryTechnicalAccountRetainedSeparately : Bool
    methodNowNamedGNFS : Bool
    executionPathIndependentlyReproduced : Bool
    factorArithmeticKernelCertifiedInDASHI : Bool
    sourceCostIndependentlyReproduced : Bool
    externalIdentityCreatesAuthority : Bool
    unresolvedNativeXInspectionIsNegativeEvidence : Bool

open RSA260SnowballBoundary public

canonicalRSA260SnowballBoundary : RSA260SnowballBoundary
canonicalRSA260SnowballBoundary =
  rsa260-snowball-boundary
    true
    true
    true
    false
    false
    false
    false
    false
