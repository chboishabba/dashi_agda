module DASHI.Wikimedia.IbrahimMonsterTeslaOEISWikimediaAttributionWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.WikipediaAllPairsPrunedMergeSnowballExact as AllPairs
import DASHI.Wikimedia.Base369OEISWikidataTeslaSnowballExact as TeslaExternal
import DASHI.Wikimedia.IbrahimBase369JOEISMoonshineSnowballExact as MoonshineExternal
import DASHI.Physics.Closure.TeslaPolyphaseHistoricalBoundary as TeslaHistorical
import DASHI.Wikimedia.IbrahimMonster236BMcKayThompsonNormalizationInvariantOEISExact as Normalization
import DASHI.Wikimedia.IbrahimMonster6BCompleteReplicabilityPowerSnowballExact as Replicability
import DASHI.Wikimedia.IbrahimMonster6BWeightTwoC6FourierOEISExact as Fourier

------------------------------------------------------------------------
-- MONSTER / TESLA / OEIS / WIKIMEDIA ATTRIBUTION WELD
--
-- Purpose:
--   retain exact source identities and navigation coordinates while keeping
--   theorem authority on the source that actually pays each premise.
--
--   Tesla / Q9036 / Wikipedia / US382281A
--     -> historical identity + polyphase / rotating-field engineering context.
--
--   Monstrous moonshine / Q392440 / pinned Wikipedia revision
--     -> topic identity and revision-bound navigation only.
--
--   OEIS A007246 / A007244 / A007255
--     -> 2B / 3B / 6B McKay--Thompson sequence manifestations and stable
--        positive-degree coordinates.
--
--   Ford--McKay--Norton / Ganter + ATLAS (upstream owners)
--     -> complete replicability / class-power meaning.
--
--   DASHI
--     -> finite Fourier consequences, refinement null models, and typed
--        non-promotion boundaries.
--
-- There is deliberately NO source edge
--
--   Tesla -> Monster theorem
--
-- and no QID, Wikipedia link, OEIS membership, or shared numeral is allowed to
-- manufacture one.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. External identities: verified when available, unresolved when not.
------------------------------------------------------------------------

teslaQid : Identity.ExternalIdentityDemand
teslaQid = Identity.mkOptionalIdentityDemand
  "Monster/Tesla/OEIS/Wikimedia attribution weld"
  "Nikola Tesla exact external identity"
  "Nikola Tesla"
  Identity.wikidataQid
  (Identity.verified "Q9036" "Wikidata inspected 2026-09-15; Nikola Tesla item")

teslaWikipedia : Identity.ExternalIdentityDemand
teslaWikipedia = Identity.mkOptionalIdentityDemand
  "Monster/Tesla/OEIS/Wikimedia attribution weld"
  "Nikola Tesla canonical English Wikipedia article"
  "Nikola Tesla"
  Identity.canonicalURL
  (Identity.verified
    "https://en.wikipedia.org/wiki/Nikola_Tesla"
    "canonical English Wikipedia article inspected 2026-09-15")

teslaWikipediaRevision : Identity.ExternalIdentityDemand
teslaWikipediaRevision = Identity.mkOptionalIdentityDemand
  "Monster/Tesla/OEIS/Wikimedia attribution weld"
  "Nikola Tesla exact current Wikipedia revision"
  "Nikola Tesla"
  Identity.wikimediaReferenceUrl
  (Identity.unresolved
    "canonical article verified; exact current oldid intentionally unresolved rather than guessed")

moonshineQid : Identity.ExternalIdentityDemand
moonshineQid = MoonshineExternal.moonshineQid

moonshineWikipedia : Identity.ExternalIdentityDemand
moonshineWikipedia = MoonshineExternal.moonshineWikipedia

-- Keep the exact already-inspected permanent-link coordinate visible here.
moonshineWikipediaPinnedRevision : String
moonshineWikipediaPinnedRevision =
  "https://en.wikipedia.org/w/index.php?title=Monstrous_moonshine&oldid=1355357732"

------------------------------------------------------------------------
-- 2. OEIS identifiers are stable coordinates, not theorem authority.
------------------------------------------------------------------------

twoBOEIS : Identity.ExternalIdentityDemand
twoBOEIS = Identity.mkOptionalIdentityDemand
  "Monster/Tesla/OEIS/Wikimedia attribution weld"
  "normalized Monster class 2B McKay-Thompson sequence"
  "OEIS A007246"
  Identity.officialIdentifier
  (Identity.verified "A007246" "retained from normalization-invariant OEIS owner")

threeBOEIS : Identity.ExternalIdentityDemand
threeBOEIS = Identity.mkOptionalIdentityDemand
  "Monster/Tesla/OEIS/Wikimedia attribution weld"
  "normalized Monster class 3B McKay-Thompson sequence"
  "OEIS A007244"
  Identity.officialIdentifier
  (Identity.verified "A007244" "retained from normalization-invariant OEIS owner")

sixBOEIS : Identity.ExternalIdentityDemand
sixBOEIS = Identity.mkOptionalIdentityDemand
  "Monster/Tesla/OEIS/Wikimedia attribution weld"
  "normalized Monster class 6B McKay-Thompson sequence"
  "OEIS A007255"
  Identity.officialIdentifier
  (Identity.verified "A007255" "retained from normalization-invariant OEIS owner")

normalizationFrontier : Normalization.NormalizationInvariantOEISFrontier
normalizationFrontier = Normalization.currentNormalizationInvariantOEISFrontier

replicabilityFrontier : Replicability.CompleteReplicabilityPowerFrontier
replicabilityFrontier = Replicability.completeReplicabilityPowerFrontier

fourierFrontier : Fourier.WeightTwoC6FourierFrontier
fourierFrontier = Fourier.weightTwoC6FourierFrontier

------------------------------------------------------------------------
-- 3. Primary Tesla engineering source.
--
-- US382281A explicitly describes progressively and continuously shifting the
-- poles / lines of maximum magnetic effect to produce motor rotation.  This is
-- a primary historical engineering source for the rotating-field/polyphase
-- context only.  It has no Monster, moonshine, Base369, or OEIS theorem role.
------------------------------------------------------------------------

teslaUS382281A : Attribution.AttributedSource
teslaUS382281A = Attribution.mkNoDOISource
  "Nikola Tesla"
  "Electrical Transmission Of Power"
  "United States Patent No. 382,281"
  "1888"
  "https://patents.google.com/patent/US382281A/en"
  (Attribution.namedSourceKind "primary patent record")
  "primary engineering provenance for progressive shifting/rotation of magnetic effect; not Base369, Monster, moonshine, OEIS, or universal-369 authority"
  Attribution.publicAttribution

teslaPatentAttribution = Snowball.canonicalSourceRoleSnowballReceipt teslaUS382281A

teslaHistoricalBoundary : TeslaHistorical.TeslaPolyphaseHistoricalBoundary
teslaHistoricalBoundary = TeslaHistorical.teslaPolyphaseBoundary

teslaExternalIdentityBoundary : TeslaExternal.Base369ExternalIdentityBoundary
teslaExternalIdentityBoundary = TeslaExternal.canonicalBase369ExternalIdentityBoundary

------------------------------------------------------------------------
-- 4. Typed attribution edges.
------------------------------------------------------------------------

record TypedAttributionEdge : Set where
  constructor typed-attribution-edge
  field
    leftReference : String
    rightReference : String
    relationReference : String
    evidenceReference : String
    sameObjectRequired : Bool
    promotionAllowed : Bool
open TypedAttributionEdge public

teslaPolyphaseEngineeringEdge : TypedAttributionEdge
teslaPolyphaseEngineeringEdge = typed-attribution-edge
  "Nikola Tesla / Q9036"
  "polyphase / rotating-field engineering context"
  "historical engineering source edge"
  "US382281A + TeslaPolyphaseHistoricalBoundary"
  true true

moonshineOEISManifestationEdge : TypedAttributionEdge
moonshineOEISManifestationEdge = typed-attribution-edge
  "monstrous moonshine / Q392440"
  "A007246 / A007244 / A007255"
  "McKay-Thompson sequence manifestation/navigation edge"
  "OEIS normalization owner + pinned Monstrous moonshine Wikipedia revision"
  false false

replicabilityPowerFamilyEdge : TypedAttributionEdge
replicabilityPowerFamilyEdge = typed-attribution-edge
  "Monster class 6B normalized McKay-Thompson series"
  "3B second replicate / 2B third replicate"
  "whole-series complete-replicability / class-power edge"
  "Ford-McKay-Norton/Ganter + ATLAS, retained through Replicability owner"
  true true

-- This is a repo-native model-reuse edge, not a historical claim about Tesla.
teslaRefinementNullModelEdge : TypedAttributionEdge
teslaRefinementNullModelEdge = typed-attribution-edge
  "Tesla-compatible polyphase engineering context"
  "Base369 binary/ternary refinement commuting-square null model"
  "modern DASHI cross-pollination of independent phase/refinement grammar"
  "JInvariantTeslaPolyphaseSeamRefinementBidiExact / TeslaPolyphaseHistoricalBoundary"
  false false

------------------------------------------------------------------------
-- 5. Wikipedia all-pairs / revision-sensitive navigation is retained.
------------------------------------------------------------------------

allPairsBoundary : AllPairs.WikipediaAllPairsBoundary
allPairsBoundary = AllPairs.canonicalWikipediaAllPairsBoundary

record WikimediaNavigationBoundary : Set where
  constructor wikimedia-navigation-boundary
  field
    teslaQidRetained : Bool
    teslaCanonicalWikipediaRetained : Bool
    teslaExactWikipediaRevisionResolved : Bool
    moonshineQidRetained : Bool
    moonshinePinnedWikipediaRevisionRetained : Bool
    oeisIdentifiersRetained : Bool
    allPairsEligibilityRetained : Bool
    wikipediaNavigationCreatesTheoremAuthority : Bool
open WikimediaNavigationBoundary public

canonicalWikimediaNavigationBoundary : WikimediaNavigationBoundary
canonicalWikimediaNavigationBoundary = wikimedia-navigation-boundary
  true true false true true true true false

------------------------------------------------------------------------
-- 6. WrongType / attribution firewalls.
------------------------------------------------------------------------

data ExternalIdentityCreatesAuthority : Set where
data WikipediaNavigationCreatesTheoremAuthority : Set where
data TeslaPatentCreatesMonsterTheorem : Set where
data OEISIdentifiersCreateLiteralAction : Set where
data TeslaQidCreates369Quote : Set where
data SharedPhaseLanguageCreatesSameObject : Set where

externalIdentityCreatesAuthority : ExternalIdentityCreatesAuthority → ⊥
externalIdentityCreatesAuthority ()

wikipediaNavigationCreatesTheoremAuthority :
  WikipediaNavigationCreatesTheoremAuthority → ⊥
wikipediaNavigationCreatesTheoremAuthority ()

teslaPatentCreatesMonsterTheorem : TeslaPatentCreatesMonsterTheorem → ⊥
teslaPatentCreatesMonsterTheorem ()

oeisIdentifiersCreateLiteralAction : OEISIdentifiersCreateLiteralAction → ⊥
oeisIdentifiersCreateLiteralAction ()

teslaQidDoesNotCreate369Quote : TeslaQidCreates369Quote → ⊥
teslaQidDoesNotCreate369Quote ()

sharedPhaseLanguageDoesNotCreateSameObject : SharedPhaseLanguageCreatesSameObject → ⊥
sharedPhaseLanguageDoesNotCreateSameObject ()

------------------------------------------------------------------------
-- 7. Frontier.
------------------------------------------------------------------------

record MonsterTeslaAttributionFrontier : Set where
  constructor monster-tesla-attribution-frontier
  field
    teslaQidVerified : Bool
    teslaCanonicalWikipediaVerified : Bool
    moonshineQidVerified : Bool
    moonshineWikipediaRevisionPinned : Bool
    normalized236BOEISCoordinatesRetained : Bool
    teslaPrimaryPolyphasePatentRetained : Bool
    tesla369QuotePrimarySourcePaid : Bool
    completeReplicabilitySourcePaidUpstream : Bool
    c6FourierClassFunctionReceiptPaidUpstream : Bool
    externalIdentityCreatesAuthorityPaid : Bool
    directTeslaToMonsterTheoremEdgePaid : Bool
    literalSixBProjectorActionPaid : Bool
    n3BMultiplicityIntertwinerPaid : Bool
    nextResidual : String
open MonsterTeslaAttributionFrontier public

canonicalMonsterTeslaAttributionFrontier : MonsterTeslaAttributionFrontier
canonicalMonsterTeslaAttributionFrontier = monster-tesla-attribution-frontier
  true true true true true true
  false true true
  false false false false
  "retain QID/Wikipedia/OEIS/patent coordinates as typed attribution/search edges. The theorem-bearing Monster residuals remain the literal 6B weight-two action/projectors and the same-action N(3B) multiplicity character/intertwiner. Once a literal 6B projector family exists, test its binary/ternary refinement squares against the existing Tesla-compatible independent-fibre null model; commutation pays independence, failure pays a scale/context-coupling obstruction. Do not promote Q9036, the unresolved Tesla 3-6-9 quotation, Wikipedia navigation, OEIS membership, or shared phase language into Monster theorem authority."
