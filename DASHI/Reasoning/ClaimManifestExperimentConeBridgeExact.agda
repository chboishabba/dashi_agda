module DASHI.Reasoning.ClaimManifestExperimentConeBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.ClaimAuditManifestExact as Manifest
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone

------------------------------------------------------------------------
-- CLAIM MANIFEST <-> EXPERIMENTAL ASSERTION / PNF / IMPLICATION CONE
--
-- The manifest owns exact published wording, source-chain/audit maturity and a
-- backward-safe assertion. The experimental cone owns design placement and
-- downstream implication structure. This bridge requires literal linkage of
-- the exact text and compiled PNF object; no key/name coincidence is enough.
------------------------------------------------------------------------

record ManifestConeBridge
    (manifest : Manifest.ManifestClaim)
    (source : Cone.NaturalLanguageExperimentalAssertion) : Set₁ where
  constructor manifestConeBridge
  field
    exactTextLinked :
      Manifest.exactPublishedText manifest ≡ Cone.exactText source

    designMap : Cone.AssertionDesignMap source

    compiledPNFLinked :
      Cone.compiled (Cone.compilation designMap)
      ≡ Manifest.normalizedAssertion manifest

    implicationCone : Cone.ExperimentalImplicationCone source

    coneUsesSameDesignMap :
      Cone.designMap implicationCone ≡ designMap

    backwardSafeAssertionReference : String
    sourceChainReference : String
    obligationCoverageReference : String
    implicationBoundaryReference : String

open ManifestConeBridge public

manifestExactTextReachesConeSource :
  ∀ {manifest source} →
  ManifestConeBridge manifest source →
  Manifest.exactPublishedText manifest ≡ Cone.exactText source
manifestExactTextReachesConeSource = exactTextLinked

manifestPNFReachesDesignMap :
  ∀ {manifest source} →
  (bridge : ManifestConeBridge manifest source) →
  Cone.compiled (Cone.compilation (designMap bridge))
  ≡ Manifest.normalizedAssertion manifest
manifestPNFReachesDesignMap = compiledPNFLinked

record ManifestConeBoundary : Set where
  constructor manifestConeBoundary
  field
    sameClaimKeyAloneLinksRepresentations : Bool
    sameClaimKeyAloneLinksRepresentationsIsFalse :
      sameClaimKeyAloneLinksRepresentations ≡ false
    exactPublishedTextMustBeLinked : Bool
    exactPublishedTextMustBeLinkedIsTrue :
      exactPublishedTextMustBeLinked ≡ true
    compiledPNFMustBeLinked : Bool
    compiledPNFMustBeLinkedIsTrue :
      compiledPNFMustBeLinked ≡ true
    implicationConeReplacesBackwardSafeAssertion : Bool
    implicationConeReplacesBackwardSafeAssertionIsFalse :
      implicationConeReplacesBackwardSafeAssertion ≡ false

canonicalManifestConeBoundary : ManifestConeBoundary
canonicalManifestConeBoundary =
  manifestConeBoundary false refl true refl true refl false refl
