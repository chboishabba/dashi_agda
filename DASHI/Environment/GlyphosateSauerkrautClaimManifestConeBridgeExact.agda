module DASHI.Environment.GlyphosateSauerkrautClaimManifestConeBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Reasoning.ClaimAuditManifestExact as Manifest
import DASHI.Reasoning.ClaimManifestExperimentConeBridgeExact as Bridge
import DASHI.Environment.GlyphosateSauerkrautAssertionPNFConeExact as Claim

------------------------------------------------------------------------
-- SHIOCTON CLAIM MANIFEST
------------------------------------------------------------------------

shioctonObligationAudits : List PNF.ObligationAudit
shioctonObligationAudits =
  PNF.obligationAudit
    Claim.resultObligation
    PNF.discharged
    "Harle et al. 2024 Table 10"
    "reported bounded TEG values are directly represented"
  ∷ PNF.obligationAudit
    Claim.timeObligation
    PNF.discharged
    "reported sampling dates"
    "non-contemporaneous dates are retained explicitly"
  ∷ PNF.obligationAudit
    Claim.causalObligation
    PNF.partiallyDischarged
    "gross difference plus DASHI one-sided residual envelope"
    "headline decline constrains but does not point-identify the RSKJ causal contribution"
  ∷ PNF.obligationAudit
    Claim.mechanismObligation
    PNF.unresolved
    "no mechanism-isolation receipt"
    "specific LAB mechanism remains unverified by the headline residue contrast"
  ∷ []

shioctonReceipts : List Manifest.TypedClaimReceipt
shioctonReceipts =
  Manifest.typedClaimReceipt
    Manifest.outcomeReceipt
    Manifest.installed
    "Harle et al. 2024 Table 10"
    "TEG 207.26 -> 26.59 ng/g at source scope"
  ∷ Manifest.typedClaimReceipt
    Manifest.associationReceipt
    Manifest.installed
    "reported treatment plus longitudinal residue observation"
    "treatment-associated observation only"
  ∷ Manifest.typedClaimReceipt
    Manifest.causalReceipt
    Manifest.partiallyInstalled
    "one-sided residual causal envelope"
    "incremental RSKJ component remains bounded rather than point-identified"
  ∷ Manifest.typedClaimReceipt
    Manifest.mechanismReceipt
    Manifest.missing
    "no specific LAB mechanism isolation receipt"
    "introduced LAB, indigenous microbiome, chemistry/sorption and combined mechanisms remain distinct"
  ∷ Manifest.typedClaimReceipt
    Manifest.transportReceipt
    Manifest.unresolved
    "single bounded site/result surface"
    "no universal soil/site transport claim"
  ∷ []

shioctonSourceChain : List Manifest.SourceChainCoordinate
shioctonSourceChain =
  Manifest.sourceChainCoordinate
    Manifest.publishedSurface
    "Harle et al. 2024, HortScience 59(11), Table 10"
    true
    "published result surface recovered"
  ∷ Manifest.sourceChainCoordinate
    Manifest.citedPrimaryStudy
    "DOI 10.21273/HORTSCI18041-24"
    true
    "primary paper identified and audited at the bounded design/result level"
  ∷ Manifest.sourceChainCoordinate
    Manifest.underlyingDatasetOrArtifact
    "raw replicate-level soil-residue dataset"
    false
    "not installed in this claim lane"
  ∷ Manifest.sourceChainCoordinate
    Manifest.independentReproduction
    "independent replication"
    false
    "not installed"
  ∷ []

shioctonManifest : Manifest.ManifestClaim
shioctonManifest = Manifest.manifestClaim
  "harle-2024-shiocton-table10-teg"
  "Harle et al. 2024 soil remediation result"
  Claim.shioctonExactResultText
  Claim.shioctonPNF
  (Manifest.ordinaryConsequence ∷ Manifest.causalConsequence ∷ [])
  shioctonSourceChain
  shioctonReceipts
  shioctonObligationAudits
  Manifest.sourceMatches
  Manifest.independentPartiallyAdmissible
  Manifest.designAudited
  Claim.boundedCausalEnvelopeAssertion
  "Measured decline is supported; RSKJ causal contribution is only bounded/qualified; full causal and specific LAB mechanism promotions remain blocked."

shioctonManifestConeBridge :
  Bridge.ManifestConeBridge Claim.shioctonManifest Claim.shioctonNaturalAssertion
shioctonManifestConeBridge = Bridge.manifestConeBridge
  refl
  Claim.shioctonDesignMap
  refl
  Claim.shioctonCone
  refl
  "backward-safe assertion is the bounded residual causal envelope rather than the full causal slogan"
  "published surface and primary study recovered; raw dataset/independent reproduction remain open"
  "outcome/time discharged; causal partial; mechanism unresolved"
  "safe implication cone stops before full causal attribution and specific LAB mechanism"

exactPublishedTextLinkedToCone :
  Manifest.exactPublishedText shioctonManifest
  ≡ Claim.Cone.exactText Claim.shioctonNaturalAssertion
exactPublishedTextLinkedToCone =
  Bridge.manifestExactTextReachesConeSource shioctonManifestConeBridge

record GlyphosateManifestConeBoundary : Set where
  constructor glyphosateManifestConeBoundary
  field
    exactTextPNFDesignConeAreLinked : Bool
    exactTextPNFDesignConeAreLinkedIsTrue :
      exactTextPNFDesignConeAreLinked ≡ true
    backwardSafeAssertionEqualsFullCausalClaim : Bool
    backwardSafeAssertionEqualsFullCausalClaimIsFalse :
      backwardSafeAssertionEqualsFullCausalClaim ≡ false
    unresolvedMechanismReceiptMayRemainInManifest : Bool
    unresolvedMechanismReceiptMayRemainInManifestIsTrue :
      unresolvedMechanismReceiptMayRemainInManifest ≡ true

canonicalGlyphosateManifestConeBoundary : GlyphosateManifestConeBoundary
canonicalGlyphosateManifestConeBoundary =
  glyphosateManifestConeBoundary true refl false refl true refl
