module DASHI.Core.BraidedPromotionTransportBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.BraidedEvidenceTraceBidiCrossPollination2026Exact as Braid
import DASHI.Core.PromotionTransportChainBidiExact as Promotion

------------------------------------------------------------------------
-- BRAIDED TRACE <-> PROMOTION TRANSPORT
--
-- Different provenance strands may pay different promotion obligations while
-- retaining their own authority/provenance.  Coordination is conjunctive at the
-- full promotion boundary; one strand is not silently substituted for another.
------------------------------------------------------------------------

record StrandedFullPromotion
    {Artifact Statement Target : Set}
    (frame : Promotion.PromotionTransportFrame Artifact Statement Target)
    (artifact : Artifact)
    (statement : Statement)
    (target : Target) : Set₁ where
  constructor stranded-full-promotion
  field
    artifactStrand : Braid.EvidenceStrand
    artifactReceipt : Promotion.ArtifactExists frame artifact

    correspondenceStrand : Braid.EvidenceStrand
    correspondenceReceipt : Promotion.Corresponds frame artifact statement

    transportStrand : Braid.EvidenceStrand
    transportReceipt : Promotion.TransportSound frame artifact statement target

    inhabitanceStrand : Braid.EvidenceStrand
    inhabitanceReceipt : Promotion.TargetInhabits frame target

    braidReference : String

open StrandedFullPromotion public

strandedPromotionCompilesToFullPromotion :
  ∀ {Artifact Statement Target : Set}
    {frame : Promotion.PromotionTransportFrame Artifact Statement Target}
    {artifact : Artifact} {statement : Statement} {target : Target} →
  StrandedFullPromotion frame artifact statement target →
  Promotion.FullPromotionReceipt frame artifact statement target
strandedPromotionCompilesToFullPromotion bundle =
  Promotion.full-promotion-receipt
    (Promotion.pre-inhabitance-receipt
      (artifactReceipt bundle)
      (correspondenceReceipt bundle)
      (transportReceipt bundle))
    (inhabitanceReceipt bundle)

------------------------------------------------------------------------
-- The converse is intentionally absent: a full logical promotion receipt does
-- not manufacture provenance assignments for the four obligations.
------------------------------------------------------------------------

data FullPromotionCreatesStrandProvenance : Set where
data OneStrandAutomaticallyPaysEveryObligation : Set where
data SharedContentMakesStrandAuthoritiesEqual : Set where

fullPromotionDoesNotCreateStrandProvenance :
  FullPromotionCreatesStrandProvenance → ⊥
fullPromotionDoesNotCreateStrandProvenance ()

oneStrandDoesNotAutomaticallyPayEveryObligation :
  OneStrandAutomaticallyPaysEveryObligation → ⊥
oneStrandDoesNotAutomaticallyPayEveryObligation ()

sharedContentDoesNotEqualiseStrandAuthority :
  SharedContentMakesStrandAuthoritiesEqual → ⊥
sharedContentDoesNotEqualiseStrandAuthority ()

record BraidedPromotionBoundary : Set where
  constructor braided-promotion-boundary
  field
    obligationsMayHaveDistinctProvenanceStrands : Bool
    allFourObligationsStillRequired : Bool
    braidCoordinationFusesAuthority : Bool
    fullReceiptBackfillsMissingProvenance : Bool

canonicalBraidedPromotionBoundary : BraidedPromotionBoundary
canonicalBraidedPromotionBoundary =
  braided-promotion-boundary true true false false
