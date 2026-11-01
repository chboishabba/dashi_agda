module DASHI.Moonshine.OggSSP3BCarnahanOrderNineFixedVectorRefinementExact where

------------------------------------------------------------------------
-- 3B CARNAHAN ORDER-9 FIXED-VECTOR REFINEMENT RECEIPT
--
-- EXTERNAL SOURCE
--
-- Scott Carnahan, "A Self-Dual Integral Form of the Moonshine Module",
-- SIGMA 15 (2019), 030, DOI 10.3842/SIGMA.2019.030.
--
-- In the small-prime modular-moonshine verification Carnahan records that,
-- after the indicated localization/base extension, an order-9 3B-pure group
-- H_3 gives a decomposition of the integral Moonshine form into pieces that
-- embed equivariantly (for the relevant centralizer-normalizer intersection)
-- into the 3B-fixed vectors.
--
-- PURPOSE
--
-- This is a genuine source-native representation-theoretic refinement that a
-- future p=3 bad-level localization should respect.
--
-- ATTRIBUTION FIREWALL
--
-- Carnahan does NOT identify those order-9 pieces with:
--   * the Deligne--Rapoport supersingular node;
--   * the Frobenius/Verschiebung branch-pair orbit;
--   * the two DASHI preferred p=3 sectors;
--   * Urano DVR composition-length-one pieces.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Source attribution.
------------------------------------------------------------------------

carnahanSelfDualIntegralForm : Source.AttributedSource
carnahanSelfDualIntegralForm =
  Source.mkDOISource
    "Scott Carnahan"
    "A Self-Dual Integral Form of the Moonshine Module"
    "Symmetry, Integrability and Geometry: Methods and Applications 15, 030"
    "2019"
    "10.3842/SIGMA.2019.030"
    "https://doi.org/10.3842/SIGMA.2019.030"
    Source.academicArticleSource
    "source for the Monster-stable self-dual integral form, pB Tate/Brauer trace formulas, and the order-9 3B-pure H_3 decomposition into pieces embedding equivariantly into 3B-fixed vectors after the stated base extension; not a source for DASHI Deligne-Rapoport sector identification or sector lengths"
    Source.publicAttribution

carnahanThreeBRefinementSourceAtlas : Source.AttributedSourceAtlas
carnahanThreeBRefinementSourceAtlas =
  Source.mkSourceAtlas
    "Carnahan 3B order-nine fixed-vector refinement"
    "DASHI.Moonshine.OggSSP3BCarnahanOrderNineFixedVectorRefinementExact"
    (carnahanSelfDualIntegralForm ∷ [])
    "records only the source-backed 3B-pure order-nine decomposition/fixed-vector embedding surface; geometric node/branch interpretation remains a separate DASHI obligation"

------------------------------------------------------------------------
-- 2. Abstract source receipt.
--
-- We intentionally do not invent the source's internal piece classifier.
-- The receipt records only the existence/relationship actually used in the
-- published argument.
------------------------------------------------------------------------

record ThreeBOrderNineFixedVectorRefinementReceipt : Set where
  constructor three-b-order-nine-fixed-vector-refinement-receipt
  field
    orderNineThreeBPureGroupUsed : Bool
    integralMoonshineFormDecomposesIntoPieces : Bool
    piecesEmbedIntoThreeBFixedVectors : Bool
    embeddingIsEquivariantForRelevantNormalizerIntersection : Bool
    statementRequiresLocalizedBaseExtension : Bool

    piecesIdentifiedWithDeligneRapoportNodeBranchSectors : Bool
    piecesHaveUranoLengthOneBySource : Bool
    sourceProvidesTwoPieceClassification : Bool

canonicalThreeBOrderNineFixedVectorRefinementReceipt :
  ThreeBOrderNineFixedVectorRefinementReceipt
canonicalThreeBOrderNineFixedVectorRefinementReceipt =
  three-b-order-nine-fixed-vector-refinement-receipt
    true true true true true
    false false false

------------------------------------------------------------------------
-- 3. No unsupported promotion.
------------------------------------------------------------------------

data OrderNinePiecesAreDeligneRapoportSectors : Set where
data FixedVectorEmbeddingDeterminesTwoLocalPieces : Set where
data OrderNinePiecesHaveUranoLengthOne : Set where
data EquivariantEmbeddingIsIgusaLocalization : Set where

orderNinePiecesNotIdentifiedWithDRSectors :
  OrderNinePiecesAreDeligneRapoportSectors -> ⊥
orderNinePiecesNotIdentifiedWithDRSectors ()

fixedVectorEmbeddingDoesNotDetermineTwoLocalPieces :
  FixedVectorEmbeddingDeterminesTwoLocalPieces -> ⊥
fixedVectorEmbeddingDoesNotDetermineTwoLocalPieces ()

orderNinePiecesNotGivenUranoLengthOne :
  OrderNinePiecesHaveUranoLengthOne -> ⊥
orderNinePiecesNotGivenUranoLengthOne ()

equivariantEmbeddingIsNotPrimeLevelIgusaLocalization :
  EquivariantEmbeddingIsIgusaLocalization -> ⊥
equivariantEmbeddingIsNotPrimeLevelIgusaLocalization ()

------------------------------------------------------------------------
-- 4. Live boundary.
------------------------------------------------------------------------

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryFormalReconstruction

record ThreeBCarnahanOrderNineRefinementBoundary : Set where
  constructor three-b-carnahan-order-nine-refinement-boundary
  field
    carnahanSourceExplicitlyAttributed : Bool
    orderNineThreeBPureGroupSourced : Bool
    integralPieceDecompositionSourced : Bool
    equivariantFixedVectorEmbeddingSourced : Bool
    baseExtensionQualificationRetained : Bool
    nodeBranchSectorIdentificationSourced : Bool
    twoPieceClassificationSourced : Bool
    uranoLengthOneSourced : Bool
    attributionFirewallPreserved : Bool

canonicalThreeBCarnahanOrderNineRefinementBoundary :
  ThreeBCarnahanOrderNineRefinementBoundary
canonicalThreeBCarnahanOrderNineRefinementBoundary =
  three-b-carnahan-order-nine-refinement-boundary
    true true true true true false false false true
