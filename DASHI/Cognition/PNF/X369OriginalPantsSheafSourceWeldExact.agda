module DASHI.Cognition.PNF.X369OriginalPantsSheafSourceWeldExact where

-- The source already owns ACTUAL central-family sheaf gluing and an
-- ACTUAL heterogeneous typed hyperfabric seam. They are DISTINCT
-- indexed constructions with different compatibility obligations.
-- This module converges the owners without conflating their types.
-- Original Leech-LILA: Anatolii Kornienko; DASHI extension.
-- Agda kernel validation deliberately deferred.
open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_)
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Foundations.TernaryThirteenCentralCompletionBundleSheafExact as Sheaf
import DASHI.Foundations.TernaryThirteenPantsSheafGluingTransportExact as Source13
import DASHI.Foundations.TernaryThirteenOriginalPantsFrontierBridgeExact as Pants13
import DASHI.Topology.TernaryPantsFrontierExact as Frontier
import DASHI.Reasoning.TypedHyperfabricPantsSourceHeterogeneousTransportExact as Heterogeneous
import DASHI.Reasoning.TypedHyperfabricPantsNonvacuousSeamQuotientExact as Seam
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Pants
import DASHI.Reasoning.WavePantsBundleGluingAdapterExact as Wave

-- Reuse exact original sheaf gluing rather than treating it as open.
originalCentralFamilyToPants :
  (locals : Sheaf.CentralLocalFamily) →
  Sheaf.centralFamilyCompatible locals →
  Frontier.PantsPath 13
originalCentralFamilyToPants = Source13.glueCompatibleLocalsToPants

-- Source local sections can be recovered from their actual glued path.
sourceThirteenGlueRestrictsEveryAxis :
  (locals : Sheaf.CentralLocalFamily) →
  (agreement : Sheaf.centralFamilyCompatible locals) →
  (axis : Atlas.StageAtlasZeroToEleven) →
  Sheaf.restrictCentral
    (Pants13.pants13ToSourceCentral
      (originalCentralFamilyToPants locals agreement)) axis
    ≡ locals axis
sourceThirteenGlueRestrictsEveryAxis =
  Source13.originalPantsGlueRestricts

-- The original heterogeneous two-incidence pants seam has already been
-- constructed from original realized five-field InterfaceMatch. We
-- consume the actual owner rather than redoing its topology quotient.
selectedOriginalInterface :
  Pants.InterfaceMatch Pants.selectedChannel2 Pants.innerInputChannel2
selectedOriginalInterface =
  Heterogeneous.OriginalRelationalPants.originalInterface

-- A matched typed semantic seam and a compatible 13-stage sheaf
-- family are independently required. Neither constructor turns an
-- arbitrary original recurrent source tensor into those typed values.
-- The existing wave source demonstrates a zero transport residual and
-- a nonzero phase-change defect; gluing cannot disregard the latter.
originalPhaseDefectAlreadyExhibited :
  Wave.bundleSheafPromotionPaid Wave.wavePantsBundleStatus ≡ false
originalPhaseDefectAlreadyExhibited = Wave.bundlePromotionStillUnpaid

-- Actual needed same-object bridge:
--  * source-owned native adapter from original 369 indexed state into
--    Sheaf.CentralLocalFamily and its matching proof;
--  * actual BranchChannel values for the original heterogeneous
--    source edges plus all five matching predicates;
--  * the real original consumer and successor commuting squares;
--  * retained history/appraisal/centre/zero/provenance after the quotient.
-- This module does not assert arbitrary bundle/sheaf global glue.
