module DASHI.Foundations.TernaryThirteenPantsSheafGluingTransportExact where

------------------------------------------------------------------------
-- H2.02: transport the ACTUAL source StageBundleSheaf matching/glue
-- to the ORIGINAL TernaryPantsFrontier depth-13 carrier.
--
-- This gives a constructive gluing map into the pants frontier
-- and a pointwise matching-family reconstruction theorem.
-- The selected 13th branch is preserved and can remain neutral.
-- Pants boundary-channel InterfaceMatch on a typed hyperfabric
-- remains a separate uninhabited semantic edge-stalk obligation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Foundations.TernaryThirteenCentralCompletionBundleSheafExact as Sheaf
import DASHI.Foundations.TernaryThirteenOriginalPantsFrontierBridgeExact as Pants
import DASHI.Biology.RelationalAppraisalPointedPhaseExact as Rel
import DASHI.Topology.TernaryPantsFrontierExact as Frontier
import DASHI.Topology.TernaryCylinderPantsGeometryExact as Junction
import Base369 as Base

-- Compatible source local sections assemble the SAME state whose
-- original ternary pants path is obtained by choosing the common
-- centre as the thirteenth branch.
glueCompatibleLocalsToPants :
  (locals : Sheaf.CentralLocalFamily) →
  Sheaf.centralFamilyCompatible locals →
  Frontier.PantsPath 13
glueCompatibleLocalsToPants locals matching =
  Pants.sourceCentralToPants13 (Sheaf.glueCentral locals matching)

gluedPantsSelectsCommonCentralBranch :
  (locals : Sheaf.CentralLocalFamily)
  (matching : Sheaf.centralFamilyCompatible locals) →
  glueCompatibleLocalsToPants locals matching
  ≡
  Frontier.appendSlot
    (Pants.wordToPants 12
      (DASHI.Foundations.TernaryThirteenOriginalAxisValuationBridgeExact.valuationToWord
        (λ axis → proj₁ (locals axis))))
    (Pants.tritToSlot
      (DASHI.Foundations.TernaryThirteenOriginalAxisValuationBridgeExact.fromSource
        (proj₂ (locals Atlas.atlas-0))))
gluedPantsSelectsCommonCentralBranch locals matching =
  Pants.originalTwelvePlusOnePantsGluing
    (λ axis → proj₁ (locals axis))
    (proj₂ (locals Atlas.atlas-0))

-- Restricting the original source state reconstructed from its
-- pants endpoint retrieves every compatible local value. This is
-- pointwise and avoids requiring equality between functions.
originalPantsGlueRestricts :
  (locals : Sheaf.CentralLocalFamily)
  (matching : Sheaf.centralFamilyCompatible locals)
  (axis : Atlas.StageAtlasZeroToEleven) →
  Sheaf.restrictCentral
    (Pants.pants13ToSourceCentral
      (glueCompatibleLocalsToPants locals matching))
    axis
  ≡ locals axis
originalPantsGlueRestricts locals matching axis =
  trans
    (cong₂ _,_
      (Pants.sourcePantsRoundTripOnAxis
        (Sheaf.glueCentral locals matching) axis)
      (Pants.sourcePantsRoundTripOnCentre
        (Sheaf.glueCentral locals matching)))
    (Sheaf.centralGlueRestricts locals matching axis)

-- The original neutral section gives a real legal pants path.
-- There is no automatic puncture at depth 13.
neutralGlobalPantsLastSlot :
  (valuation : Rel.SourceTwelveAxisValuation) →
  Pants.sourceCentralToPants13
    (Rel.sourceNeutralSection valuation)
  ≡
  Frontier.appendSlot
    (Pants.wordToPants 12
      (DASHI.Foundations.TernaryThirteenOriginalAxisValuationBridgeExact.valuationToWord valuation))
    Junction.slot6
neutralGlobalPantsLastSlot =
  Pants.originalCentralBranchNeutral
