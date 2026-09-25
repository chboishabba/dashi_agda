module DASHI.Reasoning.TrialecticGrothendieckThreeCellDescentExact where

------------------------------------------------------------------------
-- GROTHENDIECK DESCENT FOR STRUCTURED TRIALECTIC 27-CELLS
--
-- DASHI CONTRIBUTION
--
-- Reuse the existing nontrivial relational Grothendieck site:
--
--             U_AB   U_BC   U_CA
-- overlaps:      A      B      C
--
-- and instantiate RelationalStageTwelveSiteExact.TriadicRelationalSheaf with:
--
--   EdgeSection   = CellDialectic = (T^3)^3 = T^9
--   VertexSection = TrialecticBasis3Cell = T^3
--   GlobalSection = CompatibleThreeCellTrialecticBoundary = T^18
--
-- Thus the previously constructed six-cell boundary is not merely a tuple:
-- its three T^9 edge sections agree on the shared T^3 participant stalks and
-- glue to a global T^18 boundary section over the canonical Grothendieck cover.
--
-- The irreducible triadic face is deliberately NOT reconstructed by this
-- one-skeleton descent.  The existing relational site has no separate triple-
-- intersection object, and Trialectic369CechGrothendieckComparisonExact
-- explicitly keeps the face distinct from the Base369 hypercube corner.
--
-- A face-mediated next-depth synthesis therefore requires an attached
-- higher-coordinate receipt after ordinary Grothendieck descent.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Foundations.RelationalStageTwelveSiteExact as RelSheaf
import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Groth
import DASHI.Reasoning.Trialectic369CechGrothendieckComparisonExact as Compare
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell
import DASHI.Reasoning.TrialecticBoundaryFaceNonfactorabilityExact as Face

------------------------------------------------------------------------
-- 1. Exact overlap system for structured cell dialectics.
------------------------------------------------------------------------

cellOverlapSystem :
  RelSheaf.TriadicOverlapSystem
    Cell.CellDialectic
    Cell.TrialecticBasis3Cell
cellOverlapSystem =
  RelSheaf.triadic-overlap-system
    Cell.leftCell
    Cell.rightCell
    Cell.rightCell
    Cell.leftCell
    Cell.rightCell
    Cell.leftCell

------------------------------------------------------------------------
-- 2. Local sections extracted from a global structured boundary.
------------------------------------------------------------------------

restrictStructuredAB :
  Cell.CompatibleThreeCellTrialecticBoundary →
  Cell.CellDialectic
restrictStructuredAB = Cell.edgeAB

restrictStructuredBC :
  Cell.CompatibleThreeCellTrialecticBoundary →
  Cell.CellDialectic
restrictStructuredBC = Cell.edgeBC

restrictStructuredCA :
  Cell.CompatibleThreeCellTrialecticBoundary →
  Cell.CellDialectic
restrictStructuredCA = Cell.edgeCA

structuredLocals :
  Cell.CompatibleThreeCellTrialecticBoundary →
  RelSheaf.TriadicLocals Cell.CellDialectic
structuredLocals boundary =
  RelSheaf.triadic-locals
    (Cell.edgeAB boundary)
    (Cell.edgeBC boundary)
    (Cell.edgeCA boundary)

structuredCompatibility :
  (boundary : Cell.CompatibleThreeCellTrialecticBoundary) →
  RelSheaf.CompatibleOnTriadicCover
    cellOverlapSystem
    (structuredLocals boundary)
structuredCompatibility boundary =
  RelSheaf.compatible-on-triadic-cover
    (sym (Cell.aShared boundary))
    (Cell.bShared boundary)
    (Cell.cShared boundary)

------------------------------------------------------------------------
-- 3. Glue compatible local T^9 dialectics to one T^18 boundary section.
------------------------------------------------------------------------

glueStructured :
  (locals : RelSheaf.TriadicLocals Cell.CellDialectic) →
  RelSheaf.CompatibleOnTriadicCover cellOverlapSystem locals →
  Cell.CompatibleThreeCellTrialecticBoundary
glueStructured locals compatibility =
  Cell.compatible-three-cell-trialectic-boundary
    (RelSheaf.localAB locals)
    (RelSheaf.localBC locals)
    (RelSheaf.localCA locals)
    (RelSheaf.agreesAtB compatibility)
    (RelSheaf.agreesAtC compatibility)
    (sym (RelSheaf.agreesAtA compatibility))

glueStructuredRestrictsAB :
  (locals : RelSheaf.TriadicLocals Cell.CellDialectic) →
  (compatibility :
    RelSheaf.CompatibleOnTriadicCover cellOverlapSystem locals) →
  restrictStructuredAB (glueStructured locals compatibility)
  ≡ RelSheaf.localAB locals
glueStructuredRestrictsAB locals compatibility = refl

glueStructuredRestrictsBC :
  (locals : RelSheaf.TriadicLocals Cell.CellDialectic) →
  (compatibility :
    RelSheaf.CompatibleOnTriadicCover cellOverlapSystem locals) →
  restrictStructuredBC (glueStructured locals compatibility)
  ≡ RelSheaf.localBC locals
glueStructuredRestrictsBC locals compatibility = refl

glueStructuredRestrictsCA :
  (locals : RelSheaf.TriadicLocals Cell.CellDialectic) →
  (compatibility :
    RelSheaf.CompatibleOnTriadicCover cellOverlapSystem locals) →
  restrictStructuredCA (glueStructured locals compatibility)
  ≡ RelSheaf.localCA locals
glueStructuredRestrictsCA locals compatibility = refl

structuredCellTriadicSheaf :
  RelSheaf.TriadicRelationalSheaf
    Cell.CellDialectic
    Cell.TrialecticBasis3Cell
    Cell.CompatibleThreeCellTrialecticBoundary
structuredCellTriadicSheaf = record
  { RelSheaf.overlaps = cellOverlapSystem
  ; RelSheaf.restrictGlobalAB = restrictStructuredAB
  ; RelSheaf.restrictGlobalBC = restrictStructuredBC
  ; RelSheaf.restrictGlobalCA = restrictStructuredCA
  ; RelSheaf.glue = glueStructured
  ; RelSheaf.glueRestrictsAB = glueStructuredRestrictsAB
  ; RelSheaf.glueRestrictsBC = glueStructuredRestrictsBC
  ; RelSheaf.glueRestrictsCA = glueStructuredRestrictsCA
  }

structuredGlueRoundTrip :
  (boundary : Cell.CompatibleThreeCellTrialecticBoundary) →
  RelSheaf.glue structuredCellTriadicSheaf
    (structuredLocals boundary)
    (structuredCompatibility boundary)
  ≡ boundary
structuredGlueRoundTrip
  (Cell.compatible-three-cell-trialectic-boundary
    ab bc ca shareB shareC shareA)
  = refl

------------------------------------------------------------------------
-- 4. The sheaf instance lives over the already-proved Grothendieck cover.
------------------------------------------------------------------------

relationalGrothendieckCover :
  Groth.RelCover Groth.triadicRelationalSieve
relationalGrothendieckCover =
  Groth.triadicRelationalSieveCovers

grothendieckSiteBoundary :
  Groth.RelationalStageTwelveGrothendieckBoundary
grothendieckSiteBoundary =
  Groth.canonicalRelationalStageTwelveGrothendieckBoundary

cechGrothendieckBoundary :
  Compare.Trialectic369CechGrothendieckComparisonBoundary
cechGrothendieckBoundary =
  Compare.canonicalTrialectic369CechGrothendieckComparisonBoundary

------------------------------------------------------------------------
-- 5. Attach the irreducible face after ordinary one-skeleton descent.
------------------------------------------------------------------------

record FaceAttachedGlobalSection : Set where
  constructor face-attached-global-section
  field
    descendedBoundary :
      Cell.CompatibleThreeCellTrialecticBoundary
    attachedFace :
      Face.TriadicFaceRelation

open FaceAttachedGlobalSection public

toStructuredTrialecticState :
  FaceAttachedGlobalSection →
  Cell.StructuredTrialecticState
toStructuredTrialecticState section =
  Cell.structured-trialectic-state
    (descendedBoundary section)
    (attachedFace section)

sameDescentDifferentFaceLeft :
  FaceAttachedGlobalSection
sameDescentDifferentFaceLeft =
  face-attached-global-section
    Cell.canonicalCompatibleThreeCellBoundary
    Face.reciprocalFace

sameDescentDifferentFaceRight :
  FaceAttachedGlobalSection
sameDescentDifferentFaceRight =
  face-attached-global-section
    Cell.canonicalCompatibleThreeCellBoundary
    Face.underdeterminedFace

descendedBoundaryObserver :
  FaceAttachedGlobalSection →
  Cell.CompatibleThreeCellTrialecticBoundary
descendedBoundaryObserver = descendedBoundary

attachedFaceConsumer :
  FaceAttachedGlobalSection →
  Face.TriadicFaceRelation
attachedFaceConsumer = attachedFace

sameDescendedBoundary :
  descendedBoundaryObserver sameDescentDifferentFaceLeft
  ≡ descendedBoundaryObserver sameDescentDifferentFaceRight
sameDescendedBoundary = refl

differentAttachedFace :
  attachedFaceConsumer sameDescentDifferentFaceLeft
  ≡ attachedFaceConsumer sameDescentDifferentFaceRight
  →
  ⊥
differentAttachedFace ()

grothendieckBoundaryDescentDoesNotRecoverFace :
  Descent.FactorsThrough
    descendedBoundaryObserver
    attachedFaceConsumer
  →
  ⊥
grothendieckBoundaryDescentDoesNotRecoverFace =
  Descent.nonDescentWitnessBlocksFactorization
    (Descent.consumerNonDescentWitness
      sameDescentDifferentFaceLeft
      sameDescentDifferentFaceRight
      sameDescendedBoundary
      differentAttachedFace)

------------------------------------------------------------------------
-- 6. Face-mediated global section.
--
-- This is the precise replacement for treating "synthesis of syntheses" as an
-- automatic map.  First the three edge sections descend over the Grothendieck
-- cover.  Then a separate face-level mediation law may select a full next-depth
-- T^3 / 27-state cell.
------------------------------------------------------------------------

FaceMediationLaw : Set₁
FaceMediationLaw =
  Cell.CompatibleThreeCellTrialecticBoundary →
  Face.TriadicFaceRelation →
  Cell.TrialecticBasis3Cell →
  Set

record GrothendieckFaceMediatedSection
    (law : FaceMediationLaw) : Set₁ where
  constructor grothendieck-face-mediated-section
  field
    localSections :
      RelSheaf.TriadicLocals Cell.CellDialectic

    localCompatibility :
      RelSheaf.CompatibleOnTriadicCover
        cellOverlapSystem
        localSections

    face :
      Face.TriadicFaceRelation

    nextDepthCell :
      Cell.TrialecticBasis3Cell

    faceMediation :
      law
        (glueStructured localSections localCompatibility)
        face
        nextDepthCell

open GrothendieckFaceMediatedSection public

mediatedDescendedBoundary :
  {law : FaceMediationLaw} →
  GrothendieckFaceMediatedSection law →
  Cell.CompatibleThreeCellTrialecticBoundary
mediatedDescendedBoundary section =
  glueStructured
    (localSections section)
    (localCompatibility section)

mediatedStructuredState :
  {law : FaceMediationLaw} →
  GrothendieckFaceMediatedSection law →
  Cell.StructuredTrialecticState
mediatedStructuredState section =
  Cell.structured-trialectic-state
    (mediatedDescendedBoundary section)
    (face section)

------------------------------------------------------------------------
-- 7. Convert the Grothendieck-mediated section into the existing conditional
-- second-order carry interface without inventing a second semantics.
------------------------------------------------------------------------

toSecondOrderCellGluing :
  {law : FaceMediationLaw} →
  (section : GrothendieckFaceMediatedSection law) →
  Cell.SecondOrderCellGluing (mediatedStructuredState section)
toSecondOrderCellGluing {law} section = record
  { Cell.outputCell = nextDepthCell section
  ; Cell.mediates =
      λ face edgeAB edgeBC edgeCA output →
        law
          (Cell.compatible-three-cell-trialectic-boundary
            edgeAB edgeBC edgeCA
            (RelSheaf.agreesAtB (localCompatibility section))
            (RelSheaf.agreesAtC (localCompatibility section))
            (sym (RelSheaf.agreesAtA (localCompatibility section))))
          face
          output
  ; Cell.mediationReceipt = faceMediation section
  }

------------------------------------------------------------------------
-- 8. Boundary.
------------------------------------------------------------------------

record TrialecticGrothendieckThreeCellDescentBoundary : Set where
  constructor trialectic-grothendieck-three-cell-descent-boundary
  field
    existingGrothendieckSiteReused : Bool
    existingTriadicSheafInterfaceReused : Bool
    edgeSectionsAreT9CellDialectics : Bool
    overlapSectionsAreT3ParticipantCells : Bool
    compatibleLocalsGlueToT18Boundary : Bool
    globalRestrictionsRecoverAllThreeLocals : Bool
    irreducibleFaceRecoveredByOneSkeletonDescent : Bool
    faceMediationRequiresAdditionalReceipt : Bool
    mediatedOutputIsFullT3Cell : Bool
    relationalSiteHasTripleIntersectionObject : Bool
    certifiedHigherStackOrHypersheafClaimed : Bool

canonicalTrialecticGrothendieckThreeCellDescentBoundary :
  TrialecticGrothendieckThreeCellDescentBoundary
canonicalTrialecticGrothendieckThreeCellDescentBoundary =
  trialectic-grothendieck-three-cell-descent-boundary
    true
    true
    true
    true
    true
    true
    false
    true
    true
    false
    false
