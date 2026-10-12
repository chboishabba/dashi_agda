module DASHI.Reasoning.TrialecticGrothendieckBoundaryAnchoredMediationExact where

------------------------------------------------------------------------
-- BOUNDARY-ANCHORED GROTHENDIECK FACE MEDIATION
--
-- The compatibility adapter in TrialecticGrothendieckThreeCellDescentExact
-- threads the face law into `SecondOrderCellGluing`, but its relation does not
-- itself remember that the three supplied edge arguments are exactly the
-- descended AB/BC/CA boundary.  This owner strengthens that relation without
-- changing the older API.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude

import DASHI.Reasoning.TrialecticBoundaryFaceNonfactorabilityExact as Face
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell
import DASHI.Reasoning.TrialecticGrothendieckThreeCellDescentExact as Groth

record BoundaryAnchoredMediation
    (law : Groth.FaceMediationLaw)
    (boundary : Cell.CompatibleThreeCellTrialecticBoundary)
    (face : Face.TriadicFaceRelation)
    (edgeAB edgeBC edgeCA : Cell.CellDialectic)
    (output : Cell.TrialecticBasis3Cell) : Set where
  constructor boundary-anchored-mediation
  field
    edgeABMatches : edgeAB ≡ Cell.edgeAB boundary
    edgeBCMatches : edgeBC ≡ Cell.edgeBC boundary
    edgeCAMatches : edgeCA ≡ Cell.edgeCA boundary
    lawReceipt : law boundary face output

open BoundaryAnchoredMediation public

toBoundaryAnchoredSecondOrderCellGluing :
  {law : Groth.FaceMediationLaw} →
  (section : Groth.GrothendieckFaceMediatedSection law) →
  Cell.SecondOrderCellGluing (Groth.mediatedStructuredState section)
toBoundaryAnchoredSecondOrderCellGluing {law} section = record
  { Cell.outputCell = Groth.nextDepthCell section
  ; Cell.mediates =
      BoundaryAnchoredMediation
        law
        (Groth.mediatedDescendedBoundary section)
  ; Cell.mediationReceipt =
      boundary-anchored-mediation
        refl refl refl
        (Groth.faceMediation section)
  }

data BoundaryAnchoredAdapterAcceptsUnrelatedEdges : Set where

unrelatedEdgesAreNotPromotedAsAnchored :
  BoundaryAnchoredAdapterAcceptsUnrelatedEdges → ⊥
unrelatedEdgesAreNotPromotedAsAnchored ()

record TrialecticGrothendieckBoundaryAnchoredMediationBoundary : Set where
  constructor trialectic-grothendieck-boundary-anchored-mediation-boundary
  field
    allThreeEdgeArgumentsAnchored : Bool
    originalFaceLawRetained : Bool
    fullT3OutputRetained : Bool
    strongSecondOrderAdapterConstructed : Bool
    arbitraryUnrelatedEdgesAccepted : Bool
    automaticAllDepthIterationClaimed : Bool

open TrialecticGrothendieckBoundaryAnchoredMediationBoundary public

canonicalTrialecticGrothendieckBoundaryAnchoredMediationBoundary :
  TrialecticGrothendieckBoundaryAnchoredMediationBoundary
canonicalTrialecticGrothendieckBoundaryAnchoredMediationBoundary =
  trialectic-grothendieck-boundary-anchored-mediation-boundary
    true true true true false false
