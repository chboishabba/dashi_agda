module DASHI.Foundations.TernaryThirteenOriginalSourceRefinementExact where

------------------------------------------------------------------------
-- H2.02 partial: explicit source StageAtlas refinement/permutation
-- commute on the 12+1 central-completion carrier. The centre
-- projection, neutral section and last-coordinate puncture predicate
-- are natural under this chart change. This is NOT the full original
-- 144-cell Grothendieck sheaf-gluing theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Biology.RelationalAppraisalPointedPhaseExact as Rel
import Base369 as Base

-- A nontrivial invertible change of the two first source addresses.
swapFirstTwo : Atlas.StageAtlasZeroToEleven →
               Atlas.StageAtlasZeroToEleven
swapFirstTwo Atlas.atlas-0 = Atlas.atlas-1
swapFirstTwo Atlas.atlas-1 = Atlas.atlas-0
swapFirstTwo Atlas.atlas-2 = Atlas.atlas-2
swapFirstTwo Atlas.atlas-3 = Atlas.atlas-3
swapFirstTwo Atlas.atlas-4 = Atlas.atlas-4
swapFirstTwo Atlas.atlas-5 = Atlas.atlas-5
swapFirstTwo Atlas.atlas-6 = Atlas.atlas-6
swapFirstTwo Atlas.atlas-7 = Atlas.atlas-7
swapFirstTwo Atlas.atlas-8 = Atlas.atlas-8
swapFirstTwo Atlas.atlas-9 = Atlas.atlas-9
swapFirstTwo Atlas.atlas-10 = Atlas.atlas-10
swapFirstTwo Atlas.atlas-11 = Atlas.atlas-11

swapFirstTwoInvolution :
  (axis : Atlas.StageAtlasZeroToEleven) →
  swapFirstTwo (swapFirstTwo axis) ≡ axis
swapFirstTwoInvolution Atlas.atlas-0 = refl
swapFirstTwoInvolution Atlas.atlas-1 = refl
swapFirstTwoInvolution Atlas.atlas-2 = refl
swapFirstTwoInvolution Atlas.atlas-3 = refl
swapFirstTwoInvolution Atlas.atlas-4 = refl
swapFirstTwoInvolution Atlas.atlas-5 = refl
swapFirstTwoInvolution Atlas.atlas-6 = refl
swapFirstTwoInvolution Atlas.atlas-7 = refl
swapFirstTwoInvolution Atlas.atlas-8 = refl
swapFirstTwoInvolution Atlas.atlas-9 = refl
swapFirstTwoInvolution Atlas.atlas-10 = refl
swapFirstTwoInvolution Atlas.atlas-11 = refl

refineValuation :
  Rel.SourceTwelveAxisValuation → Rel.SourceTwelveAxisValuation
refineValuation valuation axis = valuation (swapFirstTwo axis)

refineCentral :
  Rel.SourceCentralCompletionCarrier →
  Rel.SourceCentralCompletionCarrier
refineCentral (valuation , centre) =
  refineValuation valuation , centre

centralProjectionCommutesWithRefinement :
  (state : Rel.SourceCentralCompletionCarrier) →
  Rel.sourceCentralProjection (refineCentral state)
  ≡ refineValuation (Rel.sourceCentralProjection state)
centralProjectionCommutesWithRefinement state = refl

centralCoordinatePreservedByRefinement :
  (state : Rel.SourceCentralCompletionCarrier) →
  Rel.sourceCentralCoordinate (refineCentral state)
  ≡ Rel.sourceCentralCoordinate state
centralCoordinatePreservedByRefinement state = refl

neutralSectionCommutesWithRefinement :
  (valuation : Rel.SourceTwelveAxisValuation) →
  refineCentral (Rel.sourceNeutralSection valuation)
  ≡ Rel.sourceNeutralSection (refineValuation valuation)
neutralSectionCommutesWithRefinement valuation = refl

-- The puncture is the NEUTRAL-FREE central coordinate (not the
-- global origin-puncture). The chart operation cannot change it.
SourceLastCoordinatePunctured :
  Rel.SourceCentralCompletionCarrier → Set
SourceLastCoordinatePunctured state =
  ¬ (Rel.sourceCentralCoordinate state ≡ Base.tri-mid)

punctureRefinementForward :
  (state : Rel.SourceCentralCompletionCarrier) →
  SourceLastCoordinatePunctured state →
  SourceLastCoordinatePunctured (refineCentral state)
punctureRefinementForward state punctured = punctured

punctureRefinementBackward :
  (state : Rel.SourceCentralCompletionCarrier) →
  SourceLastCoordinatePunctured (refineCentral state) →
  SourceLastCoordinatePunctured state
punctureRefinementBackward state punctured = punctured

refineTwicePointwise :
  (valuation : Rel.SourceTwelveAxisValuation)
  (axis : Atlas.StageAtlasZeroToEleven) →
  refineValuation (refineValuation valuation) axis
  ≡ valuation axis
refineTwicePointwise valuation axis =
  cong valuation (swapFirstTwoInvolution axis)
