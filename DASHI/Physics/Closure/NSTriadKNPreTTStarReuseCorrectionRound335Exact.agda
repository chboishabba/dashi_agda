module DASHI.Physics.Closure.NSTriadKNPreTTStarReuseCorrectionRound335Exact where

------------------------------------------------------------------------
-- ROUND335 / BIDI CORRECTION: PRE-TT* AND DELAYED ABSOLUTE VALUE ARE OLD
--
-- The new object is the heat-weighted nested R294/R326 forcing remainder.
-- The proof-search principles are not new:
--
-- * R29 already owns a signed pre-TT* cross-shell aggregation theorem;
-- * the delayed-positive-part owner already makes atomwise magnitude a lossy
--   fallback;
-- * R179 already says same-output cells must be summed before absolute values;
-- * R74 already records the Cotlar--Stein authority boundary: aggregation does
--   not manufacture the missing physical pairwise overlap theorem.
--
-- Therefore the absolute row/column Schur route developed in R329--R334 stays
-- useful as a diagnostic/fallback, but it is not the highest-alpha route once
-- the physical signed aggregate F_s is available.  The new live leaf is only:
--
--   heat-weighted nested physical pairwise overlap
--
-- on the literal R329 carrier, before any l1 majorization.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Admission
import DASHI.Physics.Closure.NSTriadKNSignedCrossShellAlmostOrthogonalityRound29Exact as R29
import DASHI.Physics.Closure.NSTriadKNDelayedPositivePartRound29Exact as Delay
import DASHI.Physics.Closure.NSTriadKNCotlarSteinAggregationBoundaryRound74Exact as R74
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNStrongLowRowColumnFrontierRound334Exact as R334

absoluteRowSchurDisposition : Admission.RouteDisposition
absoluteRowSchurDisposition = Admission.redirectedReuse

heatWeightedNestedPairwiseOverlapDisposition : Admission.RouteDisposition
heatWeightedNestedPairwiseOverlapDisposition = Admission.admitted

round335PreTTStarSignedAggregationAlreadyOwned : Bool
round335PreTTStarSignedAggregationAlreadyOwned =
  R29.crossShellAlmostOrthogonalityScalarCoreClosed

round335DelayedPositiveTaxAlreadyOwned : Bool
round335DelayedPositiveTaxAlreadyOwned =
  Delay.delayedPositivePartArchitectureClosed

round335SameOutputBeforeAbsoluteAlreadyOwned : Bool
round335SameOutputBeforeAbsoluteAlreadyOwned =
  R179.round179SignedGramCrossTermIsNextOwner

round335CotlarAggregationManufacturesPhysicalPairwiseOverlap : Bool
round335CotlarAggregationManufacturesPhysicalPairwiseOverlap =
  R74.round74AggregateEndpointImpliesPairwiseSixThreeEnvelope

round335PhysicalPairwiseOverlapStillNeedsProducer : Bool
round335PhysicalPairwiseOverlapStillNeedsProducer =
  R74.round74PhysicalPairwiseSixThreeOverlapStillRequired

round335R334AbsoluteSchurRouteRetainedAsDiagnostic : Bool
round335R334AbsoluteSchurRouteRetainedAsDiagnostic = true

round335AbsoluteRowSchurHighestAlpha : Bool
round335AbsoluteRowSchurHighestAlpha = false

round335HeatWeightedNestedPairwiseOverlapHighestAlpha : Bool
round335HeatWeightedNestedPairwiseOverlapHighestAlpha = true

round335PackageAClosed : Bool
round335PackageAClosed = false

round335ClayPromotion : Bool
round335ClayPromotion = false

round335PreTTStarSignedAggregationAlreadyOwnedIsTrue :
  round335PreTTStarSignedAggregationAlreadyOwned ≡ true
round335PreTTStarSignedAggregationAlreadyOwnedIsTrue = refl

round335AbsoluteRowSchurHighestAlphaIsFalse :
  round335AbsoluteRowSchurHighestAlpha ≡ false
round335AbsoluteRowSchurHighestAlphaIsFalse = refl

round335PackageAClosedIsFalse : round335PackageAClosed ≡ false
round335PackageAClosedIsFalse = refl

round335ClayPromotionIsFalse : round335ClayPromotion ≡ false
round335ClayPromotionIsFalse = refl
