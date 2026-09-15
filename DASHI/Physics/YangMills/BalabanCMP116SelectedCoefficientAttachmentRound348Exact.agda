{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SelectedCoefficientAttachmentRound348Exact where

------------------------------------------------------------------------
-- ROUND348 / REMOVE A FAKE "SELECT THE J DIRECTIONS" OBLIGATION
--
-- R347 correctly leaves a SAME-object attachment between the source/Cauchy
-- coefficient and R318's literal selected two-J mixed-log response.  However,
-- R318 already fixes WHICH source directions are used:
--
--   J_L = sourceDirectionOf (meaning base) left
--   J_R = sourceDirectionOf (meaning base) right.
--
-- There is no remaining theorem that must choose or discover the J pair.
-- The only same-object payment is therefore the scalar/coefficient identity on
-- those already-selected directions:
--
--   source/Cauchy coefficient(J_L,J_R)
--     = literal selected mixed-log response(J_L,J_R).
--
-- This is intentionally weaker than R318's older three-coordinate applicability
-- record: the preferred R346/R347 route already uses the selected connecting root
-- and physical distance directly.  Root and distance source-welds are not
-- reintroduced here.
--
-- Independent live leaves remain:
--   * the selected CMP116 pointwise boundary/substitution comparison;
--   * D_time, selected R318 physical distance = Euclidean spectral time.
--
-- This module is a Pareto frontier refinement only.  It does not inhabit the
-- coefficient identity and does not manufacture R346 L_marked.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116SelectedMarkedBoundaryCutRound347Exact as R347

------------------------------------------------------------------------
-- Existing selected-direction construction.
------------------------------------------------------------------------

selectedJDirectionsAlreadyChosenByR318 : Bool
selectedJDirectionsAlreadyChosenByR318 = true

selectedJDirectionsAlreadyChosenByR318IsTrue :
  selectedJDirectionsAlreadyChosenByR318 ≡ true
selectedJDirectionsAlreadyChosenByR318IsTrue = refl

-- R318's selected carrier stores `meaning`; the selected source directions are
-- obtained by applying `sourceDirectionOf meaning` to the already-selected
-- observables.  This is carrier construction, not an additional physical theorem.
selectedJDirectionConstructionLevel : ProofLevel
selectedJDirectionConstructionLevel = machineChecked

------------------------------------------------------------------------
-- Residual SAME-object payment.
------------------------------------------------------------------------

-- Identify the source/Cauchy Hessian coefficient obtained from the R347 marked
-- boundary theorem with the literal selected mixed-log response on the SAME
-- already-fixed J_L,J_R pair.  The precise coefficient carrier is supplied by
-- the eventual physical/source instantiation; this owner records only the
-- minimal theorem debt and does not guess a source representation.
selectedCoefficientSameObjectLevel : ProofLevel
selectedCoefficientSameObjectLevel = conditional

-- R347's source-specific boundary/substitution comparison remains independent.
selectedMarkedBoundarySubstitutionLevel : ProofLevel
selectedMarkedBoundarySubstitutionLevel =
  R347.selectedBoundarySubstitutionComparisonLevel

-- R346's distance/time semantics remains independent of the scalar coefficient
-- identity.  R318 fixes the physicalDistance function, not its equality to time
-- on R300's selected spectral pair.
selectedDistanceTimeLevel : ProofLevel
selectedDistanceTimeLevel = R347.selectedDistanceTimeMeaningLevel

------------------------------------------------------------------------
-- Pareto firewalls.
------------------------------------------------------------------------

freshDirectionSelectionRequired : Bool
freshDirectionSelectionRequired = false

freshDirectionSelectionRequiredIsFalse :
  freshDirectionSelectionRequired ≡ false
freshDirectionSelectionRequiredIsFalse = refl

sourceRootWeldRequiredByPreferredRoute : Bool
sourceRootWeldRequiredByPreferredRoute = false

sourceRootWeldRequiredByPreferredRouteIsFalse :
  sourceRootWeldRequiredByPreferredRoute ≡ false
sourceRootWeldRequiredByPreferredRouteIsFalse = refl

sourceDistanceWeldRequiredByPreferredRoute : Bool
sourceDistanceWeldRequiredByPreferredRoute = false

sourceDistanceWeldRequiredByPreferredRouteIsFalse :
  sourceDistanceWeldRequiredByPreferredRoute ≡ false
sourceDistanceWeldRequiredByPreferredRouteIsFalse = refl

boundaryComparisonStillIndependent : Bool
boundaryComparisonStillIndependent = true

boundaryComparisonStillIndependentIsTrue :
  boundaryComparisonStillIndependent ≡ true
boundaryComparisonStillIndependentIsTrue = refl

selectedDistanceTimeStillIndependent : Bool
selectedDistanceTimeStillIndependent = true

selectedDistanceTimeStillIndependentIsTrue :
  selectedDistanceTimeStillIndependent ≡ true
selectedDistanceTimeStillIndependentIsTrue = refl

record Round348Boundary : Set where
  constructor round348-boundary
  field
    selectedDirectionsAlreadyConstructed : Bool
    selectedDirectionsAlreadyConstructedIsTrue :
      selectedDirectionsAlreadyConstructed ≡ true

    coefficientSameObjectStillProofBearing : Bool
    coefficientSameObjectStillProofBearingIsTrue :
      coefficientSameObjectStillProofBearing ≡ true

    boundaryComparisonStillProofBearing : Bool
    boundaryComparisonStillProofBearingIsTrue :
      boundaryComparisonStillProofBearing ≡ true

    distanceTimeStillProofBearing : Bool
    distanceTimeStillProofBearingIsTrue :
      distanceTimeStillProofBearing ≡ true

canonicalRound348Boundary : Round348Boundary
canonicalRound348Boundary =
  round348-boundary
    true refl
    true refl
    true refl
    true refl

round348FrontierRefinementLevel : ProofLevel
round348FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
