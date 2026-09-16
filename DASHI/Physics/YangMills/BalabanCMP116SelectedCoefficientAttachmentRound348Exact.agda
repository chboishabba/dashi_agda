{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SelectedCoefficientAttachmentRound348Exact where

------------------------------------------------------------------------
-- ROUND348 / REMOVE A FAKE "SELECT THE J DIRECTIONS" OBLIGATION
--
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
-- The preferred R346 route already uses the selected connecting root and
-- physical distance directly.  Root and abstract source-distance welds are not
-- reintroduced here.
--
-- NOTE (R380 audit): an earlier draft imported a non-existent
-- `BalabanCMP116SelectedMarkedBoundaryFrontierRound347Exact`.  The only facts
-- consumed from that stale name were status projections already owned by R346:
-- literal selected differentiated localization and physical-distance/time
-- semantics.  This owner now depends on R346 directly.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116SharedMarkedAmplitudeDirectRound346Exact as R346

------------------------------------------------------------------------
-- Existing selected-direction construction.
------------------------------------------------------------------------

selectedJDirectionsAlreadyChosenByR318 : Bool
selectedJDirectionsAlreadyChosenByR318 = true

selectedJDirectionsAlreadyChosenByR318IsTrue :
  selectedJDirectionsAlreadyChosenByR318 ≡ true
selectedJDirectionsAlreadyChosenByR318IsTrue = refl

selectedJDirectionConstructionLevel : ProofLevel
selectedJDirectionConstructionLevel = machineChecked

------------------------------------------------------------------------
-- Residual SAME-object payment.
------------------------------------------------------------------------

-- Identify the source/Cauchy Hessian coefficient with the literal selected
-- mixed-log response on the SAME already-fixed J_L,J_R pair.  The precise
-- coefficient carrier is supplied by the eventual physical/source
-- instantiation; this owner records only the minimal theorem debt and does not
-- guess a source representation.
selectedCoefficientSameObjectLevel : ProofLevel
selectedCoefficientSameObjectLevel = conditional

-- R346's literal selected differentiated-localization theorem remains the
-- actual source-facing physical inequality.
selectedMarkedBoundarySubstitutionLevel : ProofLevel
selectedMarkedBoundarySubstitutionLevel =
  R346.round346LiteralSelectedLocalizationLevel

-- R346's distance/time semantics remains independent of the scalar coefficient
-- identity.  R318 fixes the physicalDistance function, not its equality to time
-- on the selected spectral pair.
selectedDistanceTimeLevel : ProofLevel
selectedDistanceTimeLevel =
  R346.round346SelectedPhysicalDistanceMeaningLevel

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

literalSelectedLocalizationStillIndependent : Bool
literalSelectedLocalizationStillIndependent = true

literalSelectedLocalizationStillIndependentIsTrue :
  literalSelectedLocalizationStillIndependent ≡ true
literalSelectedLocalizationStillIndependentIsTrue = refl

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

    literalSelectedLocalizationStillProofBearing : Bool
    literalSelectedLocalizationStillProofBearingIsTrue :
      literalSelectedLocalizationStillProofBearing ≡ true

    distanceTimeStillProofBearing : Bool
    distanceTimeStillProofBearingIsTrue :
      distanceTimeStillProofBearing ≡ true

canonicalRound348Boundary : Round348Boundary
canonicalRound348Boundary =
  round348-boundary true refl true refl true refl true refl

round348FrontierRefinementLevel : ProofLevel
round348FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
