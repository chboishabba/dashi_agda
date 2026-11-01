module DASHI.Physics.Closure.NSTriadKNR414CriticalObservableRealizationNoGoRound513Exact where

------------------------------------------------------------------------
-- ROUND513 / TRAJECTORY INDEXING DOES NOT REALIZE CRITICAL OBSERVABLES
--
-- Introspective collision:
--
-- R414's `CriticalSliceOnLiteralR406 T R terminal cutoff` is indexed by the
-- literal physical trajectory and fixes its remainder to the literal R406
-- integral.  However its remaining critical coordinates are free rationals:
--
--   initialCritical, terminalCritical, criticalDissipation,
--   integratedSignedProduction, viscousCoefficient, absorbedCoefficient.
--
-- Therefore trajectory indexing + literal remainder identity does not by itself
-- produce a receipt that these scalars are the actual physical critical
-- observables of T.  The downstream Clay interpretation distinguishes those
-- states, while the current formal observer need not.
--
-- This module records the logical non-collapse.  It does not modify R414 and
-- does not claim any analytic estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Physics.Closure.NSTriadKNOneCancellationPaysRemainderAndCriticalRound414Exact as R414
import DASHI.Physics.Closure.NSTriadKNR353ToUniformSignedCriticalProductionRound372Exact as R372
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalGalerkinSimonWeldRound104Exact as Simon

data Empty : Set where

record CriticalSliceCapabilityModel : Set₁ where
  field
    TrajectoryIndexedLiteralRemainderSliceReceipt : Set
    PhysicalCriticalObservableRealizationReceipt : Set

open CriticalSliceCapabilityModel public

indexedSliceWithoutPhysicalRealization : CriticalSliceCapabilityModel
indexedSliceWithoutPhysicalRealization = record
  { TrajectoryIndexedLiteralRemainderSliceReceipt = ⊤
  ; PhysicalCriticalObservableRealizationReceipt = Empty
  }

IndexedSliceImpliesPhysicalRealizationForEveryModel : Set₁
IndexedSliceImpliesPhysicalRealizationForEveryModel =
  (M : CriticalSliceCapabilityModel) →
  TrajectoryIndexedLiteralRemainderSliceReceipt M →
  PhysicalCriticalObservableRealizationReceipt M

trajectoryIndexingDoesNotCreatePhysicalCriticalRealization :
  IndexedSliceImpliesPhysicalRealizationForEveryModel → Empty
trajectoryIndexingDoesNotCreatePhysicalCriticalRealization promote =
  promote indexedSliceWithoutPhysicalRealization tt

round513R414FixesLiteralR406Remainder : Bool
round513R414FixesLiteralR406Remainder =
  R414.round414Round104RemainderIsLiteralR406Integral

round513R414TrajectoryIndexAloneRealizesCriticalObservables : Bool
round513R414TrajectoryIndexAloneRealizesCriticalObservables = false

-- Historical regression oracle: R372 already required an explicit same-cutoff
-- physical critical-production realization rather than naming one observable as
-- another.
round513R372RequiresExplicitCriticalProductionRealization : Bool
round513R372RequiresExplicitCriticalProductionRealization =
  R372.round372R303SignedIntegralMustMatchCriticalProductionExplicitly

-- The Simon weld is downstream topology; it does not repair this pre-barrier
-- scalar-realization seam.
round513SimonWeldIsPostBarrier : Bool
round513SimonWeldIsPostBarrier =
  Simon.round104BarrierTopologyBelongsToUniformCriticalBarrier

round513MissingCoordinateIsPhysicalCriticalObservableRealization : Bool
round513MissingCoordinateIsPhysicalCriticalObservableRealization = true

round513ClayPromotion : Bool
round513ClayPromotion = false

round513R414TrajectoryIndexAloneRealizesCriticalObservablesIsFalse :
  round513R414TrajectoryIndexAloneRealizesCriticalObservables ≡ false
round513R414TrajectoryIndexAloneRealizesCriticalObservablesIsFalse = refl

round513R372RequiresExplicitCriticalProductionRealizationIsTrue :
  round513R372RequiresExplicitCriticalProductionRealization ≡ true
round513R372RequiresExplicitCriticalProductionRealizationIsTrue = refl

round513MissingCoordinateIsPhysicalCriticalObservableRealizationIsTrue :
  round513MissingCoordinateIsPhysicalCriticalObservableRealization ≡ true
round513MissingCoordinateIsPhysicalCriticalObservableRealizationIsTrue = refl

round513ClayPromotionIsFalse : round513ClayPromotion ≡ false
round513ClayPromotionIsFalse = refl
