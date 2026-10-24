{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityPostScalarR136ReuseMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119AntigravityPostScalarVacuumMaxCutExact as Direct
import DASHI.Physics.Foundations.CMP119AntigravityR136ToStaticVacuumPromotionExact as R136Static
import DASHI.Physics.Foundations.CMP119AntigravityR136StaticPairToDifferentialExact as R136Pair

------------------------------------------------------------------------
-- POST-SCALAR ROUTE-SENSITIVE MAX-CUT
--
-- Direct static path:
--   V -> extensive density/volume -> metric response -> E/L continuation.
--
-- R136 reuse path:
--   V + already-paid same-state R136/Local-C Lorentzian vacuum readout
--     -> affine V->rho calibration + common cosmological convention
--     -> static receipt.
--
-- Consequently the direct extensivity/metric-response leaves remain real only
-- when the direct route is chosen.  They must not be charged a second time to a
-- consumer that already possesses the R136/Local-C physical vacuum receipt.
------------------------------------------------------------------------

directStaticExtensivityRouteRemainsValid : Bool
directStaticExtensivityRouteRemainsValid = true

r136ReuseRouteRemainsValid : Bool
r136ReuseRouteRemainsValid = true

metricFamilyDifferentiabilityRequiredOnDirectRoute : Bool
metricFamilyDifferentiabilityRequiredOnDirectRoute =
  Direct.metricFamilyDifferentiabilityStillRequired

metricFamilyDifferentiabilityRequiredAfterR136VacuumPromotion : Bool
metricFamilyDifferentiabilityRequiredAfterR136VacuumPromotion = false

sameStateRenormalizedMetricResponseRequiredOnDirectRoute : Bool
sameStateRenormalizedMetricResponseRequiredOnDirectRoute =
  Direct.renormalizedMetricResponseSameStateStillRequired

sameStateRenormalizedMetricResponseRequiredAfterR136VacuumPromotion : Bool
sameStateRenormalizedMetricResponseRequiredAfterR136VacuumPromotion =
  R136Static.independentStaticMetricResponseReceiptRequiredAfterR136Promotion

sameStateEuclideanLorentzianContinuationRequiredOnDirectRoute : Bool
sameStateEuclideanLorentzianContinuationRequiredOnDirectRoute =
  Direct.sameStateEuclideanLorentzianContinuationStillRequired

sameStateEuclideanLorentzianContinuationRequiredAfterR136VacuumPromotion : Bool
sameStateEuclideanLorentzianContinuationRequiredAfterR136VacuumPromotion = false

affineNormalizationToGravityCalibrationRequiredOnR136ReuseRoute : Bool
affineNormalizationToGravityCalibrationRequiredOnR136ReuseRoute =
  R136Static.affineNormalizationToGravityCalibrationStillRequired

commonCosmologicalRenormalizationRequiredOnR136ReuseRoute : Bool
commonCosmologicalRenormalizationRequiredOnR136ReuseRoute = true

independentDifferentialSameObjectTheoremRequiredAfterCommonR136Pair : Bool
independentDifferentialSameObjectTheoremRequiredAfterCommonR136Pair =
  R136Pair.independentDeltaSameObjectTheoremRequiredAfterCommonR136Pair

representationOnlySameObjectDebtAfterR136VacuumPromotion : Bool
representationOnlySameObjectDebtAfterR136VacuumPromotion = false

record PostScalarR136ReuseFrontier : Set where
  constructor post-scalar-r136-reuse-frontier
  field
    directRouteStillAvailable : Bool
    r136ReuseAvailable : Bool
    directMetricDifferentiabilityOpen : Bool
    r136MetricDifferentiabilityRecharged : Bool
    directMetricResponseOpen : Bool
    r136MetricResponseRecharged : Bool
    directELContinuationOpen : Bool
    r136ELContinuationRecharged : Bool
    r136AffineCalibrationOpen : Bool
    r136CommonRenormalizationOpen : Bool
    extraDeltaSameObjectTheoremOpenAfterCommonR136Pair : Bool

canonicalPostScalarR136ReuseFrontier : PostScalarR136ReuseFrontier
canonicalPostScalarR136ReuseFrontier =
  post-scalar-r136-reuse-frontier
    true true true false true false true false true true false

representationOnlySameObjectDebtAfterR136VacuumPromotionIsFalse :
  representationOnlySameObjectDebtAfterR136VacuumPromotion ≡ false
representationOnlySameObjectDebtAfterR136VacuumPromotionIsFalse = refl
