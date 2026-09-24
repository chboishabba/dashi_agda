module DASHI.Physics.Closure.NSOpenAI2026ReleasedRankGeometryRefreshExact where

------------------------------------------------------------------------
-- NATIVE PORT: MeanStageRegularity.rankGeometry_for_state
--
-- Source:
--   NavierStokes/MeanStageRegularity.lean
--
-- The released theorem reuses every state-independent rank-geometry field and
-- refreshes only the measured-debt smoothness from the new PrimitiveData.
-- This module ports exactly that dependency shape.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- 1. Split the rank geometry into static geometry and state-dependent debt.
------------------------------------------------------------------------

record ReleasedRankStaticGeometry : Set₁ where
  field
    PrimitiveInnerPositive : Set
    ExponentPositive : Set
    LambdaPositive : Set
    InnerPositive : Set
    InnerBelowOuter : Set
    CoefficientNonzero : Set
    LengthPositive : Set
    VelocityNonzero : Set
    CoefficientSmooth : Set
    LengthSmooth : Set
    VelocitySmooth : Set
    GaugeLengthPositive : Set
    GaugeLeftControl : Set
    GaugeRightControl : Set
    AngularModel : Set
    AxialModel : Set

    primitiveInnerPositive : PrimitiveInnerPositive
    exponentPositive : ExponentPositive
    lambdaPositive : LambdaPositive
    innerPositive : InnerPositive
    innerBelowOuter : InnerBelowOuter
    coefficientNonzero : CoefficientNonzero
    lengthPositive : LengthPositive
    velocityNonzero : VelocityNonzero
    coefficientSmooth : CoefficientSmooth
    lengthSmooth : LengthSmooth
    velocitySmooth : VelocitySmooth
    gaugeLengthPositive : GaugeLengthPositive
    gaugeLeftControl : GaugeLeftControl
    gaugeRightControl : GaugeRightControl
    angularModel : AngularModel
    axialModel : AxialModel

open ReleasedRankStaticGeometry public

record ReleasedRankGeometrySurface : Set₁ where
  field
    State : Set
    DebtSmooth : State → Set

open ReleasedRankGeometrySurface public

record ReleasedRankGeometry
    (S : ReleasedRankGeometrySurface)
    (u : State S) : Set₁ where
  field
    staticGeometry : ReleasedRankStaticGeometry
    debtSmooth : DebtSmooth S u

open ReleasedRankGeometry public

------------------------------------------------------------------------
-- 2. Primitive data need only reproduce debt smoothness at the target state.
------------------------------------------------------------------------

record ReleasedDebtSmoothRule
    (S : ReleasedRankGeometrySurface) : Set₁ where
  field
    PrimitiveData : State S → Set

    debtSmoothFromPrimitive :
      (u : State S) →
      PrimitiveData u →
      DebtSmooth S u

open ReleasedDebtSmoothRule public

------------------------------------------------------------------------
-- 3. Native rankGeometry_for_state.
------------------------------------------------------------------------

rankGeometryForState :
  ∀ {S} →
  (R : ReleasedDebtSmoothRule S) →
  {u v : State S} →
  PrimitiveData R u →
  ReleasedRankGeometry S v →
  ReleasedRankGeometry S u
rankGeometryForState R {u} H geometry =
  record
    { staticGeometry = staticGeometry geometry
    ; debtSmooth = debtSmoothFromPrimitive R u H
    }

------------------------------------------------------------------------
-- 4. All static coordinates are preserved definitionally.
------------------------------------------------------------------------

rankGeometryStaticPreserved :
  ∀ {S} →
  (R : ReleasedDebtSmoothRule S) →
  {u v : State S} →
  (H : PrimitiveData R u) →
  (geometry : ReleasedRankGeometry S v) →
  staticGeometry (rankGeometryForState R H geometry)
  ≡ staticGeometry geometry
rankGeometryStaticPreserved R H geometry = refl

rankGeometryDebtRefreshed :
  ∀ {S} →
  (R : ReleasedDebtSmoothRule S) →
  {u v : State S} →
  (H : PrimitiveData R u) →
  (geometry : ReleasedRankGeometry S v) →
  debtSmooth (rankGeometryForState R H geometry)
  ≡ debtSmoothFromPrimitive R u H
rankGeometryDebtRefreshed R H geometry = refl

------------------------------------------------------------------------
-- 5. Source-level trust ledger.
------------------------------------------------------------------------

rankGeometryRefreshBodyPorted : Bool
rankGeometryRefreshBodyPorted = true

rankGeometryStaticFieldsReused : Bool
rankGeometryStaticFieldsReused = true

rankGeometryDebtSmoothnessIsOnlyStateDependentField : Bool
rankGeometryDebtSmoothnessIsOnlyStateDependentField = true

actualDebtSmoothAnalysisPopulatedHere : Bool
actualDebtSmoothAnalysisPopulatedHere = false

rankGeometryRefreshBodyPortedIsTrue :
  rankGeometryRefreshBodyPorted ≡ true
rankGeometryRefreshBodyPortedIsTrue = refl

rankGeometryStaticFieldsReusedIsTrue :
  rankGeometryStaticFieldsReused ≡ true
rankGeometryStaticFieldsReusedIsTrue = refl

rankGeometryDebtSmoothnessIsOnlyStateDependentFieldIsTrue :
  rankGeometryDebtSmoothnessIsOnlyStateDependentField ≡ true
rankGeometryDebtSmoothnessIsOnlyStateDependentFieldIsTrue = refl

actualDebtSmoothAnalysisPopulatedHereIsFalse :
  actualDebtSmoothAnalysisPopulatedHere ≡ false
actualDebtSmoothAnalysisPopulatedHereIsFalse = refl
