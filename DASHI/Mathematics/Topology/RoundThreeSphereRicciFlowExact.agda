module DASHI.Mathematics.Topology.RoundThreeSphereRicciFlowExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Richard S. Hamilton,
-- "Three-manifolds with positive Ricci curvature",
-- Journal of Differential Geometry 17 (1982), 255--306.
-- DOI: 10.4310/jdg/1214436922.
--
-- Grisha Perelman,
-- "The entropy formula for the Ricci flow and its geometric applications".
-- DOI: 10.48550/arXiv.math/0211159.
--
-- DASHI CONTRIBUTION
--
-- Add a nontrivial exact smooth-model calculation beside the repository's
-- existing fail-closed Bruhat--Tits/Perelman analogue receipt.  For a round
-- three-sphere under unnormalised Ricci flow, the radius-squared parameter
-- obeys
--
--   r^2(t) = r^2(0) - 4t.
--
-- The semigroup law, constant derivative decrement, and extinction identity at
-- r^2(0)=4T are proved over exact rationals.
--
-- This finite ODE calculation is not short-time existence for arbitrary
-- metrics, entropy monotonicity, kappa-noncollapsing, canonical neighborhoods,
-- surgery continuation or geometrization.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

four six : ℚ
four = (1ℚ + 1ℚ) + (1ℚ + 1ℚ)
six = four + (1ℚ + 1ℚ)

roundRadiusSquared : ℚ → ℚ → ℚ
roundRadiusSquared initialRadiusSquared time =
  initialRadiusSquared - four * time

roundFlowAtZero : ∀ initialRadiusSquared →
  roundRadiusSquared initialRadiusSquared 0ℚ ≡ initialRadiusSquared
roundFlowAtZero initialRadiusSquared = solve (initialRadiusSquared ∷ [])

roundFlowSemigroup : ∀ initialRadiusSquared firstTime secondTime →
  roundRadiusSquared initialRadiusSquared (firstTime + secondTime)
  ≡ roundRadiusSquared
      (roundRadiusSquared initialRadiusSquared firstTime)
      secondTime
roundFlowSemigroup initialRadiusSquared firstTime secondTime =
  solve (initialRadiusSquared ∷ firstTime ∷ secondTime ∷ [])

roundFlowIncrement : ∀ initialRadiusSquared time increment →
  roundRadiusSquared initialRadiusSquared (time + increment)
  - roundRadiusSquared initialRadiusSquared time
  ≡ 0ℚ - four * increment
roundFlowIncrement initialRadiusSquared time increment =
  solve (initialRadiusSquared ∷ time ∷ increment ∷ [])

roundExtinctionAtConfiguredTime : ∀ extinctionTime →
  roundRadiusSquared (four * extinctionTime) extinctionTime ≡ 0ℚ
roundExtinctionAtConfiguredTime extinctionTime =
  solve (extinctionTime ∷ [])

record RoundThreeSphereRicciFlow : Set where
  constructor roundThreeSphereRicciFlow
  field
    initialRadiusSquared : ℚ
    time : ℚ
    radiusSquared : ℚ
    radiusLaw :
      radiusSquared ≡ roundRadiusSquared initialRadiusSquared time
    ricciTensorFactor : ℚ
    scalarCurvatureNumerator : ℚ

open RoundThreeSphereRicciFlow public

canonicalRoundFlow : ℚ → ℚ → RoundThreeSphereRicciFlow
canonicalRoundFlow initialRadiusSquared time = record
  { initialRadiusSquared = initialRadiusSquared
  ; time = time
  ; radiusSquared = roundRadiusSquared initialRadiusSquared time
  ; radiusLaw = solve (initialRadiusSquared ∷ time ∷ [])
  ; ricciTensorFactor = 1ℚ + 1ℚ
  ; scalarCurvatureNumerator = six
  }

record GeneralRicciFlowObligations : Set₁ where
  field
    SmoothManifold : Set
    RiemannianMetric : Set
    ricciTensor : RiemannianMetric → Set
    metricTimeDerivative : RiemannianMetric → Set
    ricciFlowEquation : Set
    shortTimeExistence : Set
    uniquenessModuloDiffeomorphism : Set
    maximalTimeContinuation : Set
    curvatureBlowupCriterion : Set

record PerelmanAnalyticObligations : Set₁ where
  field
    fEntropy : Set
    wEntropy : Set
    entropyMonotonicity : Set
    reducedDistance : Set
    reducedVolume : Set
    reducedVolumeMonotonicity : Set
    kappaNoncollapsing : Set
    pseudolocality : Set
    canonicalNeighborhoodTheorem : Set
    surgeryContinuation : Set
