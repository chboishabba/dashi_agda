module DASHI.Crypto.FiniteMLWETransitionGeometryExact where

------------------------------------------------------------------------
-- FINITE MLWE SEARCH TRANSITION GEOMETRY
--
-- Same four secret candidates, same two-bit rate, different traversal geometry.
-- The Gray traversal changes one secret bit per step; ordinary binary order has
-- a two-bit middle jump.  This is the candidate-search analogue of the Wave4
-- representation result and does not change the candidate set itself.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Crypto.FiniteMLWEVectorLabExact as Lab
import DASHI.Crypto.GrayPathTransitionOptimalExact as Gray
import DASHI.Crypto.ProtectedLabelSearchGeometryExact as Geometry

bitDistance : Lab.Secret2 → Lab.Secret2 → Nat
bitDistance a b =
  Gray.bitDiff (Lab.s0 a) (Lab.s0 b) +
  Gray.bitDiff (Lab.s1 a) (Lab.s1 b)

binaryTraversalCost : Nat
binaryTraversalCost =
  bitDistance Lab.s00 Lab.s01 +
  bitDistance Lab.s01 Lab.s10 +
  bitDistance Lab.s10 Lab.s11

binaryTraversalCostIs4 : binaryTraversalCost ≡ 4
binaryTraversalCostIs4 = refl

grayTraversalCost : Nat
grayTraversalCost =
  bitDistance Lab.s00 Lab.s01 +
  bitDistance Lab.s01 Lab.s11 +
  bitDistance Lab.s11 Lab.s10

grayTraversalCostIs3 : grayTraversalCost ≡ 3
grayTraversalCostIs3 = refl

sameCandidatesSameRateDifferentTransitionCost : Geometry.SameInformationDifferentGeometry
sameCandidatesSameRateDifferentTransitionCost =
  Geometry.sameInformationDifferentGeometry
    Lab.Secret2
    Gray.Bit2
    Gray.Bit2
    (λ s → Gray.bit2 (Lab.s0 s) (Lab.s1 s))
    (λ s → Gray.bit2 (Lab.s0 s) (Lab.s1 s))
    4 2 2 refl
    binaryTraversalCost grayTraversalCost

------------------------------------------------------------------------
-- Incremental residual update regression.
--
-- Candidate residuals are t-A*s'.  Along the one-bit Gray move s00 -> s01,
-- only one candidate coordinate changes; the resulting residual is exactly the
-- precomputed lab residual for s01.  The theorem is intentionally same-object
-- and finite rather than assuming a generic linear-update API.
------------------------------------------------------------------------

residualAt00 : Lab.Error2
residualAt00 = Lab.candidateResidual Lab.public22 Lab.s00

residualAfterGrayStep01 : Lab.Error2
residualAfterGrayStep01 = Lab.candidateResidual Lab.public22 Lab.s01

grayStep00to01ResidualExact :
  residualAfterGrayStep01 ≡ Lab.e01
grayStep00to01ResidualExact = refl

scoreDropsOnFirstGrayStep :
  Lab.candidateScore Lab.public22 Lab.s00 ≡ 2
  × Lab.candidateScore Lab.public22 Lab.s01 ≡ 0
scoreDropsOnFirstGrayStep = refl , refl

------------------------------------------------------------------------
-- Observation-induced geometry change on the same lab.
------------------------------------------------------------------------

labGeometryBeforeAfter : Geometry.GeometricObservationUpdate
labGeometryBeforeAfter =
  Geometry.geometricObservationUpdate
    2 1
    3 0
    5 3
    2

labGeometryObservationGain : Geometry.GeometryImprovement labGeometryBeforeAfter
labGeometryObservationGain = Geometry.geometryImprovement 3 refl
