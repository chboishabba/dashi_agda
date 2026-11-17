module DASHI.Physics.Gravity.KSW668F8AugmentedOriginRadialFVIntertwinerExact where

------------------------------------------------------------------------
-- XXXVII: SAME original F8 radial FV induced operator on physical H.
-- Reuses original first-interior FV coefficients, not a new stencil.
--
-- H_(ell,j) = (j*h/eps)^ell V_(ell,j) for ell=0,2,4.
-- For ell>0, H_0=0 for ALL V_0, but the original d=7 or 11
-- finite-volume row at j=1 contains the nonzero term cm_d*V_0.
-- Consequently H nodal values alone do not determine evolution
-- of H_1; an origin trace V_0 must be carried in the intertwiner.
--
-- At j=1, set lambda=(h/eps)^ell, H1=lambda V1,
-- H2=2^ell lambda V2. The ORIGINAL radial FV induces
-- lambda L_d V1 = cp_d*(H2/2^ell-H1)
--                    -cm_d*(H1-lambda V0).
--
-- At any interior j>=2, the exact induced operator uses
-- (j/(j+1))^ell, (j/(j-1))^ell as positive ratios.
-- This is a finite rational operator correspondence, not a
-- non-flat curvature theorem, full tensor TT invariance or
-- moving P/M/U SSPRK3 stability. Pinned Agda kernel NOT RUN.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.Gravity.KSW668AdS5TTFiniteVolumeFirstCellRationalExact as FV

four sixteen : ℚ
four = (+ 4) / 1
sixteen = (+ 16) / 1

originalFirstRow :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
originalFirstRow cp cm v0 v1 v2 =
  cp * (v2 + - v1) + - (cm * (v1 + - v0))

physicalFirstRowWithOrigin :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
physicalFirstRowWithOrigin cp cm ellFactor lambda origin h1 h2 =
  cp * (ellFactor * h2 + - h1)
    + - (cm * (h1 + - (lambda * origin)))

-- At ell=2 and ell=4: ellFactor=1/2^ell.
originalEll2FirstRowIntertwines :
  (lambda v0 v1 v2 : ℚ) →
  lambda * originalFirstRow FV.d7Plus FV.d7Minus v0 v1 v2
  ≡ physicalFirstRowWithOrigin
      FV.d7Plus FV.d7Minus ((+ 1) / 4) lambda v0
      (lambda * v1) (four * lambda * v2)
originalEll2FirstRowIntertwines lambda v0 v1 v2 = solve []

originalEll4FirstRowIntertwines :
  (lambda v0 v1 v2 : ℚ) →
  lambda * originalFirstRow FV.d11Plus FV.d11Minus v0 v1 v2
  ≡ physicalFirstRowWithOrigin
      FV.d11Plus FV.d11Minus ((+ 1) / 16) lambda v0
      (lambda * v1) (sixteen * lambda * v2)
originalEll4FirstRowIntertwines lambda v0 v1 v2 = solve []

-- The origin trace is essential: let H1=H2=0 and V0=1.
-- The actual induced H_1 force is nonzero.
ell2UnrecoverableOriginContribution :
  physicalFirstRowWithOrigin FV.d7Plus FV.d7Minus
      ((+ 1) / 4) ((+ 1) / 1) ((+ 1) / 1) 0ℚ 0ℚ
    ≡ (+ 7) / 1093
ell2UnrecoverableOriginContribution = solve []

ell4UnrecoverableOriginContribution :
  physicalFirstRowWithOrigin FV.d11Plus FV.d11Minus
      ((+ 1) / 16) ((+ 1) / 1) ((+ 1) / 1) 0ℚ 0ℚ
    ≡ (+ 11) / 88573
ell4UnrecoverableOriginContribution = solve []

-- For j>=2 use general dimensionless ratios encoded as rational
-- multipliers. No division by the physical origin coordinate needed.
-- Given Hprev=alpha Vprev, H=beta V, Hnext=gamma Vnext,
-- the induced row is determined by H and their nonzero factors.
genericInteriorAugmentedReconstruction :
  (cp cm alpha beta gamma vprev v vnext : ℚ) →
  beta * originalFirstRow cp cm vprev v vnext
  ≡ cp * ((beta * vnext) + - (beta * v))
    + - (cm * ((beta * v) + - (beta * vprev)))
genericInteriorAugmentedReconstruction
  cp cm alpha beta gamma vprev v vnext = solve []

-- A rational interior formula using explicitly supplied reconstruction
-- ratios (lambdaNext=lambda_j/lambda_(j+1),
-- lambdaPrev=lambda_j/lambda_(j-1)).
interiorInducedRow : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
interiorInducedRow cp cm nextRatio prevRatio hprev h hnext =
  cp * (nextRatio * hnext + - h)
    + - (cm * (h + - (prevRatio * hprev)))

-- A general quantitative defect equation for imperfect reconstruction
-- ratios: the entire interior discrepancy is the two face-coefficient
-- mismatches, not an unknown tensor curvature residual.
interiorOperatorDefect :
  (cp cm lambda lambdaPrev lambdaNext
    nextRatio prevRatio vprev v vnext : ℚ) →
  interiorInducedRow cp cm nextRatio prevRatio
    (lambdaPrev * vprev) (lambda * v) (lambdaNext * vnext)
    + - (lambda * originalFirstRow cp cm vprev v vnext)
  ≡ cp * ((nextRatio * lambdaNext + - lambda) * vnext)
    + cm * ((prevRatio * lambdaPrev + - lambda) * vprev)
interiorOperatorDefect cp cm lambda lambdaPrev lambdaNext
  nextRatio prevRatio vprev v vnext = solve []

-- Zero origin multiplier destroys injectivity. Keeping V0 as an
-- additional datum restores an exact operator correspondence.
originReconstructionAlwaysZero :
  (lambda origin : ℚ) →
  0ℚ * lambda * origin ≡ 0ℚ
originReconstructionAlwaysZero lambda origin = solve []

-- Original evolving U,P,M characteristic fields use the SAME
-- radial reconstruction factor lambda_j at all normal nodes and
-- at every T. Therefore their linear nonradial stage equations
-- (normal derivative, warp force, advection and SAT numerator)
-- are homogeneous under this factor, assuming the physical
-- source is scaled by the SAME lambda_j.
--
-- At a frozen stage the original wave force is
-- force = radial - 3*(P-M)/(2*z).
-- Parametrize invz=1/z externally to avoid variable division.
originalWarpForce : ℚ → ℚ → ℚ → ℚ → ℚ
originalWarpForce radial p m invz =
  radial + - (((+ 3) / 2) * invz * (p + - m))

warpForceScalesWithReconstruction :
  (lambda radial p m invz : ℚ) →
  originalWarpForce (lambda * radial)
    (lambda * p) (lambda * m) invz
    ≡ lambda * originalWarpForce radial p m invz
warpForceScalesWithReconstruction lambda radial p m invz = solve []

-- outU=.5*((1+v)P+(1-v)M), exactly as original stage().
originalUStage : ℚ → ℚ → ℚ → ℚ
originalUStage v p m =
  ((+ 1) / 2) * ((1ℚ + v) * p + (1ℚ + - v) * m)

originalUStageScales :
  (lambda v p m : ℚ) →
  originalUStage v (lambda * p) (lambda * m)
    ≡ lambda * originalUStage v p m
originalUStageScales lambda v p m = solve []

-- The original normal_order=3 stage bulk normal derivatives and
-- radial/warp force have linear characteristic dependence.
-- dpNormal and dmNormal are the ACTUAL normal stencil outputs.
originalPStage : ℚ → ℚ → ℚ → ℚ
originalPStage v dpNormal force = (1ℚ + v) * dpNormal + force
originalMStage : ℚ → ℚ → ℚ → ℚ
originalMStage v dmNormal force = (v + - 1ℚ) * dmNormal + force

originalPStageScales :
  (lambda v dpNormal force : ℚ) →
  originalPStage v (lambda * dpNormal) (lambda * force)
    ≡ lambda * originalPStage v dpNormal force
originalPStageScales lambda v dpNormal force = solve []

originalMStageScales :
  (lambda v dmNormal force : ℚ) →
  originalMStage v (lambda * dmNormal) (lambda * force)
    ≡ lambda * originalMStage v dmNormal force
originalMStageScales lambda v dmNormal force = solve []

-- Lower weak-Israel SAT correction
--   2*(1-v)/dy *(target-M), i.e. with invdy=1/dy.
originalMSATStage : ℚ → ℚ → ℚ → ℚ → ℚ
originalMSATStage v invdy target m =
  ((+ 2) / 1) * (1ℚ + - v) * invdy * (target + - m)

originalMSATStageScales :
  (lambda v invdy target m : ℚ) →
  originalMSATStage v invdy (lambda * target) (lambda * m)
  ≡ lambda * originalMSATStage v invdy target m
originalMSATStageScales lambda v invdy target m = solve []

-- Upper P penalty -2(1+v)P/dy has the same homogeneity.
originalPSATOuter : ℚ → ℚ → ℚ → ℚ
originalPSATOuter v invdy p =
  - (((+ 2) / 1) * (1ℚ + v) * invdy * p)

originalPSATOuterScales :
  (lambda v invdy p : ℚ) →
  originalPSATOuter v invdy (lambda * p)
    ≡ lambda * originalPSATOuter v invdy p
originalPSATOuterScales lambda v invdy p = solve []
