module DASHI.Physics.Closure.NSTriadKNHHGoodPhysicalThresholdStretchingRound38Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- Indiana University Mathematics Journal 42 (1993), 775--789.
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Push the Round-37/38 HH-good geometry through the actual good-threshold
-- inequality on a physical amplitude-weighted vorticity pair.
--
-- If
--
--   omega_s = a xi,   omega_t = b eta,
--   |xi|=|eta|=1,
--   Theta(xi,eta) <= delta,
--
-- then the exact physical directional identity gives
--
--   |omega_s x omega_t|^2 = a^2 b^2 Theta,
--
-- while the corrected strain estimate gives, for unit separation direction
-- theta,
--
--   |omega_t . S_theta(omega_s) omega_t|^2
--      <= |omega_t|^2 |omega_s x omega_t|^2.
--
-- Hence this module proves the fully amplitude-weighted good gain
--
--   |stretch|^2 <= delta * a^2 * b^4.
--
-- The small parameter is therefore already attached to the literal nonlinear
-- stretching scalar before PV integration.  The remaining A3/A4 problem is
-- the periodic singular-kernel/shell/time integration, not a missing local
-- geometric smallness theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNFourierBiotSavartExact as BS
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalDirectionalDefectExact as Physical
import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNVortexStretchingGeometricFactorRound37Exact as Stretch
import DASHI.Physics.Closure.NSTriadKNVortexStretchingDirectionalBoundRound37Exact as Bound

------------------------------------------------------------------------
-- The physical-direction module and the strain module use the same rational
-- R^3 coordinates under two record names.  Keep the conversion explicit.
------------------------------------------------------------------------

toV : Gram.Vec3 → V.Vector3
toV vector = V.v3 (Gram.x vector) (Gram.y vector) (Gram.z vector)

normMeaning : ∀ vector →
  V.normSquared (toV vector) ≡ Gram.normSquared vector
normMeaning vector = refl

crossNormMeaning : ∀ left right →
  V.normSquared (BS.cross (toV left) (toV right))
  ≡ Gram.crossNormSquared left right
crossNormMeaning left right = refl

sourceVector targetVector : Physical.PhysicalVorticityPair → V.Vector3
sourceVector pair = toV (Physical.leftVorticity pair)
targetVector pair = toV (Physical.rightVorticity pair)

targetNormSquaredExact : ∀ pair →
  V.normSquared (targetVector pair)
  ≡ L2.square (Physical.rightAmplitude pair)
targetNormSquaredExact pair =
  trans
    (normMeaning (Physical.rightVorticity pair))
    (trans
      (Physical.scaledNormSquared
        (Physical.rightAmplitude pair)
        (Gram.right (Physical.directions pair)))
      (cong
        (L2.square (Physical.rightAmplitude pair) *_)
        (Gram.rightUnit (Physical.directions pair))))

sourceTargetCrossSquaredExact : ∀ pair →
  V.normSquared (BS.cross (sourceVector pair) (targetVector pair))
  ≡
  L2.square (Physical.leftAmplitude pair)
    * L2.square (Physical.rightAmplitude pair)
    * Gram.directionalDefect (Physical.directions pair)
sourceTargetCrossSquaredExact pair =
  trans
    (crossNormMeaning
      (Physical.leftVorticity pair)
      (Physical.rightVorticity pair))
    (Physical.physicalDirectionalDefectIdentity pair)

stretchingSquarePhysicalDirectionalDefect :
  ∀ theta pair →
  V.normSquared theta ≡ 1ℚ →
  L2.square
    (Stretch.stretchingScalar theta (sourceVector pair) (targetVector pair))
  ≤
  L2.square (Physical.leftAmplitude pair)
    * L2.square (Physical.rightAmplitude pair)
    * L2.square (Physical.rightAmplitude pair)
    * Gram.directionalDefect (Physical.directions pair)
stretchingSquarePhysicalDirectionalDefect theta pair thetaUnit =
  let
    raw = Bound.stretchingSquareControlledByCrossMisalignment
      theta (sourceVector pair) (targetVector pair) thetaUnit

    rewrittenUpper :
      V.normSquared (targetVector pair)
        * V.normSquared (BS.cross (sourceVector pair) (targetVector pair))
      ≡
      L2.square (Physical.leftAmplitude pair)
        * L2.square (Physical.rightAmplitude pair)
        * L2.square (Physical.rightAmplitude pair)
        * Gram.directionalDefect (Physical.directions pair)
    rewrittenUpper =
      trans
        (cong
          (λ targetNorm →
            targetNorm
              * V.normSquared
                  (BS.cross (sourceVector pair) (targetVector pair)))
          (targetNormSquaredExact pair))
        (trans
          (cong
            (L2.square (Physical.rightAmplitude pair) *_)
            (sourceTargetCrossSquaredExact pair))
          (solve
            ( L2.square (Physical.leftAmplitude pair)
            ∷ L2.square (Physical.rightAmplitude pair)
            ∷ Gram.directionalDefect (Physical.directions pair)
            ∷ [])))
  in
  subst
    (λ upper →
      L2.square
        (Stretch.stretchingScalar theta (sourceVector pair) (targetVector pair))
      ≤ upper)
    rewrittenUpper
    raw

record PhysicalHHGoodPair
    (parameter : Threshold.PositiveThreshold) : Set where
  constructor physical-hh-good-pair
  field
    pair : Physical.PhysicalVorticityPair
    goodThreshold :
      Gram.directionalDefect (Physical.directions pair)
      ≤ Threshold.threshold parameter

open PhysicalHHGoodPair public

amplitudeQuarticWeight : Physical.PhysicalVorticityPair → ℚ
amplitudeQuarticWeight pair =
  L2.square (Physical.leftAmplitude pair)
  * L2.square (Physical.rightAmplitude pair)
  * L2.square (Physical.rightAmplitude pair)

amplitudeQuarticWeightNonnegative : ∀ pair →
  0ℚ ≤ amplitudeQuarticWeight pair
amplitudeQuarticWeightNonnegative pair =
  L2.nonnegativeProductMonotone
    (L2.nonnegativeProductMonotone
      (L2.squareNonnegative (Physical.leftAmplitude pair))
      (L2.squareNonnegative (Physical.rightAmplitude pair))
      (L2.squareNonnegative (Physical.leftAmplitude pair))
      (L2.squareNonnegative (Physical.rightAmplitude pair))
      ℚP.≤-refl ℚP.≤-refl)
    (L2.squareNonnegative (Physical.rightAmplitude pair))
    (L2.nonnegativeProductMonotone
      (L2.squareNonnegative (Physical.leftAmplitude pair))
      (L2.squareNonnegative (Physical.rightAmplitude pair))
      (L2.squareNonnegative (Physical.leftAmplitude pair))
      (L2.squareNonnegative (Physical.rightAmplitude pair))
      ℚP.≤-refl ℚP.≤-refl)
    (L2.squareNonnegative (Physical.rightAmplitude pair))
    ℚP.≤-refl ℚP.≤-refl

goodPhysicalStretchingThresholdBound :
  ∀ theta parameter →
  (good : PhysicalHHGoodPair parameter) →
  V.normSquared theta ≡ 1ℚ →
  L2.square
    (Stretch.stretchingScalar theta
      (sourceVector (pair good))
      (targetVector (pair good)))
  ≤
  Threshold.threshold parameter * amplitudeQuarticWeight (pair good)
goodPhysicalStretchingThresholdBound theta parameter good thetaUnit =
  let
    physical = pair good
    weight = amplitudeQuarticWeight physical

    localBound :
      L2.square
        (Stretch.stretchingScalar theta
          (sourceVector physical) (targetVector physical))
      ≤ weight * Gram.directionalDefect (Physical.directions physical)
    localBound =
      subst
        (λ upper →
          L2.square
            (Stretch.stretchingScalar theta
              (sourceVector physical) (targetVector physical))
          ≤ upper)
        (solve
          ( L2.square (Physical.leftAmplitude physical)
          ∷ L2.square (Physical.rightAmplitude physical)
          ∷ Gram.directionalDefect (Physical.directions physical)
          ∷ []))
        (stretchingSquarePhysicalDirectionalDefect theta physical thetaUnit)

    thresholdWeighted :
      weight * Gram.directionalDefect (Physical.directions physical)
      ≤ weight * Threshold.threshold parameter
    thresholdWeighted =
      L2.nonnegativeProductMonotone
        (amplitudeQuarticWeightNonnegative physical)
        (Gram.directionalDefectNonnegative (Physical.directions physical))
        (amplitudeQuarticWeightNonnegative physical)
        (Threshold.thresholdNonnegative parameter)
        ℚP.≤-refl
        (goodThreshold good)
  in
  ℚP.≤-trans
    localBound
    (subst
      (λ upper →
        weight * Gram.directionalDefect (Physical.directions physical)
        ≤ upper)
      (solve (weight ∷ Threshold.threshold parameter ∷ []))
      thresholdWeighted)

hhGoodPhysicalThresholdStretchingClosed : Bool
hhGoodPhysicalThresholdStretchingClosed = true

periodicPVHHGoodOwnerEstimateConstructed : Bool
periodicPVHHGoodOwnerEstimateConstructed = false

hhGoodPhysicalThresholdStretchingClosedIsTrue :
  hhGoodPhysicalThresholdStretchingClosed ≡ true
hhGoodPhysicalThresholdStretchingClosedIsTrue = refl
